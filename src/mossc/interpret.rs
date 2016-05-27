
use std;
use std::collections::BTreeMap;

use mossc::{Program, Function, OpCode};

use rustc::mir::mir_map::MirMap;
use rustc::ty::TyCtxt;
use rustc::hir::def_id::DefId;

use rustc::mir::repr::{Constant, BinOp, Literal};
use rustc::middle::const_val::ConstVal;

use rustc_const_math::ConstInt;


//XXX: Is it better to store Tuple/NamedTuple struct on the stack or
// should we rather use references to them to keep the theme of 64 bit values.

#[derive(Clone, Debug)]
enum StackData<'a, 'tcx:'a> {
    None,
    Const(&'a Constant<'tcx>),
    I64(i64),
    U64(u64),
    Bool(bool),
    Tuple(W_Tuple<'a, 'tcx>),
    NamedTuple(W_NamedTuple<'a, 'tcx>)
}


// TODO: implement getter and setter for tuple
#[derive(Clone, Debug)]
struct W_Tuple<'a, 'tcx:'a> {
    data: Vec<StackData<'a, 'tcx>>,
}

impl<'a, 'tcx> W_Tuple<'a, 'tcx> {
    fn with_size(size: usize) -> Self {
        let mut v = Vec::with_capacity(size);
        for _ in 0..size {
            v.push(StackData::None);
        }

        W_Tuple { data: v}
    }
}

#[derive(Clone, Debug)]
struct W_NamedTuple<'a, 'tcx:'a> {
    data: &'a BTreeMap<&'a str, StackData<'a, 'tcx>>,
}

struct Interpreter<'cx> {
    program: &'cx Program<'cx>,

    w_stack: Stack<'cx>,
    w_stack_pointer: usize,

    stack: Stack<'cx>,
}

type Stack<'tcx> = Vec<StackData<'tcx, 'tcx>>;

impl<'cx> Interpreter<'cx> {
    fn new(program: &'cx Program<'cx>) -> Self {
        Interpreter { program: program, stack: Stack::new(), w_stack: Stack::new(), w_stack_pointer: 0 }
    }

    fn run(&mut self, main: DefId) {
        let krate = self.program.get(&main.krate).unwrap();
        let main_func = krate.get(&main.index.as_u32()).unwrap();
        self.eval_func(main_func);
    }

    fn eval_func(&mut self, func: &Function) {
        let func_stacksize = match func[0] {
            OpCode::StackFrame(s) => s,
            _ => panic!("{:?}", "Unexpected Opcode")
        };

        // aquire space on the stack
        for _ in self.w_stack.len() .. self.w_stack_pointer + func_stacksize {
            self.w_stack.push(StackData::None);
        }
        self.w_stack_pointer += func_stacksize;

        let mut pc: usize = 1;
        loop {
            let opcode = &func[pc];
            println!("Execute {:?}", opcode);
            match *opcode {
                OpCode::RETURN => {
                    self.w_stack_pointer -= func_stacksize;
                    break
                },
                OpCode::JUMP_REL(n) => { pc = (pc as i32 + n) as usize; continue },

                OpCode::JUMP_REL_IF(n) => {
                    if let StackData::Bool(b) = self.stack.pop().unwrap() {
                        if b {
                            pc = (pc as i32 + n) as usize;
                            continue;
                        }
                    } else {
                        panic!("expected bool");
                    }
                }
                // OpCode::Const(ref const_val) => self.o_const( &mut stack, const_val ),

                OpCode::TUPLE(n) => self.o_tuple(n),
                OpCode::TUPLE_ASSIGN(idx) => self.o_tuple_assign(idx),

                OpCode::SignedInteger(n) => { self.stack.push(StackData::I64(n)) },
                OpCode::UnsignedInteger(n) => { self.stack.push(StackData::U64(n)) },
                OpCode::Bool(b) => { self.stack.push(StackData::Bool(b)) },

                OpCode::StoreLocal(idx) => self.o_store(idx),
                OpCode::LoadLocal(idx) => self.o_load(idx),
                OpCode::BINOP(op) => self.o_binop(op),


                _ => println!("TODO {:?}", opcode)
            }
            pc += 1;
        }
        println!("Locals: {:?}", self.w_stack);
    }

    fn o_tuple(&mut self, size: usize) {
        self.stack.push(StackData::Tuple(W_Tuple::with_size(size)));
    }

    fn o_tuple_assign(&mut self, idx: usize) {
        let value = self.stack.pop().unwrap();
        let mut s_tuple = self.stack.pop().unwrap();

        if let StackData::Tuple(ref mut w_tuple) = s_tuple  {
            w_tuple.data[idx] = value;
        } else {
            panic!("Expected tuple found {:?}", s_tuple);
        }

        self.stack.push(s_tuple);
    }

    fn o_const(&mut self, const_val: &'cx Constant<'cx>) {
        self.stack.push(StackData::Const(const_val));
    }

    fn o_store(&mut self, idx: usize) {
        let val = self.stack.pop().unwrap();
        self.w_stack[idx] = val;
    }

    fn o_load(&mut self, idx: usize) {
        let val = &self.w_stack[idx];
        // clone the pointer to the old value
        self.stack.push(val.clone());
    }

    fn o_binop(&mut self, op: BinOp) {
        let right = self.stack.pop().unwrap();
        let left = self.stack.pop().unwrap();

        self.unpack(&left);
        match op {
            BinOp::Add => {
                match (left, right) {
                    (StackData::I64(left), StackData::I64(right)) => {
                        self.stack.push(StackData::I64(left + right ));
                    },
                    _ => unimplemented!(),
                }
            },
            BinOp::Lt => {
                match (left, right) {
                    (StackData::I64(left), StackData::I64(right)) => {
                        self.stack.push(StackData::Bool(left < right));
                    },
                    _ => unimplemented!(),
                }
            }
            _ => panic!("unsoported binop {:?}", op)
        }
    }

    fn unpack(&self, value: &StackData) {
        if let StackData::Const(constval) = *value {
            if let Literal::Value{ref value} = constval.literal {
                if let ConstVal::Integral(boxed) = *value {
                    if let ConstInt::I32(n) = boxed {
                        println!("unpacked {:?}", n);
                    }
                }
            }
            // if let &ConstVal{ } = constval.literal {
            // }
        }
    }

}

fn add<T: std::ops::Add>(a: T, b: T) -> T::Output {
    a + b
}

pub fn interpret(program: &Program, main: DefId, tcx: &TyCtxt, map: &MirMap){

    let node_id = tcx.map.as_local_node_id(main).unwrap();
    let mir = map.map.get(&node_id).unwrap();
    // let node = tcx.map.get_if_local(main).unwrap();
    // println!("{:?}", map.map);
    // println!("{:?}", main);
    // tcx.map.get(main)
    // let item = map.map.get(&main).unwrap();
    // let item = tcx.map.expect_item(main.index.as_u32());
    // let x = [u32; mir.var_decls.len()];
    // println!("Len of vars {:?}", mir.var_decls.len());
    // println!("Len of tmps {:?}", mir.temp_decls.len());
    // println!("Len of args {:?}", mir.arg_decls.len());

    // let vars: Vec<u32> = Vec::with_capacity(
    //     mir.var_decls.len() + mir.temp_decls.len() + mir.arg_decls.len());
    // println!("{:?}", vars);
    // println!("{:?}", main);
    let mut interpreter = Interpreter::new(program);
    interpreter.run(main);
}