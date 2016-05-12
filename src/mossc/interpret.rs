
use std;

use mossc::{Program, Function, OpCode};

use rustc::mir::mir_map::MirMap;
use rustc::ty::TyCtxt;
use rustc::hir::def_id::DefId;

use rustc::mir::repr::{Constant, BinOp, Literal};
use rustc::middle::const_val::ConstVal;

use rustc_const_math::ConstInt;

#[derive(Clone, Debug)]

enum StackData<'a, 'tcx:'a> {
    None,
    Const(&'a Constant<'tcx>),
    I64(i64),
    U64(u64),
    Bool(bool),
}


struct Interpreter<'cx> {
    program: &'cx Program<'cx>,
}

type Stack<'tcx> = Vec<StackData<'tcx, 'tcx>>;

impl<'cx> Interpreter<'cx> {
    fn run(&mut self, main: DefId) {
        let krate = self.program.get(&main.krate).unwrap();
        let main_func = krate.get(&main.index.as_u32()).unwrap();
        self.eval_func(main_func);
    }

    fn eval_func(&mut self, func: &Function) {
        let stacksize = match func[0] {
            OpCode::StackFrame(s) => s,
            _ => panic!("{:?}", "Unexpected Opcode")
        };

        let mut locals: Vec<StackData> = vec![StackData::None; stacksize];
        let mut stack: Vec<StackData> = Vec::new();
        let mut pc: usize = 1;
        loop {
            let opcode = &func[pc];
            // println!("Execute {:?}", opcode);
            match *opcode {
                OpCode::RETURN => break,
                OpCode::JUMP_REL(n) => { pc = (pc as i32 + n) as usize; continue },
                // OpCode::Const(ref const_val) => self.o_const( &mut stack, const_val ),

                OpCode::SignedInteger(n) => { stack.push(StackData::I64(n)) },
                OpCode::UnsignedInteger(n) => { stack.push(StackData::U64(n)) },
                OpCode::Bool(b) => { stack.push(StackData::Bool(b)) },

                OpCode::StoreLocal(idx) => self.o_store( &mut stack, &mut locals, idx),
                OpCode::LoadLocal(idx) => self.o_load( &mut stack, &mut locals, idx),
                OpCode::BINOP(op) => self.o_binop( &mut stack, &mut locals, op),
                _ => println!("TODO {:?}", opcode)
            }
            pc += 1;
        }
        println!("Locals: {:?}", locals);
    }

    fn o_const<'this, 'tcx>(&mut self, stack: &'this mut Vec<StackData<'tcx, 'tcx>>, const_val: &'tcx Constant<'tcx>) {
        stack.push(StackData::Const(const_val));
    }

    fn o_store<'this, 'tcx>(&mut self, stack: &'this mut Stack<'tcx>, locals: &'this mut Stack<'tcx>, idx: usize) {
        let val = stack.pop().unwrap();
        locals[idx] = val;
    }

    fn o_load<'this, 'tcx>(&mut self, stack: &'this mut Stack<'tcx>, locals: &'this mut Stack<'tcx>, idx: usize) {
        let val = &locals[idx];
        // clone the pointer to the old value
        stack.push(val.clone());
    }

    fn o_binop<'this, 'tcx>(&mut self, stack: &'this mut Stack<'tcx>, locals: &'this mut Stack<'tcx>, op: BinOp) {
        let left = stack.pop().unwrap();
        let right = stack.pop().unwrap();

        self.unpack(&left);
        match op {
            BinOp::Add => {
                match (left, right) {
                    (StackData::I64(left), StackData::I64(right)) => {
                        stack.push(StackData::I64(left + right ));
                    }
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
    let mut interpreter = Interpreter{ program: program };
    interpreter.run(main);
}