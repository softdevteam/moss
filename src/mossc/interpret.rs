
use std::collections::BTreeMap;
use std::ops::{Deref, DerefMut};

use mossc::{Program, Function, OpCode};

use rustc::mir::mir_map::MirMap;
use rustc::ty::TyCtxt;
use rustc::hir::def_id::DefId;

use rustc::mir::repr::{BinOp, Literal};


//XXX: Is it better to store Tuple/NamedTuple struct on the stack or
// should we rather use references to them to keep the theme of 64 bit values.

#[derive(Clone, Debug)]
pub enum Address {
    StackLocal(usize),

    // address in tuple, address in vector
    StackComplex(usize, usize),

    StaticFunc(DefId),
}


#[derive(Clone, Debug)]
pub struct StackCell {
    address: Address,
    value: WrappedValue,
}

// impl<'a, 'tcx> Deref for StackCell<'a, 'tcx> {
//     type Target = WrappedValue<'a, 'tcx>;

//     fn deref<'b>(&'b self) -> &'b WrappedValue<'a, 'tcx> {
//         &self.cell
//     }
// }

// impl<'a, 'tcx> DerefMut for StackCell<'a, 'tcx> {
//     fn deref_mut<'b>(&'b mut self) -> &'b mut WrappedValue<'a, 'tcx> {
//         &mut self.value
//     }
// }

#[derive(Clone, Debug)]
pub enum StackData {
    None,

    // Flag is used for JUMP_IF, WrappedValue::Bool eventually maps to Flag
    Flag(bool),
    Value(WrappedValue),
    Tuple(WrappedTuple),

    Address(Address),
    // Value(StackCell<'a, 'tcx>),
    ArgCount(usize),
}

impl StackData {
    fn unwrap_value(&self) -> WrappedValue {
        if let StackData::Value(ref value) = *self {
            value.clone()
        } else {
            panic!("expected Value found {:?}", self);
        }
    }

    fn unwrap_address(&self) -> Address {
        if let StackData::Address(ref address) = *self {
            address.clone()
        } else {
            panic!("expected Address found {:?}", self);
        }
    }
}

#[derive(Clone, Debug)]
pub enum WrappedValue {
    None,
    StackReference(usize),
    I64(i64),
    U64(u64),
    Bool(bool),
    Address(Address),
    // Tuple(WrappedTuple<'a, 'tcx>),
    // NamedTuple(W_NamedTuple<'a, 'tcx>),
    // Function(&'a Function<'tcx>),
}


// TODO: implement getter and setter for tuple
#[derive(Clone, Debug)]
pub struct WrappedTuple {
    data: Vec<WrappedValue>,
}

impl WrappedTuple {
    fn with_size(size: usize) -> Self {
        let mut v = Vec::with_capacity(size);
        for idx in 0..size {
            v.push(WrappedValue::None);
        }

        WrappedTuple { data: v}
    }
}

// #[derive(Clone, Debug)]
// struct W_NamedTuple<'a, 'tcx:'a> {
//     data: &'a BTreeMap<&'a str, WrappedValue<'a, 'tcx>>,
// }

struct Interpreter<'cx> {
    program: &'cx Program<'cx>,

    w_stack: WStack,
    w_stack_pointer: usize,

    stack: Stack,
}

type Stack = Vec<StackData>;
type WStack = Vec<WrappedValue>;

impl<'cx> Interpreter<'cx> {
    fn new(program: &'cx Program<'cx>) -> Self {
        Interpreter { program: program, stack: Stack::new(), w_stack: WStack::new(), w_stack_pointer: 0 }
    }

    // fn load_func(&'cx mut self, defid: DefId) -> &'b Function {
        // let krate = self.program.get(&defid.krate).unwrap();
        // krate.get(&defid.index.as_u32()).unwrap()
    // }

    fn run(&mut self, main: DefId) {
        let krate = self.program.get(&main.krate).unwrap();
        let main_func = krate.get(&main.index.as_u32()).unwrap();
        // let main_func = self.load_func(main);
        self.eval_func(main_func);
    }

    // fn deref(&mut self, address: Address) -> WrappedValue {
        // match address {
            // Address::StackLocal(idx) => self.w_stack[idx].clone(),
            // _ => unimplemented!()
        // }
    // }

    fn to_value(&self, data: &StackData) -> WrappedValue {
        match data {
            &StackData::Value(ref v) => v.clone(),
            &StackData::Address(Address::StackLocal(ref other)) => {
                self.w_stack[*other].clone()
            },
            &StackData::Address(Address::StaticFunc(ref def_id)) => {
                WrappedValue::Address(Address::StaticFunc(def_id.clone()))
            },
            _ => panic!("should not load interpreter level object {:?}", data)
        }
    }

    fn pop_stack_value(&mut self) -> WrappedValue {
        let something = self.stack.pop().unwrap();
        self.to_value(&something)
    }

    fn eval_func(&mut self, func: &Function) {
        let func_stacksize = match func[0] {
            OpCode::StackFrame(s) => s,
            _ => panic!("{:?}", "Unexpected Opcode")
        };

        // aquire space on the stack
        for _ in self.w_stack.len() .. self.w_stack_pointer + func_stacksize {
            self.w_stack.push(WrappedValue::None);
        }

        if let Some(&StackData::ArgCount(n)) = self.stack.last() {
            println!("D: {:?}", self.stack);
            self.stack.pop();
            for i in 0..n {
                let something = self.stack.pop().unwrap();
                let val = self.to_value(&something);

                self.w_stack[self.w_stack_pointer + i] = val;
            }
        }
        let mut pc: usize = 1;
        loop {

            let opcode = &func[pc];
            println!("Execute {:?}", opcode);
            match *opcode {
                OpCode::RETURN => {
                    break
                },

                OpCode::RETURN_POINTER => {},

                OpCode::LoadFunc(defid) => {
                    // let krate = self.program.get(&defid.krate).unwrap();
                    // let func = krate.get(&defid.index.as_u32()).unwrap();
                    self.stack.push(StackData::Address(Address::StaticFunc(defid)));
                },

                OpCode::ArgCount(size) => {
                    self.stack.push(StackData::ArgCount(size));
                },

                OpCode::Call => {
                    self.w_stack_pointer += func_stacksize;

                    // let address = self.stack.pop().unwrap().unwrap_address();
                    let wrapped_address = self.pop_stack_value();
                    if let WrappedValue::Address(address) = wrapped_address {
                        if let Address::StaticFunc(defid) = address {
                            let krate = self.program.get(&defid.krate).unwrap();
                            let func = krate.get(&defid.index.as_u32()).unwrap();
                            self.eval_func(func);
                        } else {
                            panic!("Expected func got {:?}", address);
                        }
                        self.w_stack_pointer -= func_stacksize;
                    } else {
                        panic!("excpected address got {:?}", wrapped_address);
                    }
                },

                OpCode::JUMP_REL(n) => {
                    pc = (pc as i32 + n) as usize;
                    continue
                },

                OpCode::JUMP_REL_IF(n) => {
                    if let StackData::Flag(b) = self.stack.pop().unwrap() {
                        if b {
                            pc = (pc as i32 + n) as usize;
                            continue;
                        }
                    } else {
                        panic!("expected bool");
                    }
                },

                OpCode::TUPLE(n) => self.o_tuple(n),
                OpCode::TUPLE_ASSIGN(idx) => self.o_tuple_assign(idx),
                OpCode::TUPLE_GET(idx) => self.o_tuple_get(idx),

                OpCode::SignedInteger(n) => {
                    self.stack.push(StackData::Value(WrappedValue::I64(n)));
                },
                OpCode::UnsignedInteger(n) => {
                    self.stack.push(StackData::Value(WrappedValue::U64(n)));
                },
                OpCode::Bool(b) => {
                    self.stack.push(StackData::Value(WrappedValue::Bool(b)));
                },


                OpCode::StoreLocal(idx) => self.o_store_local(idx),
                OpCode::LoadLocal(idx) => self.o_load_local(idx),
                OpCode::BINOP(op) => self.o_binop(op),

                OpCode::BORROW(..) => {
                    let address = self.stack.pop().unwrap().unwrap_address();
                    self.stack.push(StackData::Value(
                        WrappedValue::Address(address)))
                },

                OpCode::DEREF => {
                    let wrapped_target = self.pop_stack_value();
                    if let WrappedValue::Address(target) = wrapped_target {
                        match target {
                            Address::StackLocal(idx) => {
                                let val = self.w_stack[idx].clone();
                                self.stack.push(StackData::Value(val));
                            }
                            _ => unimplemented!()
                        }
                    }  else {
                        panic!("can't resolve {:?}", wrapped_target);
                    }
                },

                OpCode::DEREF_STORE => {
                    let wrapped_target = self.pop_stack_value();
                    let value = self.pop_stack_value();

                    if let WrappedValue::Address(target) = wrapped_target {
                        match target {
                            Address::StackLocal(idx) => {
                                self.w_stack[idx] = value;
                            }
                            _ => unimplemented!()
                        }
                    } else {
                        panic!("can't resolve {:?}", wrapped_target);
                    }
                },

                _ => {
                    println!("TODO {:?}", opcode);
                    // unimplemented!();
                },
            }
            pc += 1;
        }
        println!("\nLocals: {:?}", self.w_stack);
    }

    fn o_tuple(&mut self, size: usize) {
        self.stack.push(StackData::Tuple(WrappedTuple::with_size(size)));
    }

    fn o_tuple_assign(&mut self, idx: usize) {
        let value = self.stack.pop().unwrap().unwrap_value();
        let mut s_tuple = self.stack.last_mut().unwrap();

        if let StackData::Tuple(ref mut WrappedTuple) = *s_tuple  {
            WrappedTuple.data[idx] = value;
        } else {
            panic!("Expected tuple found {:?}", s_tuple);
        }
    }

    fn o_tuple_get(&mut self, idx: usize) {
        let s_tuple = self.stack.pop().unwrap();
        if let StackData::Tuple(ref WrappedTuple) = s_tuple {
            //XXX: do we have to consider move semantics here?
            let value = WrappedTuple.data[idx].clone();
            self.stack.push(StackData::Value(value));
        } else {
            panic!("Expected tuple found {:?}", s_tuple);
        }
    }

    fn o_store_local(&mut self, idx: usize) {
        let v = self.stack.pop().unwrap();
        //XXXX
        let val = match v {
            StackData::Value(v) => v,
            StackData::Address(Address::StackLocal(other)) => {
                self.w_stack[other].clone()
            },
            StackData::Address(Address::StaticFunc(defid)) => {
                WrappedValue::Address(Address::StaticFunc(defid))
            },
            _ => panic!("should not store interpreter level object {:?}", v)
        };

        self.w_stack[self.w_stack_pointer + idx] = val;
    }

    fn o_load_local(&mut self, idx: usize) {
        // let val = &self.w_stack[self.w_stack_pointer + idx];
        // clone the pointer to the old value
        // self.stack.push(unwrap_value());
        self.stack.push(StackData::Address(Address::StackLocal(self.w_stack_pointer + idx)))
    }

    fn o_binop(&mut self, op: BinOp) {
        use self::WrappedValue::*;
        use rustc::mir::repr::BinOp::*;

        let right = self.pop_stack_value();
        let left = self.pop_stack_value();

        // copied from miri
        macro_rules! int_binops {
            ($v:ident, $l:ident, $r:ident) => ({
                match op {
                    Add    => $v($l + $r),
                    Sub    => $v($l - $r),
                    Mul    => $v($l * $r),
                    Div    => $v($l / $r),
                    Rem    => $v($l % $r),
                    BitXor => $v($l ^ $r),
                    BitAnd => $v($l & $r),
                    BitOr  => $v($l | $r),

                    // TODO(solson): Can have differently-typed RHS.
                    Shl => $v($l << $r),
                    Shr => $v($l >> $r),

                    Eq => Bool($l == $r),
                    Ne => Bool($l != $r),
                    Lt => Bool($l < $r),
                    Le => Bool($l <= $r),
                    Gt => Bool($l > $r),
                    Ge => Bool($l >= $r),
                }
            })
        }


        let val = StackData::Value(match(left, right) {
            (I64(l), I64(r)) => int_binops!(I64, l, r),
            (U64(l), U64(r)) => int_binops!(U64, l, r),

            // copied from miri
            (Bool(l), Bool(r)) => {
                Bool(match op {
                    Eq => l == r,
                    Ne => l != r,
                    Lt => l < r,
                    Le => l <= r,
                    Gt => l > r,
                    Ge => l >= r,
                    BitOr => l | r,
                    BitXor => l ^ r,
                    BitAnd => l & r,
                    Add | Sub | Mul | Div | Rem | Shl | Shr =>
                        panic!("invalid binary operation on booleans: {:?}", op),
                })

            },

            _ => unimplemented!()
        });
        self.stack.push(val);

    }
}


pub fn interpret(program: &Program, main: DefId, tcx: &TyCtxt, map: &MirMap){
    let node_id = tcx.map.as_local_node_id(main).unwrap();
    let mir = map.map.get(&node_id).unwrap();
    let mut interpreter = Interpreter::new(program);
    interpreter.run(main);
}
