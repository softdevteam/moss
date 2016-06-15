

use std::rc::Rc;
use std::cell::RefCell;

use rustc::mir::repr as mir;
use rustc::mir::mir_map::MirMap;
use rustc::mir::repr::BinOp;
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use rustc::util::nodemap::DefIdMap;


use mossc::{Program, Function, OpCode};

use std::ops::{Deref};

use std::collections::BTreeMap;


//XXX: Is it better to store Tuple/NamedTuple struct on the stack or
// should we rather use references to them to keep the theme of 64 bit values.

#[derive(Clone, Debug)]
pub enum Address {
    StackLocal(usize),

    // (address in stack, address in vector)
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

    // Most data is loaded via pointers.
    // let x = 1;
    // let y = 2;

    Pointer(Address),

    Value(WrappedValue),


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
        if let StackData::Pointer(ref address) = *self {
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
    Usize(usize),
    Bool(bool),
    Address(Address),
    Tuple(WrappedTuple),
    Array(Vec<WrappedValue>),
    // NamedTuple(W_NamedTuple<'a, 'tcx>),
    // Function(&'a Function<'tcx>),
}

impl WrappedValue {
    fn unwrap_usize(&self) -> usize {
        if let WrappedValue::Usize(size) = *self {
            size
        } else {
            panic!("expected Usize got {:?}", self);
        }
    }

    fn unwrap_tuple(&mut self) -> &mut WrappedTuple {
        if let WrappedValue::Tuple(ref mut tuple) = *self {
            tuple
        } else {
            panic!("expected Tuple, got {:?}", self);
        }
    }
}

// TODO: implement getter and setter for tuple
#[derive(Clone, Debug)]
pub struct WrappedTuple {
    data: Vec<WrappedValue>,
}

impl WrappedTuple {
    fn with_size(size: usize) -> Self {
        let mut v = Vec::with_capacity(size);
        for _ in 0..size {
            v.push(WrappedValue::None);
        }

        WrappedTuple { data: v}
    }
}


// // [1, 2, 3]
// struct WrappedArray {
//     size: usize,
//     data: Vec<WrappedValue>
// }

// impl WrappedArray {
//     fn with_size(size: usize) -> Self {
//         WrappedArray { size: size, data: Vec::with_capacity(size) }
//     }
// }

// #[derive(Clone, Debug)]
// struct W_NamedTuple<'a, 'tcx:'a> {
//     data: &'a BTreeMap<&'a str, WrappedValue<'a, 'tcx>>,
// }

struct Interpreter<'p, 'a: 'p, 'cx: 'a> {
    program: &'p mut Program<'a, 'cx>,
    internals_map: &'p BTreeMap<DefId, String>,
    // loader: &'a ModulesLoader<'a, 'cx>,

    w_stack: WStack,
    w_stack_pointer: usize,

    stack: Stack,
}

type Stack = Vec<StackData>;
type WStack = Vec<WrappedValue>;

impl<'p, 'a, 'cx> Interpreter<'p, 'a, 'cx> {
    fn new(program: &'p mut Program<'a, 'cx>, internals_map: &'p BTreeMap<DefId, String>) -> Self {
        Interpreter {
            program: program,
            internals_map: internals_map,
            stack: Stack::new(),
            w_stack: WStack::new(),
            w_stack_pointer: 0
        }
    }

    // fn load_func(&'cx mut self, defid: DefId) -> &'b Function {
        // let krate = self.program.get(&defid.krate).unwrap();
        // krate.get(&defid.index.as_u32()).unwrap()
    // }

    fn run(&mut self, main: DefId) {
        let main_func = self.program.get_func(main);
        // {
            // let main_func = self.program.get_func(main);
        // }
        // let main_func = self.program.get_func(main);



        self.eval_func(&main_func);
    }

    // fn deref(&mut self, address: Address) -> WrappedValue {
        // match address {
            // Address::StackLocal(idx) => self.w_stack[idx].clone(),
            // _ => unimplemented!()
        // }
    // }

    fn to_value(&mut self, data: &StackData) -> WrappedValue {
        match data {
            &StackData::Value(ref v) => v.clone(),
            &StackData::Pointer(Address::StackLocal(ref other)) => {
                self.w_stack[*other].clone()
            },
            &StackData::Pointer(Address::StaticFunc(ref def_id)) => {
                WrappedValue::Address(Address::StaticFunc(def_id.clone()))
            },
            &StackData::Pointer(Address::StackComplex(a, b)) => {
                let tuple = self.w_stack[a].unwrap_tuple();
                tuple.data[b].clone()
            }
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
            // println!("Execute {:?}", opcode);
            match *opcode {
                OpCode::RETURN => {
                    break
                },

                OpCode::RETURN_POINTER => {},

                OpCode::LoadFunc(defid) => {
                    // let krate = self.program.get(&defid.krate).unwrap();
                    // let func = krate.get(&defid.index.as_u32()).unwrap();
                    self.stack.push(StackData::Pointer(Address::StaticFunc(defid)));
                },

                OpCode::ArgCount(size) => {
                    self.stack.push(StackData::ArgCount(size));
                },

                OpCode::Call => {
                    self.w_stack_pointer += func_stacksize;

                    let wrapped_address = self.pop_stack_value();
                    if let WrappedValue::Address(address) = wrapped_address {
                        if let Address::StaticFunc(def_id) = address {

                            if let Some(func_name) = self.internals_map.get(&def_id) {
                                match func_name.as_ref() {
                                    "out" => {
                                        let data = self.stack[self.stack.len()-2].clone();
                                        let val = self.to_value(&data);
                                        if let WrappedValue::Usize(n) = val {
                                            print!("{}", n as u8 as char);
                                        }
                                    },
                                    _ => unimplemented!()
                                }
                            }

                            let func = self.program.get_func(def_id);
                            self.eval_func(&func);

                            // let mir = self.loader.load_mir(defid);

                            // let mut fg = FuncGen::new(&self.loader.tcx, &self.loader.mir_map);
                            // fg.analyse(&*mir);

                            // let krate = self.program.krates.get(&defid.krate).unwrap();
                            // let func = krate.get(&defid.index.as_u32()).unwrap();
                            // let func = self.program.get(&defid).unwrap();
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
                    // let data = self.stack.pop().unwrap();
                    let data = self.pop_stack_value();
                    if let WrappedValue::Bool(b) = data {
                        if b {
                            pc = (pc as i32 + n) as usize;
                            continue;
                        }
                    } else {
                        panic!("expected bool got {:?}", data);
                    }
                },

                OpCode::TUPLE(n) => self.o_tuple(n),
                OpCode::TUPLE_ASSIGN(idx) => self.o_tuple_assign(idx),
                OpCode::TUPLE_GET(idx) => self.o_tuple_get(idx),
                OpCode::TUPLE_SET(idx) => self.o_tuple_set(idx),

                OpCode::VEC(n) => self.o_vec(n),
                OpCode::Repeat(n) => self.o_repeat(n),

                OpCode::AssignIndex => self.o_assign_index(),
                OpCode::GetIndex => self.o_get_index(),

                OpCode::Len => self.o_len(),

                OpCode::SignedInteger(n) => {
                    self.stack.push(StackData::Value(WrappedValue::I64(n)));
                },
                OpCode::UnsignedInteger(n) => {
                    self.stack.push(StackData::Value(WrappedValue::U64(n)));
                },
                OpCode::Usize(size) => {
                    self.stack.push(StackData::Value(WrappedValue::Usize(size)));
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
                            Address::StackLocal(_idx) => {
                                self.stack.push(StackData::Pointer(target));
                            },
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

                OpCode::Use => {
                    //XXX DO SOMETHING
                },

                _ => {
                    println!("TODO {:?}", opcode);
                    unimplemented!();
                },
            }
            pc += 1;
        }

        // println!("\nLocals: {:?}", self.w_stack);
    }

    fn o_vec(&mut self, size: usize) {
        let mut array: Vec<WrappedValue> = Vec::with_capacity(size);
        for _ in 0..size {
            array.push(WrappedValue::None)
        }

        for idx in (0..size).rev() {
            let val = self.pop_stack_value();
            array[idx] = val;
        }
        self.stack.push(StackData::Value(WrappedValue::Array(array)));
    }

    fn o_repeat(&mut self, size: usize) {
        let mut array: Vec<WrappedValue> = Vec::with_capacity(size);
        for _ in 0..size {
            array.push(WrappedValue::None)
        }

        let val = self.pop_stack_value();
        for idx in 0..size {
            array[idx] = val.clone();
        }

        self.stack.push(StackData::Value(WrappedValue::Array(array)));
    }

    fn o_len(&mut self) {
        let v = self.pop_stack_value();

        if let WrappedValue::Array(ref array) = v {
            self.stack.push(StackData::Value(WrappedValue::Usize(array.len())));
        } else {
            panic!("expected array got {:?}", v);
        }
    }

    fn o_get_index(&mut self) {
        let array_address = self.stack.pop().unwrap().unwrap_address();
        let index = self.pop_stack_value().unwrap_usize();

        let object = match array_address {
            Address::StackLocal(addr) => {
                &self.w_stack[addr]
            },
            Address::StackComplex(a, b) => {
                &self.w_stack[a].unwrap_tuple().data[b]
            },
            _ => unimplemented!(),
        };

        if let WrappedValue::Array(ref array) = *object {
            //XXX clone
            let val = array[index].clone();
            self.stack.push(StackData::Value(val));
        }
    }

    fn o_assign_index(&mut self) {
        let array_address = self.stack.pop().unwrap().unwrap_address();
        let index = self.pop_stack_value().unwrap_usize();
        let value = self.pop_stack_value();

        let mut obj = match array_address {
            Address::StackLocal(addr) => {
                &mut self.w_stack[addr]
            },
            Address::StackComplex(a, b) => {
                &mut self.w_stack[a].unwrap_tuple().data[b]
            }
            _ => unimplemented!(),
        };

        if let WrappedValue::Array(ref mut array) = *obj {
            array[index] = value;
        } else {
            unimplemented!()
        }

    }

    fn o_tuple(&mut self, size: usize) {
        self.stack.push(StackData::Value(WrappedValue::Tuple(WrappedTuple::with_size(size))));
    }

    fn o_tuple_set(&mut self, idx: usize) {
        let tuple_address = self.stack.pop().unwrap().unwrap_address();
        let value = self.pop_stack_value();

        match tuple_address {
            Address::StackLocal(addr) => {
                if let WrappedValue::Tuple(ref mut tuple) = self.w_stack[addr] {
                    tuple.data[idx] = value;
                }
            },
            _ => panic!("can not load tuple at {:?}", tuple_address),
        }

        // if let WrappedValue::Tuple(ref mut tuple) =  *t {
        //     tuple.data[idx] = value;
        // } else {
        //     panic!("Expected tuple found {:?}", wrapped_tuple);
        // }
    }

    fn o_tuple_assign(&mut self, idx: usize) {
        let value = self.pop_stack_value();
        let mut s_tuple = self.stack.last_mut().unwrap();

        if let StackData::Value(WrappedValue::Tuple(ref mut tuple)) = *s_tuple  {
            tuple.data[idx] = value;
        } else {
            panic!("Expected tuple found {:?}", s_tuple);
        }
    }

    fn o_tuple_get(&mut self, idx: usize) {
        // let s_tuple = self.pop_stack_value();
        match self.stack.pop().unwrap().unwrap_address() {
            Address::StackLocal(tuple_address) => {
                self.stack.push(StackData::Pointer(
                    Address::StackComplex(tuple_address, idx)));
            },
            _ => unimplemented!(),
        }
        // if let WrappedValue::Tuple(ref _wrapped_tuple) = s_tuple {
            //XXX: do we have to consider move semantics here?
            // let value = wrapped_tuple.data[idx].clone();
            // self.stack.push(StackData::Value(value));
        // } else {
            // panic!("Expected tuple found {:?}", s_tuple);
        // }

    }

    fn o_store_local(&mut self, idx: usize) {
        let v = self.stack.pop().unwrap();
        //XXXX
        let val = match v {
            StackData::Value(v) => v,
            StackData::Pointer(Address::StackLocal(other)) => {
                self.w_stack[other].clone()
            },
            StackData::Pointer(Address::StaticFunc(defid)) => {
                WrappedValue::Address(Address::StaticFunc(defid))
            },
            StackData::Pointer(Address::StackComplex(a, b)) => {
                let tuple = self.w_stack[a].unwrap_tuple();
                tuple.data[b].clone()
            },

            _ => panic!("should not store interpreter level object {:?}", v)
        };

        self.w_stack[self.w_stack_pointer + idx] = val;
    }

    fn o_load_local(&mut self, idx: usize) {
        // let val = &self.w_stack[self.w_stack_pointer + idx];
        // clone the pointer to the old value
        // self.stack.push(unwrap_value());
        self.stack.push(StackData::Pointer(Address::StackLocal(self.w_stack_pointer + idx)))
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
            (Usize(l), Usize(r)) => int_binops!(Usize, l, r),

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


// #[derive(Clone)]
// enum CachedMir<'mir, 'tcx: 'mir> {
//     Ref(&'mir mir::Mir<'tcx>),
//     Owned(Rc<mir::Mir<'tcx>>)
// }

// impl<'mir, 'tcx> Deref for CachedMir<'mir, 'tcx> {
//     type Target = mir::Mir<'tcx>;

//     fn deref(&self) -> &mir::Mir<'tcx> {
//         match *self {
//             CachedMir::Ref(ref mir) => mir,
//             CachedMir::Owned(ref mir) => mir,
//         }
//     }
// }

// struct ModulesLoader<'a, 'tcx: 'a> {
//     tcx: TyCtxt<'a, 'tcx, 'tcx>,
//     mir_cache: RefCell<DefIdMap<Rc<mir::Mir<'tcx>>>>,
//     mir_map: &'a MirMap<'tcx>,
// }

// impl<'a, 'tcx> ModulesLoader<'a, 'tcx> {
//     fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>, mir_map: &'a MirMap<'tcx>) -> Self {
//         ModulesLoader {
//             tcx: tcx,
//             mir_map: mir_map,
//             mir_cache: RefCell::new(DefIdMap())
//         }
//     }

//     fn load_mir(&self, def_id: DefId) -> CachedMir<'a, 'tcx> {
//         match self.tcx.map.as_local_node_id(def_id) {
//             Some(node_id) => CachedMir::Ref(self.mir_map.map.get(&node_id).unwrap()),
//             None => {
//                 let mut mir_cache = self.mir_cache.borrow_mut();
//                 if let Some(mir) = mir_cache.get(&def_id) {
//                     return CachedMir::Owned(mir.clone());
//                 }

//                 let cs = &self.tcx.sess.cstore;
//                 let mir = cs.maybe_get_item_mir(self.tcx, def_id).unwrap_or_else(|| {
//                     panic!("no mir for {:?}", def_id);
//                 });
//                 let cached = Rc::new(mir);
//                 mir_cache.insert(def_id, cached.clone());
//                 CachedMir::Owned(cached)
//             }
//         }
//     }
// }

pub fn interpret<'a, 'tcx>(
        program: &'a mut Program<'a, 'tcx>,
        main: DefId,
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
        map: &MirMap<'tcx>,
        internals: &BTreeMap<DefId, String>
        ){

    // let node_id = tcx.map.as_local_node_id(main).unwrap();
    // let mir = map.map.get(&node_id).unwrap();

    // let loader = ModulesLoader::new(tcx, map);
    // loader.load_mir(main);
    let mut interpreter = Interpreter::new(program, internals);

    interpreter.run(main);
}
