

use std::rc::Rc;
use std::cell::RefCell;

use rustc::mir::repr as mir;
use rustc::mir::mir_map::MirMap;
use rustc::mir::repr::BinOp;
use rustc::hir::def_id::DefId;
use rustc::ty::TyCtxt;
use rustc::util::nodemap::DefIdMap;


use mossc::{Program, Function, OpCode, Guard};

use std::ops::{Deref};

use std::collections::BTreeMap;


const HOT_LOOP: usize = 5;

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

    Frame(usize),
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


type Trace<'a> = Vec<OpCode<'a>>;

struct Interpreter<'p, 'a: 'p, 'cx: 'a> {
    program: &'p mut Program<'a, 'cx>,
    internals_map: &'p BTreeMap<DefId, String>,
    trace_counter: BTreeMap<usize, usize>,
    is_tracing: bool,
    loop_start: usize,
    active_trace: Trace<'a>,
    //map pc to traces
    traces: BTreeMap<usize, Rc<Trace<'a>>>,
    // loader: &'a ModulesLoader<'a, 'cx>,

    w_stack: WStack,
    w_stack_pointer: usize,
    w_stack_pointer_stack: Vec<usize>,
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
            w_stack_pointer: 0,
            trace_counter: BTreeMap::new(),
            is_tracing: false,
            loop_start: 0,
            active_trace: Vec::new(),
            traces: BTreeMap::new(),
            w_stack_pointer_stack: Vec::new(),
        }
    }

    fn run(&mut self, main: DefId) {
        let main_func = self.program.get_func(main);
        self.eval_func(main_func);

        println!("{} traces generated", self.traces.len());
        println!("{:?}", self.traces);
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

    fn eval_trace(&mut self, pc: usize) -> Option<Guard<'a>> {
        let trace = self.traces.get(&pc).unwrap().clone();

        let mut frame_size = None;
        loop {
            for opcode in &*trace {
                // println!("Trace Execute {:?} | SP {}", opcode, self.w_stack_pointer);
                match *opcode {
                    OpCode::Guard(ref guard) => {
                        let failed = self.o_guard(guard);
                        if failed {
                            return Some(guard.clone());
                        }
                    },

                    OpCode::Debug(in_pc) => {},

                    OpCode::StackFrame(stack_size) => {
                        self.o_stackframe(stack_size);
                        frame_size = Some(stack_size);
                    },

                    OpCode::Use => {},

                    OpCode::Call => {
                        self.w_stack_pointer_stack.push(self.w_stack_pointer);
                        self.w_stack_pointer += frame_size.unwrap();

                        let wrapped_address = self.pop_stack_value();
                        if let WrappedValue::Address(address) = wrapped_address {
                            if let Address::StaticFunc(def_id) = address {

                                if let Some(func_name) = self.internals_map.get(&def_id) {
                                    match func_name.as_ref() {
                                        "out" => {
                                            let data = self.stack[self.stack.len()-2].clone();
                                            let val = self.to_value(&data);
                                            if let WrappedValue::Usize(n) = val {
                                                // print!("{}", n as u8 as char);
                                                println!("BF: {}", n);
                                            }
                                        },
                                        "print" => {
                                            let data = self.stack[self.stack.len()-2].clone();
                                            let val = self.to_value(&data);
                                            if let WrappedValue::Usize(n) = val {
                                                print!("{}", n as u8 as char);
                                            }
                                        },

                                        _ => {}
                                    };
                                }
                            }
                        }
                    },

                    OpCode::ArgCount(size) => {
                        self.stack.push(StackData::ArgCount(size));
                    },

                    OpCode::LoadFunc(defid) => {
                        self.stack.push(StackData::Pointer(Address::StaticFunc(defid)));
                    },


                    OpCode::RETURN => {
                        // println!("{:?} {:?}", self.w_stack_pointer, stack_pointers);
                        // let frame_size = stack_pointers.pop().unwrap();
                        // self.w_stack_pointer -= frame_size;
                        let old_size = self.w_stack_pointer;
                        self.o_return();
                        frame_size = Some(old_size - self.w_stack_pointer);
                    },

                    OpCode::RETURN_POINTER => {},


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
                    _ => {
                        println!("UNHANDLED {:?}", opcode);
                    }
                }
            }
        }
        None
    }

    //aquire space on the stack ahead of the current stack pointer
    fn o_stackframe(&mut self, func_stacksize: usize) {

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
        } else {
            // println!("expected ArgCount, got {:?}", self.stack.last());
        }
    }

    fn o_return(&mut self) {
        // can't return from main
        if self.w_stack_pointer != 0 {
            let old_pointer = self.w_stack_pointer_stack.pop().unwrap();
            self.w_stack_pointer = old_pointer;
        }
    }

    fn o_guard(&mut self, guard: &Guard) -> bool {
        let data = self.pop_stack_value();
        if let WrappedValue::Bool(b) = data {
            // println!("guard({}) == {}", expected, bool);
            return b != guard.expected;
            // if b != guard.expected {
                // println!("recover to {:?}[{}]", guard.recovery, guard.pc);
                // panic!("guard fail");
            // }
        } else {
            panic!("expected bool, got {:?}", data);
        }
    }

    fn eval_func(&mut self, func: Rc<Function<'a>>) {

        let mut func = func;
        let mut pc: usize = 0;
        let mut func_stacksize = None;

        loop {

            let opcode = &func[pc].clone();
            // println!("{:?} [{}]", self.w_stack[self.w_stack_pointer], self.w_stack_pointer);
            // println!("[{}] --{:?}", self.w_stack.len(), self.w_stack_pointer, );
            // println!("");
            println!("Execute {:?}| SP {}", opcode, self.w_stack_pointer);

            if self.is_tracing {
                match *opcode {
                    OpCode::JUMP(..) | OpCode::JUMP_REL(..) => {},

                    OpCode::JUMP_IF(..) | OpCode::JUMP_REL_IF(..) => {
                        let wrapped = self.stack.last().unwrap().clone();
                        let val = self.to_value(&wrapped);
                        if let WrappedValue::Bool(b) = val {
                            self.active_trace.push(
                                OpCode::Guard(Guard {
                                    expected: b,
                                    recovery: func.clone(),
                                    pc: pc,
                                }));
                        } else {
                            panic!("expected bool, got {:?}", val);
                        }
                    },

                    _ => {
                        self.active_trace.push(opcode.clone());
                    }
                }
            }

            match *opcode {
                OpCode::StackFrame(stack_size) => {
                    func_stacksize = Some(stack_size);
                    self.o_stackframe(stack_size);
                },

                OpCode::RETURN => {
                    self.o_return();
                    break
                },

                OpCode::RETURN_POINTER => {},

                OpCode::LoadFunc(defid) => {
                    self.stack.push(StackData::Pointer(Address::StaticFunc(defid)));
                },

                OpCode::ArgCount(size) => {
                    self.stack.push(StackData::ArgCount(size));
                },

                OpCode::Call => {
                    // self.w_stack_pointer += func_stacksize.unwrap();

                    // mark frame on stack
                    // self.stack.push(StackData::Frame(self.w_stack_pointer));
                    self.w_stack_pointer_stack.push(self.w_stack_pointer);
                    self.w_stack_pointer += func_stacksize.unwrap();

                    let wrapped_address = self.pop_stack_value();
                    if let WrappedValue::Address(address) = wrapped_address {
                        if let Address::StaticFunc(def_id) = address {

                            if let Some(func_name) = self.internals_map.get(&def_id) {
                                match func_name.as_ref() {
                                    "out" => {
                                        let data = self.stack[self.stack.len()-2].clone();
                                        let val = self.to_value(&data);
                                        if let WrappedValue::Usize(n) = val {
                                            // print!("{}", n as u8 as char);
                                            println!("BF: {}", n);
                                        }
                                    },
                                    "print" => {
                                        let data = self.stack[self.stack.len()-2].clone();
                                        let val = self.to_value(&data);
                                        if let WrappedValue::Usize(n) = val {
                                            // print!("{}", n as u8 as char);
                                            print!("{}", n as u8 as char);
                                        }
                                    },
                                    "met_merge_point" => {
                                        let data = self.stack[self.stack.len()-2].clone();
                                        let val = self.to_value(&data);

                                        if let WrappedValue::Usize(in_pc) = val {
                                            // println!("met_merge_point {:?}", in_pc);
                                            if self.traces.contains_key(&in_pc) {
                                                if let Some(guard) = self.eval_trace(in_pc) {
                                                    func = guard.recovery;
                                                    pc = guard.pc;
                                                    self.stack.push(StackData::Value(WrappedValue::Bool(!guard.expected)));
                                                    // println!("FAILED IN {:?}", func[pc]);
                                                    continue;
                                                }
                                            } else if !self.is_tracing {
                                                let count = {
                                                    let count = self.trace_counter.entry(in_pc).or_insert(0);
                                                    *count += 1;
                                                    *count
                                                };
                                                // println!("COUNT {:?} {}", in_pc, count);
                                                if count > HOT_LOOP {
                                                    self.trace_counter.clear();
                                                    self.is_tracing = true;
                                                    self.loop_start = in_pc;
                                                }
                                            } else {
                                                // self.active_trace.push(OpCode::Debug(in_pc));
                                                if in_pc == self.loop_start {
                                                    // println!("trace finished");
                                                    // println!("{:?}", self.active_trace);
                                                    self.is_tracing = false;
                                                    self.traces.insert(in_pc, Rc::new(self.active_trace.clone()));
                                                }
                                            }
                                        } else {
                                            panic!("expected usize got {:?}", val);
                                        }
                                    },
                                    _ => unimplemented!()
                                }
                            }

                            let func = self.program.get_func(def_id);
                            self.eval_func(func);
                        } else {
                            panic!("Expected func got {:?}", address);
                        }
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

            (l, r) => {
                println!("{:?} {:?}", l, r);
                unimplemented!();
            }
        });
        self.stack.push(val);

    }
}

pub fn interpret<'a, 'tcx>(
        program: &'a mut Program<'a, 'tcx>,
        main: DefId,
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
        map: &MirMap<'tcx>,
        internals: &BTreeMap<DefId, String>
        ){

    let mut interpreter = Interpreter::new(program, internals);

    interpreter.run(main);
}
