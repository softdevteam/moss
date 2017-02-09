
// TODO: STACK
// There are two different stacks, the interpreter level stack (push and pop)
// and the user space stack (stack vs heap).

// How are aggregates saved on the stac? e.g. `let x = (1, 2);`

// TODO: Hack an output function.

use std::collections::BTreeMap;

pub use rustc::mir::repr::BorrowKind;

pub use rustc::mir::repr::{
    BasicBlock, BasicBlockData, Mir,
    BinOp, Constant, Literal, Operand,
    Lvalue, Rvalue,
    Statement, StatementKind, Terminator, TerminatorKind,
    ProjectionElem, AggregateKind,
    Field, CastKind
};

use rustc::mir::mir_map::MirMap;
use rustc::middle::const_val::ConstVal;

use rustc::hir::map::Node;
use rustc::hir::def_id::DefId;

use rustc::ty::{TyCtxt, AdtKind, VariantKind};

use rustc_const_math::{Us32, Us64};

use std::ops::{Deref, DerefMut};

use std::rc::Rc;

use rustc_data_structures::indexed_vec::Idx;


// use std::cell::RefCell;
// use rustc_const_math::ConstInt;
// use syntax::parse::token::InternedString;

pub mod interpret;

pub type Function<'tcx> = Vec<OpCode<'tcx>>;

// pub type KrateTree<'a> = BTreeMap<u32, BTreeMap<u32, Function<'a>>>;
pub type KrateTree<'a> = BTreeMap<DefId, Rc<Function<'a>>>;
//Program: krate_id -> node_id -> Function
// pub type Program<'a> = BTreeMap<u32, BTreeMap<u32, Function<'a>>>;

pub struct Program<'a, 'tcx: 'a> {
    context: &'a Context<'a, 'tcx>,
    pub krates: KrateTree<'a>
}

impl<'a, 'tcx> Program<'a, 'tcx> {
    fn new(context: &'a Context<'a, 'tcx>) -> Program<'a, 'tcx> {
        Program {context: context, krates: BTreeMap::new() }
    }

    fn get_func<'b>(&'b mut self, def_id: DefId) -> Rc<Function<'a>> {
        let context = &self.context;

        self.krates.entry(def_id).or_insert_with(|| {
            // println!("load function {:?}", def_id);
            let cs = &context.tcx.sess.cstore;
            let mir = cs.maybe_get_item_mir(context.tcx, def_id).unwrap_or_else(||{
                panic!("no mir for {:?}", def_id);
            });
            Rc::new(context.mir_to_bytecode(&mir))
        }).clone()
    }
}

// impl<'a, 'tcx> Deref for Program<'a, 'tcx> {
//     type Target = KrateTree<'a>;

//     fn deref(&self) -> &KrateTree<'a> {
//         &self.krates
//     }
// }

// impl<'a, 'tcx> DerefMut for Program<'a, 'tcx> {

//     fn deref_mut<'b>(&'b mut self) -> &'b mut KrateTree<'a> {
//         &mut self.krates
//     }
// }

#[derive(Debug, Clone)]
pub enum Var {
    Arg,
    Var,
    Tmp,
}

#[allow(non_camel_case_types)]
#[derive(Debug, Clone)]
pub enum OpCode<'tcx>{
    Noop,

    // Assign to stack variable
    Store(Var, usize),
    Load(Var, usize),

    LoadLocal(usize),
    StoreLocal(usize),
    // Consume stack variable
    // Use(Var, u32),
    Use,
    Consume,


    Const(Constant<'tcx>),
    Static(DefId),
    LoadFunc(DefId),
    Len,
    AssignIndex,
    GetIndex,
    ArgCount(usize),
    Call,

    UnsignedInteger(u64),
    Usize(usize),
    SignedInteger(i64),
    Float(f64),
    Bool(bool),

    Repeat(usize),

    BORROW(BorrowKind),

    DEREF,
    DEREF_STORE,

    BINOP(BinOp),
    CBINOP(BinOp),

    RETURN_POINTER,

    //Terminator
    _Goto(BasicBlock),
    _GotoIf(BasicBlock),

    RETURN,
    RESUME,

    TUPLE(usize),
    VEC(usize),

    //XXX: used for creation of tuple
    TUPLE_ASSIGN(usize),

    TUPLE_SET(usize),
    TUPLE_GET(usize),

    TODO(&'static str),
    TODO_S(String),

    JUMP(usize),
    JUMP_IF(usize),

    JUMP_REL(i32),
    JUMP_REL_IF(i32),

    Pop,

    StackFrame(usize),

    Guard(Guard<'tcx>),
    Debug(usize),

}

#[derive(Clone, Debug)]
pub struct Guard<'a> {
    pub expected: bool,
    pub recovery: Rc<Function<'a>>,
    pub pc: usize,
}


pub struct Context<'a, 'tcx: 'a> {
    pub tcx: TyCtxt<'a, 'tcx, 'tcx>,
    pub map: &'a MirMap<'tcx>
}


impl<'a, 'tcx> Context<'a, 'tcx> {

    pub fn mir_to_bytecode(&'a self, func: &Mir<'a>) -> Function<'a> {
        let blocks = func.basic_blocks().iter().map(
            |bb| {
                let mut gen = BlockGen::new(self.tcx);
                gen.analyse_block(bb);
                gen.opcodes
            }).collect();

        self.optimize_blocks(&blocks, func)
    }

    fn optimize_blocks(&'a self, blocks: &Vec<Function<'a>>, func: &Mir<'a>) -> Function<'a> {
        let mut indicies = Vec::new();
        let mut n = 0_usize;
        for block in blocks {
            indicies.push(n);
            n += block.len();
        }

        let var_offset = func.arg_decls.len();
        let tmp_offset = var_offset + func.var_decls.len();

        let mut opcodes = Vec::new();

        for block in blocks {
            for opcode in block.iter() {
                let oc: OpCode = match *opcode {
                    OpCode::_Goto(ref target) => OpCode::JUMP(indicies[target.index()]),
                    OpCode::_GotoIf(ref target) => OpCode::JUMP_IF(indicies[target.index()]),

                    OpCode::Load(Var::Arg, n) => OpCode::LoadLocal(n as usize),
                    OpCode::Load(Var::Var, n) => OpCode::LoadLocal(var_offset + n as usize),
                    OpCode::Load(Var::Tmp, n) => OpCode::LoadLocal(tmp_offset + n as usize),
                    OpCode::Store(Var::Arg, n) => OpCode::StoreLocal(n as usize),
                    OpCode::Store(Var::Var, n) => OpCode::StoreLocal(var_offset + n as usize),
                    OpCode::Store(Var::Tmp, n) => OpCode::StoreLocal(tmp_offset + n as usize),
                    _ => opcode.clone(),
                };
                opcodes.push(oc);
            }
        }

        let mut opcodes_rel = vec![OpCode::StackFrame(tmp_offset+func.temp_decls.len())];

        for (ii, opcode) in opcodes.iter_mut().enumerate() {
            let i = ii as i32;
            let oc: Option<OpCode> = match *opcode {
                OpCode::JUMP(target) => {
                    let dist = target as i32 - i;
                    // if dist == 1 {
                        // None
                    // } else {
                        Some(OpCode::JUMP_REL(dist))
                    // }
                },
                OpCode::JUMP_IF(target) => {
                    let dist = target as i32 - i;
                    // if dist == 1 {
                        // None
                    // } else {
                        Some(OpCode::JUMP_REL_IF(dist))
                    // }
                },
                _ => Some(opcode.clone())
            };

            if let Some(op) = oc {
                opcodes_rel.push(op);
            }
        }


        opcodes_rel
    }
}

// }

// struct FuncGen<'a, 'tcx: 'a> {
//     tcx: &'a TyCtxt<'a, 'tcx, 'tcx>,
//     map: &'a MirMap<'tcx>,
//     blocks: Vec<Vec<OpCode<'a>>>
// }

// impl<'a, 'tcx: 'a> FuncGen<'a, 'tcx> {
//     fn new(tcx: &'a TyCtxt<'a, 'tcx, 'tcx>, map: &'a MirMap<'tcx>) -> Self {
//         FuncGen{ tcx: tcx, map: map, blocks: Vec::new() }
//     }

//     fn analyse(&mut self, func: &Mir<'a>) {
//         for block in &func.basic_blocks {
//             let mut bg = BlockGen::new(self.tcx, self.map);
//             bg.analyse_block(block);
//             self.blocks.push(bg.opcodes);
//         }
//     }
// }

struct BlockGen<'a, 'tcx: 'a>{
    opcodes: Function<'a>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>
}

impl<'a, 'tcx> BlockGen<'a, 'tcx> {

    fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        BlockGen{ opcodes: Vec::new(), tcx: tcx }
    }

    fn analyse_block(&mut self, block: &BasicBlockData<'a>) {
        for statement in &block.statements {
            self.analyse_statement(statement);
        }
        self.analyse_terminator(block.terminator());
    }

    fn analyse_statement(&mut self, statement: &Statement<'a>) {
        if let StatementKind::Assign(ref lvalue, ref rvalue) = statement.kind {
            self.handle_rvalue(rvalue);
            self.assign_to(lvalue);
        }
    }

    fn assign_to(&mut self, lvalue: &Lvalue<'a>) {
        let opcode = match *lvalue {
            Lvalue::Var(n)  => OpCode::Store(Var::Var, n.index()),
            Lvalue::Temp(n) => OpCode::Store(Var::Tmp, n.index()),
            Lvalue::Arg(_n)  => unreachable!(),
            Lvalue::Static(..)  => OpCode::TODO("assign static"),

            Lvalue::Projection(ref proj) => {
                match proj.elem {
                    ProjectionElem::Deref => {
                        let opcode = self.load_lvalue(&proj.base);
                        self.opcodes.push(opcode);
                        OpCode::DEREF_STORE
                        // OpCode::TODO_S(format!("deref projection {:?}:{:?}", proj.elem, proj.base))
                    },

                    ProjectionElem::Field(field, _type) => {
                        let opcode = self.load_lvalue(&proj.base);
                        self.opcodes.push(opcode);

                        let index = field.index();
                        OpCode::TUPLE_SET(index)
                    },

                    // x[index] = z;
                    ProjectionElem::Index(ref index) => {
                        //index
                        self.rvalue_operand(index);

                        //x
                        let opcode = self.load_lvalue(&proj.base);
                        self.opcodes.push(opcode);

                        OpCode::AssignIndex
                    },

                    _ => OpCode::TODO_S(format!("assign projection {:?}", proj.elem)),
                }
                // proj.base: Lvalue
                // proj.elem: ProjectionElem<Operand>
                // OpCode::TODO("assign projections")
            },

            // ignore, value is just left on the stack
            Lvalue::ReturnPointer => OpCode::RETURN_POINTER,

            // _ => OpCode::TODO("assign_to"),

            //TODO: assign to projections
        };
        self.opcodes.push(opcode);
    }

    fn analyse_terminator(&mut self, terminator: &Terminator<'a>) {

        let op = match terminator.kind {
            TerminatorKind::Goto{target} => OpCode::_Goto(target),
            TerminatorKind::If{ref cond, targets: (ref bb1, ref bb2)} => {
                self.rvalue_operand(cond);
                self.opcodes.push(OpCode::_GotoIf(*bb1));
                OpCode::_Goto(*bb2)
            },
            TerminatorKind::Return => OpCode::RETURN,
            TerminatorKind::Resume => OpCode::RESUME,

            TerminatorKind::Call{ref func, ref args, ref destination, ..} => {

                // self.opcodes.push(OpCode::TODO("Load Args"));
                for arg in args {
                    self.rvalue_operand(arg);
                }
                self.opcodes.push(OpCode::ArgCount(args.len()));

                self.rvalue_operand(func);

                match destination.as_ref() {
                    Some(dest) => {
                        self.opcodes.push(OpCode::Call);
                        self.assign_to(&dest.0);
                        OpCode::_Goto(dest.1)
                    },
                    None => {
                        OpCode::TODO("NO RETURN")
                    }
                }
                // println!("{:?}", destination.0);
                // OpCode::Call()
                // OpCode::TODO("CALL")
            },

            TerminatorKind::Drop{location: ref lvalue, target: _, unwind: _} => {
                let opcode = self.load_lvalue(lvalue);
                self.opcodes.push(opcode);
                OpCode::TODO("Drop")
            },

            TerminatorKind::Assert{ref cond, expected, msg: _, target, cleanup} => {
                // cond.as_rvalue(env);
                // env.add(OpCode::ConstValue(R_BoxedValue::Bool(expected)));
                // env.add(OpCode::BinOp(BinOp::Eq));
                // env.opcodes.push(MetaOpCode::GotoIf(target));

                OpCode::_Goto(target)
                // if let Some(bb) = cleanup {
                    // OpCode::_Goto(bb)
                // } else {
                    // panic!("Titanic");
                    // OpCode::Noop
                // }
            },

            _ => {
                println!("{:?}", terminator.kind);
                OpCode::TODO("Terminator")
            }
        };
        self.opcodes.push(op);
    }


    fn handle_rvalue(&mut self, rvalue: &Rvalue<'a>) {
        match *rvalue {
            Rvalue::Use(ref op) => {
                self.rvalue_operand(op);
                self.opcodes.push(OpCode::Use)
            },

            Rvalue::CheckedBinaryOp(op, ref left, ref right) => {
                self.rvalue_operand(left);
                self.rvalue_operand(right);
                self.opcodes.push(OpCode::CBINOP(op));
            },

            Rvalue::BinaryOp(op, ref left, ref right) => {
                self.rvalue_operand(left);
                self.rvalue_operand(right);
                self.opcodes.push(OpCode::BINOP(op));
            },

            Rvalue::Aggregate(AggregateKind::Tuple, ref vec) => {
                self.opcodes.push(OpCode::TUPLE(vec.len()));
                for (i, value) in vec.iter().enumerate() {
                    self.rvalue_operand(value);
                    self.opcodes.push(OpCode::TUPLE_ASSIGN(i));
                }
            },
            Rvalue::Aggregate(AggregateKind::Vec, ref vec) => {
                // println!("{:?}", vec);
                for value in vec {
                    self.rvalue_operand(value);
                }
                self.opcodes.push(OpCode::VEC(vec.len()));
            },
            Rvalue::Aggregate(AggregateKind::Adt(adt_def, _size, _subst, _), ref operands) => {
                /*
                    Adt (abstract data type) is an enum. Structs are enums with only one variant.
                    To check whether an adt is an enum or a struct one can use `.adt_kind`.


                    Variants are either VariantKind::{Struct, Tuple, Unit}
                */

                if adt_def.adt_kind() == AdtKind::Struct {
                    // the struct definition is the first variant
                    let ref struct_def = adt_def.variants[0];
                    self.opcodes.push(OpCode::TUPLE(struct_def.fields.len()));
                    for (i, operand) in operands.iter().enumerate() {
                        self.rvalue_operand(operand);
                        self.opcodes.push(OpCode::TUPLE_ASSIGN(i));
                    }
                    // self.opcodes.push(OpCode::)
                }
                // println!("S: {:?}", size);
                // for var in adt_def.variants.iter() {
                    // println!("X: {:?}", var.name);
                // }
                // println!("{:?}", adt_def.variants.iter().map(|var| var.name).collect());
                // self.opcodes.push(OpCode::TODO("Aggr Adt"));
            },
            Rvalue::Aggregate(AggregateKind::Closure(_def_id, _subst), ref _aggr) => {
                self.opcodes.push(OpCode::TODO("Aggr Closure"));
            },

            Rvalue::Ref(ref _region, ref kind, ref lvalue) => {
                let opcode = self.load_lvalue(lvalue);
                self.opcodes.push(opcode);
                self.opcodes.push(OpCode::BORROW(*kind));
            },

            // example: [0; 5] -> [0, 0, 0, 0, 0]
            Rvalue::Repeat(ref op, ref times) => {
                let size = times.value.as_u64(self.tcx.sess.target.uint_type);
                self.rvalue_operand(op);
                self.opcodes.push(OpCode::Repeat(size as usize));
            },

            Rvalue::Len(ref lvalue) => {
                // println!("{:?}", lvalue);
                let op = self.load_lvalue(lvalue);
                self.opcodes.push(op);

                self.opcodes.push(OpCode::Len);
            },

            Rvalue::Cast(ref kind, ref operand, ref ty) => {
               match *kind {
                    CastKind::Unsize => {
                        // println!("unsize {:?} to {:?}", operand, ty);

                        self.opcodes.push(OpCode::TODO("UNSIZE"));
                    },
                    _ => unimplemented!(),
               }
            },

            _ => {
                println!("TODO-rvalue: {:?}", rvalue);
                self.opcodes.push(OpCode::TODO("Rvalue"))
            },
        }
    }

    fn rvalue_operand(&mut self, op: &Operand<'a>) {
       let cmd = match op {
            &Operand::Consume(ref lvalue) => {
                let o = self.load_lvalue(lvalue);
                // self.opcodes.push(o);
                o
                // OpCode::Consume
            },
            &Operand::Constant(ref constant) => {
                if let Literal::Item{ ref def_id, .. } = constant.literal {
                // if let Literal::Value{ ref value } = constant.literal {
                    // println!("literal");
                    // if let &ConstVal::Function(def_id) = value {
                        // OpCode::LoadFunc(def_id.index.as_u32())
                    // let mir = self.tcx.map.get(def_id.index.as_u32());
                    // if let Node::NodeLocal(pat) = mir {
                    //     println!("{:?}", pat.id);
                    // }
                    // println!("XXX: {:?} {:?}", constant.ty, constant.literal);
                    // println!("{:?}", def_id);
                    // self.map.map.get(def_id);
                    OpCode::LoadFunc(def_id.clone())
                    // } else {
                        // OpCode::TODO("const literal item")
                    // }
                } else {
                    // OpCode::Const(constant.clone())
                    self.unpack_const(&constant.literal)
                }
            }
        };
        self.opcodes.push(cmd);

    }

    /// Consume a single value
    /// objects that implement the copy trait get copied
    /// other objects are moved
    ///
    /// This function is similar to handle_lvalue, but instead of storing data
    /// objects are loaded.
    // fn consume_lvalue(&mut self, lvalue: &Lvalue<'a>) -> OpCode<'a> {
        // self.load_lvalue(lvalue)
        // match *lvalue {
        //     Lvalue::Var(n)  => OpCode::Use(Var::Var, n),
        //     Lvalue::Temp(n) => OpCode::Use(Var::Tmp, n),
        //     Lvalue::Arg(n)  => OpCode::Use(Var::Arg, n),
        //     Lvalue::Projection(ref proj) => {
        //         // self.unpack_projection(&**proj);
        //         OpCode::TODO("lvalue projection")
        //     },
        //     _ => OpCode::TODO("Consume Lvalue")
        // }
    // }



    fn load_lvalue(&mut self, lvalue: &Lvalue<'a>) -> OpCode<'a> {
        match lvalue {
            &Lvalue::Var(n) => OpCode::Load(Var::Var, n.index()),
            &Lvalue::Temp(n) => OpCode::Load(Var::Tmp, n.index()),
            &Lvalue::Arg(n) => OpCode::Load(Var::Arg, n.index()),
            &Lvalue::Static(def_id) => OpCode::Static(def_id),
            &Lvalue::Projection(ref proj) => {
                match proj.elem {
                    ProjectionElem::Deref => {
                        let lv = self.load_lvalue(&proj.base);
                        self.opcodes.push(lv);
                        OpCode::DEREF
                    },
                    ProjectionElem::Field(field, _ty) => {
                        //XXX: is type arg needed here?
                        let opcode = self.load_lvalue(&proj.base);
                        self.opcodes.push(opcode);

                        OpCode::TUPLE_GET(field.index())
                    },
                    ProjectionElem::Index(ref index) => {
                        self.rvalue_operand(index);
                                                //x
                        let opcode = self.load_lvalue(&proj.base);
                        self.opcodes.push(opcode);

                        OpCode::GetIndex
                    },
                    _ => OpCode::TODO("Projection")
                }
            },
            _ => OpCode::TODO("Load Lvalue")
        }
    }

    fn unpack_const(&self, literal: &Literal) -> OpCode<'a> {
        match *literal {
            Literal::Value{ ref value } => {
                use rustc_const_math::ConstInt::*;
                if let ConstVal::Integral(ref boxed) = *value {
                    match *boxed {

                         U8(u) => OpCode::UnsignedInteger(u as u64),
                        U16(u) => OpCode::UnsignedInteger(u as u64),
                        U32(u) => OpCode::UnsignedInteger(u as u64),
                        U64(u) => OpCode::UnsignedInteger(u),

                         I8(i) => OpCode::SignedInteger(i as i64),
                        I16(i) => OpCode::SignedInteger(i as i64),
                        I32(i) => OpCode::SignedInteger(i as i64),
                        I64(i) => OpCode::SignedInteger(i),

                        Usize(Us32(us32)) => OpCode::Usize(us32 as usize),
                        Usize(Us64(us64)) => OpCode::Usize(us64 as usize),

                        _ => panic!(format!("{:?}", boxed)),
                    }
                } else if let ConstVal::Bool(b) = *value {
                    OpCode::Bool(b)
                } else {
                    unimplemented!();
                }
            },
            Literal::Item{def_id: _, ..} => {
                //let x = &42; will generate a reference to a static variable
                // println!("{:?}", def_id);
                unimplemented!()
            },
            Literal::Promoted{index} => {
                // OpCode::UnsignedInteger
                OpCode::Usize(index.index())
            },
        }
    }

    // TODO: further unpack const values
    // const(42i32) -> [I32, 42]
    // fn constant_value(&mut self, val: Constant) {
    //     if let Literal::Value{ value: literal } = val.literal {
    //         println!("{:?}", literal);
    //     }
    // }
}


pub fn generate_bytecode<'a, 'tcx>(context: &'a Context<'a, 'tcx>) -> (Program<'a, 'tcx>, DefId, BTreeMap<DefId, String>) {

    //map krate num -> node id
    let mut program = Program::new(context);
    // let mut build_ins: BTreeMap<u32, BTreeMap<u32, &'a InternedString>> = BTreeMap::new();
    let mut main: Option<DefId> = None;

    let mut internals= BTreeMap::new();

    let keys = &context.map.map.keys();
    for key in keys {
    // for (key, func_mir) in  {
        let func_mir = context.map.map.get(key).unwrap();
        // let mir = map.map.get(key).unwrap();
        // println!("{:?}", mir.id);
        // let def_index = context.tcx.map.local_def_id(*key);
        let def_index = key.to_owned();

        if let Some(Node::NodeItem(item)) = context.tcx.map.get_if_local(def_index) {
            // println!("Function: {:?} {:?}", item.name.as_str(), def_index.index.as_u32());
                // let mut collector = FuncGen::new(&context.tcx, context.map);
                // collector.analyse(&func_mir);
                // for (i, block) in collector.blocks.iter().enumerate() {
                //     // println!("{} {:?}", i, block);
                // }
                // let blocks = optimize_blocks(&collector.blocks, func_mir);

                let blocks: Function = context.mir_to_bytecode(func_mir);

                program.krates.insert(def_index, Rc::new(blocks));

                if item.name.as_str().starts_with("__") {
                    let s = item.name.as_str()[2..].to_string();
                    internals.insert(def_index, s);
                } else if def_index.krate == 0 && item.name.as_str() == "main" {
                    main = Some(def_index);
                }
        }
        // println!("{:?}", keys);
    }
    // for id in map.map.keys() {

    //     println!("Node {:?}", node);
    //     println!("Node ID: {:?}", id);
    // }

    // print out bytecode
    // for (func, block) in program.krates.iter() {
    //     println!("Func {:?}", func);
    //     for (i, opcode) in block.iter().enumerate() {
    //         println!("{} {:?}",i, opcode);
    //     }
    //     println!("");
    // }

    (program, main.unwrap(), internals)
}
