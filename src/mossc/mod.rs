
use std::collections::BTreeMap;

use rustc::mir::repr::*;
use rustc::mir::mir_map::MirMap;
use rustc::middle::const_val::ConstVal;

use rustc::hir::map::Node;
use rustc::hir::def_id::DefId;

use rustc::ty::TyCtxt;


#[derive(Debug, Clone)]
pub enum Var {
    Arg,
    Var,
    Tmp,
}

#[derive(Debug, Clone)]
pub enum OpCode<'tcx>{
    // Assign to stack variable
    Store(Var, u32),
    Load(Var, u32),

    // Consume stack variable
    // Use(Var, u32),
    Use,
    Consume,


    Const(Constant<'tcx>),
    Static(DefId),
    LoadFunc(DefId),

    ArgCount(usize),
    Call,

    BORROW(BorrowKind),

    DEREF,
    DEREF_STORE,

    BINOP(BinOp),

    RETURN_POINTER,

    //Terminator
    GOTO(BasicBlock),
    GOTO_IF(BasicBlock),
    RETURN,
    RESUME,

    TUPLE(usize),
    VEC(usize),

    TODO(&'static str),
    TODO_S(String),

    JUMP(usize),
    JUMP_IF(usize),

    JUMP_REL(i32),
    JUMP_REL_IF(i32),

}

struct FuncGen<'a, 'tcx: 'a> {
    tcx: &'a TyCtxt<'tcx>,
    map: &'a MirMap<'tcx>,
    blocks: Vec<Vec<OpCode<'a>>>
}

impl<'a, 'tcx: 'a> FuncGen<'a, 'tcx> {
    fn new(tcx: &'a TyCtxt<'tcx>, map: &'a MirMap<'tcx>) -> Self {
        FuncGen{ tcx: tcx, map: map, blocks: Vec::new() }
    }

    fn analyse(&mut self, func: &Mir<'a>) {
        for block in &func.basic_blocks {
            let mut bg = BlockGen::new(self.tcx, self.map);
            bg.analyse_block(block);
            self.blocks.push(bg.opcodes);
        }
    }
}

struct BlockGen<'a, 'tcx: 'a> {
    tcx: &'a TyCtxt<'tcx>,
    map: &'a MirMap<'tcx>,

    opcodes: Vec<OpCode<'a>>
}

impl<'a, 'tcx: 'a> BlockGen<'a, 'tcx> {
    fn new(tcx: &'a TyCtxt<'tcx>, map: &'a MirMap<'tcx>) -> Self {
        BlockGen{ tcx: tcx, map: map, opcodes: Vec::new() }
    }

    fn analyse_block(&mut self, block: &BasicBlockData<'a>) {
        for statement in &block.statements {
            self.analyse_statement(statement);
        }
        self.analyse_terminator(block.terminator());
    }

    fn analyse_statement(&mut self, statement: &Statement<'a>) {
        let StatementKind::Assign(ref lvalue, ref rvalue) = statement.kind;
        self.handle_rvalue(rvalue);
        self.assign_to(lvalue);
    }

    fn assign_to(&mut self, lvalue: &Lvalue<'a>) {
        let opcode = match *lvalue {
            Lvalue::Var(n)  => OpCode::Store(Var::Var, n),
            Lvalue::Temp(n) => OpCode::Store(Var::Tmp, n),
            Lvalue::Arg(n)  => unreachable!(),
            Lvalue::Static(..)  => OpCode::TODO("assign static"),

            Lvalue::Projection(ref proj) => {
                match proj.elem {
                    ProjectionElem::Deref => {
                        let opcode = self.load_lvalue(&proj.base);
                        self.opcodes.push(opcode);
                        OpCode::DEREF_STORE
                        // OpCode::TODO_S(format!("deref projection {:?}:{:?}", proj.elem, proj.base))
                    },

                    _ => OpCode::TODO_S(format!("assign projection {:?}", proj.elem)),
                }
                // proj.base: Lvalue
                // proj.elem: ProjectionElem<Operand>
                // OpCode::TODO("assign projections")
            },

            Lvalue::ReturnPointer => OpCode::RETURN_POINTER,

            // _ => OpCode::TODO("assign_to"),

            //TODO: assign to projections
        };
        self.opcodes.push(opcode);
    }

    fn deref_lvalue(&mut self) {
    }

    fn analyse_terminator(&mut self, terminator: &Terminator<'a>) {
        let op = match terminator.kind {
            TerminatorKind::Goto{target} => OpCode::GOTO(target),
            TerminatorKind::If{ref cond, targets: (ref bb1, ref bb2)} => {
                self.rvalue_operand(cond);
                self.opcodes.push(OpCode::GOTO_IF(*bb1));
                OpCode::GOTO(*bb2)
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
                let destination = destination.as_ref().unwrap();
                // println!("{:?}", destination.0);
                self.opcodes.push(OpCode::Call);
                self.assign_to(&destination.0);
                OpCode::GOTO(destination.1)
                // OpCode::Call()
                // OpCode::TODO("CALL")
            },

            TerminatorKind::Drop{value: ref lvalue, target, unwind} => {
                let opcode = self.load_lvalue(lvalue);
                self.opcodes.push(opcode);
                OpCode::TODO("Drop")
            },
            _ => OpCode::TODO("Terminator"),
        };
        self.opcodes.push(op);
    }


    fn handle_rvalue(&mut self, rvalue: &Rvalue<'a>) {
        match *rvalue {
            Rvalue::Use(ref op) => {
                self.rvalue_operand(op);
                self.opcodes.push(OpCode::Use)
            },
            Rvalue::BinaryOp(op, ref left, ref right) => {
                self.rvalue_operand(left);
                self.rvalue_operand(right);
                self.opcodes.push(OpCode::BINOP(op));
            },

            Rvalue::Aggregate(AggregateKind::Tuple, ref vec) => {
                self.opcodes.push(OpCode::TUPLE(vec.len()));
            },
            Rvalue::Aggregate(AggregateKind::Vec, ref vec) => {
                self.opcodes.push(OpCode::VEC(vec.len()));
            },
            Rvalue::Aggregate(_, ref _vec) => {
                self.opcodes.push(OpCode::TODO("AggrKind"));
            },

            Rvalue::Ref(ref region, ref kind, ref lvalue) => {
                let opcode = self.load_lvalue(lvalue);
                self.opcodes.push(opcode);
                self.opcodes.push(OpCode::BORROW(*kind));
            },
            _ => {self.opcodes.push(OpCode::TODO("Rvalue"))},
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
                    OpCode::Const(constant.clone())
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
            &Lvalue::Var(n) => OpCode::Load(Var::Var, n),
            &Lvalue::Temp(n) => OpCode::Load(Var::Tmp, n),
            &Lvalue::Arg(n) => OpCode::Load(Var::Arg, n),
            &Lvalue::Static(def_id) => OpCode::Static(def_id),
            &Lvalue::Projection(ref proj) => {
                if let ProjectionElem::Deref = proj.elem {
                    let lv = self.load_lvalue(&proj.base);
                    self.opcodes.push(lv);
                    OpCode::DEREF

                } else {
                    OpCode::TODO("Projection")
                }
            },
            _ => OpCode::TODO("Load Lvalue")
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



fn flatten_blocks<'tcx>(blocks: &Vec<Vec<OpCode<'tcx>>>) -> Vec<OpCode<'tcx>> {
    let mut indicies = Vec::new();
    let mut n = 0_usize;
    for block in blocks {
        indicies.push(n);
        n += block.len();
    }

    let mut opcodes = Vec::new();

    for block in blocks {
        for opcode in block.iter() {
            let oc: OpCode = match *opcode {
                OpCode::GOTO(ref target) => OpCode::JUMP(indicies[target.index()]),
                OpCode::GOTO_IF(ref target) => OpCode::JUMP_IF(indicies[target.index()]),
                // OpCode::GOTO(ref target) => OpCode::JUMP_REL(indicies[target.index()] as i32 - i),
                // OpCode::GOTO_IF(ref target) => OpCode::JUMP_REL_IF(indicies[target.index()] as i32 - i ),
                _ => opcode.clone(),
            };
            opcodes.push(oc);
        }
    }

    let mut opcodes_rel = Vec::new();

    for (ii, opcode) in opcodes.iter_mut().enumerate() {
        let i = ii as i32;
        let oc: Option<OpCode> = match *opcode {
            OpCode::JUMP(target) => {
                let dist = target as i32 - i -1;
                if dist == 0 {
                    None
                } else {
                    Some(OpCode::JUMP_REL(dist))
                }
            },
            OpCode::JUMP_IF(target) => {
                let dist = target as i32 - i -1;
                if dist == 0 {
                    None
                } else {
                    Some(OpCode::JUMP_REL_IF(dist))
                }
            },
            _ => Some(opcode.clone())
        };

        if let Some(op) = oc {
            opcodes_rel.push(op);
        }
    }


    opcodes_rel
}


pub fn generate_bytecode<'tcx>(tcx: &TyCtxt<'tcx>, map: &MirMap<'tcx>) {
    //map krate num -> node id
    let mut program : BTreeMap<u32, BTreeMap<u32, Vec<OpCode>>> = BTreeMap::new();
    let mut main = 0;

    for key in map.map.keys() {
        // let mir = map.map.get(key).unwrap();
        // println!("{:?}", mir.id);
        let def_index = tcx.map.local_def_id(*key);

        if let Node::NodeItem(item) = tcx.map.get(key.to_owned()) {
            // println!("Function: {:?} {:?}", item.name.as_str(), def_index.index.as_u32());

            // println!("FUNCTION: KEY {:?}", tcx.item_path_str(key));
            if let Some(func_mir) = map.map.get(key) {

                let mut collector = FuncGen::new(tcx, map);
                collector.analyse(&func_mir);
                for (i, block) in collector.blocks.iter().enumerate() {
                    // println!("{} {:?}", i, block);
                }
                let blocks = flatten_blocks(&collector.blocks);
                program.entry(def_index.krate).or_insert(BTreeMap::new()).insert(def_index.index.as_u32(), blocks);
                if def_index.krate == 0 && item.name.as_str() == "main" {
                    main = def_index.index.as_u32();
                }
            }
        }
        // println!("{:?}", keys);
    }
    // for id in map.map.keys() {

    //     println!("Node {:?}", node);
    //     println!("Node ID: {:?}", id);
    // }


    // println!("{:?}", program);
    // println!("Main {:?}", main);
    for (_, krate) in program {
        for (func, block) in &krate {
            println!("Func {:?}", func);
            for (i, opcode) in block.iter().enumerate() {
                println!("{} {:?}",i, opcode);
            }
            println!("");
        }
    }
}
