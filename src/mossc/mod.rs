
use rustc::mir::repr::*;
use rustc::mir::mir_map::MirMap;
use rustc::hir::def_id::DefId;

use rustc::ty::TyCtxt;

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum OpCode<'tcx>{
    NONE,

    STORE_VAR(u32),
    CONSUME_VAR(u32),
    LOAD_VAR(u32),

    STORE_TMP(u32),
    CONSUME_TMP(u32),
    LOAD_TMP(u32),

    CONSUME_ARG(u32),
    LOAD_ARG(u32),

    LOAD_CONST(Constant<'tcx>),
    LOAD_STATIC(DefId),

    BORROW(BorrowKind),

    DEREF,

    BINOP(BinOp),

    RETURN_POINTER,

    //Terminator
    GOTO(BasicBlock),
    GOTO_IF(BasicBlock),
    RETURN,
    RESUME,

    TUPLE(usize),
    VEC(usize),

    TODO(&'static str)
}

struct FuncGen<'a> {
    blocks: Vec<Vec<OpCode<'a>>>
}

impl<'a> FuncGen<'a> {
    fn new() -> FuncGen<'a> {
        FuncGen{ blocks: Vec::new() }
    }

    fn analyse(&mut self, func: &Mir<'a>) {
        for block in &func.basic_blocks {
            let mut bg = BlockGen::new();
            bg.analyse_block(block);
            self.blocks.push(bg.opcodes);
        }
    }
}

struct BlockGen<'a> {
    opcodes: Vec<OpCode<'a>>
}

impl<'a> BlockGen<'a> {
    fn new() -> BlockGen<'a> {
        BlockGen{ opcodes: Vec::new() }
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
        self.handle_lvalue(lvalue);
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

            TerminatorKind::Call{ref func, ..} => {
                self.rvalue_operand(func);
                self.opcodes.push(OpCode::TODO("Load Args"));
                OpCode::TODO("Call")
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

    fn handle_lvalue(&mut self, lvalue: &Lvalue) {
        self.opcodes.push(match lvalue {
            &Lvalue::Var(n) => {
                OpCode::STORE_VAR(n)
            },
            &Lvalue::Temp(ref n) => OpCode::STORE_TMP(*n),
            &Lvalue::ReturnPointer => OpCode::RETURN_POINTER,
            _ => {
                OpCode::TODO("Lvalue")
            }
        });
    }

    fn handle_rvalue(&mut self, rvalue: &Rvalue<'a>) {
        match *rvalue {
            Rvalue::Use(ref op) => {
                self.rvalue_operand(op);
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
                self.consume_lvalue(lvalue)
            },
            &Operand::Constant(ref constant) => {
                // if let Literal::Item{ ref def_id, .. } = constant.literal {
                    // println!("literal");
                    // if let &ConstVal::Function(def_id) = value {
                        // println!("XXX: {:?} {}", def_id, def_id.index.as_u32());
                    // }
                // }
                OpCode::LOAD_CONST(constant.clone())
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
    fn consume_lvalue(&self, lvalue: &Lvalue<'a>) -> OpCode<'a> {
        match lvalue {
            &Lvalue::Var(n) => OpCode::CONSUME_VAR(n),
            &Lvalue::Temp(n) => OpCode::CONSUME_TMP(n),
            &Lvalue::Arg(n) => OpCode::CONSUME_ARG(n),
            _ => OpCode::TODO("Consume Lvalue")
        }
    }

    fn load_lvalue(&mut self, lvalue: &Lvalue<'a>) -> OpCode<'a> {
        match lvalue {
            &Lvalue::Var(n) => OpCode::LOAD_VAR(n),
            &Lvalue::Temp(n) => OpCode::LOAD_TMP(n),
            &Lvalue::Arg(n) => OpCode::LOAD_ARG(n),
            &Lvalue::Static(def_id) => OpCode::LOAD_STATIC(def_id),
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



pub fn generate_bytecode(_tcx: &TyCtxt, map: &MirMap) {
    for key in map.map.keys() {
        println!("CRUSTY: KEY {:?}", key);
        if let Some(func_mir) = map.map.get(key) {
            let mut collector = FuncGen::new();
            collector.analyse(&func_mir);
            for (i, block) in collector.blocks.iter().enumerate() {
                println!("{} {:?}", i, block);
            }
        }
    }
}
