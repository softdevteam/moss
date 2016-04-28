
use rustc::mir::repr::*;
use rustc::mir::mir_map::MirMap;

use rustc::ty::TyCtxt;

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum OpCode<'tcx>{
    NONE,

    STORE_VAR(u32),
    CONSUME_VAR(u32),

    STORE_TMP(u32),
    CONSUME_TMP(u32),
    CONSUME_ARG(u32),

    LOAD_CONST(Constant<'tcx>),

    BINOP(BinOp),

    //Terminator
    GOTO(BasicBlock),
    GOTO_IF(BasicBlock),
    RETURN,

    TODO
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
            TerminatorKind::If{ref cond, ref targets} => {
                self.rvalue_operand(cond);
                self.opcodes.push(OpCode::GOTO_IF(targets.0));
                OpCode::GOTO(targets.1)
            },
            TerminatorKind::Return => OpCode::RETURN,
            _ => OpCode::NONE,
        };
        self.opcodes.push(op);
    }

    fn handle_lvalue(&mut self, lvalue: &Lvalue) {
        self.opcodes.push(match lvalue {
            &Lvalue::Var(n) => {
                OpCode::STORE_VAR(n)
            },
            &Lvalue::Temp(ref n) => {
                OpCode::STORE_TMP(n.clone())
            },
            _ => {
                OpCode::NONE
            }
        });
    }

    fn handle_rvalue(&mut self, rvalue: &Rvalue<'a>) {
        match rvalue {
            &Rvalue::Use(ref op) => {
                self.rvalue_operand(op);
            },
            &Rvalue::BinaryOp(op, ref left, ref right) => {
                self.rvalue_operand(left);
                self.rvalue_operand(right);
                self.opcodes.push(OpCode::BINOP(op));
            },
            _ => {},
        }
    }

    fn rvalue_operand(&mut self, op: &Operand<'a>) {
       let cmd = match op {
            &Operand::Consume(ref lvalue) => {
                self.consume_lvalue(lvalue)
            },
            &Operand::Constant(ref constant) => {
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
            _ => OpCode::TODO
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
