
use rustc::mir::repr::*;
use rustc::mir::mir_map::MirMap;

use rustc::ty::TyCtxt;

#[derive(Debug)]
#[allow(non_camel_case_types)]
enum Command<'tcx>{
    NONE,

    STORE_VAR(u32),
    CONSUME_VAR(u32),

    STORE_TMP(u32),
    CONSUME_TMP(u32),

    LOAD_CONST(Constant<'tcx>),

    BINOP(BinOp),
}

struct FuncGen<'a> {
    commands: Vec<Command<'a>>
}


impl<'a> FuncGen<'a> {
    fn new() -> FuncGen<'a> {
        FuncGen{ commands: Vec::new() }
    }

    fn analyse(&mut self, func: &Mir<'a>) {
        for block in &func.basic_blocks {
            self.analyse_block(block);
        }
    }

    fn analyse_block(&mut self, block: &BasicBlockData<'a>) {
        for statement in &block.statements {
            self.analyse_statement(statement);
        }
    }

    fn analyse_statement(&mut self, statement: &Statement<'a>) {
        let StatementKind::Assign(ref lvalue, ref rvalue) = statement.kind;
        self.handle_rvalue(rvalue);
        self.handle_lvalue(lvalue);
    }

    fn handle_lvalue(&mut self, lvalue: &Lvalue) {
        self.commands.push(match lvalue {
            &Lvalue::Var(n) => {
                Command::STORE_VAR(n)
            },
            &Lvalue::Temp(ref n) => {
                Command::STORE_TMP(n.clone())
            },
            _ => {
                Command::NONE
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
                self.commands.push(Command::BINOP(op));
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
                Command::LOAD_CONST(constant.clone())
            }
        };
        self.commands.push(cmd);

    }

    /// Consume a single value
    /// objects that implement the copy trait get copied
    /// other objects are moved
    ///
    /// This function is similar to handle_lvalue, but instead of storing data
    /// objects are loaded.
    fn consume_lvalue(&self, lvalue: &Lvalue<'a>) -> Command<'a> {
        match lvalue {
            &Lvalue::Var(n) => Command::CONSUME_VAR(n.clone()),
            &Lvalue::Temp(n) => Command::CONSUME_TMP(n.clone()),
            _ => Command::NONE
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
            println!("CRUSTY {:?}", collector.commands);
        }
    }
}
