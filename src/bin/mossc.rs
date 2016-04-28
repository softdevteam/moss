#![feature(rustc_private)]
#![feature(box_syntax)]

extern crate moss;
extern crate rustc;
extern crate rustc_driver;

use moss::mossc;

use rustc::session::Session;
use rustc_driver::{driver, CompilerCalls, Compilation};

struct MossCompilerCalls;

impl<'a> CompilerCalls<'a> for MossCompilerCalls {
    fn build_controller(&mut self, _: &Session) -> driver::CompileController<'a> {
        let mut control = driver::CompileController::basic();

        control.after_analysis.callback = box |state| {
            state.session.abort_if_errors();
            mossc::generate_bytecode(state.tcx.unwrap(), state.mir_map.unwrap());
        };

        control.after_analysis.stop = Compilation::Stop;

        control
    }
}


fn main() {
    let args: Vec<String> = std::env::args().collect();
    rustc_driver::run_compiler(&args, &mut MossCompilerCalls);
}