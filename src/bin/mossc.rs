#![feature(rustc_private)]
#![feature(box_syntax)]

extern crate moss;
extern crate rustc;
extern crate rustc_driver;
extern crate getopts;

use moss::mossc;
use moss::mossc::interpret;

use rustc::session::Session;
use rustc_driver::{driver, CompilerCalls, Compilation};
use rustc_driver::driver::CompileState;


struct MossCompilerCalls;

impl<'a> CompilerCalls<'a> for MossCompilerCalls {
    fn build_controller(
        &mut self,
        _: &Session,
        _: &getopts::Matches
    ) -> driver::CompileController<'a> {
        let mut control = driver::CompileController::basic();

        control.after_analysis.callback = Box::new(|state| {
            state.session.abort_if_errors();
            let map = state.mir_map.unwrap();
            let tcx = state.tcx.unwrap();
            let (program, main) = mossc::generate_bytecode(tcx, map);
            interpret::interpret(&program, main, tcx, map);
        });

        control.after_analysis.stop = Compilation::Stop;

        control
    }
}


fn main() {
    let args: Vec<String> = std::env::args().collect();
    rustc_driver::run_compiler(&args, &mut MossCompilerCalls);
}
