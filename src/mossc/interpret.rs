


use mossc::Program;

use rustc::mir::mir_map::MirMap;
use rustc::ty::TyCtxt;
use rustc::hir::def_id::DefId;



struct Frame {

}


pub fn interpret(program: &Program, main: DefId, tcx: &TyCtxt, map: &MirMap){

    let node_id = tcx.map.as_local_node_id(main).unwrap();
    let mir = map.map.get(&node_id).unwrap();
    // let node = tcx.map.get_if_local(main).unwrap();
    // println!("{:?}", map.map);
    // println!("{:?}", main);
    // tcx.map.get(main)
    // let item = map.map.get(&main).unwrap();
    // let item = tcx.map.expect_item(main.index.as_u32());
    // let x = [u32; mir.var_decls.len()];
    // println!("Len of vars {:?}", mir.var_decls.len());
    // println!("Len of tmps {:?}", mir.temp_decls.len());
    // println!("Len of args {:?}", mir.arg_decls.len());

    let vars: Vec<u32> = Vec::with_capacity(
        mir.var_decls.len() + mir.temp_decls.len() + mir.arg_decls.len());
    println!("{:?}", vars);
}