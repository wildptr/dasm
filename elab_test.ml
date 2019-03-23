open Batteries
open Dasm
open Inst
open Elaborate
open Semant

let dasm_config = {
  mode = Mode32bit;
  pc_opt = None
}

let () =
  Printexc.record_backtrace true;
  load_spec "spec";
  let path = Sys.argv.(1) in
  let code = File.with_file_in path IO.read_all in
  let code_len = String.length code in
  let elab_env = Elab_env.create None in
  let rec loop pos =
    if pos < code_len then begin
      let inst = disassemble dasm_config code pos in
      Format.printf "%a@." pp_inst' inst;
      elaborate_inst elab_env inst;
      loop (pos + inst_length inst)
    end
  in
  loop 0;
  Elab_env.get_stmts elab_env |> List.iter
    (Format.printf "%a@." Normal.pp_stmt)
