open Batteries
open Semant
open Plain

let rec scan db va =
  if not (Database.has_proc db va) then begin
    let proc = Build_cfg.build_cfg db va in
    Database.set_proc db va proc;
    let is_leaf = ref true in
    let cfg = proc.Database.inst_cfg in
    let n = Array.length cfg.node in
    for i=0 to n-1 do
      cfg.node.(i).stmts |> List.iter begin fun inst ->
        match inst.Inst.operation with
        | I_CALL ->
          is_leaf := false;
          begin match List.hd inst.Inst.operands with
            | O_imm (dst, _) -> scan db dst
            | _ -> ()
          end
        | _ -> ()
      end
    done;
    if !is_leaf then begin
      Printf.printf "leaf function: %nx\n" va
    end
  end
