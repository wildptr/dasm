open Batteries
open Semant

let rec scan db va =
  if not (Database.has_proc db va) then begin
    let proc = Build_cfg.build_cfg db va in
    Database.set_proc db va proc;
    let is_leaf = ref true in
    let pc = ref 0n in
    proc.Database.il |> List.iter begin function
      | S_label va -> pc := va
      | S_jump (cond_opt, dst) ->
        begin match Database.get_jump_info db !pc with
          | Database.J_call ->
            is_leaf := false;
            begin match dst with
              | E_lit bv ->
                let dst_va = Bitvec.to_nativeint bv in
                scan db dst_va
              | _ -> ()
            end
          | _ -> ()
        end;
      | _ -> ()
    end;
    if !is_leaf then begin
      Printf.printf "leaf function: %nx\n" va
    end
  end
