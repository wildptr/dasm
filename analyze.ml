open Semant

let rec scan db va =
  if not (Database.has_proc db va) then begin
    let proc = Build_cfg.build_cfg db va in
    Database.set_proc db va proc;
    proc.Database.il |> List.iter begin function
      | S_jump (cond_opt, dst) ->
        begin match dst with
          | E_lit bv -> scan db (Bitvec.to_nativeint bv)
          | _ -> ()
        end
      | _ -> ()
    end
  end
