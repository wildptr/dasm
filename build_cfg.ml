open Batteries
open Cfg
open Inst

let build_cfg db init_pc =
  Printf.printf "building CFG for %nx\n" init_pc;
  let open Database in
  let module S = Set.Nativeint in
  let code = get_code db in
  let span = ref Itree.empty in
  (* from end of basic block to start of basic block *)
  let succ_raw = Hashtbl.create 0 in
  let add_edge src dst attr =
    match Hashtbl.Exceptionless.find succ_raw src with
    | Some succ ->
      Hashtbl.replace succ_raw src ((dst, attr) :: succ)
    | None ->
      Hashtbl.add succ_raw src [dst, attr]
  in
  let exits = ref S.empty in
  let conc_table = Hashtbl.create 0 in
  let inst_table = Hashtbl.create 0 in
  let q = Queue.create () in
  Queue.add init_pc q;
  let pos = ref 0 in (* initial value not used *)
  while not (Queue.is_empty q) do
    let pc = Queue.pop q in
    (* If 'pc' is strictly between start(b) and end(b) for some basic
       block b, then split b at 'pc'.  If 'pc' equals start(b) for some b,
       then do nothing.  Otherwise add 'pc' to queue. *)
    begin match Itree.find pc !span with
      | Itree.Start -> ()
      | Itree.Middle ->
        span := Itree.split pc !span;
        Hashtbl.add conc_table pc false;
        add_edge pc pc Edge_neutral
      | Itree.Nowhere ->
        pos := translate_va db pc;
        let rec loop pc =
          let config = Dasm.{ mode = Mode32bit; pc_opt = Some pc } in
          let inst = Dasm.(disassemble config code !pos) in
          pos := !pos + String.length inst.bytes;
          Hashtbl.add inst_table pc inst;
          let l = length_of inst in
          let pc' = Nativeint.(pc + of_int l) in
          match inst.operation with
          | I_JMP ->
            begin match List.hd inst.operands with
              | O_offset _ -> failwith "offset operand???"
              | O_imm (imm, _) ->
                Hashtbl.add db.jump_info pc' J_resolved;
                pc', [imm, Edge_neutral], true
              | _ ->
                Printf.printf "unresolved jump at %nx\n" pc;
                Hashtbl.add db.jump_info pc' J_unknown;
                exits := S.add pc' !exits;
                pc', [], false
            end
          | I_JMPF -> failwith "cannot handle far jump"
          | I_CALLF -> failwith "cannot handle far call"
          | I_CJMP ->
            begin match List.hd inst.operands with
              | O_offset _ -> failwith "offset operand???"
              | O_imm (imm, _) ->
                Hashtbl.add db.jump_info pc' J_resolved;
                pc', [pc', Edge_false; imm, Edge_true], false
              | _ ->
                Printf.printf "unresolved conditional jump at %nx\n" pc;
                Hashtbl.add db.jump_info pc' J_unknown;
                pc', [pc', Edge_false], false
            end
          | I_RET | I_RETF | I_RETN ->
            Hashtbl.add db.jump_info pc' J_ret;
            exits := S.add pc' !exits;
            pc', [], false
          | _ ->
            if inst.operation = I_CALL then
              Hashtbl.add db.jump_info pc' J_call;
            if Itree.find pc' !span = Itree.Start then begin
              pc', [pc', Edge_neutral], false
            end else loop pc'
        in
        let pc', dests, conc = loop pc in
        span := Itree.add (pc,pc') !span;
        Hashtbl.add conc_table pc' conc;
        dests |> List.iter begin fun (dest, attr) ->
          add_edge pc' dest attr;
          Queue.add dest q
        end
    end
  done;
  let start_to_end =
    Itree.to_list !span |> List.enum |> Map.Nativeint.of_enum
  in
  let rpo =
    let module S = Set.Nativeint in
    let temp = ref [] in
    let visited = ref S.empty in
    let rec visit start =
      if not (S.mem start !visited) then begin
        visited := S.add start !visited;
        let stop = Map.Nativeint.find start start_to_end in
        let succ =
          Hashtbl.Exceptionless.find succ_raw stop |> Option.default []
        in
        succ |> List.iter (fun (a, _) -> visit a);
        temp := (start, stop) :: !temp
      end
    in
    visit init_pc;
    !temp
  in
  (* Procedure entry is always basic block #0 *)
  let node =
    rpo |> List.mapi begin fun i (start, stop) ->
      let rec loop pc insts =
        let inst = Hashtbl.find inst_table pc in
        let insts' = inst :: insts in
        let pc' = Nativeint.(pc + of_int (length_of inst)) in
        if pc' = stop then insts' else loop pc' insts'
      in
      let insts = List.rev (loop start []) in
      let has_final_jump =
        try Hashtbl.find conc_table stop with Not_found ->
          Printf.printf "missing entry in conclusion table: %nx\n" stop;
          raise Not_found
      in
      { start; stop; stmts = insts; has_final_jump }
    end |> Array.of_list
  in
  let n = Array.length node in
  let start_to_id = Hashtbl.create n in
  let end_to_id = Hashtbl.create n in
  node |> Array.iteri begin fun i bb ->
    Hashtbl.add start_to_id bb.start i;
    Hashtbl.add end_to_id bb.stop i
  end;
  let succ = Array.make n [] in
  let pred = Array.make n [] in
  let edges =
    succ_raw |> Hashtbl.to_list |> List.map begin fun (stop, l) ->
      l |> List.map begin fun (start, attr) ->
        let from_id = Hashtbl.find end_to_id stop in
        let to_id = Hashtbl.find start_to_id start in
        from_id, to_id, attr
      end
    end |> List.concat
  in
  edges |> List.iter begin fun (from_id, to_id, attr) ->
    succ.(from_id) <- to_id :: succ.(from_id);
    pred.(to_id) <- from_id :: pred.(to_id);
  end;
  let idom = Control_flow.compute_idom succ pred in
  let exits =
    let temp = ref Set.Int.empty in
    !exits |> S.iter begin fun a ->
      temp := Set.Int.add (Hashtbl.find end_to_id a) !temp
    end;
    !temp
  in
  let inst_cfg =
    { node; succ; pred; idom; edges; exits; temp_tab = [||] }
  in
  Printf.printf "%nx: %d basic %s\n" init_pc n
    (if n=1 then "block" else "blocks");
  inst_cfg
