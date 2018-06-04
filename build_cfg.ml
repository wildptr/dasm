open Batteries
open Cfg
open Inst

type string_iter = {
  str : string;
  mutable pos : int;
}

let build_cfg db init_pc =
  Printf.printf "building CFG for %nx\n" init_pc;
  let open Database in
  let code = get_code db in
  let span = ref Itree.empty in
  let edges = ref [] in (* from end of basic block to start of basic block *)
  let q = Queue.create () in
  Queue.add init_pc q;
  let s = { str = code; pos = 0 } in
  while not (Queue.is_empty q) do
    let pc = Queue.pop q in
    begin match Itree.find pc !span with
      | Itree.Start -> ()
      | Itree.Middle ->
        span := Itree.split pc !span;
        edges := (pc, pc, Edge_neutral) :: !edges
      | Itree.Nowhere ->
        s.pos <- translate_va db pc;
        let rec loop (pc:Nativeint.t) =
          let config = Dasm.{ mode = Mode32bit; pc_opt = Some pc } in
          let inst = Dasm.(disassemble config s.str s.pos) in
          s.pos <- s.pos + String.length inst.bytes;
          Hashtbl.add db.inst_table pc inst;
          let l = length_of inst in
          let pc' = Nativeint.(pc + of_int l) in
          match inst.operation with
          | I_JMP ->
            begin match List.hd inst.operands with
              | O_offset ofs ->
                Hashtbl.add db.jump_info pc J_resolved;
                pc', [Nativeint.(pc + ofs), Edge_neutral]
              | O_imm (imm, _) ->
                Hashtbl.add db.jump_info pc J_resolved;
                pc', [imm, Edge_neutral]
              | _ ->
                Hashtbl.add db.jump_info pc J_unknown;
                pc', []
            end
          | I_JMPF -> failwith "cannot handle far jump"
          | I_CALLF -> failwith "cannot handle far call"
          | I_CJMP ->
            begin match List.hd inst.operands with
              | O_offset ofs ->
                Hashtbl.add db.jump_info pc J_resolved;
                pc', [pc', Edge_false; Nativeint.(pc + ofs), Edge_true]
              | O_imm (imm, _) ->
                Hashtbl.add db.jump_info pc J_resolved;
                pc', [pc', Edge_false; imm, Edge_true]
              | _ ->
                Hashtbl.add db.jump_info pc J_unknown;
                pc', [pc', Edge_false]
            end
          | I_RET | I_RETF | I_RETN ->
            Hashtbl.add db.jump_info pc J_ret;
            pc', []
          | _ ->
            if inst.operation = I_CALL then
              Hashtbl.add db.jump_info pc J_call;
            if Itree.find pc' !span = Itree.Start then
              pc', [pc', Edge_neutral]
            else
              loop pc'
        in
        let pc', dests = loop pc in
        span := Itree.add (pc,pc') !span;
        dests |> List.iter begin fun (dest, attr) ->
          edges := (pc', dest, attr) :: !edges;
          (* If dest is strictly between start(b) and end(b) for some basic
             block b, then split b at dest.  If dest equals start(b) for some b,
             then do nothing.  Otherwise add dest to queue.  *)
          Queue.add dest q
        end
    end
  done;
  let span = !span in
  let start_end_list = Itree.to_list span in
  let entry_bb = { start = init_pc; stop = init_pc; stmts = [] } in
  let basic_blocks =
    entry_bb :: (start_end_list |> List.map begin fun (start, stop) ->
        let rec loop pc insts =
          let inst = Hashtbl.find db.inst_table pc in
          let insts' = inst :: insts in
          let pc' = Nativeint.(pc + of_int (length_of inst)) in
          if pc' = stop then insts' else loop pc' insts'
        in
        let insts = List.rev (loop start []) in
        { start; stop; stmts = insts }
      end)
  in
  let n = List.length basic_blocks in
  let start_table = Hashtbl.create 0 in
  let end_table = Hashtbl.create 0 in
  basic_blocks |> List.iteri begin fun i bb ->
    if i > 0 then begin
      Hashtbl.add start_table bb.start i;
      Hashtbl.add end_table bb.stop i
    end
  end;
  let entry = Hashtbl.find start_table init_pc in
  Printf.printf "entry=%d\n" entry;
  let succ = Array.make n [] in
  let pred = Array.make n [] in
  let edges =
    (0, entry, Edge_neutral) :: begin
      !edges |> List.map begin fun (stop, start, attr) ->
        let from_id = Hashtbl.find end_table stop in
        let to_id = Hashtbl.find start_table start in
        from_id, to_id, attr
      end
    end
  in
  edges |> List.iter begin fun (from_id, to_id, attr) ->
    succ.(from_id) <- to_id :: succ.(from_id);
    pred.(to_id) <- from_id :: pred.(to_id);
  end;
  for i=0 to n-1 do
    succ.(i) <- List.rev succ.(i);
    pred.(i) <- List.rev pred.(i)
  done;
  let cfg = { node = Array.of_list basic_blocks; succ; pred; edges } in
  let nbb = Array.length cfg.node in
  Printf.printf "%nx: %d basic %s\n" init_pc nbb (if nbb=1 then "block" else "blocks");
  print_cfg cfg;
  let inst_cs = Fold_cfg.fold_cfg ~debug:false cfg in
  let env = Env.create db in
  let stmt_cs =
    inst_cs |> map_ctlstruct (Elaborate.elaborate_basic_block env)
  in
  let il = Pseudocode.convert stmt_cs in
  { cfg; inst_cs; stmt_cs; span; il }
