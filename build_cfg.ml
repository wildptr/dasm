open Batteries
open Cfg
open Inst

type string_iter = {
  str : string;
  mutable pos : int;
}

let build_cfg db init_pc init_offset =
  let open Database in
  let code = db.code in
  let start_end = ref Itree.empty in
  let edges = ref [] in (* from end of basic block to start of basic block *)
  let q = Queue.create () in
  Queue.add init_pc q;
  let s = { str = code; pos = 0 } in
  while not (Queue.is_empty q) do
    let pc = Queue.pop q in
    begin match Itree.find pc !start_end with
      | Itree.Start -> ()
      | Itree.Middle ->
        start_end := Itree.split pc !start_end;
        edges := (pc, pc, Edge_neutral) :: !edges
      | Itree.End | Itree.Nowhere ->
        s.pos <- init_offset + (pc - init_pc);
        let rec loop pc =
          let config = Dasm.{ mode = Mode32bit; pc_opt = Some pc } in
          let inst = Dasm.(disassemble config s.str s.pos) in
          s.pos <- s.pos + String.length inst.bytes;
          Hashtbl.add db.inst_table pc inst;
          let l = length_of inst in
          let pc' = pc+l in
          match inst.operation with
          | I_JMP ->
            begin match List.hd inst.operands with
              | O_offset ofs ->
                Hashtbl.add db.jump_info pc Semant.J_resolved;
                pc', [pc + Nativeint.to_int ofs, Edge_neutral]
              | _ ->
                Hashtbl.add db.jump_info pc Semant.J_unknown;
                pc', []
            end
          | I_JMPF -> failwith "cannot handle far jump"
          | I_CALLF -> failwith "cannot handle far call"
          | I_CJMP ->
            begin match List.hd inst.operands with
              | O_offset ofs ->
                Hashtbl.add db.jump_info pc Semant.J_resolved;
                pc', [pc', Edge_false; pc + Nativeint.to_int ofs, Edge_true]
              | _ ->
                Hashtbl.add db.jump_info pc Semant.J_unknown;
                pc', [pc', Edge_false]
            end
          | I_RET | I_RETF | I_RETN ->
            Hashtbl.add db.jump_info pc Semant.J_ret;
            pc', []
          | _ ->
            if inst.operation = I_CALL then
              Hashtbl.add db.jump_info pc Semant.J_call;
            if Itree.find pc' !start_end = Itree.Start then
              pc', [pc', Edge_neutral]
            else
              loop pc'
        in
        let pc', dests = loop pc in
        start_end := Itree.add (pc,pc') !start_end;
        dests |> List.iter begin fun (dest, attr) ->
          edges := (pc', dest, attr) :: !edges;
          (* If dest is strictly between start(b) and end(b) for some basic
             block b, then split b at dest.  If dest equals start(b) for some b,
             then do nothing.  Otherwise add dest to queue.  *)
          Queue.add dest q
        end
    end
  done;
  let start_end_list = Itree.to_list !start_end in
  let basic_blocks =
    start_end_list |> List.map begin fun (start, stop) ->
      let rec loop pc insts =
        let inst = Hashtbl.find db.inst_table pc in
        let insts' = inst :: insts in
        let pc' = pc + length_of inst in
        if pc' = stop then insts' else loop pc' insts'
      in
      let insts = List.rev (loop start []) in
      { start; stop; stmts = insts }
    end
  in
  let n = List.length basic_blocks in
  let start_table = Hashtbl.create 0 in
  let end_table = Hashtbl.create 0 in
  basic_blocks |> List.iteri (fun i bb ->
      Hashtbl.add start_table bb.start i;
      Hashtbl.add end_table bb.stop i);
  let succ = Array.make n [] in
  let pred = Array.make n [] in
  let edges =
    !edges |> List.map begin fun (stop, start, attr) ->
      let from_id = Hashtbl.find end_table stop in
      let to_id = Hashtbl.find start_table start in
      succ.(from_id) <- to_id :: succ.(from_id);
      pred.(to_id) <- from_id :: pred.(to_id);
      from_id, to_id, attr
    end
  in
  for i=0 to n-1 do
    succ.(i) <- List.rev succ.(i);
    pred.(i) <- List.rev pred.(i)
  done;
  { node = Array.of_list basic_blocks; succ; pred; edges }
