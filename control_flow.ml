open Cfg
open Inst

type itree =
  | Leaf
  | Branch of int * int * itree * itree

let rec itree_add (lo,hi) = function
  | Leaf -> Branch (lo, hi, Leaf, Leaf)
  | Branch (lo', hi', left, right) ->
    if hi <= lo' then Branch (lo', hi', itree_add (lo,hi) left, right)
    else if hi' <= lo then Branch (lo', hi', left, itree_add (lo,hi) right)
    else assert false

type itree_find_result =
  | Nowhere
  | Middle
  | Start

let rec itree_find x = function
  | Leaf -> Nowhere
  | Branch (lo, hi, left, right) ->
    if lo = x then Start
    else if lo < x && x < hi then Middle
    else if x < lo then itree_find x left
    else itree_find x right

let rec itree_split x = function
  | Leaf -> Leaf
  | Branch (lo, hi, left, right) ->
    if lo < x && x < hi then Branch (lo, x, left, Branch (x, hi, Leaf, right))
    else if x <= lo then Branch (lo, hi, itree_split x left, right)
    else Branch (lo, hi, left, itree_split x right)

let rec itree_to_list_acc acc = function
  | Leaf -> acc
  | Branch (lo, hi, left, right) ->
    itree_to_list_acc ((lo, hi) :: itree_to_list_acc acc right) left

let itree_to_list t = itree_to_list_acc [] t

type string_stream = {
  str : string;
  mutable pos : int;
}

let build_cfg code init_pc init_offset =
  let start_end = ref Leaf in
  let edges = ref [] in (* from end of basic block to start of basic block *)
  let q = Queue.create () in
  Queue.add init_pc q;
  let s = { str = code; pos = 0 } in
  let next () =
    let c = s.str.[s.pos] in
    s.pos <- s.pos + 1;
    c
  in
  let inst_table = Hashtbl.create 0 in
  let jump_info = Hashtbl.create 0 in
  while not (Queue.is_empty q) do
    let pc = Queue.pop q in
    begin match itree_find pc !start_end with
      | Start -> ()
      | Middle ->
        start_end := itree_split pc !start_end;
        edges := (pc, pc, Edge_normal) :: !edges
      | Nowhere ->
        s.pos <- init_offset + (pc - init_pc);
        let rec loop pc =
          let inst = Dasm.(disassemble Mode32bit next) in
          Hashtbl.add inst_table pc inst;
          let l = length_of inst in
          let pc' = pc+l in
          match inst.operation with
          | I_jmp ->
            begin match List.hd inst.operands with
              | O_offset ofs ->
                Hashtbl.add jump_info pc Semant.J_resolved;
                pc', [pc+ofs, Edge_normal]
              | _ ->
                Hashtbl.add jump_info pc Semant.J_unknown;
                pc', []
            end
          | I_jmpfar -> failwith "cannot handle far jump"
          | I_callfar -> failwith "cannot handle far call"
          | I_cjmp ->
            begin match List.hd inst.operands with
              | O_offset ofs ->
                Hashtbl.add jump_info pc Semant.J_resolved;
                pc', [pc', Edge_not_taken; pc+ofs, Edge_taken]
              | _ ->
                Hashtbl.add jump_info pc Semant.J_unknown;
                pc', [pc', Edge_not_taken]
            end
          | I_ret | I_retfar | I_retn ->
            Hashtbl.add jump_info pc Semant.J_ret;
            pc', []
          | _ ->
            if inst.operation = I_call then
              Hashtbl.add jump_info pc Semant.J_call;
            if itree_find pc' !start_end = Start then
              pc', [pc', Edge_normal]
            else
              loop pc'
        in
        let pc', dests = loop pc in
        start_end := itree_add (pc,pc') !start_end;
        dests |> List.iter (fun (dest, attr) ->
            edges := (pc', dest, attr) :: !edges;
            (* If dest is strictly between start(b) and end(b) for some basic
               block b, then split b at dest.  If dest equals start(b) for some b,
               then do nothing.  Otherwise add dest to queue.  *)
            Queue.add dest q)
    end
  done;
  let start_end_list = itree_to_list !start_end in
(*   let env = Semant.new_env jump_info in *)
  let basic_blocks =
    start_end_list |> List.map begin fun (start, stop) ->
      let rec loop pc insts =
        let inst = Hashtbl.find inst_table pc in
        let insts' = inst :: insts in
        (*           Elaborate.elaborate_inst env pc inst; *)
        let pc' = pc + length_of inst in
        if pc' = stop then insts' else loop pc' insts'
      in
      let insts = List.rev (loop start []) in
(*
        Expand.expand env;
        let stmts = Semant.get_stmts env in
        env.stmts_rev <- [];
*)
      { start; stop; stmts = insts }
    end
  in
  (* basic_blocks, !edges *)
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
