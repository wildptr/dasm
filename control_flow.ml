open Batteries
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

(* adapted from Modern Compiler Implementation in C, pp. 448-449 *)
let compute_idom succ pred root =
  let n = Array.length succ in
  let bucket = Array.make n [] in
  let dfnum = Array.make n 0 in
  let semi = Array.make n (-1) in
  let ancestor = Array.make n (-1) in
  let idom = Array.make n (-1) in
  let samedom = Array.make n (-1) in
  let vertex = Array.make n 0 in
  let parent = Array.make n (-1) in
  let best = Array.make n 0 in
  let rec ancestor_with_lowest_semi v =
    let a = ancestor.(v) in
    if ancestor.(a) >= 0 then begin
      let b = ancestor_with_lowest_semi a in
      ancestor.(v) <- ancestor.(a);
      if dfnum.(semi.(b)) < dfnum.(semi.(best.(v))) then best.(v) <- b;
    end;
    best.(v)
  in
  let link p i =
    ancestor.(i) <- p;
    best.(i) <- i
  in
  let next_dfnum = ref 0 in
  let rec dfs p i =
    if dfnum.(i) = 0 then begin
      dfnum.(i) <- !next_dfnum;
      vertex.(!next_dfnum) <- i;
      parent.(i) <- p;
      incr next_dfnum;
      List.iter (fun w -> dfs i w) succ.(i)
    end
  in
  dfs (-1) root;
  let n' = !next_dfnum - 1 in
  for dfn = n' downto 1 do
    let i = vertex.(dfn) in
    let p = parent.(i) in
    (* semi-dominator of i *)
    let s =
      pred.(i) |> List.map begin fun v ->
        if dfnum.(v) <= dfnum.(i) then v
        else semi.(ancestor_with_lowest_semi v)
      end |> List.fold_left min p
    in
    semi.(i) <- s;
    bucket.(s) <- i :: bucket.(s);
    link p i;
    bucket.(p) |> List.iter begin fun v ->
      let y = ancestor_with_lowest_semi v in
      if semi.(y) = semi.(v) then idom.(v) <- p else samedom.(v) <- y
    end;
    bucket.(p) <- []
  done;
  for dfn = 1 to n' do
    let i = vertex.(dfn) in
    if samedom.(i) >= 0 then idom.(i) <- idom.(samedom.(i))
  done;
  idom

type node =
  | Absent
  | BB of int
  | Generic of node array * edge list
  | If of node * node * node
  | If_else of node * node * node * node option

exception Break

let fold_cfg cfg =
  let n = Array.length cfg.node in
  let rec fold_cfg_rec nodes node edges =
    let succ = Array.make n [] in
    let pred = Array.make n [] in
    edges |> List.iter begin fun (src, dst, _) ->
      succ.(src) <- dst :: succ.(src);
      pred.(dst) <- src :: pred.(dst)
    end;
    Format.eprintf "fold_cfg_rec";
    nodes |> List.iter (Format.eprintf " %d");
    Format.eprintf "@.";
    let parent = compute_idom succ pred (List.hd nodes) in
    let children = Array.make n [] in
    parent |> Array.iteri begin fun i p ->
      if p >= 0 then children.(p) <- i :: children.(p)
    end;
    let module S = BatSet.Int in
    let rec nodes_in i =
      children.(i) |> List.map nodes_in |> List.fold_left S.union S.empty |> S.add i
    in
    let subgraph p =
      let nodes' = nodes |> List.filter p in
      let node' = Array.init n (fun i -> if p i then node.(i) else Absent) in
      let edges' =
        edges |> List.filter (fun (src, dst, _) -> p src && p dst)
      in
      nodes', node', edges'
    in
    let recur folded new_node entry exit =
      let nodes' =
        nodes |> List.filter (fun i -> not (S.mem i folded) && i <> exit)
      in
      let node' =
        Array.init n begin fun i ->
          if i = entry then new_node
          else if i = exit || S.mem i folded then Absent
          else node.(i)
        end
      in
      let edges' =
        edges |> List.filter_map begin fun (src, dst, attr) ->
          if S.mem src folded || src = entry || S.mem dst folded || dst = exit then None
          else if src = exit then Some (entry, dst, attr)
          else Some (src, dst, attr)
        end
      in
      fold_cfg_rec nodes' node' edges'
    in
    let rec loop = function
      | [] ->
        let tbl = Array.make n 0 in
        nodes |> List.iteri (fun i' i -> tbl.(i) <- i');
        let node' = node |> Array.filter (fun x -> x <> Absent) in
        let edges' =
          edges |> List.map begin fun (src, dst, attr) ->
            tbl.(src), tbl.(dst), attr
          end
        in
        Format.eprintf "Generic";
        nodes |> List.iter (Format.eprintf " %d");
        Format.eprintf "@.";
        Generic (node', edges')
      | i :: rest ->
        begin match succ.(i) with
(*
          | [j] ->
            if i <> j && pred.(j) = [i] then begin
              let new_node = Seq (node.(i), node.(j)) in
              recur S.empty new_node i j
            end else loop rest
*)
          | [j;k] ->
            let try_fold_if br exit =
              Format.eprintf "IF candidate: (%d,%d,%d)@." i br exit;
              let nodes_in_br = nodes_in br in
              try
                let br_exits = ref [] in
                nodes_in_br |> S.iter begin fun l ->
                  succ.(l) |> List.iter begin fun m ->
                    if m <> exit && not (S.mem m nodes_in_br) then begin
                      Format.eprintf "%d -> %d dst out of branch@." l m;
                      raise Break;
                    end;
                    if m = exit then br_exits := l::!br_exits
                  end
                end;
                let br_exits = !br_exits in
                let nexit = List.length br_exits in
                if List.length pred.(exit) - 1 > nexit then begin
                  Format.eprintf "exit has too many preds@.";
                  raise Break;
                end;
                if nexit > 1 then begin
                  Format.eprintf "nexit = %d > 1@." nexit;
                  raise Break (* TODO *)
                end;
                let br_exit = List.hd br_exits in
                let nodes_br, node_br, edges_br = subgraph (fun l -> S.mem l nodes_in_br) in
                Format.eprintf "If";
                nodes_br |> List.iter (Format.eprintf " %d");
                Format.eprintf "@.";
                let br_node = fold_cfg_rec nodes_br node_br edges_br in
                let new_node = If (node.(i), br_node, node.(exit)) in
                recur nodes_in_br new_node i exit
              with Break -> loop rest
            in
            if i <> j && i <> k then
              begin match List.length pred.(j), List.length pred.(k) with
                | 1, 1 ->
                  (* if-else *)
                  loop rest
                | 1, _ ->
                  (* k is exit *)
                  try_fold_if j k
                | _, 1 ->
                  (* j is exit *)
                  try_fold_if k j
                | _, _ -> loop rest
              end
            else loop rest
          | _ -> loop rest
        end
    in
    loop nodes
  in
  fold_cfg_rec (List.range 0 `To (n-1)) (Array.init n (fun i -> BB i)) cfg.edges
