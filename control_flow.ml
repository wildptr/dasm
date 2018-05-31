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

let build_cfg db init_pc init_offset =
  let open Database in
  let code = db.code in
  let start_end = ref Leaf in
  let edges = ref [] in (* from end of basic block to start of basic block *)
  let q = Queue.create () in
  Queue.add init_pc q;
  let s = { str = code; pos = 0 } in
  while not (Queue.is_empty q) do
    let pc = Queue.pop q in
    begin match itree_find pc !start_end with
      | Start -> ()
      | Middle ->
        start_end := itree_split pc !start_end;
        edges := (pc, pc, Edge_neutral) :: !edges
      | Nowhere ->
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
                pc', [pc+ofs, Edge_neutral]
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
                pc', [pc', Edge_false; pc+ofs, Edge_true]
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
            if itree_find pc' !start_end = Start then
              pc', [pc', Edge_neutral]
            else
              loop pc'
        in
        let pc', dests = loop pc in
        start_end := itree_add (pc,pc') !start_end;
        dests |> List.iter begin fun (dest, attr) ->
          edges := (pc', dest, attr) :: !edges;
          (* If dest is strictly between start(b) and end(b) for some basic
             block b, then split b at dest.  If dest equals start(b) for some b,
             then do nothing.  Otherwise add dest to queue.  *)
          Queue.add dest q
        end
    end
  done;
  let start_end_list = itree_to_list !start_end in
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

(* adapted from Modern Compiler Implementation in C, pp. 448-449 *)
let compute_idom succ pred =
  let n = Array.length succ in
  let bucket = Array.make n [] in
  let dfnum = Array.make n (-1) in
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
    if dfnum.(i) < 0 then begin
      dfnum.(i) <- !next_dfnum;
      vertex.(!next_dfnum) <- i;
      parent.(i) <- p;
      incr next_dfnum;
      List.iter (fun w -> dfs i w) succ.(i)
    end
  in
  dfs (-1) 0;
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

let rec map_snode f = function
  | Virtual -> Virtual
  | BB (b, nexit) -> BB (f b, nexit)
  | Seq (v1, v2) -> Seq (map_snode f v1, map_snode f v2)
  | Generic (exits, node, edges) ->
    Generic (exits, Array.map (map_snode f) node, edges)
  | If (v1, t, v2, has_exit) ->
    If (map_snode f v1, t, map_snode f v2, has_exit)
  | If_else (v1, t, v2, v3) ->
    If_else (map_snode f v1, t, map_snode f v2, map_snode f v3)
  | Do_while (v, t) -> Do_while (map_snode f v, t)
  | _ -> failwith "not implemented"

exception Break

let lca parent a b =
  let visited = Array.make (Array.length parent) false in
  let rec loop a b =
    if visited.(a) then a else begin
      visited.(a) <- true;
      if visited.(b) then b else begin
        visited.(b) <- true;
        loop parent.(a) parent.(b)
      end
    end
  in
  loop a b

let rec root parent i =
  let p = parent.(i) in
  if p < 0 then i else root parent p

let fold_cfg cfg =
  let n = Array.length cfg.node in
  let parent = compute_idom cfg.succ cfg.pred in
  let children = Array.make n [] in
  parent |> Array.iteri begin fun i p ->
    if p >= 0 then children.(p) <- i :: children.(p)
  end;
  let edge_attr_table = Hashtbl.create 0 in
  cfg.edges |> List.iter begin fun (src, dst, attr) ->
    Hashtbl.add edge_attr_table (src, dst) attr
  end;
  let succ = Array.copy cfg.succ in
  let pred = Array.copy cfg.pred in
  let succ_attr =
    Array.init n begin fun i ->
      succ.(i) |> List.map begin fun j ->
        Hashtbl.find edge_attr_table (i, j)
      end
    end
  in
  let node = Array.init n (fun i -> BB (cfg.node.(i), List.length succ.(i))) in

  let module S = BatSet.Int in

  let rec nodes_in i =
    children.(i) |> List.map nodes_in |> List.fold_left S.union S.empty |> S.add i
  in

  let rec dominates i j =
    if i = j then true
    else
      let pj = parent.(j) in
      if pj < 0 then false else dominates i pj
  in

  let fix_pred entry nodes_set exit =
    pred.(exit) <-
      pred.(exit) |> List.map begin fun i ->
        if S.mem i nodes_set then entry else i
      end |> S.of_list |> S.to_list
  in

  let check_consistency () =
    let reachable = Array.make n false in
    let rec dfs i =
      if not (reachable.(i)) then begin
        reachable.(i) <- true;
        succ.(i) |> List.iter dfs
      end
    in
    dfs 0;
    succ |> Array.iteri begin fun i s ->
      if reachable.(i) then begin
        assert (List.length s = S.cardinal (S.of_list s));
        s |> List.iter begin fun j ->
          assert (List.mem i pred.(j))
        end
      end
    end;
    pred |> Array.iteri begin fun j p ->
      if reachable.(j) then begin
        assert (List.length p = S.cardinal (S.of_list p));
        p |> List.iter begin fun i ->
          assert (List.mem j succ.(i))
        end
      end
    end;
    let parent' = compute_idom succ pred in
    parent' |> Array.iteri begin fun i p ->
      if reachable.(i) then assert (parent.(i) = p)
    end;
    let children' = Array.make n [] in
    parent' |> Array.iteri begin fun i p ->
      if p >= 0 then children'.(p) <- i :: children'.(p)
    end;
    children' |> Array.iteri begin fun i c ->
      if reachable.(i) then begin
        assert (S.cardinal (S.of_list c) = List.length c);
        assert (S.equal (S.of_list c) (S.of_list children.(i)))
      end
    end
  in

  let get_edge_attr i j =
    List.combine succ.(i) succ_attr.(i) |>
    List.find (fun (j', a) -> j' = j) |> snd
  in

  let fold_generic' entry stop_opt =
    (* determine set of nodes to be merged *)
    let nodes_set =
      begin match stop_opt with
        | Some stop ->
          let rec nodes_in' i =
            List.remove children.(i) stop |> List.map nodes_in' |>
            List.fold_left S.union S.empty |> S.add i
          in
          nodes_in' entry
        | None ->
          nodes_in entry
      end
    in
    let nodes = S.to_list nodes_set in
    (* already fully reduced? *)
    if nodes = [entry] && not (List.mem entry succ.(entry)) then ()
    else begin
      let exits = ref [] in
      nodes |> List.iter begin fun i ->
        succ.(i) |> List.iter begin fun j ->
          if not (List.mem j nodes) then
            exits := j :: !exits
        end
      end;
      let exits = S.of_list !exits in
      let exits_list = S.to_list exits in
      let nodes' = nodes @ exits_list in
      (* compact subgraph *)
      let tbl = Array.make n (-1) in
      let n' = List.length nodes' in
      let node' = Array.make n' Virtual in
      nodes' |> List.iteri begin fun i' i ->
        tbl.(i) <- i';
        if not (S.mem i exits) then node'.(i') <- node.(i)
      end;
      let edges =
        nodes |> List.map begin fun i ->
          succ.(i) |> List.map (fun j -> i, j, get_edge_attr i j)
        end |> List.concat |> List.map begin fun (src, dst, attr) ->
          assert (tbl.(src) >= 0);
          assert (tbl.(dst) >= 0);
          tbl.(src), tbl.(dst), attr
        end
      in
      Format.eprintf "generic [";
      nodes |> List.iter (Format.eprintf " %d");
      Format.eprintf " ] -> [";
      exits_list |> List.iter (Format.eprintf " %d");
      Format.eprintf " ]@.";
      node.(entry) <- Generic (exits_list |> List.map (Array.get tbl), node', edges);
      succ.(entry) <- exits_list;
      succ_attr.(entry) <- exits_list |> List.map (fun _ -> Edge_neutral);
      pred.(entry) <- pred.(entry) |> List.filter (fun i -> not (List.mem i nodes));
      exits_list |> List.iter (fix_pred entry nodes_set);
      match stop_opt with
      | Some stop ->
        children.(entry) <- [stop];
        parent.(stop) <- entry
      | None ->
        children.(entry) <- []
    end;
    check_consistency ()
  in

  let fold_generic entry =
    fold_generic' entry None
  in

  let is_fork i =
    match succ_attr.(i) with
    | [Edge_true; Edge_false]
    | [Edge_false; Edge_true] -> true
    | _ -> false
  in

  (*let is_fully_reduced i =
    children.(i) = [] && List.for_all (fun j -> j <> i) succ.(i)
  in*)

  (*let try_fold_seq entry body =
    try
      (*Format.eprintf "try_fold_seq %d %d@." entry body;
      Format.eprintf "succ[entry] =";
      succ.(entry) |> List.iter (Format.eprintf " %d");
      Format.eprintf "@.pred[body] =";
      pred.(body) |> List.iter (Format.eprintf " %d");
      Format.eprintf "@.";*)
      if succ.(entry) <> [body] then raise Break;
      pred.(body) |> List.iter begin fun i ->
        if i <> entry && not (dominates body i) then raise Break
      end;
      fold_generic body;
      let new_node = Seq (node.(entry), node.(body)) in
      Format.eprintf "seq (%d,%d)@." entry body;
      node.(entry) <- new_node;
      let exits_list = succ.(body) in
      succ.(entry) <- exits_list;
      succ_attr.(entry) <- succ_attr.(body);
      exits_list |> List.iter (fix_pred entry (S.singleton body));
      children.(entry) <- [];
      true
    with Break -> false
  in*)

  let try_fold_seq entry body =
    try
      if succ.(entry) <> [body] || pred.(body) <> [entry] then raise Break;
      let new_node = Seq (node.(entry), node.(body)) in
      let exits_list = succ.(body) in
      Format.eprintf "seq (%d,%d) -> [" entry body;
      exits_list |> List.iter (Format.eprintf " %d");
      Format.eprintf " ]@.";
      node.(entry) <- new_node;
      succ.(entry) <- exits_list;
      succ_attr.(entry) <- succ_attr.(body);
      exits_list |> List.iter (fix_pred entry (S.singleton body));
      children.(entry) <- children.(body);
      children.(body) |> List.iter (fun i -> parent.(i) <- entry);
      check_consistency ();
      true
    with Break -> false
  in

  let try_fold_if entry body =
    try
      assert (is_fork entry);
      if parent.(body) <> entry then raise Break;
      let exit =
        match succ.(entry) with
        | [a;b] ->
          if body = a then b
          else if body = b then a
          else raise Break
        | _ -> assert false
      in
      if dominates exit entry then raise Break;
      pred.(body) |> List.iter begin fun i ->
        if i <> entry && not (dominates body i) then raise Break
      end;
      let t = get_edge_attr entry body = Edge_true in
      let has_exit = ref false in
      let nodes_in_body = nodes_in body in
      nodes_in_body |> S.iter begin fun i ->
        succ.(i) |> List.iter begin fun j ->
          if j = exit then
            has_exit := true
          else if not (S.mem j nodes_in_body) then begin
            raise Break
          end
        end
      end;
      let has_exit = !has_exit in
      fold_generic body;
      let new_node = If (node.(entry), t, node.(body), has_exit) in
      Format.eprintf "if (%d,%b,%d,%b) -> %d@." entry t body has_exit exit;
      node.(entry) <- new_node;
      succ.(entry) <- [exit];
      succ_attr.(entry) <- [Edge_neutral];
      fix_pred entry nodes_in_body exit;
      children.(entry) <- List.remove children.(entry) body;
      check_consistency ();
      true
    with Break -> false
  in

  let try_fold_if_else entry body1 body2 =
    try
      assert (is_fork entry);
      if parent.(body1) <> entry then raise Break;
      if parent.(body2) <> entry then raise Break;
      if not (List.mem body1 succ.(entry)) then raise Break;
      if not (List.mem body2 succ.(entry)) then raise Break;
      let nodes_in_body1 = nodes_in body1 in
      let nodes_in_body2 = nodes_in body2 in
      let body1_exits = ref [] in
      let body2_exits = ref [] in
      nodes_in_body1 |> S.iter begin fun i ->
        succ.(i) |> List.iter begin fun j ->
          if not (S.mem j nodes_in_body1) then body1_exits := j :: !body1_exits
        end
      end;
      nodes_in_body2 |> S.iter begin fun i ->
        succ.(i) |> List.iter begin fun j ->
          if not (S.mem j nodes_in_body2) then body2_exits := j :: !body2_exits
        end
      end;
      let body1_exits = S.of_list !body1_exits in
      let body2_exits = S.of_list !body2_exits in
      let all_exits = S.union body1_exits body2_exits in
      if S.cardinal all_exits > 1 then begin
(*         Format.eprintf "multiple exits found@."; *)
        raise Break
      end;
      let body1_has_exit = S.cardinal body1_exits = 1 in
      let body2_has_exit = S.cardinal body2_exits = 1 in
      assert body1_has_exit;
      assert body2_has_exit;
      let exit = body1_exits |> S.to_list |> List.hd in
      if dominates exit entry then raise Break;
      fold_generic body1;
      fold_generic body2;
      let t = get_edge_attr entry body1 = Edge_true in
      let new_node =
        If_else (node.(entry), t, node.(body1), node.(body2))
      in
      node.(entry) <- new_node;
      Format.eprintf "if-else (%d,%b,%d,%d) -> %d@." entry t body1 body2 exit;
      succ.(entry) <- [exit];
      succ_attr.(entry) <- [Edge_neutral];
      fix_pred entry (S.union nodes_in_body1 nodes_in_body2) exit;
      children.(entry) <- children.(entry) |> List.filter (fun i -> i <> body1 && i <> body2);
      check_consistency ();
      true
    with Break -> false
  in

  let try_fold_do_while entry =
    try
      let forks =
        pred.(entry) |> List.filter begin fun i ->
          dominates entry i && is_fork i
        end
      in
      if forks = [] then raise Break;
      let fork = forks |> List.reduce (lca parent) in
      let exit =
        match succ.(fork) with
        | [a;b] ->
          if entry = a then b
          else if entry = b then a
          else raise Break
        | _ -> assert false
      in
      let exit_dominated = dominates entry exit in
      let nodes_in_body =
        if exit_dominated then
          let rec nodes_in' i =
            List.remove children.(i) exit |> List.map nodes_in' |>
            List.fold_left S.union S.empty |> S.add i
          in
          nodes_in' entry
        else
          nodes_in entry
      in
(*       Format.eprintf "do-while candidate: (%d,%d,%d)@." entry fork exit; *)
      nodes_in_body |> S.iter begin fun i ->
        succ.(i) |> List.iter begin fun j ->
          if j <> exit && not (S.mem j nodes_in_body) then begin
(*             Format.eprintf "%d -> %d out of body@." i j; *)
            raise Break
          end
        end
      end;
      let t = get_edge_attr fork entry = Edge_true in
      if entry = fork then begin
        Format.eprintf "do-while (%d,%b) -> %d@." entry t exit;
        let new_node = Do_while (node.(entry), t) in
        node.(entry) <- new_node;
        (* just remove the backward edge *)
        succ.(entry) <- [exit];
        succ_attr.(entry) <- [Edge_neutral];
        pred.(entry) <- List.remove pred.(entry) entry;
      end else begin
        fold_generic' entry (if exit_dominated then Some exit else None)
      end;
      check_consistency ();
      true
    with Break -> false
  in

  (*let try_fold_fork1 entry body exit_f =
    try
      assert (is_fork entry);
      if parent.(body) <> entry then raise Break;
      if body = entry then raise Break;
      if pred.(body) <> [entry] then raise Break;
      if not (is_fork body) then raise Break;
      let exits' = S.add exit_f (S.of_list succ.(body)) |> S.to_list in
      if List.mem body exits' then raise Break;
      let exit_t =
        match exits' with
        | [a;b] -> if a=exit_f then b else a
        | _ -> raise Break
      in
      (* if entry=t1 && body=t2 then exit_t else exit_f *)
      let t1 = get_edge_attr entry body = Edge_true in
      let t2 = get_edge_attr body exit_t = Edge_true in
      Format.eprintf "fork1 (%d,%b,%d,%b) -> t=%d f=%d@." entry t1 body t2 exit_t exit_f;
      let new_node = Fork1 (node.(entry), t1, node.(body), t2) in
      node.(entry) <- new_node;
      let exits = [exit_t; exit_f] in
      succ.(entry) <- exits;
      succ_attr.(entry) <- [Edge_true; Edge_false];
      exits |> List.iter (fix_pred entry (S.singleton body));
      children.(entry) <- List.remove children.(entry) body @ children.(body);
      children.(body) |> List.iter (fun i -> parent.(i) <- entry);
      check_consistency ();
      true
    with Break -> false
  in*)

  let rec fold_cfg_rec entry =
    children.(entry) |> List.iter fold_cfg_rec;
    let rec loop () =
      if begin
        match children.(entry) with
        | [] -> false
        | [i] ->
          try_fold_seq entry i ||
          begin
            is_fork entry && begin
              try_fold_if entry i (*||
              begin match succ.(entry) with
                | [a;b] ->
                  try_fold_fork1 entry a b ||
                  try_fold_fork1 entry b a
                | _ -> assert false
              end*)
            end
          end
        | [i;j] ->
          is_fork entry && begin
            try_fold_if entry i ||
            try_fold_if entry j ||
            try_fold_if_else entry i j (*||
            try_fold_fork1 entry i j ||
            try_fold_fork1 entry j i*)
          end
        | _ ->
          is_fork entry && begin
            match succ.(entry) with
            | [a;b] ->
              try_fold_if_else entry a b (*||
              try_fold_fork1 entry a b ||
              try_fold_fork1 entry b a*)
            | _ -> assert false
          end
      end ||
         try_fold_do_while entry
      then loop ()
    in
    loop ()
  in

  fold_cfg_rec 0;
  fold_generic 0;
  node.(0)
