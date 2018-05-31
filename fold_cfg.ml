open Batteries
open Cfg
open Control_flow

exception Break

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