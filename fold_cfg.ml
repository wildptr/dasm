open Batteries
open Cfg
open Control_flow
open Printf

exception Break

type 'a folding_cfg = {
  size : int;
  node : 'a ctlstruct array;
  succ : int list array;
  pred : int list array;
  succ_attr : edge_attr list array;
  parent : int array;
  children : int list array;
}

module S = Set.Int

let debug = false

let address_of g i =
  start_of_ctlstruct g.node.(i)

let rec nodes_in g i =
  g.children.(i) |>
  List.map (nodes_in g) |>
  List.fold_left S.union S.empty |>
  S.add i

let check_consistency g =
  let reachable = Array.make g.size false in
  begin
    let rec dfs i =
      if not (reachable.(i)) then begin
        reachable.(i) <- true;
        g.succ.(i) |> List.iter dfs;
        g.pred.(i) |> List.iter dfs;
        g.children.(i) |> List.iter dfs
      end
    in
    dfs 0
  end;
  (* printf "reachable:";
     reachable |> Array.iteri begin fun i r ->
     if r then printf " %d" i
     end;
     printf "\n"; *)
  g.succ |> Array.iteri begin fun i s ->
    if reachable.(i) then begin
      assert (List.length s = S.cardinal (S.of_list s));
      s |> List.iter begin fun j ->
        assert (List.mem i g.pred.(j))
      end
    end
  end;
  g.pred |> Array.iteri begin fun j p ->
    if reachable.(j) then begin
      assert (List.length p = S.cardinal (S.of_list p));
      p |> List.iter begin fun i ->
        assert (List.mem j g.succ.(i))
      end
    end
  end;
  let parent' = compute_idom g.succ g.pred in
  parent' |> Array.iteri begin fun i p ->
    if reachable.(i) then begin
      if g.parent.(i) <> p then begin
        Printf.printf "parent of %nx is %nx ,should be %nx\n"
          (address_of g i) (address_of g g.parent.(i)) (address_of g p);
        assert false
      end
    end
  end;
  let children' = Array.make g.size [] in
  parent' |> Array.iteri begin fun i p ->
    if p >= 0 then children'.(p) <- i :: children'.(p)
  end;
  children' |> Array.iteri begin fun i c ->
    if reachable.(i) then begin
      assert (S.cardinal (S.of_list c) = List.length c);
      assert (S.equal (S.of_list c) (S.of_list g.children.(i)))
    end
  end

let get_edge_attr g i j =
  List.combine g.succ.(i) g.succ_attr.(i) |>
  List.find (fun (j', a) -> j' = j) |> snd

let add_edge' g i j a =
  if debug then begin
    Printf.printf "adding edge %nx -> %nx (%d)\n" (address_of g i) (address_of g j) (Obj.magic a)
  end;
  g.succ.(i) <- j :: g.succ.(i);
  g.succ_attr.(i) <- a :: g.succ_attr.(i);
  g.pred.(j) <- i :: g.pred.(j)

let add_edge g i j = add_edge' g i j Edge_neutral

let remove_edge' g i j =
  let a = get_edge_attr g i j in
  if debug then begin
    Printf.printf "removing edge %nx -> %nx (%d)\n" (address_of g i) (address_of g j) (Obj.magic a)
  end;
  let ind_j = List.index_of j g.succ.(i) |> Option.get in
  g.succ.(i) <- List.remove_at ind_j g.succ.(i);
  g.succ_attr.(i) <- List.remove_at ind_j g.succ_attr.(i);
  let ind_i = List.index_of i g.pred.(j) |> Option.get in
  g.pred.(j) <- List.remove_at ind_i g.pred.(j);
  a

let remove_edge g i j = remove_edge' g i j |> ignore

let is_fork g i =
  match g.succ_attr.(i) with
  | [Edge_true; Edge_false]
  | [Edge_false; Edge_true] -> true
  | [_;_] -> Printf.printf "is_fork: unusual case (%d)\n" i; false
  | _ -> false

let try_fold_seq g entry body =
  try
    if g.succ.(entry) <> [body] || g.pred.(body) <> [entry] then raise Break;
(*     remove_final_jump g.node.(entry); *)
    let exits_list = g.succ.(body) in
    if debug then begin
      printf "seq (%nx,%nx) -> [" (address_of g entry) (address_of g body);
      exits_list |> List.map (address_of g) |> List.iter (printf " %nx");
      printf " ]\n";
    end;
    g.node.(entry) <- Seq (g.node.(entry), g.node.(body));
    remove_edge g entry body;
    let attr_list = g.succ.(body) |> List.map (fun i -> remove_edge' g body i) in
    List.combine exits_list attr_list |> List.iter (fun (i,a) -> add_edge' g entry i a);
    g.children.(entry) <- g.children.(body);
    g.children.(body) |> List.iter (fun i -> g.parent.(i) <- entry);
    if debug then check_consistency g;
    true
  with Break -> false

let rec dominates g i j =
  if i=j then true
  else if j=0 then false
  else dominates g i g.parent.(j)

let check_clump g body =
  let nodes = nodes_in g body in
  (* all edges into nodes are from entry *)
  (* if not (pred.(body) |> List.for_all begin fun i ->
      i = entry || S.mem i nodes
     end) then
     raise Break; *)
  nodes |> S.iter begin fun i ->
    (* all edges into nodes are to body *)
    if i <> body then begin
      if not (g.pred.(i) |> List.for_all (fun j -> S.mem j nodes)) then
        raise Break
    end;
    (* none of the outgoing edges is a backward edge *)
    g.succ.(i) |> List.iter begin fun j ->
      if not (S.mem j nodes) && dominates g j i then raise Break
    end
  end;
  nodes

let try_fold_if g entry body =
  try
    if not (is_fork g entry && g.pred.(body) = [entry]) then raise Break;
    let exit =
      match g.succ.(entry) with
      | [a;b] ->
        if body = a then b
        else if body = b then a
        else raise Break
      | _ -> raise Break
    in
    let has_exit =
      match g.succ.(body) with
      | [] -> false
      | [i] when i = exit -> true
      | _ -> raise Break
    in
    let t = get_edge_attr g entry body = Edge_true in
    if debug then begin
      printf "if (%nx,%b,%nx,%b) -> %nx\n" (address_of g entry) t (address_of g body) has_exit (address_of g exit)
    end;
    g.node.(entry) <- If (g.node.(entry), t, g.node.(body), address_of g exit);
    remove_edge g entry body;
    if has_exit then remove_edge g body exit;
    g.children.(entry) <- List.remove g.children.(entry) body;
    if debug then check_consistency g;
    true
  with Break -> false

let try_fold_if_else g entry body1 body2 =
  try
    if not begin
        is_fork g entry &&
        g.pred.(body1) = [entry] &&
        g.pred.(body2) = [entry]
      end then raise Break;
    let exit =
      match g.succ.(body1) with
      | [i] -> i
      | _ -> raise Break
    in
    if g.succ.(body2) <> [exit] then raise Break;
    let t = get_edge_attr g entry body1 = Edge_true in
    g.node.(entry) <- IfElse (g.node.(entry), t, g.node.(body1), g.node.(body2), address_of g exit);
    if debug then begin
      printf "if-else (%nx,%b,%nx,%nx) -> %nx\n" (address_of g entry) t (address_of g body1) (address_of g body2) (address_of g exit)
    end;
    remove_edge g entry body1;
    remove_edge g entry body2;
    remove_edge g body1 exit;
    remove_edge g body2 exit;
    add_edge g entry exit;
    g.children.(entry) <-
      g.children.(entry) |> List.filter (fun i -> i <> body1 && i <> body2);
    if debug then check_consistency g;
    true
  with Break -> false

let try_fold_do_while g entry =
  try
    let exit =
      match g.succ.(entry) with
      | [i;j] ->
        if i = entry then j
        else if j = entry then i
        else raise Break
      | _ -> raise Break
    in
    let t = get_edge_attr g entry entry = Edge_true in
    if debug then
      printf "do-while (%nx,%b) -> %nx\n" (address_of g entry) t
        (address_of g exit);
    g.node.(entry) <- DoWhile (g.node.(entry), t, address_of g exit);
    (* just remove the backward edge *)
    remove_edge g entry entry;
    if debug then check_consistency g;
    true
  with Break -> false

let rec fold_cfg_rec g entry =
  g.children.(entry) |> List.iter (fold_cfg_rec g);
  if debug then Printf.printf "folding %nx\n" (address_of g entry);
  let rec loop () =
    if begin
      match g.succ.(entry) with
      | [] -> false
      | [i] ->
        try_fold_seq g entry i ||
        is_fork g entry && try_fold_if g entry i
      | [i;j] ->
        is_fork g entry && begin
          try_fold_if g entry i ||
          try_fold_if g entry j ||
          try_fold_if_else g entry i j ||
          try_fold_do_while g entry
        end
      | _ -> false
    end
    then loop ()
  in
  loop ();
  try
    let nodes = check_clump g entry in
    fold_generic g entry nodes
  with Break ->
    if debug then begin
      Printf.printf "could not fold_generic %nx\n" (address_of g entry);
(*
      let nodes = nodes_in entry in
      print_string "nodes:";
      nodes |> S.iter ( Printf.printf " %d" );
      print_endline "";
      (* all edges into nodes are to entry *)
      nodes |> S.iter begin fun i ->
        if i <> entry then begin
          pred i |> List.iter begin fun j ->
            if not (S.mem j nodes) then Printf.printf "%d -> %d\n" j i
          end
        end
      end
*)
    end

and fold_generic g entry nodes =
  let rest = S.remove entry nodes in
  (* already fully reduced? *)
  if not (S.equal rest S.empty) then begin
    let exits =
      let temp = ref S.empty in
      nodes |> S.iter begin fun i ->
        g.succ.(i) |> List.iter begin fun j ->
          if not (S.mem j nodes) then temp := S.add j !temp
        end
      end;
      !temp
    in
    let exit_list = S.to_list exits in
    let new_node =
      try
        raise Break
(*
        if debug then Printf.printf "do-while with break? %nx\n" (address_of g entry);
        (* do-while with break statements? *)
        let fork =
          match g.pred.(entry) |> List.filter (fun i -> S.mem i nodes_set) with
          | [i] -> i
          | _ ->
            if debug then Printf.printf "no fork\n";
            raise Break
        in
        if not (is_fork g fork) then begin
          if debug then Printf.printf "%nx is not a fork\n" (address_of g fork);
          raise Break
        end;
        let exit =
          match g.succ.(fork) with
          | [i;j] -> if entry = i then j else i
          | _ -> assert false
        in
        let body =
          if dominates g entry exit then
            S.diff nodes_set (nodes_in g exit)
          else
            nodes_set
        in
        body |> S.iter begin fun i ->
          g.succ.(i) |> List.iter begin fun j ->
            if not (S.mem j body) && j <> exit then raise Break
          end
        end;
        if debug then begin
          Printf.printf "do-while with break [";
          body |> S.iter (fun i -> Printf.printf " %nx" (address_of g i));
          Printf.printf " ] -> %nx\n" (address_of g exit)
        end;
        (* index in subgraph *)
        let next_break_id = ref (S.cardinal nodes_set) in
        let break_id_tab = Hashtbl.create 0 in
        g.pred.(exit) |> List.iter begin fun i ->
          if i <> fork && S.mem i body then begin
            Hashtbl.add break_id_tab i !next_break_id;
            incr next_break_id
          end
        end;
        let n_break = !next_break_id - S.cardinal nodes_set in
        let break_id = Hashtbl.find break_id_tab in
        let break = BreakLoop (start_of_ctlstruct g.node.(exit)) in
        let nodes' = nodes @ exits_list in
        let t = Array.make g.size (-1) in
        let n' = List.length nodes' + n_break in
        let node' = Array.make n' break in
        nodes' |> List.iteri begin fun i' i ->
          t.(i) <- i';
          node'.(i') <-
            if i = exit then
              break
            else if S.mem i exits then
              Virtual (start_of_ctlstruct g.node.(i))
            else
              g.node.(i)
        end;
        let succ' = Array.make n' [] in
        let succ_attr' = Array.make n' [] in
        let pred' = Array.make n' [] in
        nodes |> List.iter begin fun i ->
          let i' = t.(i) in
          assert (i' >= 0);
          g.succ.(i) |> List.iter begin fun j ->
            let j' =
              if j = exit then break_id i else t.(j)
            in
            if j' >= 0 then begin
              let a = get_edge_attr g i j in
              succ'.(i') <- j' :: succ'.(i');
              succ_attr'.(i') <- a :: succ_attr'.(i');
              pred'.(j') <- i' :: pred'.(j')
            end
          end
        end;
        let parent' = compute_idom succ' pred' in
        let children' = Array.make n' [] in
        parent' |> Array.iteri begin fun i p ->
          if p >= 0 then children'.(p) <- i :: children'.(p)
        end;
        let g' = { size = n'; node = node'; succ = succ'; succ_attr = succ_attr'; pred = pred'; parent = parent'; children = children' } in
        fold_cfg_rec g' entry;
        g'.node.(0)
*)
      with Break ->
(*
        let nodes' = nodes @ exits_list in (* compact subgraph *)
        let t = Array.make g.size (-1) in
        let n' = List.length nodes' in
        let node' = Array.make n' (Virtual 0n) in
        nodes' |> List.iteri begin fun i' i ->
          t.(i) <- i';
          node'.(i') <-
            if S.mem i exits then
              Virtual (start_of_ctlstruct g.node.(i))
            else
              g.node.(i)
        end;
        let edges =
          nodes |> List.map begin fun i ->
            g.succ.(i) |> List.map (fun j -> i, j, get_edge_attr g i j)
          end |> List.concat |> List.map begin fun (src, dst, attr) ->
            assert (t.(src) >= 0);
            assert (t.(dst) >= 0);
            t.(src), t.(dst), attr
          end
        in
        Generic (exits_list |> List.map (Array.get t), node', edges)
*)
        let node_list = entry :: S.to_list rest in
        if debug then begin
          printf "generic [";
          node_list |> List.map (address_of g) |> List.iter (printf " %nx");
          printf " ] -> [";
          exit_list |> List.map (address_of g) |> List.iter (printf " %nx");
          printf " ]\n";
        end;
        (* let edges' =
          let temp = ref [] in
          node_list |> List.iter begin fun i ->
            let i_va = address_of g i in
            g.succ.(i) |> List.iter begin fun j ->
              let j_va = address_of g j in
              let a = get_edge_attr g i j in
              temp := (i_va, j_va, a) :: !temp
            end
          end;
          !temp
        in *)
        Generic (node_list |> List.map (Array.get g.node) |> Array.of_list)
    in
    g.node.(entry) <- new_node;
    g.succ.(entry) |> List.iter (remove_edge g entry);
    exit_list |> List.iter (add_edge g entry);
    rest |> S.iter begin fun i ->
      g.pred.(i) |> List.iter (fun j -> if not (S.mem j rest) then remove_edge g j i);
      g.succ.(i) |> List.iter (fun j -> if not (S.mem j rest) then remove_edge g i j);
    end;
    g.children.(entry) <- [];
    if debug then check_consistency g
  end

let fold_cfg (cfg : 'a Cfg.cfg) =
  let size = Array.length cfg.node in
  let g =
    let parent = compute_idom cfg.succ cfg.pred in
    let children = Array.make size [] in
    parent |> Array.iteri begin fun i p ->
      if p >= 0 then children.(p) <- i :: children.(p)
    end;
    let succ = Array.copy cfg.succ in
    let pred = Array.copy cfg.pred in
    let edge_attr_table = Hashtbl.create 0 in
    cfg.edges |> List.iter begin fun (src, dst, attr) ->
      Hashtbl.add edge_attr_table (src, dst) attr
    end;
    let succ_attr =
      Array.init size begin fun i ->
        succ.(i) |> List.map begin fun j ->
          Hashtbl.find edge_attr_table (i, j)
        end
      end
    in
    let node =
      Array.init size begin fun i ->
        let fall_succ =
          begin match succ_attr.(i) with
            | [Edge_true; Edge_false] -> Some (List.nth succ.(i) 1)
            | [Edge_false; Edge_true] -> Some (List.nth succ.(i) 0)
            | [_] ->
              begin match succ.(i) with
                | [j] -> Some j
                | _ -> assert false
              end
            | [] -> None
            | _ -> assert false
          end |> Option.map (fun i -> cfg.node.(i).start)
        in
        BB (cfg.node.(i), fall_succ)
      end
    in
    { size; node; succ; pred; succ_attr; parent; children }
  in

  if debug then begin
    for i=0 to size-1 do
      Printf.printf "%nx ->" (address_of g i);
      g.succ.(i) |> List.map (address_of g) |> List.iter (Printf.printf " %nx");
      print_endline ""
    done
  end;

  fold_cfg_rec g 0;
  g.node.(0)
