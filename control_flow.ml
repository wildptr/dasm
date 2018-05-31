open Cfg

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
