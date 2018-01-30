open Batteries
open Cfg

type color =
  | Black
  | Red
  | Green

type node = {
  mutable x : int;
  mutable y : int;
  mutable width : int;
  mutable height : int;
  mutable text : string list;
  is_virtual : bool;
  color : color;
}

type segment = (int * int) list * color

type layout = {
  nodes : node array;
  connections : segment list array;
  width : int;
  height : int;
}

type top_bot = Top | Bot

let node_width = 256
let margin = 4
let text_height = 16
let text_height_f = float_of_int text_height

let layout_cfg cfg =
  let n = Array.length cfg.node in
  let succ = Array.make n [] in
  let npred = Array.make n 0 in
  cfg.edges |> List.iter begin fun (src, dst, _) ->
    if src < dst then begin
      succ.(src) <- dst :: succ.(src);
      npred.(dst) <- npred.(dst) + 1
    end else if src > dst then begin
      succ.(dst) <- src :: succ.(dst);
      npred.(src) <- npred.(src) + 1
    end
  end;
  let node_col = Array.make n 0 in
  let ncol = ref 0 in
  (* topological sort *)
  let rec loop nodes acc =
    let current_rank, rest = List.partition (fun i -> npred.(i) = 0) nodes in
    let acc' = current_rank :: acc in
    current_rank |> List.iter (fun i ->
        succ.(i) |> List.iter (fun s ->
            npred.(s) <- npred.(s) - 1));
    current_rank |> List.iteri (fun x i -> node_col.(i) <- x);
    let w = List.length current_rank in
    ncol := max !ncol w;
    if rest = [] then Array.of_list (List.rev acc') else loop rest acc'
  in
  let all_ranks = loop (List.range 0 `To (n-1)) [] in
  let ncol = !ncol in
  let node_rank = Array.make n 0 in
  all_ranks |> Array.iteri (fun r nodes ->
      nodes |> List.iter (fun i ->
          (* node i has rank r *)
          node_rank.(i) <- r));
  let nrank = Array.length all_ranks in
  let con = Array.make (nrank-1) [] in
  (* compute the number of virtual nodes needed *)
  let nvirt = ref 0 in
  cfg.edges |> List.iter begin fun (src, dst, _) ->
    let sr = node_rank.(src) in
    let dr = node_rank.(dst) in
    nvirt := !nvirt + abs (dr-sr-1)
  end;
  let nvirt = !nvirt in
  let nvpath = ref 0 in
  let n' = n + nvirt in
  (* extend node_rank *)
  let node_rank =
    let node_rank' = Array.make n' 0 in
    Array.blit node_rank 0 node_rank' 0 n;
    node_rank'
  in
  let next_vid = ref n in
  let vpath_cols = ref [] in
  let vnode_vpath = Array.make nvirt 0 in
  let vnode_color = Array.make nvirt Black in
  cfg.edges |> List.iter begin fun (src, dst, attr) ->
    let sr = node_rank.(src) in
    let dr = node_rank.(dst) in
    let vnode_ranks =
      if dr > sr then
        if dr > sr+1 then List.range (sr+1) `To (dr-1) else []
      else
        List.range sr `Downto dr
    in
    let vpath = !nvpath in
    if vnode_ranks <> [] then begin
      incr nvpath;
      let vpath_col = min node_col.(src) node_col.(dst) in
      vpath_cols := vpath_col :: !vpath_cols
    end;
    let edge_color =
      let open Control_flow in
      match attr with
      | Edge_normal -> Black
      | Edge_taken -> Green
      | Edge_not_taken -> Red
    in
    (* add v-nodes *)
    let vnodes =
      vnode_ranks |> List.map begin fun vr ->
        let vid = !next_vid in
        incr next_vid;
        (*             all_ranks.(vr) <- vid :: all_ranks.(vr); *)
        node_rank.(vid) <- vr;
        vnode_vpath.(vid-n) <- vpath;
        vnode_color.(vid-n) <- edge_color;
        vid
      end
    in
    (* add connections *)
    List.combine (src :: vnodes) (vnodes @ [dst]) |> List.iter begin fun (f,t) ->
      let fr = node_rank.(f) in
      let tr = node_rank.(t) in
      let cr =
        if fr = tr then
          if f >= n then
            (* from virtual to real *)
            fr-1
          else
            (* from real to virtual *)
            fr
        else
          min fr tr
      in
      con.(cr) <- (f, t, edge_color) :: con.(cr)
    end;
  end;

  let vpath_col = Array.of_list (List.rev !vpath_cols) in
  let nvpath = !nvpath in
  (* offset is relative to x of node at specified column *)
  let vpath_x_offset = Array.make nvpath 0 in
  let col_nvpath = Array.make ncol 0 in
  vpath_col |> Array.iteri begin fun vpath col ->
    let nvp = col_nvpath.(col) in
    col_nvpath.(col) <- nvp + 1;
    vpath_x_offset.(vpath) <- -8*(nvp+1)
  end;

  let nodes =
    Array.init n' begin fun i ->
      let text =
        if i < n then
          let insts = cfg.node.(i).stmts in
          insts |> List.map begin fun inst ->
            let buf = Buffer.create 0 in
            let fmtr = Format.formatter_of_buffer buf in
            Inst.pp fmtr inst;
            Format.pp_print_flush fmtr ();
            Buffer.contents buf
          end
        else []
      in
      let nline = List.length text in
      let height = text_height * nline + margin*2 in
      let color = if i < n then Black else vnode_color.(i-n) in
      { x = 0; y = 0; width = if i>=n then 0 else node_width; height;
        text; is_virtual = i>=n; color }
    end
  in

  (* determine x for each real node *)
  let col_x = Array.make ncol 0 in
  let x = ref 0 in
  for col=0 to ncol-1 do
    x := !x + col_nvpath.(col) * 8;
    col_x.(col) <- !x;
    x := !x + node_width + 8
  done;
  for i=0 to n-1 do
    let col = node_col.(i) in
    nodes.(i).x <- col_x.(col)
  done;

  (* determine x for each virtual node *)
  for v=0 to nvirt-1 do
    let vpath = vnode_vpath.(v) in
    let col = vpath_col.(vpath) in
    let offset = vpath_x_offset.(vpath) in
    nodes.(n+v).x <- col_x.(col) + offset
  done;

  let deg_top = Array.make n' 0 in
  let deg_bot = Array.make n' 0 in
  let con' =
    con |> Array.mapi begin fun r0 c ->
      c |> List.map begin fun (src, dst, color) ->
        let sr = node_rank.(src) in
        let dr = node_rank.(dst) in
        if sr < dr then begin
          assert (sr+1 = dr);
          let sj = deg_bot.(src) in
          let dj = deg_top.(dst) in
          deg_bot.(src) <- sj + 1;
          deg_top.(dst) <- dj + 1;
          (Bot, src, sj), (Top, dst, dj), color
        end else if sr > dr then begin
          assert (sr = dr+1);
          let sj = deg_top.(src) in
          let dj = deg_bot.(dst) in
          deg_top.(src) <- sj + 1;
          deg_bot.(dst) <- dj + 1;
          (Top, src, sj), (Bot, dst, dj), color
        end else begin
          (* sr = dr *)
          if src >= n then begin
            (* virt -> real, top -> top *)
            let sj = deg_top.(src) in
            let dj = deg_top.(dst) in
            deg_top.(src) <- sj + 1;
            deg_top.(dst) <- dj + 1;
            (Top, src, sj), (Top, dst, dj), color
          end else begin
            let sj = deg_bot.(src) in
            let dj = deg_bot.(dst) in
            deg_bot.(src) <- sj + 1;
            deg_bot.(dst) <- dj + 1;
            (Bot, src, sj), (Bot, dst, dj), color
          end
        end
      end
    end
  in
  let x_start_top =
    Array.init n' (fun i -> nodes.(i).x + nodes.(i).width / 2 - 4*(deg_top.(i)-1))
  in
  let x_start_bot =
    Array.init n' (fun i -> nodes.(i).x + nodes.(i).width / 2 - 4*(deg_bot.(i)-1))
  in
  let y_of_rank = Array.make nrank 0 in
  let rank_height =
    Array.init nrank begin fun rank ->
      all_ranks.(rank) |> List.map (fun i -> nodes.(i).height) |> List.max
    end
  in
  (* fix height of virtual nodes *)
  for i=n to n'-1 do
    let rank = node_rank.(i) in
    nodes.(i).height <- rank_height.(rank)
  done;
  let connections =
    con' |> Array.mapi begin fun r0 c ->
      let nc = List.length c in
      c |> List.mapi begin fun ci ((stb, si, sj), (dtb, di, dj), color) ->
        let sx =
          match stb with
          | Top -> x_start_top.(si) + 8*sj
          | Bot -> x_start_bot.(si) + 8*sj
        in
        let dx =
          match dtb with
          | Top -> x_start_top.(di) + 8*dj
          | Bot -> x_start_bot.(di) + 8*dj
        in
        let bot_y = y_of_rank.(r0) + rank_height.(r0) in
        let top_y = bot_y + 8*(nc+1) in
        y_of_rank.(r0+1) <- top_y;
        let sy =
          match stb with
          | Top -> top_y
          | Bot -> bot_y
        in
        let dy =
          match dtb with
          | Top -> top_y
          | Bot -> bot_y
        in
        if sx = dx then
          [sx,sy;dx,dy], color
        else
          let lane_y = bot_y + (1+ci)*8 in
          [sx,sy;sx,lane_y;dx,lane_y;dx,dy], color
      end
    end
  in

  (* determine y for each node *)
  for i=0 to n'-1 do
    let r = node_rank.(i) in
    nodes.(i).y <- y_of_rank.(r)
  done;

  (* compute width & height of whole layout *)
  let width = ref 0 in
  let height = ref 0 in
  for r=0 to nrank-1 do
    all_ranks.(r) |> List.iteri (fun x i ->
        width := max !width (nodes.(i).x + nodes.(i).width);
        height := max !height (nodes.(i).y + nodes.(i).height))
  done;

  { nodes; connections; width = !width; height = !height }
