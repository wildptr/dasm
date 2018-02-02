open Batteries
open Control_flow
open Cfg

type color =
  | Black
  | Red
  | Green

type box = {
  text : string list;
}

type segment = (int * int) list * color

type layout_shape =
  | Layout_box of box
  | Layout_composite of composite

and layout_node = {
  left : int;
  right : int;
  height: int;
  shape : layout_shape;
}

and composite = {
  nodes : (int * int * layout_node) array;
  connections : segment list;
}

type top_bot = Top | Bot

let node_spacing = 16
let line_spacing = 8

type vpath_info = {
  x : int;
  top : int; (* rank *)
  bot : int; (* rank, insclusive *)
  color : color;
}

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

let convert_to_dag n edges =
  let cfg_succ = Array.make n [] in
  edges |> List.iter begin fun (src, dst, _) ->
    cfg_succ.(src) <- dst :: cfg_succ.(src)
  end;
  let visited = Array.make n false in
  let parent = Array.make n 0 in
  let succ = Array.make n [] in
  let rec dfs p i =
    if visited.(i) then begin
      if p <> i then begin
        let a = lca parent p i in
        if a = i then (* backward edge *)
          succ.(i) <- p :: succ.(i)
        else
          succ.(p) <- i :: succ.(p)
      end
    end else begin
      visited.(i) <- true;
      parent.(i) <- p;
      if i > 0 then succ.(p) <- i :: succ.(p);
      List.iter (fun w -> dfs i w) cfg_succ.(i)
    end
  in
  dfs 0 0;
  succ

type config = {
  char_width : int;
  char_height : int;
}

let rec layout_node conf node = function
  | Absent -> assert false
  | BB i ->
    let insts = node.(i).stmts in
    let text, maxw =
      List.fold_right begin fun inst (text, maxw) ->
        let buf = Buffer.create 0 in
        let fmtr = Format.formatter_of_buffer buf in
        Inst.pp fmtr inst;
        Format.pp_print_flush fmtr ();
        let s = Buffer.contents buf in
        let w = String.length s in
        s :: text, max maxw w
      end insts ([], 0)
    in
    let width = max conf.char_width @@ maxw * conf.char_width in
    let left = -width/2 in
    let right = left+width in
    let height = max conf.char_height @@ List.length text * conf.char_height in
    { left; right; height; shape = Layout_box { text } }
  | Generic (cfg_node, edges) ->
    layout_node_generic conf node cfg_node edges
  | If (a, b, c) ->
    let a' = layout_node conf node a in
    let b' = layout_node conf node b in
    let c' = layout_node conf node c in
    let bx = line_spacing - b'.left in
    let by = a'.height + line_spacing*2 in
    let cy = by + b'.height + line_spacing*2 in
    let left = List.min [a'.left;bx+b'.left;c'.left] in
    let right = List.max [a'.right;bx+b'.right;c'.right] in
    let height = cy + c'.height in
    let nodes = [|0,0,a';bx,by,b';0,cy,c'|] in
    let ay1 = a'.height in
    let by1 = by + b'.height in
    let connections =
      [[0,ay1;0,cy],Black;
       [line_spacing,ay1;line_spacing,ay1+line_spacing;bx,ay1+line_spacing;bx,by],Black;
       [bx,by1;bx,by1+line_spacing;line_spacing,by1+line_spacing;line_spacing,cy],Black]
    in
    { left; right; height; shape = Layout_composite { nodes; connections } }
  | If_else _ -> failwith "not implemented"

and layout_node_generic conf node cfg_node edges =
  let n = Array.length cfg_node in
  let succ = convert_to_dag n edges in
  let npred = Array.make n 0 in
  succ |> Array.iter (List.iter (fun dst -> npred.(dst) <- npred.(dst) + 1));
  let node_col = Array.make n 0 in
  let node_rank = Array.make n 0 in
  (* topological sort *)
  let rec loop cur_rank ncol nodes acc =
    let nodes_in_cur_rank, rest = List.partition (fun i -> npred.(i) = 0) nodes in
    assert (nodes_in_cur_rank <> []);
    let nodes_in_cur_rank = Array.of_list nodes_in_cur_rank in
    let acc' = nodes_in_cur_rank :: acc in
    nodes_in_cur_rank |> Array.iter begin fun i ->
      succ.(i) |> List.iter (fun s -> npred.(s) <- npred.(s) - 1)
    end;
    nodes_in_cur_rank |> Array.iteri begin fun col i ->
      node_rank.(i) <- cur_rank;
      node_col.(i) <- col
    end;
    let w = Array.length nodes_in_cur_rank in
    let next_rank = cur_rank + 1 in
    let ncol' = max ncol w in
    if rest = [] then
      Array.of_list (List.rev acc'), next_rank, ncol'
    else
      loop next_rank ncol' rest acc'
  in
  let rank_nodes, nrank, ncol = loop 0 0 (List.range 0 `To (n-1)) [] in
  let rank_ncol = Array.init nrank (fun r -> Array.length rank_nodes.(r)) in
  let node_x = Array.make n 0 in
  let node_y = Array.make n 0 in
  let node_layout = cfg_node |> Array.map (layout_node conf node) in
  let node_width i = node_layout.(i).right - node_layout.(i).left in
  let node_height i = node_layout.(i).height in
  let rank_y0 = Array.make nrank 0 in
  let rank_height =
    Array.init nrank begin fun r ->
      rank_nodes.(r) |> Array.map node_height |> Array.max
    end
  in
  let rank_y1 r = rank_y0.(r) + rank_height.(r) in
  let rank_leftmost = Array.make nrank 0 in
  let rank_rightmost = Array.make nrank 0 in
  for r=0 to nrank-1 do
    let cur_rank_nodes = rank_nodes.(r) in
    let w =
      let sum = ref 0 in
      for col = 0 to rank_ncol.(r)-2 do
        let i0 = cur_rank_nodes.(col) in
        let i1 = cur_rank_nodes.(col) in
        sum := !sum + node_layout.(i0).right + node_spacing - node_layout.(i1).left
      done;
      !sum
    in
    let x = ref (-w/2) in
    rank_leftmost.(r) <- !x + node_layout.(cur_rank_nodes.(0)).left;
    cur_rank_nodes |> Array.iter begin fun i ->
      node_x.(i) <- !x;
      if i+1 < n then x := !x + node_layout.(i).right + node_spacing - node_layout.(i+1).left
    end;
    rank_rightmost.(r) <- !x + node_layout.(cur_rank_nodes.(rank_ncol.(r)-1)).right
  done;
  let succ = Array.make n [] in
  let pred = Array.make n [] in
  edges |> List.iter begin fun (src, dst, _) ->
    succ.(src) <- dst :: succ.(src);
    pred.(dst) <- src :: pred.(dst)
  end;
  let nsucc i = List.length succ.(i) in
  let npred i = List.length pred.(i) in

  let con_rev = ref [] in

  let con = Array.make (nrank-1) [] in
  let vpath_info = ref [] in
  edges |> List.map begin fun (src, dst, attr) ->
    let sj = List.index_of dst succ.(src) |> Option.get in
    let dj = List.index_of src pred.(dst) |> Option.get in
    src, dst, sj, dj, attr
  end |> List.iter begin fun (src, dst, sj, dj, attr) ->
    let sr = node_rank.(src) in
    let dr = node_rank.(dst) in
    let vnode_ranks =
      if dr > sr then
        if dr > sr+1 then List.range (sr+1) `To (dr-1) else []
      else
        List.range sr `Downto dr
    in
    let color =
      let open Control_flow in
      match attr with
      | Edge_normal -> Black
      | Edge_taken -> Green
      | Edge_not_taken -> Red
    in
    let sx =
      node_x.(src) - (nsucc(src)-1)*(line_spacing/2) + sj*line_spacing
    in
    let dx =
      node_x.(dst) - (npred(dst)-1)*(line_spacing/2) + dj*line_spacing
    in
    if vnode_ranks <> [] then begin
      (* compute x for vpath *)
      let x_left =
        (vnode_ranks |> List.map (fun vr -> rank_leftmost.(vr)) |> List.min) - line_spacing
      in
      let x_right =
        (vnode_ranks |> List.map (fun vr -> rank_rightmost.(vr)) |> List.max) + line_spacing
      in
      let dist_left =
        abs (node_x.(src) - x_left) + abs (node_x.(dst) - x_left)
      in
      let dist_right =
        abs (node_x.(src) - x_right) + abs (node_x.(dst) - x_right)
      in
      let x =
        if dist_left < dist_right then begin
          vnode_ranks |> List.iter (fun vr -> rank_leftmost.(vr) <- x_left);
          x_left
        end else begin
          vnode_ranks |> List.iter (fun vr -> rank_rightmost.(vr) <- x_right);
          x_right
        end
      in
      let top, bot =
        if dr > sr then (* forward *)
          sr+1, dr-1
        else (* backward *)
          dr, sr
      in
      vpath_info := { x; top; bot; color } :: !vpath_info;
      if dr > sr then begin
        (* forward *)
        con.(sr) <- ((Bot, sx), (Top, x), color) :: con.(sr);
        con.(dr-1) <- ((Bot, x), (Top, dx), color) :: con.(dr-1)
      end else begin
        (* backward *)
        con.(sr) <- ((Bot, sx), (Bot, x), color) :: con.(sr);
        con.(dr-1) <- ((Top, x), (Top, dx), color) :: con.(dr-1)
      end
    end else begin
      con.(sr) <- ((Bot, sx), (Top, dx), color) :: con.(sr)
    end
  end;

  let vpath_info = Array.of_list (List.rev !vpath_info) in

  let left = Array.min rank_leftmost in
  let right = Array.max rank_rightmost in

  for r0 = 0 to nrank-2 do
    let c = con.(r0) in
    let nc = List.length c in
    let bot_y = rank_y1 r0 in
    let spacing = line_spacing*(nc+1) in
    let top_y = bot_y + spacing in
    rank_y0.(r0+1) <- top_y;
    c |> List.iteri begin fun ci ((stb, sx), (dtb, dx), color) ->
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
      let new_con =
        if sx = dx then
          [sx,sy;dx,dy], color
        else
          let lane_y = bot_y + (1+ci)*line_spacing in
          [sx,sy;sx,lane_y;dx,lane_y;dx,dy], color
      in
      con_rev := new_con :: !con_rev
    end
  done;

  vpath_info |> Array.iter begin fun { x; top; bot; color } ->
    let y0 = rank_y0.(top) in
    let y1 = rank_y1 bot in
    con_rev := ([x,y0;x,y1], color) :: !con_rev
  end;

  (* determine y for each node in range *)
  for r=0 to nrank-1 do
    rank_nodes.(r) |> Array.iter (fun i -> node_y.(i) <- rank_y0.(r))
  done;

  let height = rank_y1 (nrank-1) in
  let nodes =
    Array.init n (fun i -> node_x.(i), node_y.(i), node_layout.(i))
  in
  let connections = List.rev !con_rev in

  { left; right; height; shape = Layout_composite { nodes; connections } }
