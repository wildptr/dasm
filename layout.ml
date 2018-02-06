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
  | Layout_none
  | Layout_box of box
  | Layout_composite of composite

and layout_node = {
  left : int;
  right : int;
  height: int;
  exit : int array;
  shape : layout_shape;
}

and composite = {
  nodes : (int * int * layout_node) array;
  connections : segment list;
}

type top_bot = Top | Bot of int

let node_spacing = 16
let line_spacing = 8

type vpath_info = {
  x : int;
  top : int; (* rank *)
  bot : int; (* rank, insclusive *)
  color : color;
}

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
        let a = Control_flow.lca parent p i in
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

let color_of_attr attr =
  let open Control_flow in
  match attr with
  | Edge_neutral -> Black
  | Edge_true -> Green
  | Edge_false -> Red

let rec layout_node conf node = function
  | Exit ->
    { left = 0; right = 0; height = 0; exit = [||]; shape = Layout_none }
  | BB (i, nexit) ->
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
    let text = Printf.sprintf "[%d]" i :: text in
    let width = max conf.char_width @@ maxw * conf.char_width in
    let left = -width/2 in
    let right = left+width in
    let height = max conf.char_height @@ List.length text * conf.char_height in
    let exit =
      Array.init nexit (fun i -> i*line_spacing-(nexit-1)*line_spacing/2)
    in
    { left; right; height; exit; shape = Layout_box { text } }
  | Generic (exits, cfg_node, edges) ->
    layout_node_generic conf exits node cfg_node edges
  | If (a, t, b, b_has_exit) ->
    let a', a_is_bb = layout_fork conf node t a in
    let b' = layout_node conf node b in
    let bx = a'.exit.(0) + line_spacing - b'.left in
    let by = a'.height + line_spacing*2 in
    let left = a'.left in
    let right = max a'.right (bx+b'.right) in
    let nodes = [|0,0,a';bx,by,b'|] in
    let ay1 = a'.height in
    let lane1 = ay1 + line_spacing in
    let by1 = by + b'.height in
    let height = by1 + line_spacing in
    let con1_color, con2_color =
      if a_is_bb then
        if t then Red, Green else Green, Red
      else Black, Black
    in
    let con_a_exit = [a'.exit.(0),ay1; a'.exit.(0),height], con1_color in
    let con_a_b =
      [a'.exit.(1),ay1; a'.exit.(1),lane1; bx,lane1; bx,by], con2_color
    in
    let connections =
      if b_has_exit then
        let con_b_exit = [bx,by1; bx,height; a'.exit.(0),height], Black in
        [con_a_exit; con_a_b; con_b_exit]
      else
        [con_a_exit; con_a_b]
    in
    { left; right; height; exit = [|0|]; shape = Layout_composite { nodes; connections } }
  | If_else (a, t, b, c, has_exit) ->
    let a', a_is_bb = layout_fork conf node t a in
    let b' = layout_node conf node b in
    let c' = layout_node conf node c in
    let w = b'.right + node_spacing - c'.left in
    let bx = -w/2 in
    let cx = bx + w in
    let left = min a'.left bx+b'.left in
    let right = max a'.right cx+c'.right in
    let bcy = a'.height + line_spacing*2 in
    let nodes = [|0,0,a';bx,bcy,b';cx,bcy,c'|] in
    let ay1 = a'.height in
    let lane1 = ay1 + line_spacing in
    let bcy1 = bcy + max b'.height c'.height in
    let lane2 = bcy1 + line_spacing in
    let c1_init_x = a'.exit.(0) in
    let c2_init_x = a'.exit.(1) in
    let con1_color, con2_color =
      if a_is_bb then
        if t then Red, Green else Green, Red
      else Black, Black
    in
    let con1 =
      [c1_init_x,ay1;c1_init_x,lane1;bx,lane1;bx,bcy], con1_color
    in
    let con2 =
      [c2_init_x,ay1;c2_init_x,lane1;cx,lane1;cx,bcy], con2_color
    in
    let con = ref [con2;con1] in
    if has_exit then begin
      let new_con = [bx,bcy+b'.height;bx,lane2;cx,lane2;cx,bcy+c'.height], Black in
      con := new_con :: !con
    end;
    let connections = List.rev !con in
    let height = if has_exit then lane2 else bcy1 in
    let exit = if has_exit then [|0|] else [||] in
    { left; right; height; exit; shape = Layout_composite { nodes; connections } }
  | Fork1 _
  | Fork2 _ -> assert false
  | Seq (a, b) ->
    let a' = layout_node conf node a in
    let b' = layout_node conf node b in
    layout_seq conf node a' b'
  | Do_while (a, t) ->
    { left = -32; right = 32; height = conf.char_height; exit = [|0|];
      shape = Layout_box { text = ["do while"] } }
  | While_true a ->
    { left = -32; right = 32; height = conf.char_height; exit = [||];
      shape = Layout_box { text = ["while true"] } }

and layout_fork conf node t = function
  | BB (_, nexit) as b ->
    assert (nexit = 2);
    layout_node conf node b, true
  | Seq (a, b) ->
    let a' = layout_node conf node a in
    let b', is_bb = layout_fork conf node t b in
    layout_seq conf node a' b', is_bb
  | Generic _ -> assert false
  | Fork1 (a, t1, b, t2) ->
    let a', a_is_bb = layout_fork conf node (t=t1) a in
    let b', b_is_bb = layout_fork conf node (t=t2) b in
    let bx =
      if t then
        a'.exit.(0) + line_spacing - b'.left
      else
        a'.exit.(1) - line_spacing - b'.right
    in
    let by = a'.height + line_spacing*2 in
    let left = min a'.left (bx+b'.left) in
    let right = max a'.right (bx+b'.right) in
    let nodes = [|0,0,a';bx,by,b'|] in
    let ay1 = a'.height in
    let lane1 = ay1 + line_spacing in
    let by1 = by + b'.height in
    let height = by1 + line_spacing in
    let con1_color, con2_color =
      if a_is_bb then
        if t1 then Red, Green else Green, Red
      else Black, Black
    in
    let con3_color, con4_color =
      if b_is_bb then
        if t2 then Red, Green else Green, Red
      else Black, Black
    in
    let con1x = if t then a'.exit.(0) else a'.exit.(1) in
    let con2x = if t then a'.exit.(1) else a'.exit.(0) in
    let con3x = bx + (if t then b'.exit.(0) else b'.exit.(1)) in
    let con4x = bx + (if t then b'.exit.(1) else b'.exit.(0)) in
    let con1 = [con1x,ay1; con1x,height], con1_color in
    let con2 = [con2x,ay1; con2x,lane1; bx,lane1; bx,by], con2_color in
    let con3 = [con3x,by1; con3x,height; con1x,height], con3_color in
    let con4 = [con4x,by1; con4x,height], con4_color in
    let exit = if t then [|con1x; con4x|] else [|con4x; con1x|] in
    let connections = [con1;con2;con3;con4] in
    { left; right; height; exit; shape = Layout_composite { nodes; connections } }, false
  | Fork2 _ ->
    { left = -32; right = 32; height = conf.char_height; exit = [|-line_spacing/2;line_spacing/2|];
      shape = Layout_box { text = ["Fork2"] } }, false
  | _ -> assert false

and layout_seq conf node a' b' =
  let by = a'.height + line_spacing in
  let left = min a'.left b'.left in
  let right = max a'.right b'.right in
  let nodes = [|0,0,a';0,by,b'|] in
  let height = by + b'.height in
  let connections = [[0,a'.height; 0,by], Black] in
  { left; right; height; exit = b'.exit; shape = Layout_composite { nodes; connections } }

and layout_node_generic conf exits node cfg_node edges =
  let n = Array.length cfg_node in
  let succ = convert_to_dag n edges in
  let npred = Array.make n 0 in
  succ |> Array.iter (List.iter (fun dst -> npred.(dst) <- npred.(dst) + 1));
  let node_col = Array.make n 0 in
  let node_rank = Array.make n 0 in
  (* topological sort *)
  let rec loop cur_rank nodes =
    let nodes_in_cur_rank, rest = List.partition (fun i -> npred.(i) = 0) nodes in
    let nodes_in_cur_rank = Array.of_list nodes_in_cur_rank in
    nodes_in_cur_rank |> Array.iter begin fun i ->
      succ.(i) |> List.iter (fun s -> npred.(s) <- npred.(s) - 1)
    end;
    nodes_in_cur_rank |> Array.iteri begin fun col i ->
      node_rank.(i) <- cur_rank;
      node_col.(i) <- col
    end;
    let next_rank = cur_rank + 1 in
    if rest = [] then
      next_rank
    else
      loop next_rank rest
  in
  let nrank = loop 0 (List.range 0 `To (n-1)) in
  exits |> List.iter begin fun i ->
    node_rank.(i) <- nrank-1
  end;
  let rank_nodes = Array.make nrank [] in
  for i=0 to n-1 do
    let r = node_rank.(i) in
    rank_nodes.(r) <- i :: rank_nodes.(r)
  done;
  let rank_nodes =
    Array.init nrank (fun r -> rank_nodes.(r) |> List.rev |> Array.of_list)
  in
  let rank_ncol = Array.init nrank (fun r -> Array.length rank_nodes.(r)) in
  let node_x = Array.make n 0 in
  let node_y = Array.make n 0 in
  let node_layout = cfg_node |> Array.map (layout_node conf node) in
(*   let node_width i = node_layout.(i).right - node_layout.(i).left in *)
  let node_height i = node_layout.(i).height in
  let rank_y0 = Array.make nrank 0 in
  let rank_height =
    Array.init nrank begin fun r ->
      rank_nodes.(r) |> Array.map node_height |> Array.max
    end
  in
  let tail_len i =
    let r = node_rank.(i) in
    rank_height.(r) - node_layout.(i).height
  in
  let rank_y1 r = rank_y0.(r) + rank_height.(r) in
  let rank_leftmost = Array.make nrank 0 in
  let rank_rightmost = Array.make nrank 0 in
  for r=0 to nrank-1 do
    let cur_rank_nodes = rank_nodes.(r) in
    let cur_rank_ncol = rank_ncol.(r) in
    let w =
      let sum = ref 0 in
      for col = 0 to cur_rank_ncol-2 do
        let i0 = cur_rank_nodes.(col) in
        let i1 = cur_rank_nodes.(col) in
        sum := !sum + node_layout.(i0).right + node_spacing - node_layout.(i1).left
      done;
      !sum
    in
    let x = ref (-w/2) in
    rank_leftmost.(r) <- !x + node_layout.(cur_rank_nodes.(0)).left;
    cur_rank_nodes |> Array.iteri begin fun col i ->
      node_x.(i) <- !x;
      if col+1 < cur_rank_ncol then
        x := !x + node_layout.(i).right + node_spacing - node_layout.(cur_rank_nodes.(col+1)).left
    end;
    rank_rightmost.(r) <- !x + node_layout.(cur_rank_nodes.(cur_rank_ncol-1)).right
  done;
  let succ = Array.make n [] in
  let pred = Array.make n [] in
  edges |> List.iter begin fun (src, dst, _) ->
    succ.(src) <- dst :: succ.(src);
    pred.(dst) <- src :: pred.(dst)
  end;
  let npred i = List.length pred.(i) in

  let con_rev = ref [] in

  let con = Array.make (nrank+1) [] in
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
    let color = color_of_attr attr in
    let sx =
      let exit_arr = node_layout.(src).exit in
      let nexit = Array.length exit_arr in
      if sj >= nexit then begin
        Format.eprintf "src=%d sj=%d nexit=%d@." src sj nexit;
        assert false
      end;
      node_x.(src) + node_layout.(src).exit.(sj)
    in
    let dx =
      node_x.(dst) - (npred(dst)-1)*(line_spacing/2) + dj*line_spacing
    in
    let src_tail_len = tail_len src in
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
        con.(sr+1) <- ((Bot src_tail_len, sx), (Top, x), color) :: con.(sr+1);
        con.(dr) <- ((Bot 0, x), (Top, dx), color) :: con.(dr)
      end else begin
        (* backward *)
        con.(sr+1) <- ((Bot src_tail_len, sx), (Bot 0, x), color) :: con.(sr+1);
        con.(dr) <- ((Top, x), (Top, dx), color) :: con.(dr)
      end
    end else begin
      con.(sr+1) <- ((Bot src_tail_len, sx), (Top, dx), color) :: con.(sr+1)
    end
  end;

  let vpath_info = Array.of_list (List.rev !vpath_info) in

  let left = Array.min rank_leftmost in
  let right = Array.max rank_rightmost in

  let height = ref 0 in

  for r0 = 0 to nrank do
    let c = con.(r0) in
    let nc = List.length c in
    let bot_y = if r0=0 then 0 else rank_y1 (r0-1) in
    let spacing = if bot_y=0 && nc=0 then 0 else line_spacing*(nc+1) in
    let top_y = bot_y + spacing in
    if r0 = nrank then
      height := bot_y + line_spacing * nc
    else
      rank_y0.(r0) <- top_y;
    c |> List.iteri begin fun ci ((stb, sx), (dtb, dx), color) ->
      let y_of_tb = function
        | Top -> top_y
        | Bot tail_len -> bot_y - tail_len
      in
      let sy = y_of_tb stb in
      let dy = y_of_tb dtb in
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

  let height = !height in

  vpath_info |> Array.iter begin fun { x; top; bot; color } ->
    let y0 = rank_y0.(top) in
    let y1 = rank_y1 bot in
    con_rev := ([x,y0;x,y1], color) :: !con_rev
  end;

  (* determine y for each node in range *)
  for r=0 to nrank-1 do
    rank_nodes.(r) |> Array.iter (fun i -> node_y.(i) <- rank_y0.(r))
  done;

  let nodes =
    Array.init n (fun i -> node_x.(i), node_y.(i), node_layout.(i))
  in
  let connections = List.rev !con_rev in

  let exit =
    exits |> List.map (fun i -> node_x.(i)) |> Array.of_list
  in
  { left; right; height; exit; shape = Layout_composite { nodes; connections } }
