open Cfg
open Layout

open GMain
open GdkKeysyms
open Cairo

type rect = { x : int; y : int; width : int; height : int }

let layout_margin = 32

let intersects {x=x1;y=y1;width=w1;height=h1} {x=x2;y=y2;width=w2;height=h2} =
  not (x1+w1 <= x2 || x2+w2 <= x1 || y1+h1 <= y2 || y2+h2 <= y1)

let rec draw_object cr x y (node:layout_node) =
  let fx = float_of_int (x) in
  let fy = float_of_int (y) in
  match node.shape with
  | Layout_none -> ()
  | Layout_box box ->
    set_source_rgb cr 1.0 1.0 1.0;
    (* draw box *)
    rectangle cr (float_of_int (x + node.left)) fy (float_of_int (node.right - node.left)) (float_of_int node.height);
    fill cr;
    (* draw text *)
    set_source_rgb cr 0.0 0.0 0.0;
    let fe = font_extents cr in
    let tx = float_of_int (x + node.left) in
    let ty = ref (fy +. fe.ascent) in
    box.text |> List.iter begin fun text ->
      move_to cr tx !ty;
      show_text cr text;
      ty := !ty +. fe.baseline
    end
  | Layout_composite com ->
    save cr;
    translate cr fx fy;
    com.nodes |> Array.iter (fun (x,y,n) -> draw_object cr x y n);
    com.connections |> List.iter begin fun (path, color) ->
      let set_color cr = function
        | Black -> set_source_rgb cr 0.0 0.0 0.0
        | Red -> set_source_rgb cr 0.75 0.0 0.0
        | Green -> set_source_rgb cr 0.0 0.75 0.0
      in
      match path with
      | [] -> ()
      | (x,y) :: tl ->
        set_color cr color;
        move_to cr (float_of_int x) (float_of_int y);
        tl |> List.iter (fun (x,y) -> line_to cr (float_of_int x) (float_of_int y));
        stroke cr
    end;
    restore cr

(*
let bounding_box = function
  | Node node ->
    { x = node.x; y = node.y; width = node.width; height = node.height }
  | Segment (_, bbox) -> bbox
*)

let set_cairo_font cr =
  select_font_face cr "Monospace";
  set_font_size cr 16.0

let expose drawing_area layout ev =
  let area = GdkEvent.Expose.area ev in
  let x = Gdk.Rectangle.x area in
  let y = Gdk.Rectangle.y area in
  let width = Gdk.Rectangle.width area in
  let height = Gdk.Rectangle.height area in

  let cr = Cairo_gtk.create drawing_area#misc#window in
  set_cairo_font cr;

  set_source_rgb cr 1.0 1.0 0.75;
  rectangle cr (float_of_int x) (float_of_int y)
    (float_of_int width) (float_of_int height);
  fill cr;

  draw_object cr (layout_margin - layout.left) layout_margin layout;

  true

let bounding_box_of_path path =
  match path with
  | [] -> assert false
  | (x,y) :: tl ->
    let x0 = ref x in
    let x1 = ref x in
    let y0 = ref y in
    let y1 = ref y in
    tl |> List.iter begin fun (x,y) ->
      x0 := min !x0 x;
      x1 := max !x1 x;
      y0 := min !y0 y;
      y1 := max !y1 y
    end;
    let x = !x0 - 1 in
    let y = !y0 - 1 in
    let width = !x1 - !x0 + 2 in
    let height = !y1 - !y0 + 2 in
    { x; y; width; height }

let () =
  Printexc.record_backtrace true;
  let init_pc = int_of_string Sys.argv.(1) in
  let in_path = Sys.argv.(2) in
  let init_offset = int_of_string Sys.argv.(3) in
  Elaborate.load_spec "spec";
  let in_chan = open_in in_path in
  let in_chan_len = in_channel_length in_chan in
  let code = really_input_string in_chan in_chan_len in
  close_in in_chan;
  let cfg = Control_flow.build_cfg code init_pc init_offset in

  let _ = GtkMain.Main.init () in

  let window = GWindow.window ~width:512 ~height:512
      ~title:"dasm" () in
  let _ = window#connect#destroy ~callback:Main.quit in

  let sw = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~packing:window#add () in

  let da = GMisc.drawing_area ~packing:sw#add_with_viewport () in

(*
  let pixmap_width = layout.width+48 in
  let pixmap_height = layout.height+48 in

  let pixmap = GDraw.pixmap ~width:pixmap_width ~height:pixmap_height () in

  (* fill pixmap with white *)
  pixmap#set_foreground GDraw.(`WHITE);
  pixmap#rectangle ~x:0 ~y:0 ~width:pixmap_width ~height:pixmap_height ~filled:true ();

  let _ = da#event#connect#expose (expose da pixmap) in

  let cr = Cairo_gtk.create pixmap#pixmap in

  draw_layout cr ~x:24 ~y:24 layout;
*)

  window#show ();

  let cr = Cairo_gtk.create window#misc#window in
  set_cairo_font cr;
  let fe = font_extents cr in

  let conf = { char_width = int_of_float fe.max_x_advance; char_height = int_of_float fe.baseline } in
  let cfg' = Control_flow.fold_cfg cfg in
  let layout = layout_node conf cfg.node cfg' in
  let _ = da#event#connect#expose (expose da layout) in
  let layout_width = layout.right - layout.left in
  Format.eprintf "layout width: %d@." layout_width;
  da#misc#set_size_request ~width:(layout_width+layout_margin*2)
    ~height:(layout.height+layout_margin*2) ();

  Main.main ()
