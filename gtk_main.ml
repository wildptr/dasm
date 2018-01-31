open Cfg
open Layout

open GMain
open GdkKeysyms
open Cairo

type shape =
  | Node of node
  | Segment of segment

type drawing_object = {
  x : int;
  y : int;
  width : int;
  height : int;
  shape : shape;
}

let layout_margin = 32
let layout_margin_f = float_of_int layout_margin

let intersects (x1, y1, w1, h1) (x2, y2, w2, h2) =
  not (x1+w1 <= x2 || x2+w2 <= x1 || y1+h1 <= y2 || y2+h2 <= y1)

let draw_object cr obj =
  match obj.shape with
  | Node node ->
    let nx = float_of_int (node.x) in
    let ny = float_of_int (node.y) in
    set_source_rgb cr 0.0 0.0 0.0;
    (* draw box *)
    rectangle cr nx ny (float_of_int node.width) (float_of_int node.height);
    stroke cr;
    (* draw text *)
    let tx = float_of_int (node.x + margin) in
    let ty = ref @@ float_of_int (node.y + margin) in
    node.text |> List.iter begin fun text ->
      ty := !ty +. text_height_f;
      move_to cr tx !ty;
      show_text cr text
    end
  | Segment (path, color) ->
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

let expose drawing_area objects ev =
  let area = GdkEvent.Expose.area ev in
  let x = Gdk.Rectangle.x area in
  let y = Gdk.Rectangle.y area in
  let width = Gdk.Rectangle.width area in
  let height = Gdk.Rectangle.height area in

  let cr = Cairo_gtk.create drawing_area#misc#window in
  select_font_face cr "Monospace";
  set_font_size cr text_height_f;

  set_source_rgb cr 1.0 1.0 1.0;
  rectangle cr (float_of_int x) (float_of_int y)
    (float_of_int width) (float_of_int height);
  fill cr;

  translate cr layout_margin_f layout_margin_f;
  objects |> List.iter begin fun obj ->
    if intersects (x, y, width, height)
        (obj.x+layout_margin, obj.y+layout_margin, obj.width, obj.height)
    then begin
      draw_object cr obj
    end
  end;

  true

let bounding_box path =
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
    !x0 - 1, !y0 - 1, !x1 - !x0 + 2, !y1 - !y0 + 2

let convert_layout (layout:layout) =
  let result = ref [] in
  layout.nodes |> Array.iter begin fun (node:node) ->
    result :=
      { x = node.x; y = node.y; width = node.width; height = node.height;
        shape = Node node } :: !result
  end;
  layout.connections |> List.iter begin fun (path, color) ->
    let x, y, width, height = bounding_box path in
    result :=
      { x; y; width; height; shape = Segment (path, color) } :: !result
  end;
  !result

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

  let layout = layout_cfg cfg in
  let objects = convert_layout layout in

  let _ = GtkMain.Main.init () in

  let window = GWindow.window ~width:512 ~height:512
      ~title:"dasm" () in
  let _ = window#connect#destroy ~callback:Main.quit in

  let sw = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~packing:window#add () in

  let da = GMisc.drawing_area ~packing:sw#add_with_viewport () in
  let _ = da#event#connect#expose (expose da objects) in

  da#misc#set_size_request ~width:(layout.width+layout_margin*2)
    ~height:(layout.height+layout_margin*2) ();

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
  Main.main ()
