open Cfg
open Layout

open GMain
open GdkKeysyms
open Cairo

(*
let pi2 = 8. *. atan 1.

let draw cr width height =
  let r = 0.25 *. width in
  set_source_rgba cr 0. 1. 0. 0.5;
  arc cr (0.5 *. width) (0.35 *. height) r 0. pi2;
  fill cr;
  set_source_rgba cr 1. 0. 0. 0.5;
  arc cr (0.35 *. width) (0.65 *. height) r 0. pi2;
  fill cr;
  set_source_rgba cr 0. 0. 1. 0.5;
  arc cr (0.65 *. width) (0.65 *. height) r 0. pi2;
  fill cr
*)

let expose (drawing_area:GMisc.drawing_area) (backing:GDraw.pixmap) ev =
  let area = GdkEvent.Expose.area ev in
  let x = Gdk.Rectangle.x area in
  let y = Gdk.Rectangle.y area in
  let width = Gdk.Rectangle.width area in
  let height = Gdk.Rectangle.height area in
  let drawing =
    drawing_area#misc#realize ();
    new GDraw.drawable (drawing_area#misc#window)
  in
  drawing#put_pixmap ~x ~y ~xsrc:x ~ysrc:y ~width ~height backing#pixmap;
  false

(*
let expose drawing_area ev =
  let cr = Cairo_gtk.create drawing_area#misc#window in
  let allocation = drawing_area#misc#allocation in
  draw cr (float allocation.Gtk.width) (float allocation.Gtk.height);
  true
*)

let draw_layout cr ~x ~y (layout:Layout.layout) =
  let set_color cr = function
    | Layout.Black -> set_source_rgb cr 0.0 0.0 0.0
    | Layout.Red -> set_source_rgb cr 0.8 0.0 0.0
    | Layout.Green -> set_source_rgb cr 0.45 0.8 0.1
  in
  save cr;
  translate cr (float_of_int x) (float_of_int y);
  layout.nodes |> Array.iter begin fun (node:Layout.node) ->
    let nx = float_of_int (node.x) in
    let ny = float_of_int (node.y) in
    if node.is_virtual then begin
      set_color cr node.color;
      move_to cr nx ny;
      line_to cr nx (float_of_int (node.y+node.height));
      stroke cr
    end else begin
      set_source_rgb cr 0.0 0.0 0.0;
      (* draw box *)
      rectangle cr nx ny (float_of_int node.width) (float_of_int node.height);
      stroke cr;
      (* draw text *)
      let tx = float_of_int (node.x + Layout.margin) in
      let ty = ref @@ float_of_int (node.y + Layout.margin) in
      move_to cr tx !ty;
      node.text |> List.iter begin fun text ->
        ty := !ty +. Layout.text_height_f;
        move_to cr tx !ty;
        show_text cr text
      end
    end;
  end;
  layout.connections |> Array.iter begin fun c ->
    c |> List.iter begin fun (path, color) ->
      set_color cr color;
      match path with
      | [] -> ()
      | (x,y) :: tl ->
        move_to cr (float_of_int x) (float_of_int y);
        tl |> List.iter (fun (x,y) -> line_to cr (float_of_int x) (float_of_int y));
        stroke cr
    end
  end;
  restore cr

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

  let _ = GtkMain.Main.init () in

  let window = GWindow.window ~width:512 ~height:512
      ~title:"dasm" () in
  let _ = window#connect#destroy ~callback:Main.quit in

  let sw = GBin.scrolled_window ~packing:window#add () in

  let da = GMisc.drawing_area ~packing:sw#add_with_viewport () in

  let pixmap_width = layout.width+48 in
  let pixmap_height = layout.height+48 in

  let pixmap = GDraw.pixmap ~width:pixmap_width ~height:pixmap_height () in

  (* fill pixmap with white *)
  pixmap#set_foreground GDraw.(`WHITE);
  pixmap#rectangle ~x:0 ~y:0 ~width:pixmap_width ~height:pixmap_height ~filled:true ();

  let _ = da#event#connect#expose (expose da pixmap) in

  let cr = Cairo_gtk.create pixmap#pixmap in

  select_font_face cr "Monospace";
  set_font_size cr Layout.text_height_f;

  draw_layout cr ~x:24 ~y:24 layout;

(*
  set_source_rgb cr 0.5 0.5 0.5;
  rectangle cr 40. 40. 40. 40.;
  stroke cr;

  set_line_width cr 1.;
  move_to cr 60. 80.;
  line_to cr 60. 100.;
  line_to cr 20. 100.;
  line_to cr 20. 20.;
  line_to cr 60. 20.;
  line_to cr 60. 40.;
  stroke cr;

  set_source_rgb cr 1. 1. 1.;
  move_to cr 40. 52.;
  show_text cr "Hello";
*)

  window#show ();
  Main.main ()
