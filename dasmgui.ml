open Batteries
open Cfg
open Database
open Layout

open GMain

type rect = { x : int; y : int; width : int; height : int }

let layout_margin = 32

let intersects {x=x1;y=y1;width=w1;height=h1} {x=x2;y=y2;width=w2;height=h2} =
  not (x1+w1 <= x2 || x2+w2 <= x1 || y1+h1 <= y2 || y2+h2 <= y1)

(*
let point_in_rect (x,y) (rect:rect) =
  let x0 = rect.x in
  let y0 = rect.y in
  let x1 = x0 + rect.width in
  let y1 = y0 + rect.height in
  x0 < x && x < x1 && y0 < y && y < y1
*)

type view = {
  cairo : Cairo.context;
  canvas : GMisc.drawing_area;
  text_view : GText.view;
  mutable layout : layout_node option;
  mutable current_function_va : nativeint;
  db : Database.db;
}

let rec draw_object cr (exposed:rect) x y (node:layout_node) =
  let open Cairo in
  let fx = float_of_int x in
  let fy = float_of_int y in
  let node_bbox = {
    x = x + node.left; y;
    width = node.right - node.left; height = node.height
  } in
  if intersects node_bbox exposed then begin
    match node.shape with
    | Layout_virtual ->
      set_source_rgb cr 1.0 1.0 1.0;
      move_to cr (fx +. float_of_int node.left) fy;
      line_to cr (fx +. float_of_int node.right) fy;
      stroke cr;
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
      let exposed' = { exposed with x = exposed.x - x; y = exposed.y - y } in
      com.nodes |> Array.iter (fun (x,y,n) -> draw_object cr exposed' x y n);
      com.connections |> List.iter begin fun (path, color) ->
        let set_color cr = function
          | Black -> set_source_rgb cr 0.0 0.0 0.0
          | Red -> set_source_rgb cr 0.75 0.0 0.0
          | Green -> set_source_rgb cr 0.0 0.75 0.0
        in
        match path with
        | [] -> ()
        | (x1,y1) :: tl ->
          set_color cr color;
          move_to cr (float_of_int x1) (float_of_int y1);
          tl |> List.iter begin fun (x2,y2) ->
            line_to cr (float_of_int x2) (float_of_int y2)
          end;
          stroke cr
      end;
      restore cr
  end

let set_cairo_font cr =
  let open Cairo in
  select_font_face cr "Monospace";
  set_font_size cr 14.0

let expose view ev =
  let open Cairo in
  let area = GdkEvent.Expose.area ev in
  let x = Gdk.Rectangle.x area in
  let y = Gdk.Rectangle.y area in
  let width = Gdk.Rectangle.width area in
  let height = Gdk.Rectangle.height area in

  let cr = Cairo_gtk.create view.canvas#misc#window in
  set_cairo_font cr;

  set_source_rgb cr 1.0 1.0 0.875;
  rectangle cr (float_of_int x) (float_of_int y)
    (float_of_int width) (float_of_int height);
  fill cr;

  begin match view.layout with
    | Some layout ->
      draw_object cr { x; y; width; height }
        (layout_margin - layout.left) layout_margin layout;
    | None -> ()
  end;

  true

let show_pseudocode view () =
  let proc = Database.get_proc view.db view.current_function_va in
  let stmts = proc.il in
  let buf = Buffer.create 0 in
  let open Format in
  let fmtr = formatter_of_buffer buf in
  let open Semant in
  let rec print_stmt indent stmt =
    match stmt with
    | S_if (cond, body) ->
      fprintf fmtr "%sif (%a) {@." indent pp_expr cond;
      body |> List.iter (print_stmt (indent^"  "));
      fprintf fmtr "%s}@." indent
    | S_if_else (cond, body_t, body_f) ->
      fprintf fmtr "%sif (%a) {@." indent pp_expr cond;
      body_t |> List.iter (print_stmt (indent^"  "));
      fprintf fmtr "%s} else {@." indent;
      body_f |> List.iter (print_stmt (indent^"  "));
      fprintf fmtr "%s}@." indent
    | S_do_while (body, cond) ->
      fprintf fmtr "%sdo {@." indent;
      body |> List.iter (print_stmt (indent^"  "));
      fprintf fmtr "%s} while (%a)@." indent pp_expr cond
    | _ -> fprintf fmtr "%s%a@." indent pp_stmt stmt
  in
  stmts |> List.iter (print_stmt "");
  let text = Buffer.contents buf in
  view.text_view#buffer#set_text text

let show_ssa view () =
  let db = view.db in
  let proc = Hashtbl.find db.Database.proc_table view.current_function_va in
  let cfg', env' = Elaborate.elaborate_cfg db true proc.cfg in
  Dataflow.convert_to_ssa cfg';
  let rec loop () =
    if Dataflow.auto_subst cfg' ||
       Simplify.simplify_cfg env' cfg' ||
       Dataflow.remove_dead_code cfg' then loop ()
  in
  loop ();
  show_pseudocode view ()

let goto_function view va =
  let db = view.db in
  let proc =
    match Hashtbl.find_option db.Database.proc_table va with
    | Some proc -> proc
    | None ->
      let proc = Build_cfg.build_cfg db va in
      Hashtbl.add db.Database.proc_table va proc;
      proc
  in
  let conf =
    let open Cairo in
    let fe = font_extents view.cairo in
      { char_width = int_of_float fe.max_x_advance;
        char_height = int_of_float fe.baseline }
  in
  let layout =
    try layout_node conf 0 proc.inst_cs
    with e ->
      Printexc.to_string e |> print_endline;
      { left=0; right=0; height=0; entry=[||]; exit=[||]; shape=Layout_virtual }
  in
  let layout_width = layout.right - layout.left in
  view.canvas#misc#set_size_request ~width:(layout_width+layout_margin*2)
    ~height:(layout.height+layout_margin*2) ();
  view.current_function_va <- va;
  view.layout <- Some layout

let goto_function_prompt view () =
  let dlg = GWindow.dialog ~title:"Go to function" () in
  let textbox = GEdit.entry ~packing:dlg#vbox#add () in
  let ok_button = GButton.button ~label:"OK" ~packing:dlg#action_area#add () in
  let _ =
    ok_button#connect#clicked ~callback:begin fun () ->
      goto_function view (Nativeint.of_string textbox#text)
    end
  in
  dlg#show ()

let () =
  Printexc.record_backtrace true;
  if Array.length Sys.argv <= 1 then begin
    Printf.eprintf "incorrect usage\n";
    exit 1
  end;
  let in_path = Sys.argv.(1) in

  Elaborate.load_spec "spec";
  let pe = Pe.load in_path in
  let code = pe.Pe.code in
  let entry_point = pe.Pe.entry_point in
  let init_pc = Nativeint.(entry_point + 0x400000n) (* FIXME *) in
  let db = Database.create code in

  let _ = GtkMain.Main.init () in

  let window = GWindow.window ~width:640 ~height:480
      ~title:"dasm" () in
  let _ = window#connect#destroy ~callback:Main.quit in

  let vbox = GPack.vbox ~packing:window#add () in

  let toolbar = GButton.toolbar ~packing:vbox#pack () in

  let button1 = GButton.button ~label:"pseudocode" ~packing:toolbar#add () in
  let button2 = GButton.button ~label:"SSA" ~packing:toolbar#add () in
  let button3 = GButton.button ~label:"Go to function" ~packing:toolbar#add () in

  let hbox = GPack.hbox ~packing:vbox#add () in

  let sw1 = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~packing:hbox#add () in

  let sw2 = GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~packing:hbox#add () in

  let canvas = GMisc.drawing_area ~packing:sw1#add_with_viewport () in

  let text_view = GText.view ~packing:sw2#add_with_viewport () in

  window#show ();

  let cr = Cairo_gtk.create window#misc#window in
  set_cairo_font cr;

  let view = {
    cairo = cr;
    canvas;
    text_view;
    layout = None;
    current_function_va = 0n;
    db;
  } in

  let _ = canvas#event#connect#expose (expose view) in
  let _ = button1#connect#clicked ~callback:(show_pseudocode view) in
  let _ = button2#connect#clicked ~callback:(show_ssa view) in
  let _ = button3#connect#clicked ~callback:(goto_function_prompt view) in

  goto_function view init_pc;

  Main.main ()