open Batteries
open Analyze

let asm_listing (cfg : Inst.inst Cfg.cfg) =
  let open Format in
  let n = Array.length cfg.node in
  for i=0 to n-1 do
    fprintf str_formatter "%nx:\n" cfg.node.(i).start;
    cfg.node.(i).stmts |> List.iter (fprintf str_formatter "%a@." Inst.pp)
  done;
  flush_str_formatter ()

let ssa_listing (cfg : Semant.Normal.stmt Cfg.cfg) =
  let open Format in
  let n = Array.length cfg.node in
  for i=0 to n-1 do
    fprintf str_formatter "%nx:\n" cfg.node.(i).start;
    cfg.node.(i).stmts |> List.iter
      (fprintf str_formatter "%a@." Semant.Normal.pp_stmt)
  done;
  flush_str_formatter ()

(*
type rect = { x : int; y : int; width : int; height : int }

let layout_margin = 32

let intersects {x=x1;y=y1;width=w1;height=h1} {x=x2;y=y2;width=w2;height=h2} =
  not (x1+w1 <= x2 || x2+w2 <= x1 || y1+h1 <= y2 || y2+h2 <= y1)

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
      set_source_rgb cr 0.0 0.0 0.0;
      (* draw box *)
      rectangle cr (float_of_int (x + node.left)) fy (float_of_int (node.right - node.left)) (float_of_int node.height);
      stroke cr;
      (* draw text *)
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

let expose canvas layout ev =
  let open Cairo in
  let area = GdkEvent.Expose.area ev in
  let x = Gdk.Rectangle.x area in
  let y = Gdk.Rectangle.y area in
  let width = Gdk.Rectangle.width area in
  let height = Gdk.Rectangle.height area in
  begin
    let cr = Cairo_gtk.create canvas#misc#window in
    set_source_rgb cr 1.0 1.0 1.0;
    rectangle cr (float_of_int x) (float_of_int y)
      (float_of_int width) (float_of_int height);
    fill cr;
    draw_object cr { x; y; width; height }
      (layout_margin - layout.left) layout_margin layout;
    finalize cr
  end;
  true
*)

let show_il db va32 =
  let va = Nativeint.of_int32 va32 in
  let proc = Database.get_proc db va in
  let icfg = proc.inst_cfg in
  let scfg = Elaborate.elaborate_cfg db icfg in
  let ssa_cfg = Dataflow.convert_to_ssa db scfg in
  Analyze.simplify_ssa_cfg ssa_cfg;
  let cs = ssa_cfg |> Dataflow.convert_from_ssa |> Fold_cfg.fold_cfg in
  let il = cs |> Pseudocode.convert in
  il |> List.iter (Pseudocode.pp_pstmt Format.str_formatter);
  let il_text = Format.flush_str_formatter () in

  let title = Printf.sprintf "%nx" va in
  let window = GWindow.window ~width:640 ~height:480 ~title () in
  let box = GPack.vbox ~packing:window#add () in
  let toolbar = GButton.toolbar ~packing:box#pack () in
  (* "defs" button *)
  let _ =
    let btn = GButton.button ~label:"defs" ~packing:toolbar#add () in
    btn#connect#clicked begin fun () ->
      let dlg = GWindow.dialog ~title:(Printf.sprintf "Defs of %nx" va) () in
      let text =
        proc.defs |> List.map Semant.string_of_global |> String.concat " "
      in
      let _ = GMisc.label ~text ~packing:dlg#vbox#add () in
      dlg#show ()
    end
  in
  (* "uses" button *)
  let _ =
    let btn = GButton.button ~label:"uses" ~packing:toolbar#add () in
    btn#connect#clicked begin fun () ->
      let dlg = GWindow.dialog ~title:(Printf.sprintf "Uses of %nx" va) () in
      let text =
        proc.uses |> List.map Semant.string_of_global |> String.concat " "
      in
      let _ = GMisc.label ~text ~packing:dlg#vbox#add () in
      dlg#show ()
    end
  in
  let sw =
    GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~packing:box#add ()
  in
  let text_view = GText.view ~packing:sw#add () in
  toolbar#insert_space ();
  (* "asm" button *)
  let _ =
    let btn = GButton.button ~label:"asm" ~packing:toolbar#add () in
    btn#connect#clicked begin fun () ->
      let text = asm_listing proc.inst_cfg in
      text_view#buffer#set_text text
    end
  in
  (* "SSA" button *)
  let _ =
    let btn = GButton.button ~label:"SSA" ~packing:toolbar#add () in
    btn#connect#clicked begin fun () ->
      let text = ssa_listing ssa_cfg in
      text_view#buffer#set_text text
    end
  in
  (* "IL" button *)
  let _ =
    let btn = GButton.button ~label:"IL" ~packing:toolbar#add () in
    btn#connect#clicked begin fun () ->
      text_view#buffer#set_text il_text
    end
  in
  (* "CFG" button *)
  (* let _ =
    let btn = GButton.button ~label:"CFG" ~packing:toolbar#add () in
    btn#connect#clicked begin fun () ->
      let cfg_window =
        GWindow.window ~width:640 ~height:480
          ~title:(Printf.sprintf "CFG for %nx" va) ()
      in
      let cfg_sw =
        GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
          ~packing:cfg_window#add ()
      in
      let canvas = GMisc.drawing_area ~packing:cfg_sw#add_with_viewport () in
      let conf =
        { char_width = 8; char_height = 16 }
      in
      let layout = Layout.layout_node conf 0 cs in
      let _ = canvas#event#connect#expose (expose canvas layout) in
      let layout_margin = 32 in
      canvas#misc#set_size_request
        ~width:(layout.right - layout.left + layout_margin*2)
        ~height:(layout.height + layout_margin*2) ();
      cfg_window#show ()
    end
  in *)
  let _ =
    let btn = GButton.button ~label:"CFG" ~packing:toolbar#add () in
    btn#connect#clicked begin fun () ->
      let exitcode =
        File.with_temporary_out begin fun oc filepath ->
          let out_filepath = filepath ^ ".pdf" in
          Graphviz_intf.write_dot (Format.formatter_of_output oc) icfg;
          Sys.command
            (Printf.sprintf "dot -Tpdf %s > %s && open %s"
               filepath out_filepath out_filepath)
        end;
      in
      Printf.eprintf "exited with %d\n" exitcode;
      flush stderr
    end
  in
  text_view#buffer#set_text il_text;
  window#show ()

let show_gui db =
  let _ = GMain.init () in
  Lwt_glib.install ();
  let window = GWindow.window ~width:640 ~height:480 ~title:"dasm" () in
  let cols = new GTree.column_list in
  (* Gobject.Data does not have nativeint *)
  let addr_col = cols#add Gobject.Data.int32 in
  let compl_col = cols#add Gobject.Data.boolean in
  let leaf_col = cols#add Gobject.Data.boolean in
  let bb_col = cols#add Gobject.Data.int in
  let model = GTree.list_store cols in
  Database.get_proc_entry_list db |> List.iter begin fun va ->
    let proc = Database.get_proc db va in
    let va32 = Nativeint.to_int32 va in
    let row = model#append () in
    model#set ~row ~column:addr_col va32;
    model#set ~row ~column:compl_col proc.is_complete;
    model#set ~row ~column:leaf_col proc.is_leaf;
    model#set ~row ~column:bb_col (Cfg.basic_block_count proc.inst_cfg)
  end;
  let va_data_func renderer (model:GTree.model) iter =
    let va = model#get ~row:iter ~column:addr_col in
    renderer#set_properties [`TEXT (Printf.sprintf "%lx" va)]
  in
  let sw =
    GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~packing:window#add ()
  in
  let view = GTree.view ~model ~packing:sw#add () in
  let renderer_text = GTree.cell_renderer_text [] in
  let _ =
    let view_col =
      GTree.view_column ~title:"Address"~renderer:(renderer_text, []) ()
    in
    view_col#set_cell_data_func renderer_text (va_data_func renderer_text);
    view#append_column view_col
  in
  let _ =
    let view_col =
      GTree.view_column ~title:"Complete"
        ~renderer:(renderer_text, ["text", compl_col]) ()
    in
    view#append_column view_col
  in
  let _ =
    let view_col =
      GTree.view_column ~title:"Leaf"
        ~renderer:(renderer_text, ["text", leaf_col]) ()
    in
    view#append_column view_col
  in
  let _ =
    let view_col =
      GTree.view_column ~title:"BB"
        ~renderer:(renderer_text, ["text", bb_col]) ()
    in
    view#append_column view_col
  in
  let on_row_activated (view:GTree.view) path _col =
    let model = view#model in
    let row = model#get_iter path in
    let va = model#get ~row ~column:addr_col in
    show_il db va
  in
  let _ = view#connect#row_activated ~callback:(on_row_activated view) in
  window#show ()
