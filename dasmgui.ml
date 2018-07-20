open Analyze

let show_il db va32 =
  let va = Nativeint.of_int32 va32 in
  let icfg = Database.get_cfg db va in
  let scfg = Elaborate.elaborate_cfg db icfg in
  let il = Analyze.ssa scfg in
  il |> List.iter (Pseudocode.Plain.pp_pstmt Format.str_formatter);
  let il_text = Format.flush_str_formatter () in

  let title = Printf.sprintf "%nx" va in
  let window = GWindow.window ~width:640 ~height:480 ~title () in
  let sw =
    GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~packing:window#add ()
  in
  let text_view = GText.view ~packing:sw#add () in
  text_view#buffer#set_text il_text;
  window#show ()

let show_gui db =
  let _ = GMain.init () in
  Lwt_glib.install ();
  let window = GWindow.window ~width:640 ~height:480 ~title:"dasm" () in
  let model, col =
    (* Gobject.Data does not have nativeint *)
    Database.get_proc_entry_list db |> List.map Nativeint.to_int32 |>
    GTree.store_of_list Gobject.Data.int32
  in
  let va_data_func renderer (model:GTree.model) iter =
    let va = model#get ~row:iter ~column:col in
    renderer#set_properties [`TEXT (Printf.sprintf "%lx" va)]
  in
  let sw =
    GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~packing:window#add ()
  in
  let view = GTree.view ~model ~packing:sw#add () in
  let renderer_text = GTree.cell_renderer_text [] in
  let view_col = GTree.view_column ~renderer:(renderer_text, []) () in
  view_col#set_cell_data_func renderer_text (va_data_func renderer_text);
  let _ = view#append_column view_col in
  let on_row_activated (view:GTree.view) path _col =
    let model = view#model in
    let row = model#get_iter path in
    let va = model#get ~row ~column:col in
    show_il db va
  in
  let _ = view#connect#row_activated ~callback:(on_row_activated view) in
  window#show ()
