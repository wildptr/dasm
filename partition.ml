open Core_kernel.Std

let pratition stmts =
  let n = List.length stmts in
  let label_table = String.Table.create () in
  List.iteri stmts ~f:begin fun i stmt ->
    match stmt with
    | S_label label ->
        String.Table.add_exn label_table ~key:label ~data:i
    | _ -> ()
  end;
  let succ =
    List.mapi stmts ~f:begin fun i stmt ->
      match stmt with
      | S_jump dst_label ->
          List.filter_opt
            [ String.Table.find label_table dst_label ]
      | S_jump_var _ -> []
      | S_br (_, dst_label) ->
          List.filter_opt
            [ if i+1 < n then Some (i+1) else None;
              String.Table.find label_table dst_label ]
      | _ ->
          List.filter_opt
            [ if i+1 < n then Some (i+1) else None ]
    end
    |> Array.of_list
  in
  let pred = Array.create [] ~len:n in
  for i := 0 to n-1 do
    List.iter succ.(i) ~f:(fun s -> pred.(s) <- i :: pred.(s))
  done;
  let mapping =
    List.fold (List.range 1 n) ~init:[0] ~f:begin fun m i ->
      let hd = List.hd m in
      let hd' = if succ.(i-1) = [i] && pred.(i) = [i-1] then hd else hd+1 in
      hd' :: m
    end |> List.rev |> Array.of_list
  in
  mapping
