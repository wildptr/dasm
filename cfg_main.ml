open Inst

type itree =
  | Leaf
  | Branch of int * int * itree * itree

let rec itree_add (lo,hi) = function
  | Leaf -> Branch (lo, hi, Leaf, Leaf)
  | Branch (lo', hi', left, right) ->
    if hi <= lo' then Branch (lo', hi', itree_add (lo,hi) left, right)
    else if hi' <= lo then Branch (lo', hi', left, itree_add (lo,hi) right)
    else assert false

type itree_find_result =
  | Nowhere
  | Middle
  | Start

let rec itree_find x = function
  | Leaf -> Nowhere
  | Branch (lo, hi, left, right) ->
    if lo = x then Start
    else if lo < x && x < hi then Middle
    else if x < lo then itree_find x left
    else itree_find x right

let rec itree_split x = function
  | Leaf -> Leaf
  | Branch (lo, hi, left, right) ->
    if lo < x && x < hi then Branch (lo, x, left, Branch (x, hi, Leaf, right))
    else if x <= lo then Branch (lo, hi, itree_split x left, right)
    else Branch (lo, hi, left, itree_split x right)

let rec itree_to_list_acc acc = function
  | Leaf -> acc
  | Branch (lo, hi, left, right) ->
    itree_to_list_acc ((lo, hi) :: itree_to_list_acc acc right) left

let itree_to_list t = itree_to_list_acc [] t

type string_stream = {
  str : string;
  mutable pos : int;
}

let build_cfg code init_pc =
  let start_end = ref Leaf in
  let edges = ref [] in (* from end of basic block to start of basic block *)
  let q = Queue.create () in
  Queue.add init_pc q;
  let s = { str = code; pos = 0 } in
  let next () =
    let c = s.str.[s.pos] in
    s.pos <- s.pos + 1;
    c
  in
  while not (Queue.is_empty q) do
    let pc = Queue.pop q in
    begin match itree_find pc !start_end with
      | Start -> ()
      | Middle ->
        start_end := itree_split pc !start_end;
        edges := (pc, pc) :: !edges
      | Nowhere ->
        s.pos <- pc - init_pc;
        let rec loop pc =
          let inst = Dasm.(disassemble Mode32bit next) in
          let l = length_of inst in
          let pc' = pc+l in
          match inst.operation with
          | I_jmp ->
            begin match List.hd inst.operands with
              | O_offset ofs -> pc', [pc+ofs]
              | _ -> pc', []
            end
          | I_jmpfar -> failwith "cannot handle far jump"
          | I_cjmp ->
            begin match List.hd inst.operands with
              | O_offset ofs -> pc', [pc'; pc+ofs]
              | _ -> pc', [pc']
            end
          | I_ret | I_retfar -> pc', []
          | _ ->
            if itree_find pc' !start_end = Start then pc', [pc'] else
              loop pc'
        in
        let pc', dests = loop pc in
        (*Printf.printf "(%x,%x)\n" pc pc';*)
        start_end := itree_add (pc,pc') !start_end;
        dests |> List.iter (fun dest ->
            edges := (pc', dest) :: !edges;
            (* If dest is strictly between start(b) and end(b) for some basic
               block b, then split b at dest.  If dest equals start(b) for some b,
               then do nothing.  Otherwise add dest to queue.  *)
            Queue.add dest q)
    end
  done;
  let start_end_list = itree_to_list !start_end in
  start_end_list, !edges

let write_cfg (start_end, edges) =
  let end_start = Hashtbl.create 0 in
  List.iter (fun (start, stop) -> Hashtbl.add end_start stop start) start_end;
  let open Format in
  print_string "digraph {\n";
  (*let insts = ref [] in
  let insts = List.rev !insts in*)
  List.iter (fun (start, _) -> printf "  loc_%x;\n" start) start_end;
  List.iter (fun (f, t) -> printf "  loc_%x -> loc_%x;\n" (Hashtbl.find end_start f) t) edges;
  print_string "}\n"

let () =
  let init_pc = int_of_string Sys.argv.(1) in
  let in_path = Sys.argv.(2) in
  let in_chan = open_in in_path in
  let in_chan_len = in_channel_length in_chan in
  let code = really_input_string in_chan in_chan_len in
  close_in in_chan;
  let cfg = build_cfg code init_pc in
  write_cfg cfg
