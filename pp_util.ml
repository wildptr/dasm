open Batteries
open Format

let pp_sep_list sep pp f = function
  | [] -> ()
  | hd :: tl ->
    fprintf f "%a" pp hd;
    List.iter (fprintf f "%s%a" sep pp) tl

let pp_list pp f = List.iter (pp f)
