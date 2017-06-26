open Core

type t = bool list (* LSB first *)

let rec zero len =
  if len <= 0
  then []
  else false :: zero (len-1)

let part (lo, hi) bv =
  List.drop (List.take bv hi) lo

let concat bvs =
  List.concat (List.rev bvs)

let bit_value b =
  if b then 1 else 0

let rec add_c bv1 bv2 c =
  match bv1, bv2 with
  | [], [] -> []
  | h1 :: bv1', h2 :: bv2' ->
      let sum = bit_value h1 + bit_value h2 + bit_value c in
      (sum land 1 <> 0) :: add_c bv1' bv2' (sum land 2 <> 0)
  | _ -> assert false

let add bv1 bv2 =
  add_c bv1 bv2 false

let notv bv =
  List.map ~f:not bv

let sub bv1 bv2 =
  add_c bv1 (notv bv2) true

let len bv =
  List.length bv

let neg bv =
  sub (zero (len bv)) bv

let rec bitwise f bv1 bv2 =
  match bv1, bv2 with
  | [], [] -> []
  | h1 :: bv1', h2 :: bv2' -> (f h1 h2) :: bitwise f bv1' bv2'
  | _ -> assert false

let andv = bitwise (&&)
let xorv = bitwise (<>)
let orv  = bitwise (||)

let of_string s =
  List.map ~f:(fun c -> c = '1') (List.rev (String.to_list s))

let to_string bv =
  String.of_char_list (List.map ~f:(fun b -> if b then '1' else '0') (List.rev bv))

let of_bool b =
  [b]
