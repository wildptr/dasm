module StringMap = Map.Make(String)

let rec union l1 l2 =
  match l1, l2 with
  | [], _ -> l2
  | _, [] -> l1
  | hd1::tl1, hd2::tl2 ->
      let hd, tl =
        if hd1 < hd2 then hd1, union tl1 l2 else hd2, union l1 tl2
      in
      match tl with
      | [] -> [hd]
      | hd'::tl' -> if hd = hd' then tl else hd::tl

let union_set l = List.fold_left union [] l

let rec drop l n = if n <= 0 then l else drop (List.tl l) (n-1)

let index x l =
  let rec loop l i =
    match l with
    | [] -> raise Not_found
    | hd :: tl ->
      if hd = x then i
      else loop tl (i+1)
  in
  loop l 0

let rec range a b = if a >= b then [] else a :: range (a+1) b
