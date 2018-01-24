module StringMap = Map.Make(String)

let rec zip l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | h1::t1,  h2::t2 -> (h1, h2) :: zip t1 t2
  | _ -> failwith "zip"

let rec unzip = function
  | [] -> ([], [])
  | (a, b)::tl -> let a', b' = unzip tl in a::a', b::b'
