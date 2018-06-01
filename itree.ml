type 'a t =
  | Leaf
  | Branch of 'a * 'a * 'a t * 'a t

let rec add (lo,hi) = function
  | Leaf -> Branch (lo, hi, Leaf, Leaf)
  | Branch (lo', hi', left, right) ->
    if hi <= lo' then Branch (lo', hi', add (lo,hi) left, right)
    else if hi' <= lo then Branch (lo', hi', left, add (lo,hi) right)
    else assert false

type find_result = Nowhere | Start | Middle

let rec find x = function
  | Leaf -> Nowhere
  | Branch (lo, hi, left, right) ->
    if x < lo then find x left
    else if x = lo then Start
    else if x < hi then Middle
    else find x right

let rec split x = function
  | Leaf -> Leaf
  | Branch (lo, hi, left, right) ->
    if lo < x && x < hi then Branch (lo, x, left, Branch (x, hi, Leaf, right))
    else if x <= lo then Branch (lo, hi, split x left, right)
    else Branch (lo, hi, left, split x right)

let rec to_list_acc acc = function
  | Leaf -> acc
  | Branch (lo, hi, left, right) ->
    to_list_acc ((lo, hi) :: to_list_acc acc right) left

let to_list t = to_list_acc [] t

let empty = Leaf
