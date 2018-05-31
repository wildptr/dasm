type t
type find_result = Nowhere | Start | Middle | End

val add : int * int -> t -> t
val find : int -> t -> find_result
val split : int -> t -> t
val to_list : t -> (int * int) list
val empty : t
