type 'a t
type find_result = Nowhere | Start | Middle | End

val add : 'a * 'a -> 'a t -> 'a t
val find : 'a -> 'a t -> find_result
val split : 'a -> 'a t -> 'a t
val to_list : 'a t -> ('a * 'a) list
val empty : 'a t
