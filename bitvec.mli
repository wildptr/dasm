type t

val zero : int -> t
val len : t -> int
val concat : t list -> t
val add : t -> t -> t
val sub : t -> t -> t
val andv : t -> t -> t
val xorv : t -> t -> t
val orv : t -> t -> t
val notv : t -> t
val neg : t -> t
val of_string : string -> t
val to_string : t -> string
val of_bool : bool -> t
val part : int * int -> t -> t
