type t

val zero : int -> t
val length : t -> int
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
val of_int : int -> int -> t
val to_int : t -> int
val of_bytestring : string -> t
val pp : Format.formatter -> t -> unit
val add_c : t -> t -> bool -> t
val to_bool : t -> bool
val equal : t -> t -> bool
