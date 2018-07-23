type t

val zero : int -> t
val length : t -> int
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
val of_nativeint : int -> nativeint -> t
val to_nativeint : t -> nativeint
val of_bytestring : string -> t
val pp : Format.formatter -> t -> unit
val to_bool : t -> bool
val equal : t -> t -> bool
val truncate : int -> t -> t
val zero_extend : int -> t -> t
val sign_extend : int -> t -> t
