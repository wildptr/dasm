type t

val zero : int -> t
val length : t -> int
val add : t -> t -> t
val sub : t -> t -> t
val logand : t -> t -> t
val logxor : t -> t -> t
val logor : t -> t -> t
val lognot : t -> t
val neg : t -> t
val of_string_base : int -> string -> t
val to_string : t -> string
val of_bool : bool -> t
val extract : int -> int -> t -> t
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
