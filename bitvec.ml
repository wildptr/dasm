type t = {
  len : int;
  bits : Z.t;
  mask : Z.t
}

let zero len =
  { len; bits = Z.zero; mask = Z.zero }

let mk_mask len =
  Z.(pred (Z.one lsl len))

let add bv1 bv2 =
  { bv1 with bits = Z.((bv1.bits + bv2.bits) land bv1.mask) }

let sub bv1 bv2 =
  { bv1 with bits = Z.((bv1.bits - bv2.bits) land bv1.mask) }

let lognot bv =
  { bv with bits = Z.(lognot bv.bits land bv.mask) }

let neg bv =
  { bv with bits = Z.(neg bv.bits land bv.mask) }

let length bv = bv.len

let rec bitwise f bv1 bv2 =
  { bv1 with bits = f bv1.bits bv2.bits }

let logand = bitwise Z.logand
let logxor = bitwise Z.logxor
let logor  = bitwise Z.logor

let of_string s =
  let len = String.length s in
  let bits = Z.of_string_base 2 s in
  { len; bits; mask = mk_mask len }

let to_string bv =
  let fmt = Printf.sprintf "0%db" bv.len in
  Z.format fmt bv.bits

let of_bool b =
  { len = 1; bits = if b then Z.one else Z.zero; mask = Z.one }

let extract off len bv =
  let mask = mk_mask len in
  { len; bits = Z.extract bv.bits off len; mask }

let of_int len i =
  let mask = mk_mask len in
  { len; bits = Z.(of_int i land mask); mask }

let of_nativeint len bits =
  let mask = mk_mask Sys.word_size in
  { len; bits = Z.(of_nativeint bits land mask); mask }

let sign_bit bv =
  Z.testbit bv.bits (bv.len-1)

let to_nativeint bv =
  Z.to_nativeint bv.bits

let of_bytestring s =
  let len = String.length s * 8 in
  let mask = mk_mask len in
  { len; bits = Z.of_bits s; mask }

let pp f bv = Format.pp_print_string f (to_string bv)

let to_bool bv =
  not Z.(equal bv.bits zero)

let equal b1 b2 =
  Z.equal b1.bits b2.bits

let truncate len bv =
  let mask = mk_mask len in
  { len; bits = Z.(logand bv.bits mask); mask }

let zero_extend len bv =
  let mask = mk_mask len in
  { len; bits = bv.bits; mask }

let sign_extend len bv =
  let s = sign_bit bv in
  let bits =
    if s then
      let lmask = Z.(shift_left one len - one) in
      let smask = Z.(shift_left one bv.len - one) in
      Z.(logor bv.bits (logxor lmask smask))
    else
      bv.bits
  in
  { len; bits; mask = mk_mask len }
