open Batteries

type t = {
  len : int;
  bits : nativeint;
}

let zero len =
  { len; bits = 0n }

let add bv1 bv2 =
  let len = bv1.len in
  { len; bits = Nativeint.(bv1.bits + bv2.bits) }

let notv bv =
  { len = bv.len; bits = Nativeint.lognot bv.bits }

let sub bv1 bv2 =
  let len = bv1.len in
  { len; bits = Nativeint.(bv1.bits - bv2.bits) }

let length bv = bv.len

let neg bv =
  { len = bv.len; bits = Nativeint.neg bv.bits }

let rec bitwise f bv1 bv2 =
  let len = bv1.len in
  { len; bits = f bv1.bits bv2.bits }

let andv = bitwise Nativeint.logand
let xorv = bitwise Nativeint.logxor
let orv  = bitwise Nativeint.logor

let of_string s =
  let len = String.length s in
  let w = ref 0n in
  for i=0 to len-1 do
    if s.[i] <> '0' then
      let shamt = len-1-i in
      w := Nativeint.(logor !w (shift_left 1n shamt))
  done;
  { len; bits = !w }

let to_string bv =
  let s = Bytes.create bv.len in
  for i=0 to bv.len-1 do
    let c =
      if Nativeint.(logor bv.bits (shift_left 1n i) = 0n) then '0' else '1'
    in
    Bytes.set s (bv.len-1-i) c
  done;
  Bytes.to_string s

let of_bool b = { len = 1; bits = if b then 1n else 0n }

let part (lo, hi) bv =
  let len = hi-lo in
  let mask = Nativeint.(shift_left 1n len - 1n) in
  { len; bits = Nativeint.(logand mask (shift_right bv.bits lo)) }

let of_int len i =
  { len; bits = Nativeint.of_int i }

let of_nativeint len bits =
  { len; bits }

let sign_bit bv =
  Nativeint.logand (Nativeint.shift_right bv.bits (bv.len-1)) 1n = 1n

let to_nativeint bv =
  let mask = Nativeint.shift_left (-1n) bv.len in
  if sign_bit bv then
    Nativeint.logor mask bv.bits
  else
    Nativeint.(logand (lognot mask) bv.bits)

let of_bytestring s = failwith "Bitvec.of_bytestring: not implemented"

let pp f bv = Format.pp_print_string f (to_string bv)

let to_bool bv =
  bv.bits <> 0n

let equal b1 b2 = b1 = b2

let truncate len bv =
  let mask = Nativeint.(shift_left 1n len - 1n) in
  { len; bits = Nativeint.(logand bv.bits mask) }

let zero_extend len bv =
  { len; bits = bv.bits }

let sign_extend len bv =
  let s = sign_bit bv in
  let bits =
    if s then
      let lmask = Nativeint.(shift_left 1n len - 1n) in
      let smask = Nativeint.(shift_left 1n bv.len - 1n) in
      Nativeint.(logor bv.bits (logxor lmask smask))
    else
      bv.bits
  in
  { len; bits }
