(* LSB first *)
type t = {
  len : int;
  bits : int array;
}

let bpi = Sys.word_size-1

let make_bits len = Array.make ((len+bpi-1)/bpi) 0

let rec zero len =
  if len <= 0 then invalid_arg "Bitvec.zero";
  let bits = make_bits len in
  { len; bits }

let copy_bits1 len dst di src sb =
  let si = sb/bpi in
  let sr = sb mod bpi in
  let q = len/bpi in
  let r = len mod bpi in
  (* copy full words *)
  for i=0 to q-1 do
    dst.(i) <- (src.(si+i) lsr sr) lor (src.(si+i+1) lsl (bpi-sr))
  done;
  if r > 0 then begin
    (* deal with final partial word *)
    let hi =
      if sr+r > bpi then
        (src.(si+q) lsr sr) lor (src.(si+q+1) lsl (bpi-sr))
      else
        (src.(si+q) lsr sr)
    in
    let mask = (1 lsl r)-1 in
    dst.(q) <- (dst.(q) land (lnot mask)) lor (hi land mask)
  end

let copy_bits len dst db src sb =
  let di = db/bpi in
  let dr = db mod bpi in
  if dr > 0 then begin
    let si = sb/bpi in
    let sr = sb mod bpi in
    let r = min len (bpi-dr) in
    let lo =
      if sr+r > bpi then
        (src.(si) lsr sr) lor (src.(si+1) lsl (bpi-sr))
      else
        (src.(si) lsr sr)
    in
    let mask = ((1 lsl r)-1) lsl dr in
    dst.(di) <- (dst.(di) land (lnot mask)) lor (lo land mask);
    copy_bits1 (len-r) dst (di+1) src (sb+r)
  end else begin
    copy_bits1 len dst di src sb
  end

let part (lo, hi) bv =
  if not (0 <= lo && lo <= hi && hi <= bv.len) then
    invalid_arg "Bitvec.part";
  let len = hi-lo in
  let bits = make_bits len in
  copy_bits1 len bits 0 bv.bits lo;
  { len; bits }

let concat bvs =
  let src = Array.of_list bvs in
  let len = src |> Array.fold_left (fun sum bv -> sum + bv.len) 0 in
  let bits = make_bits len in
  let db = ref 0 in
  for i=0 to Array.length src - 1 do
    let src_length = src.(i).len in
    copy_bits src_length bits !db src.(i).bits 0;
    db := !db + src_length
  done;
  { len; bits }

let bit_value b =
  if b then 1 else 0

let add_c bv1 bv2 c =
  if bv1.len <> bv2.len then invalid_arg "Bitvec.add_c";
  let n = Array.length bv1.bits in
  let bits = Array.make n 0 in
  let rec loop i c =
    if i < n then begin
      let open Nativeint in
      let w1 = of_int bv1.bits.(i) in
      let w2 = of_int bv2.bits.(i) in
      let sum = add w1 w2 in
      let sum_c = if c then add sum one else sum in
      bits.(i) <- to_int sum_c;
      loop (i+1) (compare sum_c zero < 0)
    end
  in
  loop 0 c;
  { len = bv1.len; bits }

let add bv1 bv2 = add_c bv1 bv2 false

let notv bv =
  let n = Array.length bv.bits in
  let bits = Array.make n 0 in
  for i=0 to n-1 do
    bits.(i) <- lnot bv.bits.(i)
  done;
  { len = bv.len; bits }

let sub bv1 bv2 = add_c bv1 (notv bv2) true

let length bv = bv.len

let neg bv = sub (zero (length bv)) bv

let rec bitwise f bv1 bv2 =
  if bv1.len <> bv2.len then invalid_arg "Bitvec.bitwise";
  let n = Array.length bv1.bits in
  let bits = Array.make n 0 in
  for i=0 to n-1 do
    bits.(i) <- f bv1.bits.(i) bv2.bits.(i)
  done;
  { len = bv1.len; bits }

let andv = bitwise (land)
let xorv = bitwise (lxor)
let orv  = bitwise (lor)

let of_string s =
  let len = String.length s in
  let bits = make_bits len in
  let q = len/bpi in
  let r = len mod bpi in
  for i=0 to q-1 do
    let w = ref 0 in
    for j=0 to bpi-1 do
      match s.[len-1-(i*bpi+j)] with
      | '0' -> ()
      | '1' -> w := !w lor (1 lsl j)
      | _ -> invalid_arg "Bitvec.of_string"
    done;
    bits.(i) <- !w
  done;
  if r > 0 then begin
    let w = ref 0 in
    for j=0 to r-1 do
      match s.[r-1-j] with
      | '0' -> ()
      | '1' -> w := !w lor (1 lsl j)
      | _ -> invalid_arg "Bitvec.of_string"
    done;
    bits.(q) <- !w;
  end;
  { len; bits }

let to_string bv =
  let s = Bytes.create bv.len in
  for i=0 to Array.length bv.bits - 1 do
    for j=0 to bpi-1 do
      let c = if bv.bits.(i) lor (1 lsl j) = 0 then '0' else '1' in
      Bytes.set s (bv.len-1-(i*bpi+j)) c
    done
  done;
  Bytes.to_string s

let of_bool b = { len = 1; bits = Array.make 1 (if b then 1 else 0) }

let of_int len i =
  if len <= 0 then invalid_arg "Bitvec.of_int";
  { len; bits = Array.make 1 i }

let to_int bv = bv.bits.(0)

let of_bytestring s = failwith "not implemented"

let pp f bv = Format.pp_print_string f (to_string bv)

let to_bool bv =
  if bv.len <> 1 then invalid_arg "Bitvec.to_bool";
  bv.bits.(0) <> 0
