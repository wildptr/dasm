open Batteries
open Printf

exception Invalid_offset

let read_u16 s offset =
  if String.length s < offset+2 then raise Invalid_offset;
  (int_of_char s.[offset  ]       ) lor
  (int_of_char s.[offset+1] lsl  8)

let read_u32 s offset =
  let module I = Int32 in
  if String.length s < offset+4 then raise Invalid_offset;
  (             (s.[offset  ] |> int_of_char |> I.of_int)   ) |> I.logor
  (I.shift_left (s.[offset+1] |> int_of_char |> I.of_int)  8) |> I.logor
  (I.shift_left (s.[offset+2] |> int_of_char |> I.of_int) 16) |> I.logor
  (I.shift_left (s.[offset+3] |> int_of_char |> I.of_int) 24)

type pe = {
  code : string;
  entry_point : nativeint;
  coff_header_raw : string;
  optional_header_raw : string;
}

let load path =
  try
    let code = File.with_file_in path IO.read_all in
    if not (String.starts_with code "MZ") then begin
      failwith "invalid DOS executable signature\n";
    end;
    let e_lfanew = read_u32 code 0x3c |> Int32.to_int in
    let pe_signature = String.sub code e_lfanew 4 in
    if pe_signature <> "PE\x00\x00" then begin
      failwith "invalid PE signature\n";
    end;
    let coff_header_offset = e_lfanew + 4 in
    let coff_header_raw = String.sub code coff_header_offset 20 in
    let size_of_opt_header = read_u16 coff_header_raw 16 in
    let opt_header_offset = coff_header_offset + 20 in
    let optional_header_raw =
      String.sub code opt_header_offset size_of_opt_header
    in
    let opt_header_magic = read_u16 optional_header_raw 0 in
    if opt_header_magic <> 0x10b then begin
      failwith "not a PE32 file\n";
    end;
    let entry_point = read_u32 optional_header_raw 16 |> Nativeint.of_int32 in
    { code; entry_point; coff_header_raw; optional_header_raw }
  with Invalid_offset ->
    failwith "invalid PE file\n";
