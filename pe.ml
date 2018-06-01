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
}

let load path =

  let code = File.with_file_in path IO.read_all in
  let entry_point =
    try
      if not (String.starts_with code "MZ") then begin
        eprintf "invalid DOS executable signature\n";
        exit 1
      end;
      let e_lfanew = read_u32 code 0x3c |> Int32.to_int in
      let pe_signature = String.sub code e_lfanew 4 in
      if pe_signature <> "PE\x00\x00" then begin
        eprintf "invalid PE signature\n";
        exit 1
      end;
      let coff_header_offset = e_lfanew + 4 in
      let size_of_opt_header = read_u16 code (coff_header_offset + 16) in
      printf "SizeOfOptionalHeader = %d\n" size_of_opt_header;
      let opt_header_offset = coff_header_offset + 20 in
      let opt_header_magic = read_u16 code opt_header_offset in
      printf "Magic = %04x\n" opt_header_magic;
      if opt_header_magic <> 0x10b then begin
        eprintf "not a PE32 file\n";
        exit 1
      end;
      read_u32 code (opt_header_offset + 16) |> Nativeint.of_int32
    with Invalid_offset ->
      eprintf "invalid PE file\n";
      exit 1
  in
  printf "AddressOfEntryPoint = %08nx\n" entry_point;

  { code; entry_point }
