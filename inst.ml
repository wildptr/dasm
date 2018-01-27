open Format

type reg =
  | R_AL | R_CL | R_DL | R_BL | R_AH | R_CH | R_DH | R_BH
  | R_AX | R_CX | R_DX | R_BX | R_SP | R_BP | R_SI | R_DI
  | R_EAX | R_ECX | R_EDX | R_EBX | R_ESP | R_EBP | R_ESI | R_EDI
  | R_ES | R_CS | R_SS | R_DS | R_FS | R_GS
  | R_fpu of int | R_xmm of int

let string_of_reg = function
  | R_AL -> "al"
  | R_CL -> "cl"
  | R_DL -> "dl"
  | R_BL -> "bl"
  | R_AH -> "ah"
  | R_CH -> "ch"
  | R_DH -> "dh"
  | R_BH -> "bh"
  | R_AX -> "ax"
  | R_CX -> "cx"
  | R_DX -> "dx"
  | R_BX -> "bx"
  | R_SI -> "si"
  | R_DI -> "di"
  | R_SP -> "sp"
  | R_BP -> "bp"
  | R_EAX -> "eax"
  | R_ECX -> "ecx"
  | R_EDX -> "edx"
  | R_EBX -> "ebx"
  | R_ESI -> "esi"
  | R_EDI -> "edi"
  | R_ESP -> "esp"
  | R_EBP -> "ebp"
  | R_ES -> "es"
  | R_CS -> "cs"
  | R_SS -> "ss"
  | R_DS -> "ds"
  | R_FS -> "fs"
  | R_GS -> "gs"
  | R_fpu i -> "st" ^ (string_of_int i)
  | R_xmm i -> "xmm" ^ (string_of_int i)

let size_of_reg = function
  | R_AL | R_CL | R_DL | R_BL | R_AH | R_CH | R_DH | R_BH -> 8
  | R_AX | R_CX | R_DX | R_BX | R_SI | R_DI | R_SP | R_BP -> 16
  | R_EAX | R_ECX | R_EDX | R_EBX | R_ESI | R_EDI | R_ESP | R_EBP -> 32
  | R_ES | R_CS | R_SS | R_DS | R_FS | R_GS -> 16
  | R_fpu _ -> 80
  | R_xmm _ -> 128

(* let index_of_reg = function
  | R_AL -> 0
  | R_CL -> 1
  | R_DL -> 2
  | R_BL -> 3
  | R_AH -> 4
  | R_CH -> 5
  | R_DH -> 6
  | R_BH -> 7
  | R_AX -> 0
  | R_CX -> 1
  | R_DX -> 2
  | R_BX -> 3
  | R_SI -> 4
  | R_DI -> 5
  | R_SP -> 6
  | R_BP -> 7
  | R_EAX -> 0
  | R_ECX -> 1
  | R_EDX -> 2
  | R_EBX -> 3
  | R_ESI -> 4
  | R_EDI -> 5
  | R_ESP -> 6
  | R_EBP -> 7 *)

(* TODO: add segment field *)
type mem = {
  base : reg option;
  index : (reg * int (* scale *)) option;
  disp : int;
}

let pp_mem f m =
  let open Format in
  let pp_index f (reg, scale) =
    pp_print_string f (string_of_reg reg);
    if scale > 1 then fprintf f "*%d" scale
  in
  match m.base, m.index with
  | Some base, Some index ->
    fprintf f "[%s+%a" (string_of_reg base) pp_index index;
    if m.disp <> 0 then fprintf f "%+d" m.disp;
    fprintf f "]"
  | Some base, None ->
    fprintf f "[%s" (string_of_reg base);
    if m.disp <> 0 then fprintf f "%+d" m.disp;
    fprintf f "]"
  | None, Some index ->
    fprintf f "[%a" pp_index index;
    if m.disp <> 0 then fprintf f "%+d" m.disp;
    fprintf f "]"
  | None, None ->
    fprintf f "[%d]" m.disp

type regmem =
  | Reg of int
  | Mem of mem

type prefix =
  | Prefix_26
  | Prefix_2e
  | Prefix_36
  | Prefix_3e
  | Prefix_64
  | Prefix_65
  | Prefix_66
  | Prefix_67
  | Prefix_f0
  | Prefix_f2
  | Prefix_f3

(* prefixes can be packed into 7 bits *)
let prefix_mask = function
  | Prefix_26
  | Prefix_2e
  | Prefix_36
  | Prefix_3e
  | Prefix_64
  | Prefix_65 -> 0x1c
  | Prefix_66 -> 0x20
  | Prefix_67 -> 0x40
  | Prefix_f0
  | Prefix_f2
  | Prefix_f3 -> 3

let prefix_value = function
  | Prefix_26 -> 1 lsl 2
  | Prefix_2e -> 2 lsl 2
  | Prefix_36 -> 3 lsl 2
  | Prefix_3e -> 4 lsl 2
  | Prefix_64 -> 5 lsl 2
  | Prefix_65 -> 6 lsl 2
  | Prefix_66 -> 0x20
  | Prefix_67 -> 0x40
  | Prefix_f0 -> 1
  | Prefix_f2 -> 2
  | Prefix_f3 -> 3

let format_size = function
  | 1 -> "byte"
  | 2 -> "word"
  | 4 -> "dword"
  | 8 -> "qword"
  | 10 -> "tword"
  | 16 -> "oword"
  | _ -> assert false

type operand =
  | O_reg of reg
  | O_mem of mem * int (* size in bytes; 0 means unspecified *)
  | O_imm of int * int
  | O_offset of int
  | O_farptr of (int * int)

let pp_operand f = function
  | O_reg r -> pp_print_string f (string_of_reg r)
  | O_mem (m, size) ->
    if size > 0 then fprintf f "%s " (format_size size);
    pp_mem f m
  | O_imm (i, size) ->
    if size > 0 then fprintf f "%s " (format_size size);
    pp_print_int f i
  | O_offset disp ->
    pp_print_string f "$";
    if disp <> 0 then fprintf f "%+d" disp
  | O_farptr (seg, off) -> fprintf f "0x%x:0x%x" seg off

type operation =
  | I_
  | I_aaa
  | I_aad
  | I_aam
  | I_aas
  | I_adc
  | I_add
  | I_and
  | I_arpl
  | I_bound
  | I_call
  | I_callfar
  | I_cbw
  | I_cjmp
  | I_clc
  | I_cld
  | I_cli
  | I_cmc
  | I_cmp
  | I_cmps
  | I_cwd
  | I_daa
  | I_das
  | I_dec
  | I_div
  | I_enter
  | I_f2xm1
  | I_fabs
  | I_fadd
  | I_fadd_to
  | I_faddp
  | I_fbld
  | I_fbstp
  | I_fchs
  | I_fcmovb
  | I_fcmovbe
  | I_fcmove
  | I_fcmovnb
  | I_fcmovnbe
  | I_fcmovne
  | I_fcmovnu
  | I_fcmovu
  | I_fcom
  | I_fcomi
  | I_fcomip
  | I_fcomp
  | I_fcompp
  | I_fcos
  | I_fdecstp
  | I_fdiv
  | I_fdiv_to
  | I_fdivp
  | I_fdivr
  | I_fdivr_to
  | I_fdivrp
  | I_ffree
  | I_fiadd
  | I_ficom
  | I_ficomp
  | I_fidiv
  | I_fidivr
  | I_fild
  | I_fimul
  | I_fincstp
  | I_fist
  | I_fistp
  | I_fisttp
  | I_fisub
  | I_fisubr
  | I_fld
  | I_fld1
  | I_fldcw
  | I_fldenv
  | I_fldl2e
  | I_fldl2t
  | I_fldlg2
  | I_fldln2
  | I_fldpi
  | I_fldz
  | I_fmul
  | I_fmul_to
  | I_fmulp
  | I_fnclex
  | I_fninit
  | I_fnop
  | I_fnsave
  | I_fnstcw
  | I_fnstenv
  | I_fnstsw
  | I_fpatan
  | I_fprem
  | I_fprem1
  | I_fptan
  | I_frndint
  | I_frstor
  | I_fscale
  | I_fsin
  | I_fsincos
  | I_fsqrt
  | I_fst
  | I_fstp
  | I_fsub
  | I_fsub_to
  | I_fsubp
  | I_fsubr
  | I_fsubr_to
  | I_fsubrp
  | I_ftst
  | I_fucom
  | I_fucomi
  | I_fucomip
  | I_fucomp
  | I_fucompp
  | I_fxam
  | I_fxch
  | I_fxtract
  | I_fyl2x
  | I_fyl2xp1
  | I_hlt
  | I_idiv
  | I_imul
  | I_in
  | I_inc
  | I_ins
  | I_int
  | I_int1
  | I_int3
  | I_into
  | I_iret
  | I_jcxz
  | I_jmp
  | I_jmpfar
  | I_lahf
  | I_lds
  | I_lea
  | I_leave
  | I_les
  | I_lods
  | I_loop
  | I_loopnz
  | I_loopz
  | I_mov
  | I_movfromseg
  | I_movs
  | I_movsx
  | I_movtoseg
  | I_movups
  | I_movzx
  | I_mul
  | I_neg
  | I_not
  | I_or
  | I_out
  | I_outs
  | I_pop
  | I_popa
  | I_popf
  | I_push
  | I_pusha
  | I_pushf
  | I_rcl
  | I_rcr
  | I_ret
  | I_retfar
  | I_retn
  | I_retnfar
  | I_rol
  | I_ror
  | I_sahf
  | I_sar
  | I_sbb
  | I_scas
  | I_set
  | I_shl
  | I_shr
  | I_stc
  | I_std
  | I_sti
  | I_stos
  | I_sub
  | I_test
  | I_wait
  | I_xchg
  | I_xlat
  | I_xor

type t = {
  ext_opcode : int; (* opcode << 3 | opcode_extension *)
  prefix : int;
  bytes : string;
  operation : operation;
  variant : int;
  operands : operand list;
}

let make ext_opcode prefix bytes operation variant operands =
  { ext_opcode; prefix; bytes; operation; variant; operands }

let ext_opcode_of inst = inst.ext_opcode

let prefix_of inst = inst.prefix

let bytes_of inst = inst.bytes

let length_of inst = String.length inst.bytes

let operands_of inst = inst.operands

let operation_of inst = inst.operation

let cond_code =
  [|"o";"no";"b";"ae";"z";"nz";"be";"a";
    "s";"ns";"p";"np";"l";"ge";"le";"g"|]

let suffix_of_size = function
  | 0 -> "b"
  | 1 -> "w"
  | 2 -> "d"
  | 3 -> "q"
  | 4 -> "o"
  | _ -> assert false

let prefix_of_size = function
  | 1 -> "o16 "
  | 2 -> "o32 "
  | 3 -> "o64 "
  | _ -> assert false

let mnemonic_of inst =
  match inst.operation with
  | I_ -> "<invalid instruction>"
  | I_aaa -> "aaa"
  | I_aad -> "aad"
  | I_aam -> "aam"
  | I_aas -> "aas"
  | I_adc -> "adc"
  | I_add -> "add"
  | I_and -> "and"
  | I_arpl -> "arpl"
  | I_bound -> "bound"
  | I_call -> "call"
  | I_callfar -> "callfar"
  | I_cbw -> "cbw"
  | I_cjmp -> "j"^cond_code.(inst.variant lsr 2)
  | I_clc -> "clc"
  | I_cld -> "cld"
  | I_cli -> "cli"
  | I_cmc -> "cmc"
  | I_cmp -> "cmp"
  | I_cmps -> "cmps" ^ suffix_of_size inst.variant
  | I_cwd -> "cwd"
  | I_daa -> "daa"
  | I_das -> "das"
  | I_dec -> "dec"
  | I_div -> "div"
  | I_enter -> "enter"
  | I_f2xm1 -> "f2xm1"
  | I_fabs -> "fabs"
  | I_fadd -> "fadd"
  | I_fadd_to -> "fadd to"
  | I_faddp -> "faddp"
  | I_fbld -> "fbld"
  | I_fbstp -> "fbstp"
  | I_fchs -> "fchs"
  | I_fcmovb -> "fcmovb"
  | I_fcmovbe -> "fcmovbe"
  | I_fcmove -> "fcmove"
  | I_fcmovnb -> "fcmovnb"
  | I_fcmovnbe -> "fcmovnbe"
  | I_fcmovne -> "fcmovne"
  | I_fcmovnu -> "fcmovnu"
  | I_fcmovu -> "fcmovu"
  | I_fcom -> "fcom"
  | I_fcomi -> "fcomi"
  | I_fcomip -> "fcomip"
  | I_fcomp -> "fcomp"
  | I_fcompp -> "fcompp"
  | I_fcos -> "fcos"
  | I_fdecstp -> "fdecstp"
  | I_fdiv -> "fdiv"
  | I_fdiv_to -> "fdiv to"
  | I_fdivp -> "fdivp"
  | I_fdivr -> "fdivr"
  | I_fdivr_to -> "fdivr to"
  | I_fdivrp -> "fdivrp"
  | I_ffree -> "ffree"
  | I_fiadd -> "fiadd"
  | I_ficom -> "ficom"
  | I_ficomp -> "ficomp"
  | I_fidiv -> "fidiv"
  | I_fidivr -> "fidivr"
  | I_fild -> "fild"
  | I_fimul -> "fimul"
  | I_fincstp -> "fincstp"
  | I_fist -> "fist"
  | I_fistp -> "fistp"
  | I_fisttp -> "fisttp"
  | I_fisub -> "fisub"
  | I_fisubr -> "fisubr"
  | I_fld -> "fld"
  | I_fld1 -> "fld1"
  | I_fldcw -> "fldcw"
  | I_fldenv -> "fldenv"
  | I_fldl2e -> "fldl2e"
  | I_fldl2t -> "fldl2t"
  | I_fldlg2 -> "fldlg2"
  | I_fldln2 -> "fldln2"
  | I_fldpi -> "fldpi"
  | I_fldz -> "fldz"
  | I_fmul -> "fmul"
  | I_fmul_to -> "fmul to"
  | I_fmulp -> "fmulp"
  | I_fnclex -> "fnclex"
  | I_fninit -> "fninit"
  | I_fnop -> "fnop"
  | I_fnsave -> "fnsave"
  | I_fnstcw -> "fnstcw"
  | I_fnstenv -> "fnstenv"
  | I_fnstsw -> "fnstsw"
  | I_fpatan -> "fpatan"
  | I_fprem -> "fprem"
  | I_fprem1 -> "fprem1"
  | I_fptan -> "fptan"
  | I_frndint -> "frndint"
  | I_frstor -> "frstor"
  | I_fscale -> "fscale"
  | I_fsin -> "fsin"
  | I_fsincos -> "fsincos"
  | I_fsqrt -> "fsqrt"
  | I_fst -> "fst"
  | I_fstp -> "fstp"
  | I_fsub -> "fsub"
  | I_fsub_to -> "fsub to"
  | I_fsubp -> "fsubp"
  | I_fsubr -> "fsubr"
  | I_fsubr_to -> "fsubr to"
  | I_fsubrp -> "fsubrp"
  | I_ftst -> "ftst"
  | I_fucom -> "fucom"
  | I_fucomi -> "fucomi"
  | I_fucomip -> "fucomip"
  | I_fucomp -> "fucomp"
  | I_fucompp -> "fucompp"
  | I_fxam -> "fxam"
  | I_fxch -> "fxch"
  | I_fxtract -> "fxtract"
  | I_fyl2x -> "fyl2x"
  | I_fyl2xp1 -> "fyl2xp1"
  | I_hlt -> "hlt"
  | I_idiv -> "idiv"
  | I_imul -> "imul"
  | I_in -> "in"
  | I_inc -> "inc"
  | I_ins -> "ins" ^ suffix_of_size inst.variant
  | I_int -> "int"
  | I_int1 -> "int1"
  | I_int3 -> "int3"
  | I_into -> "into"
  | I_iret -> "iret"
  | I_jcxz -> "jcxz"
  | I_jmp -> "jmp"
  | I_jmpfar -> "jmpfar"
  | I_lahf -> "lahf"
  | I_lds -> "lds"
  | I_lea -> "lea"
  | I_leave -> "leave"
  | I_les -> "les"
  | I_lods -> "lods" ^ suffix_of_size inst.variant
  | I_loop -> "loop"
  | I_loopnz -> "loopnz"
  | I_loopz -> "loopz"
  | I_mov -> "mov"
  | I_movfromseg -> "mov"
  | I_movs -> "movs" ^ suffix_of_size inst.variant
  | I_movsx -> "movsx"
  | I_movtoseg -> prefix_of_size inst.variant ^ "mov"
  | I_movups -> "movups"
  | I_movzx -> "movzx"
  | I_mul -> "mul"
  | I_neg -> "neg"
  | I_not -> "not"
  | I_or -> "or"
  | I_out -> "out"
  | I_outs -> "outs" ^ suffix_of_size inst.variant
  | I_pop -> prefix_of_size inst.variant ^ "pop"
  | I_popa -> prefix_of_size inst.variant ^ "popa"
  | I_popf -> "popf"
  | I_push -> prefix_of_size inst.variant ^ "push"
  | I_pusha -> prefix_of_size inst.variant ^ "pusha"
  | I_pushf -> "pushf"
  | I_rcl -> "rcl"
  | I_rcr -> "rcr"
  | I_ret -> "ret"
  | I_retfar -> "retfar"
  | I_retn -> "retn"
  | I_retnfar -> "retnfar"
  | I_rol -> "rol"
  | I_ror -> "ror"
  | I_sahf -> "sahf"
  | I_sar -> "sar"
  | I_sbb -> "sbb"
  | I_scas -> "scas" ^ suffix_of_size inst.variant
  | I_set -> "set"^cond_code.(inst.variant lsr 2)
  | I_shl -> "shl"
  | I_shr -> "shr"
  | I_stc -> "stc"
  | I_std -> "std"
  | I_sti -> "sti"
  | I_stos -> "stos" ^ suffix_of_size inst.variant
  | I_sub -> "sub"
  | I_test -> "test"
  | I_wait -> "wait"
  | I_xchg -> "xchg"
  | I_xlat -> "xlat"
  | I_xor -> "xor"

let pp f inst =
  pp_print_string f (mnemonic_of inst);
  match inst.operands with
  | [] -> ()
  | o_hd::o_tl ->
    pp_print_string f " ";
    pp_operand f o_hd;
    List.iter (fun o -> pp_print_string f ","; pp_operand f o) o_tl

let has_prefix inst prefix =
  inst.prefix land (prefix_mask prefix) = prefix_value prefix
