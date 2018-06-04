open Format

type reg =
  | R_AL | R_CL | R_DL | R_BL | R_AH | R_CH | R_DH | R_BH
  | R_AX | R_CX | R_DX | R_BX | R_SP | R_BP | R_SI | R_DI
  | R_EAX | R_ECX | R_EDX | R_EBX | R_ESP | R_EBP | R_ESI | R_EDI
  | R_ES | R_CS | R_SS | R_DS | R_FS | R_GS
  | R_ST0 | R_ST1 | R_ST2 | R_ST3 | R_ST4 | R_ST5 | R_ST6 | R_ST7
  | R_XMM0 | R_XMM1 | R_XMM2 | R_XMM3 | R_XMM4 | R_XMM5 | R_XMM6 | R_XMM7
  | R_CF | R_PF | R_AF | R_ZF | R_SF | R_DF | R_OF

let string_of_reg = function
  | R_AL -> "AL"
  | R_CL -> "CL"
  | R_DL -> "DL"
  | R_BL -> "BL"
  | R_AH -> "AH"
  | R_CH -> "CH"
  | R_DH -> "DH"
  | R_BH -> "BH"
  | R_AX -> "AX"
  | R_CX -> "CX"
  | R_DX -> "DX"
  | R_BX -> "BX"
  | R_SI -> "SI"
  | R_DI -> "DI"
  | R_SP -> "SP"
  | R_BP -> "BP"
  | R_EAX -> "EAX"
  | R_ECX -> "ECX"
  | R_EDX -> "EDX"
  | R_EBX -> "EBX"
  | R_ESP -> "ESP"
  | R_EBP -> "EBP"
  | R_ESI -> "ESI"
  | R_EDI -> "EDI"
  | R_CF -> "CF"
  | R_PF -> "PF"
  | R_AF -> "AF"
  | R_ZF -> "ZF"
  | R_SF -> "SF"
  | R_DF -> "DF"
  | R_OF -> "OF"
  | R_ES -> "ES"
  | R_CS -> "CS"
  | R_SS -> "SS"
  | R_DS -> "DS"
  | R_FS -> "FS"
  | R_GS -> "GS"
  | R_ST0 -> "ST0"
  | R_ST1 -> "ST1"
  | R_ST2 -> "ST2"
  | R_ST3 -> "ST3"
  | R_ST4 -> "ST4"
  | R_ST5 -> "ST5"
  | R_ST6 -> "ST6"
  | R_ST7 -> "ST7"
  | R_XMM0 -> "XMM0"
  | R_XMM1 -> "XMM1"
  | R_XMM2 -> "XMM2"
  | R_XMM3 -> "XMM3"
  | R_XMM4 -> "XMM4"
  | R_XMM5 -> "XMM5"
  | R_XMM6 -> "XMM6"
  | R_XMM7 -> "XMM7"

let size_of_reg = function
  | R_AL | R_CL | R_DL | R_BL | R_AH | R_CH | R_DH | R_BH -> 8
  | R_AX | R_CX | R_DX | R_BX | R_SI | R_DI | R_SP | R_BP -> 16
  | R_EAX | R_ECX | R_EDX | R_EBX | R_ESI | R_EDI | R_ESP | R_EBP -> 32
  | R_ES | R_CS | R_SS | R_DS | R_FS | R_GS -> 16
  | R_ST0 | R_ST1 | R_ST2 | R_ST3 | R_ST4 | R_ST5 | R_ST6 | R_ST7 -> 80
  | R_XMM0 | R_XMM1 | R_XMM2 | R_XMM3 | R_XMM4 | R_XMM5 | R_XMM6 | R_XMM7 -> 128
  | R_CF | R_PF | R_AF | R_ZF | R_SF | R_DF | R_OF -> 1

let lookup_reg name =
  match name with
  | "AL" -> R_AL
  | "CL" -> R_CL
  | "DL" -> R_DL
  | "BL" -> R_BL
  | "AH" -> R_AH
  | "CH" -> R_CH
  | "DH" -> R_DH
  | "BH" -> R_BH
  | "AX" -> R_AX
  | "CX" -> R_CX
  | "DX" -> R_DX
  | "BX" -> R_BX
  | "SP" -> R_SP
  | "BP" -> R_BP
  | "SI" -> R_SI
  | "DI" -> R_DI
  | "EAX" -> R_EAX
  | "ECX" -> R_ECX
  | "EDX" -> R_EDX
  | "EBX" -> R_EBX
  | "ESP" -> R_ESP
  | "EBP" -> R_EBP
  | "ESI" -> R_ESI
  | "EDI" -> R_EDI
  | "CF" -> R_CF
  | "PF" -> R_PF
  | "AF" -> R_AF
  | "ZF" -> R_ZF
  | "SF" -> R_SF
  | "DF" -> R_DF
  | "OF" -> R_OF
  | "ES" -> R_ES
  | "CS" -> R_CS
  | "SS" -> R_SS
  | "DS" -> R_DS
  | "FS" -> R_FS
  | "GS" -> R_GS
  | _ -> failwith ("lookup_reg: " ^ name)

type mem = {
  base : reg option;
  index : (reg * int (* scale *)) option;
  disp : nativeint;
  seg : reg;
}

let pp_mem f m =
  let open Format in
  let pp_index f (reg, scale) =
    pp_print_string f (string_of_reg reg);
    if scale > 1 then fprintf f "*%d" scale
  in
  let seg_name = string_of_reg m.seg in
  fprintf f "%s:" seg_name;
  match m.base, m.index with
  | Some base, Some index ->
    fprintf f "[%s+%a" (string_of_reg base) pp_index index;
    if m.disp <> 0n then fprintf f "%+nd" m.disp;
    fprintf f "]"
  | Some base, None ->
    fprintf f "[%s" (string_of_reg base);
    if m.disp <> 0n then fprintf f "%+nd" m.disp;
    fprintf f "]"
  | None, Some index ->
    fprintf f "[%a" pp_index index;
    if m.disp <> 0n then fprintf f "%+nd" m.disp;
    fprintf f "]"
  | None, None ->
    fprintf f "[%nd]" m.disp

type regmem =
  | Reg of int
  | Mem of mem

let format_size = function
  | 1 -> "BYTE"
  | 2 -> "WORD"
  | 4 -> "DWORD"
  | 8 -> "QWORD"
  | 10 -> "TWORD"
  | 16 -> "OWORD"
  | _ -> assert false

type operand =
  | O_reg of reg
  | O_mem of mem * int (* size in bytes; 0 means unspecified *)
  | O_imm of nativeint * int
  | O_offset of nativeint
  | O_farptr of int * nativeint

let pp_operand f = function
  | O_reg r -> pp_print_string f (string_of_reg r)
  | O_mem (m, size) ->
    if size > 0 then fprintf f "%s " (format_size size);
    pp_mem f m
  | O_imm (i, size) ->
    if size > 0 then fprintf f "%s " (format_size size);
    fprintf f "%nd" i
  | O_offset disp ->
    pp_print_string f "$";
    if disp <> 0n then fprintf f "%+nd" disp
  | O_farptr (seg, off) -> fprintf f "0x%x:0x%nx" seg off

type operation =
  | I_BAD
  | I_AAA
  | I_AAD
  | I_AAM
  | I_AAS
  | I_ADC
  | I_ADD
  | I_AND
  | I_ARPL
  | I_BOUND
  | I_CALL
  | I_CALLF
  | I_CBW
  | I_CJMP
  | I_CLC
  | I_CLD
  | I_CLI
  | I_CMC
  | I_CMP
  | I_CMPS
  | I_CPUID
  | I_CWD
  | I_DAA
  | I_DAS
  | I_DEC
  | I_DIV
  | I_ENTER
  | I_F2XM1
  | I_FABS
  | I_FADD
  | I_FADD_TO
  | I_FADDP
  | I_FBLD
  | I_FBSTP
  | I_FCHS
  | I_FCMOVB
  | I_FCMOVBE
  | I_FCMOVE
  | I_FCMOVNB
  | I_FCMOVNBE
  | I_FCMOVNE
  | I_FCMOVNU
  | I_FCMOVU
  | I_FCOM
  | I_FCOMI
  | I_FCOMIP
  | I_FCOMP
  | I_FCOMPP
  | I_FCOS
  | I_FDECSTP
  | I_FDIV
  | I_FDIV_TO
  | I_FDIVP
  | I_FDIVR
  | I_FDIVR_TO
  | I_FDIVRP
  | I_FFREE
  | I_FIADD
  | I_FICOM
  | I_FICOMP
  | I_FIDIV
  | I_FIDIVR
  | I_FILD
  | I_FIMUL
  | I_FINCSTP
  | I_FIST
  | I_FISTP
  | I_FISTTP
  | I_FISUB
  | I_FISUBR
  | I_FLD
  | I_FLD1
  | I_FLDCW
  | I_FLDENV
  | I_FLDL2E
  | I_FLDL2T
  | I_FLDLG2
  | I_FLDLN2
  | I_FLDPI
  | I_FLDZ
  | I_FMUL
  | I_FMUL_TO
  | I_FMULP
  | I_FNCLEX
  | I_FNINIT
  | I_FNOP
  | I_FNSAVE
  | I_FNSTCW
  | I_FNSTENV
  | I_FNSTSW
  | I_FPATAN
  | I_FPREM
  | I_FPREM1
  | I_FPTAN
  | I_FRNDINT
  | I_FRSTOR
  | I_FSCALE
  | I_FSIN
  | I_FSINCOS
  | I_FSQRT
  | I_FST
  | I_FSTP
  | I_FSUB
  | I_FSUB_TO
  | I_FSUBP
  | I_FSUBR
  | I_FSUBR_TO
  | I_FSUBRP
  | I_FTST
  | I_FUCOM
  | I_FUCOMI
  | I_FUCOMIP
  | I_FUCOMP
  | I_FUCOMPP
  | I_FXAM
  | I_FXCH
  | I_FXTRACT
  | I_FYL2X
  | I_FYL2XP1
  | I_HLT
  | I_IDIV
  | I_IMUL
  | I_IN
  | I_INC
  | I_INS
  | I_INT
  | I_INT1
  | I_INT3
  | I_INTO
  | I_IRET
  | I_JCXZ
  | I_JMP
  | I_JMPF
  | I_LAHF
  | I_LDS
  | I_LEA
  | I_LEAVE
  | I_LES
  | I_LODS
  | I_LOOP
  | I_LOOPNZ
  | I_LOOPZ
  | I_MOV
  | I_MFS (* move from seg *)
  | I_MOVS
  | I_MOVSX
  | I_MTS (* move to seg *)
  | I_MOVUPS
  | I_MOVZX
  | I_MUL
  | I_NEG
  | I_NOT
  | I_OR
  | I_OUT
  | I_OUTS
  | I_POP
  | I_POPA
  | I_POPF
  | I_PUSH
  | I_PUSHA
  | I_PUSHF
  | I_RCL
  | I_RCR
  | I_RDMSR
  | I_RDPMC
  | I_RDTSC
  | I_RET
  | I_RETF
  | I_RETN
  | I_RETNF
  | I_ROL
  | I_ROR
  | I_SAHF
  | I_SAR
  | I_SBB
  | I_SCAS
  | I_SET
  | I_SHL
  | I_SHLD
  | I_SHR
  | I_SHRD
  | I_STC
  | I_STD
  | I_STI
  | I_STOS
  | I_SUB
  | I_TEST
  | I_WAIT
  | I_XCHG
  | I_XLAT
  | I_XOR

type inst = {
  bytes : string;
  operation : operation;
  variant : int;
  operands : operand list;
}

let make bytes operation variant operands =
  { bytes; operation; variant; operands }

let bytes_of inst = inst.bytes

let length_of inst = String.length inst.bytes

let operands_of inst = inst.operands

let operation_of inst = inst.operation

let cond_code =
  [|"O";"NO";"B";"AE";"Z";"NZ";"BE";"A";
    "S";"NS";"P";"NP";"L";"GE";"LE";"G"|]

let suffix_of_size = function
  | 0 -> "B"
  | 1 -> "W"
  | 2 -> "D"
  | 3 -> "Q"
  | 4 -> "O"
  | _ -> assert false

let prefix_of_size = function
  | 1 -> "o16 "
  | 2 -> "o32 "
  | 3 -> "o64 "
  | _ -> assert false

let mnemonic_of inst =
  match inst.operation with
  | I_BAD -> "<invalid instruction>"
  | I_AAA -> "AAA"
  | I_AAD -> "AAD"
  | I_AAM -> "AAM"
  | I_AAS -> "AAS"
  | I_ADC -> "ADC"
  | I_ADD -> "ADD"
  | I_AND -> "AND"
  | I_ARPL -> "ARPL"
  | I_BOUND -> "BOUND"
  | I_CALL -> "CALL"
  | I_CALLF -> "CALL FAR"
  | I_CBW -> "CBW"
  | I_CJMP -> "J"^cond_code.(inst.variant lsr 4)
  | I_CLC -> "CLC"
  | I_CLD -> "CLD"
  | I_CLI -> "CLI"
  | I_CMC -> "CMC"
  | I_CMP -> "CMP"
  | I_CMPS -> "CMPS" ^ suffix_of_size inst.variant
  | I_CPUID -> "CPUID"
  | I_CWD -> "CWD"
  | I_DAA -> "DAA"
  | I_DAS -> "DAS"
  | I_DEC -> "DEC"
  | I_DIV -> "DIV"
  | I_ENTER -> "ENTER"
  | I_F2XM1 -> "F2XM1"
  | I_FABS -> "FABS"
  | I_FADD -> "FADD"
  | I_FADD_TO -> "FADD TO"
  | I_FADDP -> "FADDP"
  | I_FBLD -> "FBLD"
  | I_FBSTP -> "FBSTP"
  | I_FCHS -> "FCHS"
  | I_FCMOVB -> "FCMOVB"
  | I_FCMOVBE -> "FCMOVBE"
  | I_FCMOVE -> "FCMOVE"
  | I_FCMOVNB -> "FCMOVNB"
  | I_FCMOVNBE -> "FCMOVNBE"
  | I_FCMOVNE -> "FCMOVNE"
  | I_FCMOVNU -> "FCMOVNU"
  | I_FCMOVU -> "FCMOVU"
  | I_FCOM -> "FCOM"
  | I_FCOMI -> "FCOMI"
  | I_FCOMIP -> "FCOMIP"
  | I_FCOMP -> "FCOMP"
  | I_FCOMPP -> "FCOMPP"
  | I_FCOS -> "FCOS"
  | I_FDECSTP -> "FDECSTP"
  | I_FDIV -> "FDIV"
  | I_FDIV_TO -> "FDIV TO"
  | I_FDIVP -> "FDIVP"
  | I_FDIVR -> "FDIVR"
  | I_FDIVR_TO -> "FDIVR TO"
  | I_FDIVRP -> "FDIVRP"
  | I_FFREE -> "FFREE"
  | I_FIADD -> "FIADD"
  | I_FICOM -> "FICOM"
  | I_FICOMP -> "FICOMP"
  | I_FIDIV -> "FIDIV"
  | I_FIDIVR -> "FIDIVR"
  | I_FILD -> "FILD"
  | I_FIMUL -> "FIMUL"
  | I_FINCSTP -> "FINCSTP"
  | I_FIST -> "FIST"
  | I_FISTP -> "FISTP"
  | I_FISTTP -> "FISTTP"
  | I_FISUB -> "FISUB"
  | I_FISUBR -> "FISUBR"
  | I_FLD -> "FLD"
  | I_FLD1 -> "FLD1"
  | I_FLDCW -> "FLDCW"
  | I_FLDENV -> "FLDENV"
  | I_FLDL2E -> "FLDL2E"
  | I_FLDL2T -> "FLDL2T"
  | I_FLDLG2 -> "FLDLG2"
  | I_FLDLN2 -> "FLDLN2"
  | I_FLDPI -> "FLDPI"
  | I_FLDZ -> "FLDZ"
  | I_FMUL -> "FMUL"
  | I_FMUL_TO -> "FMUL TO"
  | I_FMULP -> "FMULP"
  | I_FNCLEX -> "FNCLEX"
  | I_FNINIT -> "FNINIT"
  | I_FNOP -> "FNOP"
  | I_FNSAVE -> "FNSAVE"
  | I_FNSTCW -> "FNSTCW"
  | I_FNSTENV -> "FNSTENV"
  | I_FNSTSW -> "FNSTSW"
  | I_FPATAN -> "FPATAN"
  | I_FPREM -> "FPREM"
  | I_FPREM1 -> "FPREM1"
  | I_FPTAN -> "FPTAN"
  | I_FRNDINT -> "FRNDINT"
  | I_FRSTOR -> "FRSTOR"
  | I_FSCALE -> "FSCALE"
  | I_FSIN -> "FSIN"
  | I_FSINCOS -> "FSINCOS"
  | I_FSQRT -> "FSQRT"
  | I_FST -> "FST"
  | I_FSTP -> "FSTP"
  | I_FSUB -> "FSUB"
  | I_FSUB_TO -> "FSUB TO"
  | I_FSUBP -> "FSUBP"
  | I_FSUBR -> "FSUBR"
  | I_FSUBR_TO -> "FSUBR TO"
  | I_FSUBRP -> "FSUBRP"
  | I_FTST -> "FTST"
  | I_FUCOM -> "FUCOM"
  | I_FUCOMI -> "FUCOMI"
  | I_FUCOMIP -> "FUCOMIP"
  | I_FUCOMP -> "FUCOMP"
  | I_FUCOMPP -> "FUCOMPP"
  | I_FXAM -> "FXAM"
  | I_FXCH -> "FXCH"
  | I_FXTRACT -> "FXTRACT"
  | I_FYL2X -> "FYL2X"
  | I_FYL2XP1 -> "FYL2XP1"
  | I_HLT -> "HLT"
  | I_IDIV -> "IDIV"
  | I_IMUL -> "IMUL"
  | I_IN -> "IN"
  | I_INC -> "INC"
  | I_INS -> "INS" ^ suffix_of_size inst.variant
  | I_INT -> "INT"
  | I_INT1 -> "INT1"
  | I_INT3 -> "INT3"
  | I_INTO -> "INTO"
  | I_IRET -> "IRET"
  | I_JCXZ -> "JCXZ"
  | I_JMP -> "JMP"
  | I_JMPF-> "JMP FAR"
  | I_LAHF -> "LAHF"
  | I_LDS -> "LDS"
  | I_LEA -> "LEA"
  | I_LEAVE -> "LEAVE"
  | I_LES -> "LES"
  | I_LODS -> "LODS" ^ suffix_of_size inst.variant
  | I_LOOP -> "LOOP"
  | I_LOOPNZ -> "LOOPNZ"
  | I_LOOPZ -> "LOOPZ"
  | I_MOV -> "MOV"
  | I_MFS -> "MOV"
  | I_MOVS -> "MOVS" ^ suffix_of_size inst.variant
  | I_MOVSX -> "MOVSX"
  | I_MTS -> prefix_of_size inst.variant ^ "MOV"
  | I_MOVUPS -> "MOVUPS"
  | I_MOVZX -> "MOVZX"
  | I_MUL -> "MUL"
  | I_NEG -> "NEG"
  | I_NOT -> "NOT"
  | I_OR -> "OR"
  | I_OUT -> "OUT"
  | I_OUTS -> "OUTS" ^ suffix_of_size inst.variant
  | I_POP -> prefix_of_size inst.variant ^ "POP"
  | I_POPA -> prefix_of_size inst.variant ^ "POPA"
  | I_POPF -> "POPF"
  | I_PUSH -> prefix_of_size inst.variant ^ "PUSH"
  | I_PUSHA -> prefix_of_size inst.variant ^ "PUSHA"
  | I_PUSHF -> "PUSHF"
  | I_RCL -> "RCL"
  | I_RCR -> "RCR"
  | I_RDMSR -> "RDMSR"
  | I_RDPMC -> "RDPMC"
  | I_RDTSC -> "RDTSC"
  | I_RET -> "RET"
  | I_RETF-> "RET FAR"
  | I_RETN -> "RETN"
  | I_RETNF -> "RETN FAR"
  | I_ROL -> "ROL"
  | I_ROR -> "ROR"
  | I_SAHF -> "SAHF"
  | I_SAR -> "SAR"
  | I_SBB -> "SBB"
  | I_SCAS -> "SCAS" ^ suffix_of_size inst.variant
  | I_SET -> "SET"^cond_code.(inst.variant lsr 4)
  | I_SHL -> "SHL"
  | I_SHLD -> "SHLD"
  | I_SHR -> "SHR"
  | I_SHRD -> "SHRD"
  | I_STC -> "STC"
  | I_STD -> "STD"
  | I_STI -> "STI"
  | I_STOS -> "STOS" ^ suffix_of_size inst.variant
  | I_SUB -> "SUB"
  | I_TEST -> "TEST"
  | I_WAIT -> "WAIT"
  | I_XCHG -> "XCHG"
  | I_XLAT -> "XLAT"
  | I_XOR -> "XOR"

let pp f inst =
  pp_print_string f (mnemonic_of inst);
  match inst.operands with
  | [] -> ()
  | o_hd::o_tl ->
    pp_print_string f " ";
    pp_operand f o_hd;
    List.iter (fun o -> pp_print_string f ","; pp_operand f o) o_tl
