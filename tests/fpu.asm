[bits 32]
; d8
fadd dword [eax]
fmul dword [eax]
fcom dword [eax]
fcomp dword [eax]
fsub dword [eax]
fsubr dword [eax]
fdiv dword [eax]
fdivr dword [eax]
fadd st0
fadd st1
fadd st2
fadd st3
fadd st4
fadd st5
fadd st6
fadd st7
fmul st0
fmul st1
fmul st2
fmul st3
fmul st4
fmul st5
fmul st6
fmul st7
fcom st0
fcom st1
fcom st2
fcom st3
fcom st4
fcom st5
fcom st6
fcom st7
fcomp st0
fcomp st1
fcomp st2
fcomp st3
fcomp st4
fcomp st5
fcomp st6
fcomp st7
fsub st0
fsub st1
fsub st2
fsub st3
fsub st4
fsub st5
fsub st6
fsub st7
fsubr st0
fsubr st1
fsubr st2
fsubr st3
fsubr st4
fsubr st5
fsubr st6
fsubr st7
fdiv st0
fdiv st1
fdiv st2
fdiv st3
fdiv st4
fdiv st5
fdiv st6
fdiv st7
fdivr st0
fdivr st1
fdivr st2
fdivr st3
fdivr st4
fdivr st5
fdivr st6
fdivr st7
; d9
fld dword [eax]
fst dword [eax]
fstp dword [eax]
fldenv [eax]
fldcw [eax]
fnstenv [eax]
fnstcw [eax]
fld st0
fld st1
fld st2
fld st3
fld st4
fld st5
fld st6
fld st7
fxch st0
fxch st1
fxch st2
fxch st3
fxch st4
fxch st5
fxch st6
fxch st7
fnop
fchs
fabs
ftst
fxam
fld1
fldl2t
fldl2e
fldpi
fldlg2
fldln2
fldz
f2xm1
fyl2x
fptan
fpatan
fxtract
fprem1
fdecstp
fincstp
fprem
fyl2xp1
fsqrt
fsincos
frndint
fscale
fsin
fcos
; da
fiadd dword [eax]
fimul dword [eax]
ficom dword [eax]
ficomp dword [eax]
fisub dword [eax]
fisubr dword [eax]
fidiv dword [eax]
fidivr dword [eax]
fcmovb st0
fcmovb st1
fcmovb st2
fcmovb st3
fcmovb st4
fcmovb st5
fcmovb st6
fcmovb st7
fcmove st0
fcmove st1
fcmove st2
fcmove st3
fcmove st4
fcmove st5
fcmove st6
fcmove st7
fcmovbe st0
fcmovbe st1
fcmovbe st2
fcmovbe st3
fcmovbe st4
fcmovbe st5
fcmovbe st6
fcmovbe st7
fcmovu st0
fcmovu st1
fcmovu st2
fcmovu st3
fcmovu st4
fcmovu st5
fcmovu st6
fcmovu st7
fucompp
; db
fild dword [eax]
fisttp dword [eax]
fist dword [eax]
fld tword [eax]
fstp tword [eax]
fcmovnb st0
fcmovnb st1
fcmovnb st2
fcmovnb st3
fcmovnb st4
fcmovnb st5
fcmovnb st6
fcmovnb st7
fcmovne st0
fcmovne st1
fcmovne st2
fcmovne st3
fcmovne st4
fcmovne st5
fcmovne st6
fcmovne st7
fcmovnbe st0
fcmovnbe st1
fcmovnbe st2
fcmovnbe st3
fcmovnbe st4
fcmovnbe st5
fcmovnbe st6
fcmovnbe st7
fcmovnu st0
fcmovnu st1
fcmovnu st2
fcmovnu st3
fcmovnu st4
fcmovnu st5
fcmovnu st6
fcmovnu st7
fnclex
fninit
fucomi st0
fucomi st1
fucomi st2
fucomi st3
fucomi st4
fucomi st5
fucomi st6
fucomi st7
fcomi st0
fcomi st1
fcomi st2
fcomi st3
fcomi st4
fcomi st5
fcomi st6
fcomi st7
; dc
fadd qword [eax]
fmul qword [eax]
fcom qword [eax]
fcomp qword [eax]
fsub qword [eax]
fsubr qword [eax]
fdiv qword [eax]
fdivr qword [eax]
fadd to st0
fadd to st1
fadd to st2
fadd to st3
fadd to st4
fadd to st5
fadd to st6
fadd to st7
fmul to st0
fmul to st1
fmul to st2
fmul to st3
fmul to st4
fmul to st5
fmul to st6
fmul to st7
fsubr to st0
fsubr to st1
fsubr to st2
fsubr to st3
fsubr to st4
fsubr to st5
fsubr to st6
fsubr to st7
fsub to st0
fsub to st1
fsub to st2
fsub to st3
fsub to st4
fsub to st5
fsub to st6
fsub to st7
fdivr to st0
fdivr to st1
fdivr to st2
fdivr to st3
fdivr to st4
fdivr to st5
fdivr to st6
fdivr to st7
fdiv to st0
fdiv to st1
fdiv to st2
fdiv to st3
fdiv to st4
fdiv to st5
fdiv to st6
fdiv to st7
; dd
fld qword [eax]
fisttp qword [eax]
fst qword [eax]
fstp qword [eax]
frstor [eax]
fnsave [eax]
fnstsw [eax]
ffree st0
ffree st1
ffree st2
ffree st3
ffree st4
ffree st5
ffree st6
ffree st7
fst st0
fst st1
fst st2
fst st3
fst st4
fst st5
fst st6
fst st7
fstp st0
fstp st1
fstp st2
fstp st3
fstp st4
fstp st5
fstp st6
fstp st7
fucom st0
fucom st1
fucom st2
fucom st3
fucom st4
fucom st5
fucom st6
fucom st7
fucomp st0
fucomp st1
fucomp st2
fucomp st3
fucomp st4
fucomp st5
fucomp st6
fucomp st7
; de
fiadd word [eax]
fimul word [eax]
ficom word [eax]
ficomp word [eax]
fisub word [eax]
fisubr word [eax]
fidiv word [eax]
fidivr word [eax]
faddp st0
faddp st1
faddp st2
faddp st3
faddp st4
faddp st5
faddp st6
faddp st7
fmulp st0
fmulp st1
fmulp st2
fmulp st3
fmulp st4
fmulp st5
fmulp st6
fmulp st7
fcompp
fsubrp st0
fsubrp st1
fsubrp st2
fsubrp st3
fsubrp st4
fsubrp st5
fsubrp st6
fsubrp st7
fsubp st0
fsubp st1
fsubp st2
fsubp st3
fsubp st4
fsubp st5
fsubp st6
fsubp st7
fdivrp st0
fdivrp st1
fdivrp st2
fdivrp st3
fdivrp st4
fdivrp st5
fdivrp st6
fdivrp st7
fdivp st0
fdivp st1
fdivp st2
fdivp st3
fdivp st4
fdivp st5
fdivp st6
fdivp st7
; df
fild word [eax]
fisttp word [eax]
fist word [eax]
fistp word [eax]
fbld [eax]
fild qword [eax]
fbstp [eax]
fistp qword [eax]
fnstsw ax
fucomip st0
fucomip st1
fucomip st2
fucomip st3
fucomip st4
fucomip st5
fucomip st6
fucomip st7
fcomip st0
fcomip st1
fcomip st2
fcomip st3
fcomip st4
fcomip st5
fcomip st6
fcomip st7
