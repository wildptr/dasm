[bits 32]
; 66ff/6 push g16
push word [eax]
; ff/6 push g32
push dword [eax]
; 6650+r push r16
push ax
push cx
push dx
push bx
push sp
push bp
push si
push di
; 50+r push r32
push eax
push ecx
push edx
push ebx
push esp
push ebp
push esi
push edi
; 6a push i8
push 4
; 6668 push i16
push 0x400
; 68 push i32
push 0x40000
; 0e push cs
push cs
; 16 push ss
push ss
; 1e push ds
push ds
; 06 push es
push es
; 0fa0 push fs
push fs
; 0fa8 push gs
push gs

; 668f/0 pop g16
pop word [eax]
; 8f/0 pop g32
pop dword [eax]
