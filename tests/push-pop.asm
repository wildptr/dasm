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
push word 0x400
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
; 660e
o16 push cs
; 6616
o16 push ss
; 661e
o16 push ds
; 6606
o16 push es
; 660fa0
o16 push fs
; 660fa8
o16 push gs

; 668f/0 pop g16
pop word [eax]
; 8f/0 pop g32
pop dword [eax]

pop ax
pop cx
pop dx
pop bx
pop sp
pop bp
pop si
pop di

pop eax
pop ecx
pop edx
pop ebx
pop esp
pop ebp
pop esi
pop edi

pop ss
pop ds
pop es
pop fs
pop gs

o16 pop ss
o16 pop ds
o16 pop es
o16 pop fs
o16 pop gs
