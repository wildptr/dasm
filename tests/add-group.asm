[bits 32]
; 04 add al,i8
add al,4
; 6605 add ax,i16
add ax,0x400
; 05 add eax,i32
add eax,0x40000
; 80/0 add g8,i8
add byte [eax],4
; 6681/0 add g16,i16
add word [eax],0x400
; 81/0 add g32,i32
add dword [eax],0x40000
; 6683/0 add g16,i8
add word [eax],4
; 83/0 add g32,i8
add dword [eax],4
; 00 add g8,r8
add [eax],al
; 6601 add g16,r16
add [eax],ax
; 01 add g32,r32
add [eax],eax
; 02 add r8,g8
add al,[eax]
; 6603 add r16,g16
add ax,[eax]
; 03 add r32,g32
add eax,[eax]

or al,4
or ax,0x400
or eax,0x40000
or byte [eax],4
or word [eax],0x400
or dword [eax],0x40000
or word [eax],4
or dword [eax],4
or [eax],al
or [eax],ax
or [eax],eax
or al,[eax]
or ax,[eax]
or eax,[eax]

adc al,4
adc ax,0x400
adc eax,0x40000
adc byte [eax],4
adc word [eax],0x400
adc dword [eax],0x40000
adc word [eax],4
adc dword [eax],4
adc [eax],al
adc [eax],ax
adc [eax],eax
adc al,[eax]
adc ax,[eax]
adc eax,[eax]

sbb al,4
sbb ax,0x400
sbb eax,0x40000
sbb byte [eax],4
sbb word [eax],0x400
sbb dword [eax],0x40000
sbb word [eax],4
sbb dword [eax],4
sbb [eax],al
sbb [eax],ax
sbb [eax],eax
sbb al,[eax]
sbb ax,[eax]
sbb eax,[eax]

and al,4
and ax,0x400
and eax,0x40000
and byte [eax],4
and word [eax],0x400
and dword [eax],0x40000
and word [eax],4
and dword [eax],4
and [eax],al
and [eax],ax
and [eax],eax
and al,[eax]
and ax,[eax]
and eax,[eax]

sub al,4
sub ax,0x400
sub eax,0x40000
sub byte [eax],4
sub word [eax],0x400
sub dword [eax],0x40000
sub word [eax],4
sub dword [eax],4
sub [eax],al
sub [eax],ax
sub [eax],eax
sub al,[eax]
sub ax,[eax]
sub eax,[eax]

xor al,4
xor ax,0x400
xor eax,0x40000
xor byte [eax],4
xor word [eax],0x400
xor dword [eax],0x40000
xor word [eax],4
xor dword [eax],4
xor [eax],al
xor [eax],ax
xor [eax],eax
xor al,[eax]
xor ax,[eax]
xor eax,[eax]

cmp al,4
cmp ax,0x400
cmp eax,0x40000
cmp byte [eax],4
cmp word [eax],0x400
cmp dword [eax],0x40000
cmp word [eax],4
cmp dword [eax],4
cmp [eax],al
cmp [eax],ax
cmp [eax],eax
cmp al,[eax]
cmp ax,[eax]
cmp eax,[eax]
