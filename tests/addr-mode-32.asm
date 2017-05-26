[bits 32]
; m=0 r=0 [base]
db 0,0o000
; m=0 r=4 b=0 [base+index]
db 0,0o004,0o200
; m=0 r=4 b=4 [base+index]
db 0,0o004,0o204
; m=0 r=4 b=5 [index+disp32]
db 0,0o004,0o205
dd 0x400
db 0,0o004,0o205
dd 0
db 0,0o004,0o205
dd -0x400
; m=0 r=5 [disp32]
db 0,0o005
dd 0x400
db 0,0o005
dd 0
db 0,0o005
dd -0x400
; m=1 r=0 [base+disp8]
db 0,0o100
db 4
db 0,0o100
db -4
; m=1 r=4 b=0 [base+index+disp8]
db 0,0o104,0o200
db 4
db 0,0o104,0o200
db -4
; m=1 r=4 b=4 [base+index+disp8]
db 0,0o104,0o204
db 4
; m=1 r=4 b=5 [base+index+disp8]
db 0,0o104,0o205
db 4
; m=1 r=5 [base+disp8]
db 0,0o105
db 4
; m=2 r=0 [base+disp32]
db 0,0o200
dd 0x400
; m=3 r=0 (reg)
db 0,0o300

; r
db 0,0o300
db 0,0o301
db 0,0o302
db 0,0o303
db 0,0o304
db 0,0o305
db 0,0o306
db 0,0o307

; s
db 0,0o004,0o000
db 0,0o004,0o100
db 0,0o004,0o200
db 0,0o004,0o300

; i
db 0,0o104,0o004,4
db 0,0o104,0o014,4
db 0,0o104,0o024,4
db 0,0o104,0o034,4
db 0,0o104,0o044,4
db 0,0o104,0o054,4
db 0,0o104,0o064,4
db 0,0o104,0o074,4

; b
db 0,0o104,0o000,4
db 0,0o104,0o001,4
db 0,0o104,0o002,4
db 0,0o104,0o003,4
db 0,0o104,0o004,4
db 0,0o104,0o005,4
db 0,0o104,0o006,4
db 0,0o104,0o007,4
