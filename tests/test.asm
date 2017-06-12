[bits 32]
test al,0x6d
test ax,0x36d
test eax,0x36d
test byte [eax],0x6d
test word [eax],0x36d
test dword [eax],0x36d
test byte [eax],cl
test word [eax],cx
test dword [eax],ecx
