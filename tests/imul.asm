[bits 32]
imul byte [eax]
imul word [eax]
imul dword [eax]
imul ax,word [eax]
imul eax,dword [eax]
imul ax,word [eax],byte 0x6d
imul eax,dword [eax],byte 0x6d
imul ax,word [eax],word 0x36d
imul eax,dword [eax],dword 0x36d
