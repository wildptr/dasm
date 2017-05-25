if [ -d ~/tmp ]; then
	tmpdir=~/tmp
else
	tmpdir="/tmp/$USER"
fi
set -e
mkdir -p "$tmpdir"
for f; do
	stem=`basename "$f" .asm`
	binfile="$tmpdir/$stem.bin"
	rt_binfile="$tmpdir/$stem.rt.bin"
	disasm_file="$tmpdir/$stem.disasm"
	nasm "$f" -o "$binfile"
	ocaml dasm.ml "$binfile" > "$disasm_file"
	nasm "$disasm_file" -o "$rt_binfile"
	cmp "$binfile" "$rt_binfile"
done
