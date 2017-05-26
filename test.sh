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
	ndisasm_file="$tmpdir/$stem.ndisasm"
	nasm "$f" -o "$binfile"
	ndisasm -u "$binfile" > "$ndisasm_file"
	ocaml dasm.ml "$binfile" > "$disasm_file"
	nasm "$disasm_file" -o "$rt_binfile"
	cmp "$binfile" "$rt_binfile"
done
