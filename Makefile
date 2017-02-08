.PHONY: test
test: dasm.ml
	bash test.sh tests/*.asm
