.PHONY: all FORCE

all: elab_test.native

%.native: FORCE
	ocamlbuild -use-ocamlfind $*.native
