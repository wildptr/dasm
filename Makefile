.PHONY: all FORCE

all: elab_test.native dasmgui.native

%.native: FORCE
	ocamlbuild -use-ocamlfind $*.native
