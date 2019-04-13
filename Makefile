.PHONY: all FORCE

all: elab_test.native dasmgui.native
#all: z3_intf.cma

%.native: FORCE
	ocamlbuild -use-ocamlfind $*.native

%.cma: FORCE
	ocamlbuild -use-ocamlfind $*.cma
