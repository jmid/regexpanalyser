future:
	ocamlbuild -use-ocamlfind src/future.byte

future.top:
	ocamlbuild -use-ocamlfind src/future.top

domcheck:
	ocamlbuild -use-ocamlfind -package qcheck src/redomcheck.byte

domcheck.top:
	ocamlbuild -use-ocamlfind -package qcheck src/redomcheck.top

clean:
	ocamlbuild -clean
	rm -f *~ src/*~
