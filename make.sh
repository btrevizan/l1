mkdir bin
ocaml -c src/definitions.ml
ocaml -c src/bigstep.ml
ocaml -c src/inferator.ml
ocaml -o l1 definitions.o bigstep.o inferator.o
rm *.o
