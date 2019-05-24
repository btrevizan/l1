mkdir bin
mkdir obj
ocamlopt src/definitions.ml src/inferator.ml src/bigstep.ml -o bin/l1
mv src/*.cmi obj/
mv src/*.cmx obj/

