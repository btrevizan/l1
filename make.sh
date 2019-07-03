mkdir bin
mkdir obj
ocamlopt -o bin/main main.ml
mv *.cmi obj/
mv *.cmx obj/

