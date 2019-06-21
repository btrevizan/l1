mkdir bin
mkdir obj
ocamlopt -o bin/tests main.ml
mv *.cmi obj/
mv *.cmx obj/

