OCAMLBUILDFLAGS=-use-ocamlfind

# Please add new default build targets into sjsil.itarget, to improve build speed
default:
	ocamlbuild ${OCAMLBUILDFLAGS} sjsil.otarget

init: init_build
	.git-hooks/install.sh .

init_build: init_parser
	opam pin -y add JS_Parser "https://github.com/resource-reasoning/JS_Parser.git#c0749a53d80ca4890e13e2d9492ccac158a248db"
	#opam pin -y add JS_Parser ~/Projects/JS_Parser
	opam pin -yn add .
	opam install -y JaVerT2 --deps-only

init_parser:
	opam pin -y add JS_Parser-runtime "https://github.com/resource-reasoning/JS_Parser.git#c0749a53d80ca4890e13e2d9492ccac158a248db"
	#opam pin -y add JS_Parser-runtime ~/Projects/JS_Parser
	opam install -y JS_Parser-runtime

clean:
	ocamlbuild ${OCAMLBUILDFLAGS} -clean
