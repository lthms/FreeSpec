docs:
	@make -f Makefile.coq html
	@make -f Makefile.coq mlihtml
	@mkdir -p docs/
	@rm -rf docs/coq docs/ml
	@mv html docs/coq
	@mv mlihtml docs/ml

install: clean
	@cd core;   dune build @install; dune install; cd -
	@cd exec;   dune build @install; dune install; cd -
	@cd stdlib; dune build @install; dune install; cd -

mrproper: clean
	@cd core;   dune clean; cd -
	@cd exec;   dune clean; cd -
	@cd stdlib; dune clean; cd -

uninstall:
	@cd core;   dune uninstall; cd -
	@cd exec;   dune uninstall; cd -
	@cd stdlib; dune uninstall; cd -

clean:
	@make -f Makefile.coq clean
	@rm -rf docs/coq docs/ml

.PHONY: install docs clean mrproper uninstall
