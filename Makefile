.PHONY: dune clean install

dune:
	cd core;       dune build; dune install; cd ..
	cd exec;       dune build; dune install; cd ..
	cd stdlib;     dune build; dune install; cd ..
	cd experiment; dune build; dune install; cd ..

clean:
	git clean -fXd

uninstall:
	cd core;       dune uninstall; cd ..
	cd exec;       dune uninstall; cd ..
	cd stdlib;     dune uninstall; cd ..
	cd experiment; dune uninstall; cd ..
