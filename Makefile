all: core experiment exec stdlib

install: all install-stdlib install-experiment

html: html-core html-experiment html-exec html-stdlib
	mkdir -p html
	cp -r core/html html/core
	cp -r exec/html html/exec
	cp -r exec/mlihtml html/exec-ml
	cp -r stdlib/console/html html/console
	cp -r stdlib/console/mlihtml html/console-ml

core:
	make -C core

experiment: install-core
	make -C experiment

exec: install-core
	make -C exec

stdlib-console: install-exec
	make -C stdlib/console

stdlib: stdlib-console

install-core: core
	make -C core uninstall || true
	make -C core install

install-experiment: experiment
	make -C experiment uninstall || true
	make -C experiment install

install-exec:
	make -C exec uninstall || true
	make -C exec install

install-stdlib-console: stdlib-console
	make -C stdlib/console uninstall || true
	make -C stdlib/console install

html-core: core
	make -C core html

html-experiment: install-core
	make -C experiment html

html-exec: install-core
	make -C exec html
	make -C exec mlihtml

html-stdlib-console: install-exec
	make -C stdlib/console html
	make -C stdlib/console mlihtml

html-stdlib: html-stdlib-console

clean:
	make -C core clean
	make -C exec clean
	make -C stdlib/console clean
	make -C experiment clean

.PHONY: all core experiment exec stdlib-console stdlib
.PHONY: install install-core install-experiment install-exec install-stdlib-console install-stdlib
.PHONY: html html-core html-experiment html-exec html-stdlib-console html-stdlib
.PHONY: clean
