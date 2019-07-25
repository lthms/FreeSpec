all: core exec stdlib

install: all install-stdlib

html: html-core html-exec html-stdlib
	mkdir -p html
	cp -r core/html html/core
	cp -r exec/html html/exec
	cp -r exec/mlihtml html/exec-ml
	cp -r stdlib/console/html html/console
	cp -r stdlib/console/mlihtml html/console-ml
	cp -r stdlib/env/html html/env
	cp -r stdlib/env/mlihtml html/env-ml

core:
	make -C core

exec: install-core
	make -C exec

stdlib: stdlib-console stdlib-env

stdlib-env: install-exec
	make -C stdlib/env

stdlib-console: install-exec
	make -C stdlib/console

install-core: core
	make -C core uninstall || true
	make -C core install

install-exec:
	make -C exec uninstall || true
	make -C exec install

install-stdlib: install-stdlib-console install-stdlib-env

install-stdlib-console: stdlib-console
	make -C stdlib/console uninstall || true
	make -C stdlib/console install

install-stdlib-env: stdlib-env
	make -C stdlib/env uninstall || true
	make -C stdlib/env install

html-core: core
	make -C core html

html-exec: install-core
	make -C exec html
	make -C exec mlihtml

html-stdlib-console: install-exec
	make -C stdlib/console html
	make -C stdlib/console mlihtml

html-stdlib-env: install-exec
	make -C stdlib/env html
	make -C stdlib/env mlihtml

html-stdlib: html-stdlib-console html-stdlib-env

clean:
	make -C core clean
	make -C exec clean
	make -C stdlib/console clean
	make -C stdlib/env clean

.PHONY: all core exec stdlib-console stdlib
.PHONY: install install-core install-exec install-stdlib-env install-stdlib-console install-stdlib
.PHONY: html html-core html-exec html-stdlib-console html-stdlib-env html-stdlib
.PHONY: clean
