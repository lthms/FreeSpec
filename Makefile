NAME    = $(shell basename `pwd`)
PROJECT = _CoqProject
FLIST   = Files
SRC     = $(shell cat $(FLIST))
SUBMAKE = Makefile.proj

.PHONY:all clean mrproper docs html tex

all: $(SUBMAKE) $(SRC)
	@(echo "[*] Compiling the project")
	@(make -f $(SUBMAKE))

$(SUBMAKE): .make
	@(echo "[*] Generating $(SUBMAKE)")
	@(coq_makefile -f .make -o $@)

.make: $(FLIST) $(PROJECT)
	@(rm -f $@)
	@(cat $(PROJECT) >> .make)
	@(cat $(FLIST) >> .make)

clean: $(SUBMAKE)
	make -f $(SUBMAKE) clean

mrproper: clean
	rm .make
	rm -rf docs/html
	rm -f docs/$(NAME).pdf
	rm -f $(SUBMAKE)

docs: html tex

html:
	rm -rf docs/html
	make -f $(SUBMAKE) gallinahtml
	mv html docs/
	cp docs/assets/coqdoc.css docs/html

tex:
	make -f $(SUBMAKE) all-gal.pdf
	mv all-gal.pdf docs/$(NAME).pdf
