all: PrintArgs

%.vo: %.v
	coqc $^

%: %.vo
	fsc $^
