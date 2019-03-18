all: Hello

%.vo: %.v
	coqc $^

%: %.vo
	fsc $^
