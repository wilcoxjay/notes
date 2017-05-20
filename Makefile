VFILES:=$(wildcard *.v)

all: $(VFILES) Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq:
	coq_makefile $(VFILES) > Makefile.coq
