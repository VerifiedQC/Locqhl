COQPROJECT := _CoqProject
COQMAKEFILE := Makefile.coq

.PHONY: all clean mrproper

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) all

$(COQMAKEFILE): $(COQPROJECT)
	rocq makefile -f $(COQPROJECT) -o $(COQMAKEFILE)

clean:
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi

mrproper: clean
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf .Makefile.coq.d
