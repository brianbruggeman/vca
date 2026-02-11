COQC = coqc
COQDEP = coqdep

SOURCES = Core.v Admissibility.v Transitions.v Towers.v CoreStar.v Commutativity.v Temporal.v Replay.v Lambda.v Model.v

all: $(SOURCES:.v=.vo)

%.vo: %.v
	$(COQC) -Q . VCA $<

depend: .depend

.depend: $(SOURCES)
	$(COQDEP) -Q . VCA $(SOURCES) > .depend

clean:
	rm -f *.vo *.vok *.vos *.glob .*.aux .depend

-include .depend

.PHONY: all clean depend
