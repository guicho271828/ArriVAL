
ARRIVAL  := ../roswell/arrival.ros
solutions = $(wildcard axioms/*.plan)
valid     = $(patsubst %.plan, %.valid, $(solutions))

$(info $(solutions))
$(info $(valid))

all: $(valid)

$(valid) : %.valid : %.plan
	LANG=en_US.utf8 $(ARRIVAL) -vvv $*-domain.pddl $*.pddl $< $*.trace > $*.out 2> $*.err && touch $@

clean:
	-rm -v */*.trace */*.out */*.err */*.valid
