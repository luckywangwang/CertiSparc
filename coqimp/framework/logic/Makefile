ROOT:=../../
RELATIVE:=framework/logic/

SRCFILES := $(shell find "." -type f -name "*.v")
FORAC := $(patsubst %.v, %.vo, $(SRCFILES))
FORAC2 := $(patsubst %.v, %.vio, $(SRCFILES))

all:
	$(MAKE) -C $(ROOT)

%.vo: phony_target
	$(MAKE) -C $(ROOT) $(RELATIVE)$@

%.vio: phony_target
	$(MAKE) -C $(ROOT) $(RELATIVE)$@

clean:
	find . -type f -name "*.vo" -delete
	find . -type f -name "*.glob" -delete
	find . -type f -name "*.d" -delete
	find . -type f -name "*.vio" -delete
	rm -f .deps

$(FORAC):

$(FORAC2):

.PHONY: phony_target

