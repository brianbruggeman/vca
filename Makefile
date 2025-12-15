.PHONY: all clean reference-implementation proof

all: clean proof reference-implementation

clean:
	cargo clean
	cd coq && $(MAKE) clean

reference-implementation:
	cargo build

proof:
	cd coq && $(MAKE)

