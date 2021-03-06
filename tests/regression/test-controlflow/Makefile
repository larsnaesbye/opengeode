include ../shared.mk

all: test-ada test-llvm

edit:
	$(OPENGEODE) controlflow.pr system_structure.pr

test-parse:
	$(OPENGEODE) controlflow.pr system_structure.pr --check

test-ada: controlflow.ali dataview-uniq.o | test_ada.o
	$(GNATBIND) -n controlflow.ali
	$(GNATLINK) test_ada.o controlflow.ali -lgnat -lm -o test_ada
	./test_ada | diff expected -

test-c: controlflow.c test_c.o dataview-uniq.o
	$(CC) controlflow.c -c -o controlflow.o
	$(CC) test_c.o controlflow.c -lm -o test_c
	./test_c | diff expected -

test-llvm: controlflow.o dataview-uniq.o | test_llvm.o
	$(CC) controlflow.o dataview-uniq.o test_llvm.o -o test_llvm -lm
	./test_llvm | diff expected -

test-vhdl : test-c
	bambu controlflow.c test_c.c --experimental-setup=BAMBU --debug-classes=MuxConnectionBinding --print-dot --no-clean --pretty-print=a.c -d2

coverage:
	coverage run -p $(OPENGEODE) controlflow.pr system_structure.pr --toAda

.PHONY: all edit test-parse test-ada test-llvm coverage
