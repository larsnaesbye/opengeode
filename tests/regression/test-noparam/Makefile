include ../shared.mk

all: test-ada test-llvm

edit:
	$(OPENGEODE) og.pr

test-parse:
	$(OPENGEODE) og.pr --check

test-ada: 
	$(OPENGEODE) og.pr --toAda
	$(GNATMAKE) -O$(O) -c *.adb
	$(GNATBIND) -n og.ali

test-c: 
	$(OPENGEODE) og.pr --toC
	$(CC) -O$(O) -c *.c


test-llvm:
	$(OPENGEODE) og.pr --llvm -O$(O)
	$(LLC) *.ll
	$(CC) -O$(O) -c *.s


coverage:
	coverage run -p $(OPENGEODE) og.pr --toAda

.PHONY: all edit test-parse test-ada test-llvm coverage
