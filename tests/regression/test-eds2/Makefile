include ../shared.mk

all: test-ada test-llvm

edit:
	$(OPENGEODE) demodevicedsap.pr

test-parse:
	$(OPENGEODE) demodevicedsap.pr --check

test-ada: 
	$(OPENGEODE) demodevicedsap.pr --toAda
	$(ASN1SCC) -Ada *.asn -typePrefix asn1Scc -equal
	$(GNATMAKE) -O$(O) -c *.adb
	$(GNATBIND) -n demodevicedsap.ali

test-c: 
	$(OPENGEODE) demodevicedsap.pr --toC
	$(ASN1SCC) -c *.asn -typePrefix asn1Scc -equal
	$(CC) -O$(O) -c *.c


test-llvm:
	$(OPENGEODE) demodevicedsap.pr --llvm -O$(O)
	$(LLC) *.ll
	$(CC) -O$(O) -c *.s


coverage:
	coverage run -p $(OPENGEODE) demodevicedsap.pr --toAda

.PHONY: all edit test-parse test-ada test-llvm coverage
