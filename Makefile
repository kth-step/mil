default: hol

hol:
	Holmake -r -I executable

examples:
	Holmake -r -I examples

cakeml:
	Holmake -r -I cakeml

bir:
	Holmake -r -I bir

clean:
	cd misc && Holmake clean
	cd semantics && Holmake clean
	cd executable && Holmake clean
	cd examples && Holmake clean
	cd bir && Holmake clean
	cd cakeml && Holmake clean

.PHONY: default clean hol examples cakeml bir
