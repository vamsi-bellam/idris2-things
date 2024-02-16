.PHONY: clean

clean: 
	echo "Removing build folder.."; rm -rf build

build: 
	idris2 --build Examples.ipkg