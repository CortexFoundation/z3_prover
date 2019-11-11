
all: z3_prover

z3_prover: 3rdparty/z3/build/libz3.so
	mkdir -p build; cd build; cmake ..
	+make -C build

3rdparty/z3/build/libz3.so:
	cd 3rdparty/z3; ./configure
	+make -C 3rdparty/z3/build
	rm 3rdparty/z3/src/util/z3_version.h

clean:
	cd 3rdparty/z3; rm -rf build

run:
	@cd build && ./z3_prover
