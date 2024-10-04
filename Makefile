# TODO: integrate into build.zig
SOURCE_DIR=src
BUILD_DIR=build
MAIN_SOURCE=${SOURCE_DIR}/main.zig
SOURCES=${MAIN_SOURCE}
# TODO: zon dependency on compiler debug build possible?
# debug build required for --verbose-air support
ZIG_DEBUG=../zig/zig-out-debug/bin/zig
Z3_HEADER=/usr/include/z3.h
Z3_BINDINGS=${SOURCE_DIR}/z3.zig
AIR=${BUILD_DIR}/air
Z3_PY=${BUILD_DIR}/out.py

all: test

${BUILD_DIR}:
	mkdir -p ${BUILD_DIR}

${Z3_BINDINGS}: ${BUILD_DIR} ${Z3_HEADER}
	zig translate-c -lc /usr/include/z3.h > ${Z3_BINDINGS}

${AIR}: ${BUILD_DIR}
	${ZIG_DEBUG} build-exe --verbose-air ./zero_division.zig 2> ${AIR}

test: ${BUILD_DIR} ${AIR}
	${MAKE} check

check: ${BUILD_DIR} ${Z3_BINDINGS}
	zig build && \
	./zig-out/bin/zig-analyze 1> ${Z3_PY} && \
	echo "" && \
	chmod +x ${Z3_PY} && \
	python3 ${Z3_PY}
