# Definicje stałych
SRC_DIR 	= src
BUILD_DIR	= build
LIB_DIR		= lib


GHC			= ghc
GHCFLAGS	= -O -fsimplifier-phases=10 -fregs-graph -fstatic-argument-transformation
BNFC		= ${LIB_DIR}/bnfc


.PHONY: grammar clean

all: latc_x86_64

grammar: ${SRC_DIR}/grammar.cf
	@echo "\n-- Tworzenie gramatyki --\n"
	make BNFC=${BNFC} --directory  ${SRC_DIR}

internals: ${LIB_DIR}/libinternals.c
	@echo "\n-- Kompilowanie zintegrowanej biblioteki kompilatora --\n"
	cd ${LIB_DIR} && gcc -g -Wall -c libinternals.c 

latc_x86_64: grammar internals
	@echo "\n-- Tworzenie pliku wykonywalnego kompilatora --\n"
	cd ${SRC_DIR} && ${GHC} ${GHCFLAGS} -cpp -D__LIB_PATH__=\"$(realpath ${LIB_DIR})\" Main.hs -o ../$@

clean:
	rm -rf ${SRC_DIR}/*.hi ${SRC_DIR}/*.o 
	rm -rf ${LIB_DIR}/*.o
	rm -rf ${SRC_DIR}/Grammar
	rm latc_x86_64

