# Simple Makefile for pdrt-sandbox

FLAGS=--prefix=${HOME} --user

SRC=src/Data/*.hs src/Data/DRS/*.hs src/Data/DRS/Input/*.hs src/Data/FOL/*.hs src/Data/PDRS/*.hs

### build ###

all: configure build install

configure:
	runhaskell Setup.hs configure ${FLAGS}

build:
	runhaskell Setup.hs build

install:
	runhaskell Setup.hs install

clean:
	runhaskell Setup.hs clean

### distribution ###

sdist:
	runhaskell Setup.hs sdist

### haddock ###

haddock:
	runhaskell Setup.hs haddock --haddock-option --ignore-all-exports

### hlint ###

hlint:
	hlint ${SRC}

### count ###

count:
	wc -l ${SRC}
