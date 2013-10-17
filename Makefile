# Simple Makefile for pdrt-sandbox

FLAGS=--prefix=${HOME} --user

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
	hlint src/Data/*.hs
	hlint src/Data/DRS/*.hs
	hlint src/Data/FOL/*.hs
	hlint src/Data/PDRS/*.hs
