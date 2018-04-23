#!/bin/sh

agda -i . \
     -i $AGDA_STDLIB \
     -c --compile-dir=__build \
     "$1"
