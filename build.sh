#!/bin/sh

agda -i . -i ~/languages/agda/libs/agda-stdlib/src/ -i ~/projects/potpourri/agda/ $1 -c --compile-dir=__build
