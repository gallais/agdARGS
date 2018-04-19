#!/bin/sh

echo "module agdARGS.All where" > All.agda
git ls-tree --full-tree -r --name-only HEAD | grep "\.agda$" | sed "s/\.agda$//" | sed "s|^|open import |" | sed "s|/|.|g" | sort >> All.agda
