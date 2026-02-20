#/bin/bash

set -x
PREBUILD=$(mktemp -d)
mkdir $PREBUILD/rocq
BUILD=$PREBUILD/rocq

# git clone https://github.com/dariusf/IxFree.git
cp -r IxFree ctx-equiv-ixfree Binding shiftreset staged slf $BUILD

# edit files
cat _CoqProject | grep -v iris | grep -v future | grep -v types > $BUILD/_CoqProject
printf 'Makefile.coq:\n\trocq makefile -f _CoqProject -o Makefile.coq\n-include Makefile.coq' > $BUILD/Makefile
echo 'Rocq 9.0.1 is required. To compile the development and its dependencies,

```sh
(cd IxFree; make && make install)
make
```

This should take 2-3 minutes.

The simple formalisation is in the shiftreset directory, while the one based on contextual equivalence is in ctx-equiv-ixfree.' > $BUILD/readme.md

cd $PREBUILD
zip -r rocq.zip rocq

cd -
cp $PREBUILD/rocq.zip .
