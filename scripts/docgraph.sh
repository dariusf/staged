#!/bin/sh

set -ex

scripts/linked_depgraph.py | tred > deps.dot
dot -o deps.svg -Tsvg deps.dot

set +x

GRAPH="$(cat deps.svg)" envsubst < "docs/shiftreset.preindex.html" > "docs/shiftreset.index.html"