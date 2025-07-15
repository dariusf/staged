#!/bin/sh

# Modified from https://discourse.rocq-prover.org/t/tool-for-drawing-coq-project-dependency-graph/653/16

project=msl

( echo "digraph $project_deps {" ;
  # echo "node [shape=ellipse, style=filled, URL=\"html/$PROJECT.\N.html\", color=black];";
  echo "rankdir=BT";
  ( coqdep -f _CoqProject ) |
    sed -n -e 's,/,.,g;s/[.]vo.*: [^ ]*[.]v//p' | grep $project |
    while read src dst; do
      # color=$(echo "$src" | sed -e 's,Real.*,turquoise,;s,$PROJECT[.].*,plum,;s,Integral.*,lightcoral,;s,Poly.*,yellow,;s,Float.*,cornflowerblue,;s,Eval.*,green,;s,[A-Z].*,white,')
      # echo "\"$src\" [fillcolor=$color];"
      for d in $dst; do
        echo "\"$src\" -> \"${d%.vo}\" ;"
      done
    done;
  echo "}" ) | tred > deps.dot
dot -T png deps.dot > deps.png
open deps.png || true