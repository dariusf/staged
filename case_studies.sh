#!/bin/bash


echo '--- LINE COUNTS ---'
cloc types/Logic.v

echo '--- CASE STUDIES ---'

set -x
echo $(( $(awk '/BEGIN ID/,/END ID/' types/Logic.v | wc -l) - 2))
echo $(( $(awk '/BEGIN TAIL/,/END TAIL/' types/Logic.v | wc -l) -2))
echo $(( $(awk '/BEGIN APPLY/,/END APPLY/' types/Logic.v | wc -l) -2))
echo $(( $(awk '/BEGIN LENGTH/,/END LENGTH/' types/Logic.v | wc -l) -2))
set +x

echo '--- LEMMAS ---'

grep Lemma types/Logic.v | wc -l