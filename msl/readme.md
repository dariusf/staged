
Imported from https://github.com/PrincetonUniversity/VST. Examples imported from https://vst.cs.princeton.edu/msl.

Replaced VST.msl prefix with msl
Some files deleted as they depend on CompCert:

ramification_lemmas.v
rmaps.v
rmaps_lemmas.v
sepalg_list.v
Coqlib2.v

Some files don't build and were removed:

extract.v
knot_hered_sa.v (syntax errors, then missing defn)
knot_setoid.v
predicates_sl_simple.v

Imported zlist library in the same way
