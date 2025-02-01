
A formalization of Expressive Type-Safety via Hoare Logic.

# Build

The project was developed on Coq 8.20.1. To compile it, which checks all proofs,

```sh
make
```

There will be warnings from upstream libraries, but no errors at the end if all proofs are checked successfully.

The documentation may be built with [coq2html](https://github.com/xavierleroy/coq2html) installed and:

```sh
make docs
```

# Project structure

The whole development is contained in types/Logic.v.

The slf directory contains version 2.2 of Separation Logic Foundations.

The lib directory contains miscellaneous library code.

# Correspondence with the paper

The following table records how the key definitions and lemmas correspond.

| Paper                   | types/Logic.v                              |
| ----------------------- | ------------------------------------------ |
| Fig. 8                  | type                                       |
| t_1 $\to$  t_2          | tarrow                                     |
| t_1 $\to'$  t_2         | tarrow_                                    |
| e $\leadsto$  v         | bigstep_pure                               |
| Lemma 1                 | tarrow_triple, tarrow_triple_conv          |
| Theorem 1               | Proved implicitly via compatibility lemmas |
| Compatibility lemmas    | Lemmas prefixed with type_triple_          |
| Fig. 7, rules Val, Var2 | type_triple_val                            |
| Fig. 7, rule Constancy  | type_triple_constancy                      |
| Fig. 7, rule Conseq     | type_triple_conseq                         |
| Fig. 7, rule Var1       | type_triple_var1                           |
| Fig. 7, rule Call       | type_triple_call                           |
| Fig. 7, rule Let        | type_triple_plet                           |
| Fig. 7, rule Cast       | type_triple_cast                           |
| Fig. 7, rule Match      | type_triple_match                          |
| Fig. 7, rule Constr     | type_triple_constr                         |
| Fig. 7, rule Lambda     | type_triple_lambda                         |

Sections of the file corresponding to the case study named `$NAME` are delimited by `(* BEGIN $NAME *)` and `(* END $NAME *)` markers.

The results of Table 1 may be reproduced by running the following script, which outputs the sizes of the various case studies.
It relies on the tools `awk`, `cloc`, and `grep` being available on the PATH.

```sh
./case_studies.sh
```