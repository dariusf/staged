
A formalization of Specifying and Verifying Future Conditions.

# Build

The project was developed on Coq 8.20.1. To compile it, which checks all proofs,

```sh
make
```

There will be warnings from upstream libraries, but no errors at the end if all proofs are checked successfully.

# Project structure

The whole development is contained in future/Logic.v.

The slf directory contains version 2.2 of Separation Logic Foundations.

The lib directory contains miscellaneous library code.

# Correspondence with the paper

The following table records how the key definitions and lemmas correspond.

| Paper                                                                    | future/Logic.v                           |
| ------------------------------------------------------------------------ | ---------------------------------------- |
| $\rho \vDash_{t} \theta$ (Fig. 8)                                        | trace_model                              |
| $\rho \vDash_{f} F$ (Fig. 8)                                             | fc_model                                 |
| $\theta_1 \leq \theta_2$ (Sec. 4.1)                                      | inclusion                                |
| $F_1 \sqsubseteq F_2$ (Sec. 4.2)                                         | futureCondEntail                         |
| $F_1 \circleddash \theta \hookrightarrow F_2$ (Sec. 4.3)                 | futureSubtraction                        |
| $F_1 \circleddash_{\mathit{lin}} \theta \hookrightarrow F_2$  (Sec. 4.4) | futureSubtraction_linear                 |
| Theorem 1                                                                | inclusion_sound                          |
| Theorem 2                                                                | futureCond_sound                         |
| Theorem 3                                                                | futureSubtraction_sound                  |
| Theorem 4                                                                | soundness                                |
| Lemma 1                                                                  | strenthen_futureCond_big_step            |  |
| Lemma 2                                                                  | futureSubtraction_strengthing_linear_res |
| Definition 1 (Nullable)                                                  | nullable                                 |
| Definition 2 (First)                                                     | fst                                      |
| Definition 3 (Partial Derivative)                                        | theta_der, fc_der                        |

