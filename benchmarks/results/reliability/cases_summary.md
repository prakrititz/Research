| arm | trials | success | 95% interval | calls median (max) | mean calls (all) | wall median s | other outcomes | Coq-certified |
|---|---|---|---|---|---|---|---|---|
| cases_A1-skip | 20 | 20/20 = 100% | 84% - 100% | 2.0 (2) | 2.0 | 4 | - | 20/20 |
| cases_A2-assign | 20 | 20/20 = 100% | 84% - 100% | 2.0 (2) | 2.0 | 6 | - | 20/20 |
| cases_A3-assign-guarded | 20 | 20/20 = 100% | 84% - 100% | 2.0 (2) | 2.0 | 6 | - | 20/20 |
| cases_A4-impossible | 5 | 0/5 = 0% | 0% - 43% | None (None) | 16.0 | - | EXHAUSTED 5 | - |
| cases_B1-sequential | 20 | 20/20 = 100% | 84% - 100% | 2.0 (2) | 2.0 | 6 | - | 20/20 |
| cases_B2-max | 20 | 20/20 = 100% | 84% - 100% | 2.0 (4) | 2.1 | 7 | - | 20/20 |
| cases_B3-abs | 20 | 20/20 = 100% | 84% - 100% | 4.0 (4) | 4.0 | 15 | - | 20/20 |
| cases_C1-sqrt-loose | 20 | 20/20 = 100% | 84% - 100% | 2.0 (3) | 2.1 | 7 | - | 20/20 |
| cases_C2-sqrt-tight | 20 | 20/20 = 100% | 84% - 100% | 2.0 (8) | 2.4 | 10 | - | 20/20 |
| cases_C3-loop-pinned | 20 | 20/20 = 100% | 84% - 100% | 2.0 (6) | 2.4 | 11 | - | 20/20 |
| cases_C4-loop-invariant | 20 | 20/20 = 100% | 84% - 100% | 2.0 (2) | 2.0 | 7 | - | 20/20 |
| cases_D1-intdiv | 20 | 1/20 = 5% | 1% - 24% | 26 (26) | 29.8 | 183 | BUDGET 19 | 1/1 |
