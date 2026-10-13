# Derivation of he_148_bf

kind: **restate**

- **cases** on `planet1 ∈ solarPlanets ∧ planet2 ∈ solarPlanets`
  - helper lemma `planet_witness`: `∀ (p1 p2 : String), p1 ∈ solarPlanets → p2 ∈ solarPlanets → ∃ i, i < 8 ∧ solarPlanets[i]! = p1 ∧ ∃ j, j < 8 ∧ solarPlanets[j]! = p2 ∧ (solarPlanets.drop (min (solarPlanets.idxOf p1) (solarPlanets.idxOf p2) + 1)).take (max (solarPlanets.idxOf p1) (solarPlanets.idxOf p2) - min (solarPlanets.idxOf p1) (solarPlanets.idxOf p2) - 1) = (solarPlanets.drop (min i j + 1)).take (max i j - min i j - 1)`
  - _then_:
    - **term**: `(solarPlanets.drop (min (solarPlanets.idxOf planet1) (solarPlanets.idxOf planet2) + 1)).take (max (solarPlanets.idxOf planet1) (solarPlanets.idxOf planet2) - min (solarPlanets.idxOf planet1) (solarPlanets.idxOf planet2) - 1)`
  - _else_:
    - **term**: `[]`
