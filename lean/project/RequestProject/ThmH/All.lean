module

public import RequestProject.ThmH.Dictionary
public import RequestProject.ThmH.FreeTorsion
public import RequestProject.ThmH.TheoremH
public import RequestProject.ThmH.Numbers

/-!
# `CSH1_theorem_H_the_prime_two.md` — Theorem H of «The Coloured Sand Theorem» (the prime 2)

Folder `RequestProject/ThmH/`, namespace `ColouredSand.ThmH`.  Nothing of this project nor of the
23 Coloured Sand files (`RequestProject/Strings`, `Splitting`, `TheoremB`, `Corollaries`, created
verbatim from `CSH0_coloured_sand_sources.md`) is modified or redefined.

* `Dictionary.lean` — Part D: (D1) `beta`, `D1`; (D2) `Psi` (`f ↦ f ∘ (beta A m).symm`), `D2`;
  (D3) `D3`.  `A` is any commutative ring.
* `FreeTorsion.lean` — the splitting `coker (q(c+H)+U) ≅ R^{[c=0]} ⊕ torsion` over a domain of
  characteristic zero (`freeTorsionEquiv`), used in (T3).
* `TheoremH.lean` — Part T: (T1) `T1` (`T1equiv`), (T2) `T2`, (T3) `T3`, (T4) `T4`,
  (T5) `T5_exponent`, `T5`.
* `Numbers.lean` — Part N: (N1) `N1`; (N2) `N2_lists`, `N2_halves`.

Deviations from the file (all generalisations): (T2) omits the hypothesis `q ≥ 1`, which follows
from `1 ≤ v_2(q)`; (T4) and (T5) hold for every `d`, including `d = 0`.
-/
