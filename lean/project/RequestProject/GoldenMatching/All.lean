module

public import RequestProject.GoldenMatching.Binary
public import RequestProject.GoldenMatching.Dancers
public import RequestProject.GoldenMatching.Complement
public import RequestProject.GoldenMatching.NaturalMinor

/-!
# `C4_golden_matching.md`: the unique golden matching and the natural minor

Index of the formalization (namespace `GoldenMatching`):

* **Part A, Theorem A** (Theorem O in binary form): `GoldenMatching.theorem_A`, with the golden
  images `GoldenMatching.IsGoldenImage` (`Binary.lean`).
* **Part B, Theorem B** (Theorem O for dancers): `GoldenMatching.theorem_B`, with
  `GoldenMatching.rank`, `GoldenMatching.Lr`, `GoldenMatching.Fr` and
  `GoldenMatching.IsGoldenArrow` (`Dancers.lean`).
* **Part C, Lemma C1** (the complement): `GoldenMatching.lemma_C1_oE` (and
  `lemma_C1_oE_add`), `GoldenMatching.lemma_C1_lt`, `GoldenMatching.lemma_C1_rank`,
  `GoldenMatching.lemma_C1_bijOn` (`Complement.lean`).
* **Part C, Lemma C2** (cost of a bijection): `GoldenMatching.lemma_C2`, with
  `GoldenMatching.cHat` (`ĉ`), `GoldenMatching.xVal` (`x_D`) and `GoldenMatching.U` (`U(r)`)
  (`Complement.lean`).
* **Part D, Corollary D** (Corollary 6.3): `GoldenMatching.corollary_D` (`NaturalMinor.lean`).

Golden images, ranks, `L_r`, `F_r`, the normalized cost and `U(r)` are encoded as described in
the module docstrings of the files above.  The definitions `o_D`, `γ`, `h` and the rulers are
those of piece C3 (`Rulers.oE`, `Rulers.gamma`, `Rulers.h`, `Rulers.ruler`; `Rulers.kappa` and
`Rulers.h` enter through `Rulers.ruler` and `Rulers.gamma`), and the proof of Corollary D uses
`SmithBounds.corollary_B'` of piece C2.
-/
