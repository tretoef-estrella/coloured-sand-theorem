module

public import RequestProject.CellFloor.Basic
public import RequestProject.CellFloor.Integrality
public import RequestProject.CellFloor.Floor

/-!
# Integrality and the floor of every cell (`C9_integrality_and_cell_floor.md`)

Index of the formalization (namespace `CellFloor`).

## Encodings

* A **house** `H = (I, k, ℓ, α)` is given by its components `I : Finset ℕ`, `k ℓ : ℕ`, `α : ℤ`,
  with the house conditions as hypotheses `hI : ∀ t ∈ I, t < k`, `hℓ : ℓ < 2 ^ k`, `hα : 1 ≤ α`
  (each theorem carries only those its proof uses; this is said in its docstring).
  `N = 2^{|I|}` is `2 ^ #I`; the dancer at position `p` is `TheoremF.dancer I p`.
* Sequences of length `N` are functions `ℕ → ℤ` (or `ℕ → ℝ`) of which only the positions `< N`
  matter (as in C1, C7, C8).  `x_H = TheoremF.xHseq I k ℓ α`, `J_H = TheoremF.JHseq I k ℓ`
  (in `ℕ`, cast to `ℤ`), `ŷ_H = Potential.yhat I k ℓ α = AntitonicFit.ifit N x_H`,
  `fit_N(x) = AntitonicFit.fit N (AntitonicFit.toR x)` for an integer sequence `x`,
  `ĉ_H = Potential.cHat I k ℓ α`; potentials are `Potential.IsPotential I k ℓ α V`.
* Penalties `Pr Pc : ℕ`.  Cell clocks `cellClock I k ℓ α Pr Pc p = x_H(p) − P_r J_H(p) +
  P_c J_H(N − 1 − p)`; cell costs `cellCost I k ℓ α Pr Pc p q = ĉ_H(p, q) − P_r J_H(p) +
  P_c J_H(q)`; cell arrows `IsCellArrow I p q := p < N ∧ q < N ∧ dancer I q ⊆ dancer I p`.
* Theorem B: `v = penal V I k ℓ Pr` and `w = penal V I k ℓ Pc`, where
  `penal V I k ℓ P p = V(p) − P J_H(p)`.
* (I3) and Theorem C: `xSharp I k ℓ α j = x_H(j + 1)` (`x^♯`, length `N − 1`),
  `yhatSharp I k ℓ α = ifit_{N−1}(x^♯)` (`ŷ^♯`), `costSharp I k ℓ α a b = ĉ_H(a + 1, b)`
  (`cost^♯`), `IsSharpArrow I a b := a < N − 1 ∧ b < N − 1 ∧ dancer I b ⊆ dancer I (a + 1)`;
  `v(j) = V(j + 1)`, `w(j) = V(j)` are written out.  `ℓ = 2^k − 1` is the hypothesis
  `hℓ' : ℓ = 2 ^ k - 1` and `I ≠ ∅` is `hne : I.Nonempty`.
* `r`-matchings and `tailSum` are those of C2 (`SmithBounds.IsRMatching`,
  `SmithBounds.tailSum`); the consequences are stated over `ℝ` (everything cast), as
  `SmithBounds.theorem_U` is.

## Where each statement is

* *Part A* (`Integrality.lean`): **Lemma 7.9** — (I1) `lemma_7_9_I1`; (I2) `lemma_7_9_I2`;
  (I3) `lemma_7_9_I3`.
* *Part B* (`Floor.lean`): **Theorem B** — (U1) `theorem_B_U1`, (U2) `theorem_B_U2`,
  (U3) `theorem_B_U3`, together `theorem_B`; the consequence `T(r) ≥ Y(r)` is `theorem_B_floor`.
* *Part C* (`Floor.lean`): **Theorem C** — (U1)–(U3) `theorem_C`; the consequence is
  `theorem_C_floor`.
* The consequences `theorem_B_floor` and `theorem_C_floor` take no potential as hypothesis: one is
  supplied by `Potential.theorem_F` (more general than the file, which assumes a potential `V`).
-/
