module

public import RequestProject.Potential.Basic
public import RequestProject.Potential.LemmaP
public import RequestProject.Potential.Junction
public import RequestProject.Potential.Flat
public import RequestProject.Potential.TheoremF

/-!
# Theorem F, second half: the potential (`C8_theorem_F_potential.md`)

Index of the formalization (namespace `Potential`).

## Encodings

* A **house** `H = (I, k, ℓ, α)` is given by its components `I : Finset ℕ`, `k ℓ : ℕ`, `α : ℤ`,
  with the house conditions as hypotheses `hI : ∀ t ∈ I, t < k`, `hℓ : ℓ < 2 ^ k`, `hα : 1 ≤ α`
  (each theorem carries only the ones its proof uses; this is said in its docstring).
  `N = 2^{|I|}` is `2 ^ #I`; `c = max I` is `hne : I.Nonempty`, `hc : c = I.max' hne`;
  `I' = I.erase c`, `M = 2 ^ #(I.erase c)`, `h = k − c` (the natural number `k - c` cast to `ℤ`),
  `H' = (I.erase c, c, ℓ % 2 ^ c, α)`.
* **Positions and sequences**: a position is a natural number; a sequence is a function
  `ℕ → ℤ` of which only positions `< N` matter (as in C1 and C7).  The dancer at `p` is
  `TheoremF.dancer I p` (C7); `x_H`, `J_H`, `d` are `TheoremF.xHseq`, `TheoremF.JHseq`,
  `TheoremF.dWalk` (C7); `ŷ_H` is `yhat I k ℓ α = AntitonicFit.ifit (2 ^ #I) (xHseq I k ℓ α)`
  (C1's integer fit); `T, κ, τ` are `Houses.typ ℓ c`, `Houses.kap I k ℓ c`,
  `Houses.tau I k ℓ α c` (C6).
* `cHat I k ℓ α p q := Houses.cHatH I k ℓ α (dancer I p) (dancer I q)` is `ĉ_H(p, q)`;
  `IsArrow I p q := p < N ∧ q < N ∧ dancer I q ⊂ dancer I p` is an arrow `p → q`.
* A **potential** is a function `V : ℕ → ℤ` of the position; `IsPotential I k ℓ α V` is the
  structure with fields `E`, `M`, `G`, exactly (E), (M), (G) of the *Setting*.
* `X1 I k ℓ α c p := ŷ'(p) + d(p)` is `X_1`; `vPrime I k ℓ α c V'` is `v'` of Part 1 (at `p ≥ M`
  it is defined as `τ + V'(p − M) − [T = 0] κ J'(p − M)`, so `v'(M + p)` is as in the file).
* Lemma F: `f` is given with `IsLeast {p | p < M ∧ X_1(p) ≤ 0} f` (`exists_flat_start`: such an
  `f` exists when `X_1(M − 1) ≤ 0`); `F = [f, N − 1 − f]` is `f ≤ p ∧ p ≤ N − 1 − f`;
  `lo`, `hi` are `loF`, `hiF`; the potential of (F4) is `flatV … f cF`.
* Corollary F′: subsets are `Finset ℕ`s contained in `I`, `rank_I = GoldenMatching.rank I` (C4),
  `o = Rulers.oE` (C3), `ĉ_H(a, b) = Houses.cHatH I k ℓ α a b` (C6).

## Where each statement is

* *Setting* (`Basic.lean`): `yhat`, `cHat`, `IsArrow` (and `IsArrow.lt`: `q < p`),
  `IsPotential`, `X1`, `vPrime`.
* *Part 1* (`LemmaP.lean`): **Lemma P** — (P1) `lemma_P1_low`, `lemma_P1_high`, `lemma_P1_cross`,
  `lemma_P1_no_arrow`; (P2) `lemma_P2`; (P3) `lemma_P3`; (P4) `lemma_P4`; all together `lemma_P`.
* *Part 2* (`Junction.lean`, `Flat.lean`): **Lemma X** `lemma_X`; **Lemma N** `lemma_N`;
  **Lemma F** — (F1) `lemma_F1`, (F2) `lemma_F2`, (F3) `lemma_F3`, (F4) `lemma_F4` (for every
  integer `c_F ∈ [lo, hi]`); all together `lemma_F`; existence of `f`: `exists_flat_start`.
* *Part 3* (`TheoremF.lean`): **Theorem F** `theorem_F` (by induction on `|I|`:
  `potential_exists_aux`, `potential_empty`, `potential_step`); **Corollary F′** `corollary_F'`.
-/
