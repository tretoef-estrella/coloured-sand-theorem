module

public import RequestProject.TheoremF.Dancers
public import RequestProject.TheoremF.Sequences
public import RequestProject.TheoremF.Walk
public import RequestProject.TheoremF.TheoremF

/-!
# Theorem F, first half (`C7_theorem_F_walk_and_cut.md`)

Index of the formalization (namespace `TheoremF`).

## Encodings

* A house `H = (I, k, ℓ, α)` is given by its components `I : Finset ℕ`, `k ℓ : ℕ`, `α : ℤ`, with
  the house conditions as hypotheses `hI : ∀ t ∈ I, t < k`, `hℓ : ℓ < 2 ^ k`, `hα : 1 ≤ α`
  (each theorem only carries the ones its proof uses; this is said in its docstring).
  `N = 2^{|I|}` is `2 ^ #I`.
* `dancer I p := I.filter (fun t => Houses.bit (#(I.filter (· < t))) p = 1)` is `dancer_I(p)`.
* Sequences of length `N` are functions on `ℕ` (only positions `< N` matter), as in piece C1:
  `xHseq I k ℓ α : ℕ → ℤ` is `x_H` (`p ↦ Houses.xH I k ℓ α (dancer I p)`), `JHseq I k ℓ : ℕ → ℕ`
  is `J_H` (`p ↦ Houses.JH k ℓ (dancer I p)`), `ŷ_H` is `AntitonicFit.ifit (2 ^ #I) (xHseq I k ℓ α)`
  and the real fit is `AntitonicFit.fit (2 ^ #I) (AntitonicFit.toR (xHseq I k ℓ α))`.
* For the walk: `c = max I` is `hne : I.Nonempty` with `hc : c = I.max' hne`; `I' = I.erase c`;
  `M = 2 ^ #(I.erase c)`; `H' = (I.erase c, c, ℓ % 2 ^ c, α)`, so `x' = xHseq (I.erase c) c
  (ℓ % 2 ^ c) α` and `J' = JHseq (I.erase c) c (ℓ % 2 ^ c)`; `d = dWalk I k ℓ α c`
  (`p ↦ Houses.d1 I k ℓ α c (dancer (I.erase c) p)`).  `Z_1 = fit M (toR x') + toR d` and
  `X_1 = ifit M x' + d` (pointwise sums); `concat`, `mirror` and `IsStrictCut` are those of C1.
* «`b` is the first position with `J(b) = 1`» is `J b = 1 ∧ ∀ p < b, J p = 0`.

## Where each statement is

* *Part 0* (`Dancers.lean`): **Lemma 0** — (0a) `lemma_0a`; (0b) `lemma_0b`;
  (0c) `lemma_0c_existsUnique`, `lemma_0c_rank`; (0d) `lemma_0d`; (0e) `lemma_0e`.
* `Sequences.lean`: **Lemma 0f** — `lemma_0f_antisymm`, `lemma_0f_J0`.
* *Part 2* (`Walk.lean`, `TheoremF.lean`): **Theorem F0** — (W0) `theorem_F0_W0`;
  (W1) `theorem_F0_W1_antitone`, `theorem_F0_W1_change`; (W2) `theorem_F0_W2`;
  (W3) `theorem_F0_W3`; all together `theorem_F0`.
* *Part 1* (`TheoremF.lean`): **Theorem F1** (Theorem 7.8: (Λ) and (Cut)) — `theorem_F1`,
  `theorem_F1_Lambda`, `theorem_F1_Cut`.
* F0 and F1 are proved together by induction on `|I|` (`F1_all`, with base `F1_empty` and step
  `F1_step`; the walk for `H` is first proved from (Cut) for `H'` in `walk_W2_of_cut`,
  `walk_W3_of_cut`).
-/
