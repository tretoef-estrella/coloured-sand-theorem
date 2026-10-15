module

public import RequestProject.TheoremF.Dancers
public import RequestProject.Houses.TopDigit
public import RequestProject.AntitonicFit.Gluing

/-!
# The sequences of a house and Lemma 0f of `C7_theorem_F_walk_and_cut.md`

## Encoding

* A **house** `H = (I, k, ℓ, α)` is given by its components `I : Finset ℕ`, `k ℓ : ℕ`,
  `α : ℤ`; the house conditions are the hypotheses `hI : ∀ t ∈ I, t < k`, `hℓ : ℓ < 2 ^ k`
  and `hα : 1 ≤ α` (each theorem only carries the ones it uses; this is noted).
  `N = 2^{|I|}` is `2 ^ #I`.
* `xHseq I k ℓ α : ℕ → ℤ` is the sequence `p ↦ x_H(p) := Houses.xH I k ℓ α (dancer I p)`;
  `JHseq I k ℓ : ℕ → ℕ` is `p ↦ J_H(p) := Houses.JH k ℓ (dancer I p)`.  As in piece C1, a
  sequence of length `N` is a function on `ℕ` of which only the positions `< N` matter.
  `ŷ_H` is `AntitonicFit.ifit (2 ^ #I) (xHseq I k ℓ α)` and the real fit is
  `AntitonicFit.fit (2 ^ #I) (AntitonicFit.toR (xHseq I k ℓ α))`.
* For the walk (Part 2): `c = max I` is `hne : I.Nonempty`, `hc : c = I.max' hne`;
  `I' = I.erase c`, `M = 2 ^ #(I.erase c)`, `H' = (I.erase c, c, ℓ % 2 ^ c, α)`, and
  `dWalk I k ℓ α c : ℕ → ℤ` is `p ↦ d(p) := Houses.d1 I k ℓ α c (dancer (I.erase c) p)`.
-/

@[expose] public section

namespace TheoremF

open Finset Rulers AntitonicFit

/-- *Setting* (the sequences of a house) of `C7_theorem_F_walk_and_cut.md`:
`x_H(p) := Houses.xH I k ℓ α (dancer_I(p))`. -/
def xHseq (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) : ℕ → ℤ := fun p => Houses.xH I k ℓ α (dancer I p)

/-- *Setting* (the sequences of a house) of `C7_theorem_F_walk_and_cut.md`:
`J_H(p) := Houses.JH k ℓ (dancer_I(p))`. -/
def JHseq (I : Finset ℕ) (k ℓ : ℕ) : ℕ → ℕ := fun p => Houses.JH k ℓ (dancer I p)

/-- *Part 2* (Theorem F0) of `C7_theorem_F_walk_and_cut.md`: the walk increment
`d(p) := Houses.d1 I k ℓ α c (dancer_{I'}(p))`, with `I' = I ∖ {c}`. -/
def dWalk (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c : ℕ) : ℕ → ℤ :=
  fun p => Houses.d1 I k ℓ α c (dancer (I.erase c) p)

variable {I : Finset ℕ} {k ℓ : ℕ}

/-- **Lemma 0f** of `C7_theorem_F_walk_and_cut.md`, first claim: `x_H` is antisymmetric on
`[0, N)`, i.e. `x_H(N − 1 − p) = −x_H(p)` for `p < N`.  (More general than the file: none of the
house conditions is needed.) -/
theorem lemma_0f_antisymm (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) :
    IsAntisymm (2 ^ #I) (xHseq I k ℓ α) := by
  intro p hp
  simp only [xHseq]
  rw [lemma_0d hp, Houses.lemma_A0_antisymm ℓ α (lemma_0a I p)]

/-- **Lemma 0f** of `C7_theorem_F_walk_and_cut.md`, second claim: `J_H(0) = 0`.  (Only
`ℓ < 2^k` is needed.) -/
theorem lemma_0f_J0 (I : Finset ℕ) (hℓ : ℓ < 2 ^ k) : JHseq I k ℓ 0 = 0 := by
  simp [JHseq, dancer_zero, Houses.JH, oE_empty, hℓ]

/-- `J_H` takes values in `{0, 1}` (*Setting* of `C7_theorem_F_walk_and_cut.md`). -/
lemma JHseq_le_one (I : Finset ℕ) (k ℓ p : ℕ) : JHseq I k ℓ p ≤ 1 := by
  unfold JHseq Houses.JH; split_ifs <;> omega

/-- `J_H` is an up-set of the o-order: non-decreasing on `[0, N)` (Lemma A0 of C6 and (0b); step 1
of the proof of F0 in `C7_theorem_F_walk_and_cut.md`). -/
lemma JHseq_mono {p q : ℕ} (hpq : p ≤ q) (hq : q < 2 ^ #I) : JHseq I k ℓ p ≤ JHseq I k ℓ q :=
  Houses.lemma_A0_upset ℓ (oE_dancer_mono hpq hq)

/-- `N = 2M` (*Part 2* of `C7_theorem_F_walk_and_cut.md`). -/
lemma card_erase_max (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) :
    2 ^ #I = 2 * 2 ^ #(I.erase c) := by
  have hcI : c ∈ I := hc ▸ I.max'_mem hne
  have := card_erase_add_one hcI
  rw [← this, pow_succ]; ring

/-- The explicit formula of `d`:
`d(p) = −τ − [T = 1] κ J'(p) + [T = 0] κ J'(M − 1 − p)` for `p < M`
(*Part 2* of `C7_theorem_F_walk_and_cut.md`). -/
lemma dWalk_eq (α : ℤ) (c : ℕ) {p : ℕ} (hp : p < 2 ^ #(I.erase c)) :
    dWalk I k ℓ α c p = -Houses.tau I k ℓ α c
      - (if Houses.typ ℓ c = 1 then (Houses.kap I k ℓ c : ℤ) else 0) *
          JHseq (I.erase c) c (ℓ % 2 ^ c) p
      + (if Houses.typ ℓ c = 0 then (Houses.kap I k ℓ c : ℤ) else 0) *
          JHseq (I.erase c) c (ℓ % 2 ^ c) (2 ^ #(I.erase c) - 1 - p) := by
  simp only [dWalk, Houses.d1, JHseq]
  rw [lemma_0d hp]

end TheoremF
