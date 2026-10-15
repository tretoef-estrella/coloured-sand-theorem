module

public import RequestProject.OddHouses.All
public import RequestProject.OddCeiling.Order
public import RequestProject.TheoremF.All

/-!
# `CSI16_theorem_F_at_p.md` — *Setting*: the sequences of a base-`p` house

Namespace `ColouredSand.OddTwist`.  This is the base-`p` analogue of
`RequestProject/TheoremF/Sequences.lean` (C7), built from the houses of CSI15
(`RequestProject/OddHouses/`).

## Encoding

* The prime is `p : ℕ` with `[Fact p.Prime]` (the file's `p` odd is never used: everything also
  holds for `p = 2`).
* A **house** `H = (I, k, ℓ, e, d)` is not bundled (as in CSI15): its components are
  `I : Finset ℕ`, `k ℓ : ℕ`, `e : ℤ` and the digit function `dg : ℕ → ℕ` (`d_t = dg t`).  The
  house conditions are hypotheses: `hI : ∀ t ∈ I, t < k`, `hℓ : ℓ < p ^ k`,
  `hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1`, and the file's `e ≥ 1` is `he : 1 ≤ e`.  Each theorem
  carries only the hypotheses it uses.
* `N = 2^{|I|}` is `2 ^ #I`.  Positions are natural numbers `q < N`; the dancer at position `q` is
  C7's `TheoremF.dancer I q` (binary digits of `q` select elements of `I`).  By CSI14 (A1)
  (`A1_same_order`) the dancers are in base-`p` o-order as well (`oW_dancer_mono`).
* As in C1 and C7, a sequence of length `N` is a function `ℕ → ℤ` (or `ℕ → ℕ`) of which only the
  positions `< N` matter:
  - `xHseqP p k I dg ℓ e q := xHP p k I dg ℓ e (dancer I q)` is `x_H(q)`;
  - `JHseqP p k I dg ℓ q := JHP p k dg ℓ (dancer I q)` is `J_H(q)`;
  - `ŷ_H` is `AntitonicFit.ifit (2 ^ #I) (xHseqP p k I dg ℓ e)` and the real fit is
    `AntitonicFit.fit (2 ^ #I) (AntitonicFit.toR (xHseqP p k I dg ℓ e))`.
* For the recursion: `c = max I` is `hne : I.Nonempty`, `hc : c = I.max' hne`; `I' = I.erase c`,
  `M = 2 ^ #(I.erase c)`, `H' = (I.erase c, c, ℓ % p ^ c, e, dg)`, and
  `dWalkP p k I dg ℓ e c q := d1P p k I dg ℓ e c (dancer (I.erase c) q)` is the walk
  `d_1(q) = −τ − [OR]·κ·J'(q) + [AND]·κ·J'(M − 1 − q)` (`dWalkP_eq`).
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset AntitonicFit TheoremF

/-- *Setting* of `CSI16_theorem_F_at_p.md`: `x_H(q) := x_H(dancer_I(q))` (CSI15's `xHP`). -/
def xHseqP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) : ℕ → ℤ :=
  fun q => xHP p k I dg ℓ e (dancer I q)

/-- *Setting* of `CSI16_theorem_F_at_p.md`: `J_H(q) := J_H(dancer_I(q))` (CSI15's `JHP`). -/
def JHseqP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) : ℕ → ℕ :=
  fun q => JHP p k dg ℓ (dancer I q)

/-- *Setting* of `CSI16_theorem_F_at_p.md`: the walk `d_1(q) := d1P … c (dancer_{I'}(q))`
(CSI15 (C6)), with `I' = I ∖ {c}`. -/
def dWalkP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (c : ℕ) : ℕ → ℤ :=
  fun q => d1P p k I dg ℓ e c (dancer (I.erase c) q)

variable {p : ℕ} {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ}

/-- *Setting* of `CSI16_theorem_F_at_p.md` (as Lemma 0f of C7): `x_H` is antisymmetric on
`[0, N)`.  (No hypothesis is needed.) -/
theorem oddF_xH_antisymm (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) :
    IsAntisymm (2 ^ #I) (xHseqP p k I dg ℓ e) := by
  intro q hq
  simp only [xHseqP]
  rw [lemma_0d hq, houseP_A0_antisymm ℓ e (lemma_0a I q)]

/-- *Setting* of `CSI16_theorem_F_at_p.md` (as Lemma 0f of C7): `J_H(0) = 0`, since
`dancer_I(0) = ∅` and `ℓ < p^k`. -/
theorem oddF_J0 (I : Finset ℕ) (hℓ : ℓ < p ^ k) : JHseqP p k I dg ℓ 0 = 0 := by
  simp only [JHseqP, dancer_zero, JHP, oW, sum_empty, add_zero]
  rw [if_neg (by omega)]

/-- `J_H ≤ 1` (*Setting* of `CSI16_theorem_F_at_p.md`). -/
lemma JHseqP_le_one (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ q : ℕ) : JHseqP p k I dg ℓ q ≤ 1 :=
  JHP_le_one k ℓ _

/-- The dancers are in base-`p` o-order (*Setting* of `CSI16_theorem_F_at_p.md`, by CSI14 (A1) and
Lemma 0b of C7): for `a ≤ b < N`, `o_{dancer(a)} ≤ o_{dancer(b)}`. -/
lemma oW_dancer_mono (h2 : 2 ≤ p) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {a b : ℕ}
    (hab : a ≤ b) (hb : b < 2 ^ #I) : oW p dg (dancer I a) ≤ oW p dg (dancer I b) := by
  by_contra hlt
  push_neg at hlt
  have h1 := (A1_same_order h2 hd (lemma_0a I b) (lemma_0a I a)).1 hlt
  have h2 := oE_dancer_mono hab hb
  omega

/-- `J_H` is an up-set of the o-order, i.e. non-decreasing on `[0, N)` (CSI15 (A0) with
`oW_dancer_mono`; step 1 of the proof of F0, `CSI16_theorem_F_at_p.md` Part Δ). -/
lemma JHseqP_mono (h2 : 2 ≤ p) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {a b : ℕ} (hab : a ≤ b)
    (hb : b < 2 ^ #I) : JHseqP p k I dg ℓ a ≤ JHseqP p k I dg ℓ b :=
  houseP_A0_upset ℓ (oW_dancer_mono h2 hd hab hb)

/-- The explicit formula of the walk (*Setting* of `CSI16_theorem_F_at_p.md`):
`d_1(q) = −τ − [OR]·κ·J'(q) + [AND]·κ·J'(M − 1 − q)` for `q < M`. -/
lemma dWalkP_eq (e : ℤ) (c : ℕ) {q : ℕ} (hq : q < 2 ^ #(I.erase c)) :
    dWalkP p k I dg ℓ e c q = -tauP p k I dg ℓ e c
      - (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) *
          JHseqP p c (I.erase c) dg (ℓ % p ^ c) q
      + (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) *
          JHseqP p c (I.erase c) dg (ℓ % p ^ c) (2 ^ #(I.erase c) - 1 - q) := by
  simp only [dWalkP, d1P, JHseqP]
  rw [lemma_0d hq]

/-- The digits of `H` restricted to `I' = I ∖ {c}` (auxiliary). -/
lemma hd_erase (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (c : ℕ) :
    ∀ t ∈ I.erase c, 1 ≤ dg t ∧ dg t ≤ p - 1 := fun t ht => hd t (mem_of_mem_erase ht)

end ColouredSand.OddTwist
