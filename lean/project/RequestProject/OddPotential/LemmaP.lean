module

public import RequestProject.OddPotential.TheoremF1
public import RequestProject.Potential.All

/-!
# `CSI16_theorem_F_at_p.md` — *Setting* (potentials) and *Part P*: the inherited potential (Lemma P)

Base-`p` analogue of `RequestProject/Potential/Basic.lean` and `RequestProject/Potential/LemmaP.lean`
(C8), with `α` replaced by `e` and the changes of Part Δ (step 3 for (P4)).

## Encoding (in addition to `RequestProject/OddPotential/Sequences.lean`)

* `yhatP p k I dg ℓ e = AntitonicFit.ifit (2 ^ #I) (xHseqP p k I dg ℓ e)` is `ŷ_H`.
* `cHatSeqP p k I dg ℓ e q q' = cHatHP p k I dg ℓ e (dancer I q) (dancer I q')` is `ĉ_H(q, q')`
  (CSI15's cost).
* Arrows are C8's `Potential.IsArrow I q q'` (`q, q' < N` and `dancer_I(q') ⊊ dancer_I(q)`), which
  only depends on `I` and is reused as it is.
* `IsPotentialP p k I dg ℓ e V` (`V : ℕ → ℤ` is a **potential** for `H`) is the structure with
  fields `E`, `M`, `G`, exactly (E), (M), (G) of C8 for the base-`p` data.
* For the recursion (`c = max I`, `I' = I.erase c`, `M = 2 ^ #(I.erase c)`, `h = k − c` as the
  natural number `k - c` cast to `ℤ`, `H' = (I.erase c, c, ℓ % p ^ c, e, dg)`):
  `X1P p k I dg ℓ e c q = ŷ'(q) + d_1(q)` is `X_1`, and `vPrimeP p k I dg ℓ e c V'` is `v'`:
  at `q < M` it is `V'(q) − [OR]·κ·J'(q)`, and at `q ≥ M` it is
  `τ + V'(q − M) − [AND]·κ·J'(q − M)` (so `v'(M + q)` is as in the file).
  Indicators `[P]·κ` are `if P then (κ : ℤ) else 0`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset AntitonicFit TheoremF Potential

/-- *Setting* of `CSI16_theorem_F_at_p.md`: `ŷ_H := ifit_N(x_H)`, `N = 2^{|I|}`. -/
noncomputable def yhatP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) : ℕ → ℤ :=
  ifit (2 ^ #I) (xHseqP p k I dg ℓ e)

/-- *Setting* of `CSI16_theorem_F_at_p.md`: `ĉ_H(q, q') := ĉ_H(dancer_I(q), dancer_I(q'))`
(CSI15's `cHatHP`). -/
def cHatSeqP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (q q' : ℕ) : ℤ :=
  cHatHP p k I dg ℓ e (dancer I q) (dancer I q')

/-- *Setting* of `CSI16_theorem_F_at_p.md`: `V : ℕ → ℤ` is a **potential** for the base-`p` house
`H = (I, k, ℓ, e, d)` if (E), (M) and (G) of C8 hold. -/
structure IsPotentialP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (V : ℕ → ℤ) :
    Prop where
  /-- (E) `V(q) − V(N − 1 − q) = ŷ_H(q)` for every `q < N`. -/
  E : ∀ q < 2 ^ #I, V q - V (2 ^ #I - 1 - q) = yhatP p k I dg ℓ e q
  /-- (M) `V(q') ≤ V(q)` whenever `q ≤ q' < N`. -/
  M : ∀ q q', q ≤ q' → q' < 2 ^ #I → V q' ≤ V q
  /-- (G) `V(q) − V(q') ≤ ĉ_H(q, q')` for every arrow `q → q'`. -/
  G : ∀ q q', IsArrow I q q' → V q - V q' ≤ cHatSeqP p k I dg ℓ e q q'

/-- *Setting* of `CSI16_theorem_F_at_p.md`: `X_1(q) := ŷ'(q) + d_1(q)`. -/
noncomputable def X1P (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (c : ℕ) : ℕ → ℤ :=
  fun q => yhatP p c (I.erase c) dg (ℓ % p ^ c) e q + dWalkP p k I dg ℓ e c q

/-- *Part P* of `CSI16_theorem_F_at_p.md`: `v'(q) := V'(q) − [OR]·κ·J'(q)` and
`v'(M + q) := τ + V'(q) − [AND]·κ·J'(q)` for `q < M`. -/
def vPrimeP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (c : ℕ) (V' : ℕ → ℤ) :
    ℕ → ℤ := fun q =>
  if q < 2 ^ #(I.erase c) then
    V' q - (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) *
      JHseqP p c (I.erase c) dg (ℓ % p ^ c) q
  else
    tauP p k I dg ℓ e c + V' (q - 2 ^ #(I.erase c)) -
      (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) *
        JHseqP p c (I.erase c) dg (ℓ % p ^ c) (q - 2 ^ #(I.erase c))

/-- The function `ω` of the proof of Lemma P: `w(q) := V'(q) − R_{H'}(dancer_{I'}(q))`. -/
def wAuxP (p : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (c : ℕ) (V' : ℕ → ℤ) (q : ℕ) : ℤ :=
  V' q - RHP p c (I.erase c) dg (ℓ % p ^ c) e (dancer (I.erase c) q)

variable {p : ℕ} {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ} {c : ℕ} {V' : ℕ → ℤ}

/-- The value of `v'` at a position `M + q`. -/
lemma vPrimeP_high (q : ℕ) :
    vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c) + q) = tauP p k I dg ℓ e c + V' q -
      (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) *
        JHseqP p c (I.erase c) dg (ℓ % p ^ c) q := by
  simp [vPrimeP]

/-- The value of `v'` at a position `q < M`. -/
lemma vPrimeP_low {q : ℕ} (hq : q < 2 ^ #(I.erase c)) :
    vPrimeP p k I dg ℓ e c V' q = V' q -
      (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) *
        JHseqP p c (I.erase c) dg (ℓ % p ^ c) q := by
  simp [vPrimeP, hq]

section prime

variable [hp : Fact p.Prime]

/-- Proof of Lemma P: `v'(q) = R_H(dancer_I(q)) + ω(q)` for `q < M` (CSI15 (C1), Lemma 0e). -/
lemma vPrimeP_low_eq (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) (hne : I.Nonempty) (hc : c = I.max' hne) {q : ℕ}
    (hq : q < 2 ^ #(I.erase c)) :
    vPrimeP p k I dg ℓ e c V' q = RHP p k I dg ℓ e (dancer I q) + wAuxP p I dg ℓ e c V' q := by
  rw [vPrimeP_low hq, (lemma_0e hne hc hq).1, houseP_C1 hI hd hℓ e hne hc (lemma_0a _ q)]
  simp only [wAuxP, JHseqP]; ring

/-- Proof of Lemma P: `v'(M + q) = R_H(dancer_I(M + q)) + ω(q)` for `q < M` (CSI15 (C2)). -/
lemma vPrimeP_high_eq (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) (hne : I.Nonempty) (hc : c = I.max' hne) {q : ℕ}
    (hq : q < 2 ^ #(I.erase c)) :
    vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c) + q) =
      RHP p k I dg ℓ e (dancer I (2 ^ #(I.erase c) + q)) + wAuxP p I dg ℓ e c V' q := by
  rw [vPrimeP_high, (lemma_0e hne hc hq).2, houseP_C2 hI hd hℓ e hne hc (lemma_0a _ q)]
  simp only [wAuxP, JHseqP]; ring

end prime

/-- Proof of Lemma P: if `dancer_{I'}(q') ⊆ dancer_{I'}(q)`, then
`ω(q) − ω(q') ≤ γ_{I'}(dancer_{I'}(q) ∖ dancer_{I'}(q'))`, by (G) for `V'`. -/
lemma wAuxP_le (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') {q q' : ℕ}
    (hq : q < 2 ^ #(I.erase c)) (hq' : q' < 2 ^ #(I.erase c))
    (hsub : dancer (I.erase c) q' ⊆ dancer (I.erase c) q) :
    wAuxP p I dg ℓ e c V' q - wAuxP p I dg ℓ e c V' q' ≤
      (Rulers.gamma c (I.erase c) (dancer (I.erase c) q \ dancer (I.erase c) q') : ℤ) := by
  rcases hsub.eq_or_ssubset with heq | hss
  · have hqq : q' = q := by
      have := lemma_0c_rank hq' (I := I.erase c)
      rw [heq, lemma_0c_rank hq] at this
      exact this.symm
    subst hqq; simp
  · have := hV'.G q q' ⟨hq, hq', hss⟩
    simp only [cHatSeqP, cHatHP] at this
    simp only [wAuxP]; linarith

section P1

variable [hp : Fact p.Prime] (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
  (hℓ : ℓ < p ^ k) (hne : I.Nonempty) (hc : c = I.max' hne)
  (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V')
include hI hd hℓ hne hc hV'

/-- **(P1)** of Lemma P (`CSI16_theorem_F_at_p.md`, Part P), arrows in the first half: for an arrow
`q → q'` with `q, q' < M`, `v'(q) − v'(q') + h ≤ ĉ_H(q, q')`, `h = k − c`. -/
theorem oddF_P1_low {q q' : ℕ} (harr : IsArrow I q q') (hq : q < 2 ^ #(I.erase c))
    (hq' : q' < 2 ^ #(I.erase c)) :
    vPrimeP p k I dg ℓ e c V' q - vPrimeP p k I dg ℓ e c V' q' + ((k - c : ℕ) : ℤ) ≤
      cHatSeqP p k I dg ℓ e q q' := by
  obtain ⟨-, -, hss⟩ := harr
  have e1 := (lemma_0e hne hc hq).1
  have e2 := (lemma_0e hne hc hq').1
  have hΔI : dancer I q \ dancer I q' ⊆ I := sdiff_subset.trans (lemma_0a I q)
  have hcΔ : c ∉ dancer I q \ dancer I q' := by
    rw [e1]; intro h; exact c_not_mem_dancer_erase c q (mem_sdiff.1 h).1
  have hΔne : dancer I q \ dancer I q' ≠ ∅ := by
    intro h; rw [sdiff_eq_empty_iff_subset] at h; exact hss.2 h
  have hγ := houseP_C5_not_mem hI hne hc hΔI hcΔ hΔne
  have hw := wAuxP_le (I := I) (dg := dg) hV' hq hq' (by rw [← e1, ← e2]; exact hss.subset)
  rw [← e1, ← e2] at hw
  rw [vPrimeP_low_eq hI hd hℓ hne hc hq, vPrimeP_low_eq hI hd hℓ hne hc hq']
  simp only [cHatSeqP, cHatHP]
  rw [hγ]; push_cast; linarith

/-- **(P1)** of Lemma P (`CSI16_theorem_F_at_p.md`, Part P), arrows in the second half: for an
arrow `q → q'` with `q, q' ≥ M`, `v'(q) − v'(q') + h ≤ ĉ_H(q, q')`. -/
theorem oddF_P1_high {q q' : ℕ} (harr : IsArrow I q q') (hq : 2 ^ #(I.erase c) ≤ q)
    (hq' : 2 ^ #(I.erase c) ≤ q') :
    vPrimeP p k I dg ℓ e c V' q - vPrimeP p k I dg ℓ e c V' q' + ((k - c : ℕ) : ℤ) ≤
      cHatSeqP p k I dg ℓ e q q' := by
  have hN := card_erase_max hne hc
  obtain ⟨hqN, hqN', hss⟩ := harr
  obtain ⟨p₀, rfl⟩ := Nat.exists_eq_add_of_le hq
  obtain ⟨q₀, rfl⟩ := Nat.exists_eq_add_of_le hq'
  have hp₀ : p₀ < 2 ^ #(I.erase c) := by omega
  have hq₀ : q₀ < 2 ^ #(I.erase c) := by omega
  have e1 := (lemma_0e hne hc hp₀).2
  have e2 := (lemma_0e hne hc hq₀).2
  have hΔI : dancer I (2 ^ #(I.erase c) + p₀) \ dancer I (2 ^ #(I.erase c) + q₀) ⊆ I :=
    sdiff_subset.trans (lemma_0a I _)
  have hcΔ : c ∉ dancer I (2 ^ #(I.erase c) + p₀) \ dancer I (2 ^ #(I.erase c) + q₀) := by
    rw [e2]; simp
  have hΔne : dancer I (2 ^ #(I.erase c) + p₀) \ dancer I (2 ^ #(I.erase c) + q₀) ≠ ∅ := by
    intro h; rw [sdiff_eq_empty_iff_subset] at h; exact hss.2 h
  have hγ := houseP_C5_not_mem hI hne hc hΔI hcΔ hΔne
  have hcp := c_not_mem_dancer_erase (I := I) c p₀
  have hcq := c_not_mem_dancer_erase (I := I) c q₀
  have hΔ : dancer I (2 ^ #(I.erase c) + p₀) \ dancer I (2 ^ #(I.erase c) + q₀) =
      dancer (I.erase c) p₀ \ dancer (I.erase c) q₀ := by
    rw [e1, e2]
    ext x
    simp only [mem_sdiff, mem_union, mem_singleton]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact ⟨h1, fun h => h2 (Or.inl h)⟩
      · exact absurd (Or.inr h1) h2
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inl h1, ?_⟩
      rintro (h | h)
      · exact h2 h
      · exact hcp (h ▸ h1)
  have hsub : dancer (I.erase c) q₀ ⊆ dancer (I.erase c) p₀ := by
    intro x hx
    have := hss.subset (by rw [e2]; exact mem_union_left _ hx)
    rw [e1, mem_union, mem_singleton] at this
    rcases this with h | h
    · exact h
    · exact absurd (h ▸ hx) hcq
  have hw := wAuxP_le (I := I) (dg := dg) hV' hp₀ hq₀ hsub
  rw [vPrimeP_high_eq hI hd hℓ hne hc hp₀, vPrimeP_high_eq hI hd hℓ hne hc hq₀]
  simp only [cHatSeqP, cHatHP]
  rw [hγ, hΔ]; push_cast; linarith

/-- **(P1)** of Lemma P (`CSI16_theorem_F_at_p.md`, Part P), arrows across the junction: for an
arrow `q → q'` with `q ≥ M > q'`, `v'(q) − v'(q') ≤ ĉ_H(q, q')`. -/
theorem oddF_P1_cross {q q' : ℕ} (harr : IsArrow I q q') (hq : 2 ^ #(I.erase c) ≤ q)
    (hq' : q' < 2 ^ #(I.erase c)) :
    vPrimeP p k I dg ℓ e c V' q - vPrimeP p k I dg ℓ e c V' q' ≤ cHatSeqP p k I dg ℓ e q q' := by
  have hN := card_erase_max hne hc
  obtain ⟨hqN, -, hss⟩ := harr
  obtain ⟨p₀, rfl⟩ := Nat.exists_eq_add_of_le hq
  have hp₀ : p₀ < 2 ^ #(I.erase c) := by omega
  have e1 := (lemma_0e hne hc hp₀).2
  have e2 := (lemma_0e hne hc hq').1
  have hcq := c_not_mem_dancer_erase (I := I) c q'
  have hsub : dancer (I.erase c) q' ⊆ dancer (I.erase c) p₀ := by
    intro x hx
    have := hss.subset (by rw [e2]; exact hx)
    rw [e1, mem_union, mem_singleton] at this
    rcases this with h | h
    · exact h
    · exact absurd (h ▸ hx) hcq
  have hΔ : dancer I (2 ^ #(I.erase c) + p₀) \ dancer I q' =
      (dancer (I.erase c) p₀ \ dancer (I.erase c) q') ∪ {c} := by
    rw [e1, e2]
    ext x
    simp only [mem_sdiff, mem_union, mem_singleton]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr h1
    · rintro (⟨h1, h2⟩ | h1)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, fun h => hcq (h1 ▸ h)⟩
  have hγ := houseP_C5_mem hI hne hc
    (Δ₀ := dancer (I.erase c) p₀ \ dancer (I.erase c) q') (sdiff_subset.trans (lemma_0a _ _))
  have hw := wAuxP_le (I := I) (dg := dg) hV' hp₀ hq' hsub
  rw [vPrimeP_high_eq hI hd hℓ hne hc hp₀, vPrimeP_low_eq hI hd hℓ hne hc hq']
  simp only [cHatSeqP, cHatHP]
  rw [hΔ, hγ]; linarith

end P1

/-- **(P2)** of Lemma P (`CSI16_theorem_F_at_p.md`, Part P): for `q < M`,
`v'(q) − v'(N − 1 − q) = X_1(q)` and `v'(M + q) − v'(M − 1 − q) = −X_1(M − 1 − q)`.
(Uses only (E) for `V'` and `c ∈ I`; no house condition.) -/
theorem oddF_P2 (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') :
    (∀ q < 2 ^ #(I.erase c),
      vPrimeP p k I dg ℓ e c V' q - vPrimeP p k I dg ℓ e c V' (2 ^ #I - 1 - q) =
        X1P p k I dg ℓ e c q) ∧
    (∀ q < 2 ^ #(I.erase c),
      vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c) + q) -
        vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c) - 1 - q) =
        -X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1 - q)) := by
  have hN := card_erase_max hne hc
  constructor
  · intro q hq
    have e' : 2 ^ #I - 1 - q = 2 ^ #(I.erase c) + (2 ^ #(I.erase c) - 1 - q) := by omega
    rw [e', vPrimeP_high, vPrimeP_low hq]
    have hE := hV'.E q hq
    simp only [X1P, yhatP] at hE ⊢
    rw [dWalkP_eq e c hq]
    linarith
  · intro q hq
    have hq' : 2 ^ #(I.erase c) - 1 - q < 2 ^ #(I.erase c) := by omega
    rw [vPrimeP_high, vPrimeP_low hq']
    have hE := hV'.E _ hq'
    have e' : 2 ^ #(I.erase c) - 1 - (2 ^ #(I.erase c) - 1 - q) = q := by omega
    rw [e'] at hE
    simp only [X1P, yhatP] at hE ⊢
    rw [dWalkP_eq e c hq', e']
    linarith

/-- **(P3)** of Lemma P (`CSI16_theorem_F_at_p.md`, Part P): `v'` is non-increasing on `[0, M)`
and on `[M, N)`.  (Uses (M) for `V'`, `c = max I` and the digit condition.) -/
theorem oddF_P3 [Fact p.Prime] (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hne : I.Nonempty)
    (hc : c = I.max' hne) (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') :
    (∀ q q', q ≤ q' → q' < 2 ^ #(I.erase c) →
      vPrimeP p k I dg ℓ e c V' q' ≤ vPrimeP p k I dg ℓ e c V' q) ∧
    (∀ q q', 2 ^ #(I.erase c) ≤ q → q ≤ q' → q' < 2 ^ #I →
      vPrimeP p k I dg ℓ e c V' q' ≤ vPrimeP p k I dg ℓ e c V' q) := by
  have hN := card_erase_max hne hc
  have hd' := hd_erase hd c
  have h2p := oddHou_two_le_p (p := p)
  have hA : (0 : ℤ) ≤ if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0 := by
    split_ifs <;> simp
  have hB : (0 : ℤ) ≤ if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0 := by
    split_ifs <;> simp
  constructor
  · intro q q' hqq hq'
    rw [vPrimeP_low hq', vPrimeP_low (by omega)]
    have h1 := hV'.M q q' hqq hq'
    have h2 : (JHseqP p c (I.erase c) dg (ℓ % p ^ c) q : ℤ) ≤
        JHseqP p c (I.erase c) dg (ℓ % p ^ c) q' := by
      exact_mod_cast JHseqP_mono h2p hd' hqq hq'
    nlinarith [mul_le_mul_of_nonneg_left h2 hA]
  · intro q q' hq hqq hq'
    obtain ⟨p₀, rfl⟩ := Nat.exists_eq_add_of_le hq
    obtain ⟨q₀, rfl⟩ := Nat.exists_eq_add_of_le (hq.trans hqq)
    have hq₀ : q₀ < 2 ^ #(I.erase c) := by omega
    rw [vPrimeP_high, vPrimeP_high]
    have h1 := hV'.M p₀ q₀ (by omega) hq₀
    have h2 : (JHseqP p c (I.erase c) dg (ℓ % p ^ c) p₀ : ℤ) ≤
        JHseqP p c (I.erase c) dg (ℓ % p ^ c) q₀ := by
      exact_mod_cast JHseqP_mono h2p hd' (by omega) hq₀
    nlinarith [mul_le_mul_of_nonneg_left h2 hB]

/-- **(P4)** of Lemma P (`CSI16_theorem_F_at_p.md`, Part P, and Part Δ step 3), in its sharp form:
`v'(M) − v'(M − 1) = −X_1(M − 1)` and `−X_1(M − 1) ≤ h − e·(d_c p^c − o_{I'}) ≤ h − e`,
`h = k − c`. -/
theorem oddF_P4 [hp : Fact p.Prime] (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (he : 1 ≤ e) (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') :
    vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c)) -
        vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c) - 1) =
      -X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1) ∧
    -X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1) ≤
      ((k - c : ℕ) : ℤ) - e * ((dg c : ℤ) * (p : ℤ) ^ c - (oW p dg (I.erase c) : ℤ)) ∧
    ((k - c : ℕ) : ℤ) - e * ((dg c : ℤ) * (p : ℤ) ^ c - (oW p dg (I.erase c) : ℤ)) ≤
      ((k - c : ℕ) : ℤ) - e := by
  have hcI : c ∈ I := hc ▸ I.max'_mem hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ I.le_max' t ht
  have hI' : ∀ t ∈ I.erase c, t < c := fun t ht =>
    lt_of_le_of_ne (hcmax t (mem_of_mem_erase ht)) (ne_of_mem_erase ht)
  have hMpos : 0 < 2 ^ #(I.erase c) := Nat.two_pow_pos _
  have hℓ' : ℓ % p ^ c < p ^ c := Nat.mod_lt _ (pow_pos hp.out.pos c)
  refine ⟨?_, ?_, ?_⟩
  · have := (oddF_P2 (k := k) hne hc hV').2 0 hMpos
    simpa using this
  · have hM1 : 2 ^ #(I.erase c) - 1 < 2 ^ #(I.erase c) := by omega
    have hΛ := oddF_F1_Lambda hI' (hd_erase hd c) hℓ' he _ hM1
    have hJ0 := oddF_J0 (dg := dg) (I.erase c) hℓ'
    have hJ1 := JHseqP_le_one p c (I.erase c) dg (ℓ % p ^ c) (2 ^ #(I.erase c) - 1)
    have hh := Houses.h_max hI hcI hcmax
    simp only [X1P, yhatP]
    rw [dWalkP_eq e c hM1, Nat.sub_self, hJ0]
    simp only [tauP, hh]
    have hA : (0 : ℤ) ≤ if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0 := by
      split_ifs <;> simp
    have hAs : (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) ≤
        (if typP p dg ℓ c = .OR ∨ typP p dg ℓ c = .DIG then (kapP p k I ℓ c : ℤ) else 0) := by
      split_ifs <;> simp_all
    have hJ1' : (JHseqP p c (I.erase c) dg (ℓ % p ^ c) (2 ^ #(I.erase c) - 1) : ℤ) ≤ 1 := by
      exact_mod_cast hJ1
    have habs := neg_abs_le (ifit (2 ^ #(I.erase c)) (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e)
      (2 ^ #(I.erase c) - 1))
    have p1 := mul_le_mul_of_nonneg_left hJ1' hA
    push_cast
    nlinarith
  · have h1 := oW_lt_erase (I := I) hd hcmax (D₀ := I.erase c) subset_rfl
    have h2 := (hd c hcI).1
    have h3 : p ^ c ≤ dg c * p ^ c := Nat.le_mul_of_pos_left _ h2
    have h4 : oW p dg (I.erase c) + 1 ≤ dg c * p ^ c := by omega
    have h5 : ((oW p dg (I.erase c) : ℕ) : ℤ) + 1 ≤ ((dg c * p ^ c : ℕ) : ℤ) := by
      exact_mod_cast h4
    push_cast at h5
    have := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ dg c * (p : ℤ) ^ c - oW p dg (I.erase c)
      by linarith) (by omega : (0 : ℤ) ≤ e)
    linarith

/-- **Lemma P** (`CSI16_theorem_F_at_p.md`, Part P), all four parts together, for every house with
`I ≠ ∅` and every potential `V'` for `H'`: (P1)–(P4) (with (P4) in its sharp form). -/
theorem oddF_lemma_P [Fact p.Prime] (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') :
    -- (P1)
    ((∀ q q', IsArrow I q q' → q < 2 ^ #(I.erase c) → q' < 2 ^ #(I.erase c) →
        vPrimeP p k I dg ℓ e c V' q - vPrimeP p k I dg ℓ e c V' q' + ((k - c : ℕ) : ℤ) ≤
          cHatSeqP p k I dg ℓ e q q') ∧
      (∀ q q', IsArrow I q q' → 2 ^ #(I.erase c) ≤ q → 2 ^ #(I.erase c) ≤ q' →
        vPrimeP p k I dg ℓ e c V' q - vPrimeP p k I dg ℓ e c V' q' + ((k - c : ℕ) : ℤ) ≤
          cHatSeqP p k I dg ℓ e q q') ∧
      (∀ q q', IsArrow I q q' → 2 ^ #(I.erase c) ≤ q → q' < 2 ^ #(I.erase c) →
        vPrimeP p k I dg ℓ e c V' q - vPrimeP p k I dg ℓ e c V' q' ≤
          cHatSeqP p k I dg ℓ e q q') ∧
      (∀ q q', q < 2 ^ #(I.erase c) → 2 ^ #(I.erase c) ≤ q' → ¬ IsArrow I q q')) ∧
    -- (P2)
    ((∀ q < 2 ^ #(I.erase c),
      vPrimeP p k I dg ℓ e c V' q - vPrimeP p k I dg ℓ e c V' (2 ^ #I - 1 - q) =
        X1P p k I dg ℓ e c q) ∧
    (∀ q < 2 ^ #(I.erase c),
      vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c) + q) -
        vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c) - 1 - q) =
        -X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1 - q))) ∧
    -- (P3)
    ((∀ q q', q ≤ q' → q' < 2 ^ #(I.erase c) →
      vPrimeP p k I dg ℓ e c V' q' ≤ vPrimeP p k I dg ℓ e c V' q) ∧
    (∀ q q', 2 ^ #(I.erase c) ≤ q → q ≤ q' → q' < 2 ^ #I →
      vPrimeP p k I dg ℓ e c V' q' ≤ vPrimeP p k I dg ℓ e c V' q)) ∧
    -- (P4)
    (vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c)) -
        vPrimeP p k I dg ℓ e c V' (2 ^ #(I.erase c) - 1) =
      -X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1) ∧
    -X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1) ≤
      ((k - c : ℕ) : ℤ) - e * ((dg c : ℤ) * (p : ℤ) ^ c - (oW p dg (I.erase c) : ℤ)) ∧
    ((k - c : ℕ) : ℤ) - e * ((dg c : ℤ) * (p : ℤ) ^ c - (oW p dg (I.erase c) : ℤ)) ≤
      ((k - c : ℕ) : ℤ) - e) :=
  ⟨⟨fun _ _ ha hq hq' => oddF_P1_low hI hd hℓ hne hc hV' ha hq hq',
    fun _ _ ha hq hq' => oddF_P1_high hI hd hℓ hne hc hV' ha hq hq',
    fun _ _ ha hq hq' => oddF_P1_cross hI hd hℓ hne hc hV' ha hq hq',
    fun _ _ hq hq' => lemma_P1_no_arrow hne hc hq hq'⟩,
    oddF_P2 hne hc hV', oddF_P3 hd hne hc hV', oddF_P4 hI hd he hne hc hV'⟩

end ColouredSand.OddTwist
