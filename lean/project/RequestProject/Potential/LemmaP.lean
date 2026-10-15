module

public import RequestProject.Potential.Basic

/-!
# Part 1 of `C8_theorem_F_potential.md`: the inherited potential (Lemma P)

Encodings as in `RequestProject/Potential/Basic.lean`.  Throughout, `c = max I` is given by
`hne : I.Nonempty` and `hc : c = I.max' hne`, `M = 2 ^ #(I.erase c)`, `N = 2 ^ #I = 2M`, and
`V'` is a potential for `H' = (I.erase c, c, ℓ % 2 ^ c, α)`.
-/

@[expose] public section

namespace Potential

open Finset AntitonicFit TheoremF

/-- The function `ω` of the proof of Lemma P (`C8_theorem_F_potential.md`), on positions of `H'`:
`w(p) := V'(p) − R_{H'}(dancer_{I'}(p))`, so that `v' = R_H + w` (`vPrime_low_eq`,
`vPrime_high_eq`). -/
def wAux (I : Finset ℕ) (ℓ : ℕ) (α : ℤ) (c : ℕ) (V' : ℕ → ℤ) (p : ℕ) : ℤ :=
  V' p - Houses.RH (I.erase c) c (ℓ % 2 ^ c) α (dancer (I.erase c) p)

variable {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} {c : ℕ} {V' : ℕ → ℤ}

lemma c_not_mem_dancer_erase (c p : ℕ) : c ∉ dancer (I.erase c) p := fun h => by
  simpa using lemma_0a _ p h

/-- Proof of Lemma P (`C8_theorem_F_potential.md`): `v'(p) = R_H(dancer_I(p)) + ω(p)` for
`p < M`, by (C1) of C6 and Lemma 0e of C7. -/
lemma vPrime_low_eq (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hne : I.Nonempty)
    (hc : c = I.max' hne) {p : ℕ} (hp : p < 2 ^ #(I.erase c)) :
    vPrime I k ℓ α c V' p = Houses.RH I k ℓ α (dancer I p) + wAux I ℓ α c V' p := by
  rw [vPrime_low α c V' hp, (lemma_0e hne hc hp).1,
    Houses.lemma_C1 hI hℓ α hne hc (lemma_0a _ p)]
  simp only [wAux, JHseq]; ring

/-- Proof of Lemma P (`C8_theorem_F_potential.md`): `v'(M + p) = R_H(dancer_I(M + p)) + ω(p)` for
`p < M`, by (C2) of C6 and Lemma 0e of C7. -/
lemma vPrime_high_eq (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hne : I.Nonempty)
    (hc : c = I.max' hne) {p : ℕ} (hp : p < 2 ^ #(I.erase c)) :
    vPrime I k ℓ α c V' (2 ^ #(I.erase c) + p) =
      Houses.RH I k ℓ α (dancer I (2 ^ #(I.erase c) + p)) + wAux I ℓ α c V' p := by
  rw [vPrime_high, (lemma_0e hne hc hp).2, Houses.lemma_C2 hI hℓ α hne hc (lemma_0a _ p)]
  simp only [wAux, JHseq]; ring

/-- Proof of Lemma P (`C8_theorem_F_potential.md`): if `dancer_{I'}(q) ⊆ dancer_{I'}(p)`, then
`ω(p) − ω(q) ≤ γ_{I'}(dancer_{I'}(p) ∖ dancer_{I'}(q))`, by (G) for `V'` (and `0` when the two
dancers are equal). -/
lemma wAux_le (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') {p q : ℕ}
    (hp : p < 2 ^ #(I.erase c)) (hq : q < 2 ^ #(I.erase c))
    (hsub : dancer (I.erase c) q ⊆ dancer (I.erase c) p) :
    wAux I ℓ α c V' p - wAux I ℓ α c V' q ≤
      (Rulers.gamma c (I.erase c) (dancer (I.erase c) p \ dancer (I.erase c) q) : ℤ) := by
  rcases hsub.eq_or_ssubset with heq | hss
  · have hqp : q = p := by
      have := lemma_0c_rank hq (I := I.erase c)
      rw [heq, lemma_0c_rank hp] at this
      exact this.symm
    subst hqp; simp
  · have := hV'.G p q ⟨hp, hq, hss⟩
    simp only [cHat, Houses.cHatH] at this
    simp only [wAux]; linarith

section P1

variable (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hne : I.Nonempty) (hc : c = I.max' hne)
  (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V')
include hI hℓ hne hc hV'

/-- **(P1)** of Lemma P (`C8_theorem_F_potential.md`), arrows in the first half: for an arrow
`p → q` with `p, q < M`, `v'(p) − v'(q) + h ≤ ĉ_H(p, q)`, `h = k − c`. (Uses `I ⊆ {0,…,k−1}`,
`ℓ < 2^k` and (G) for `V'`; not `α ≥ 1`.) -/
theorem lemma_P1_low {p q : ℕ} (harr : IsArrow I p q) (hp : p < 2 ^ #(I.erase c))
    (hq : q < 2 ^ #(I.erase c)) :
    vPrime I k ℓ α c V' p - vPrime I k ℓ α c V' q + ((k - c : ℕ) : ℤ) ≤ cHat I k ℓ α p q := by
  obtain ⟨-, -, hss⟩ := harr
  have e1 := (lemma_0e hne hc hp).1
  have e2 := (lemma_0e hne hc hq).1
  have hΔI : dancer I p \ dancer I q ⊆ I := sdiff_subset.trans (lemma_0a I p)
  have hcΔ : c ∉ dancer I p \ dancer I q := by
    rw [e1]; intro h; exact c_not_mem_dancer_erase c p (mem_sdiff.1 h).1
  have hΔne : dancer I p \ dancer I q ≠ ∅ := by
    intro h; rw [sdiff_eq_empty_iff_subset] at h; exact hss.2 h
  have hγ := Houses.lemma_C5_not_mem hI hne hc hΔI hcΔ hΔne
  have hw := wAux_le (I := I) hV' hp hq (by rw [← e1, ← e2]; exact hss.subset)
  rw [← e1, ← e2] at hw
  rw [vPrime_low_eq hI hℓ hne hc hp, vPrime_low_eq hI hℓ hne hc hq]
  simp only [cHat, Houses.cHatH]
  rw [hγ]; push_cast; linarith

/-- **(P1)** of Lemma P (`C8_theorem_F_potential.md`), arrows in the second half: for an arrow
`p → q` with `p, q ≥ M`, `v'(p) − v'(q) + h ≤ ĉ_H(p, q)`, `h = k − c`. (Uses `I ⊆ {0,…,k−1}`,
`ℓ < 2^k` and (G) for `V'`; not `α ≥ 1`.) -/
theorem lemma_P1_high {p q : ℕ} (harr : IsArrow I p q) (hp : 2 ^ #(I.erase c) ≤ p)
    (hq : 2 ^ #(I.erase c) ≤ q) :
    vPrime I k ℓ α c V' p - vPrime I k ℓ α c V' q + ((k - c : ℕ) : ℤ) ≤ cHat I k ℓ α p q := by
  have hN := card_erase_max hne hc
  obtain ⟨hpN, hqN, hss⟩ := harr
  obtain ⟨p₀, rfl⟩ := Nat.exists_eq_add_of_le hp
  obtain ⟨q₀, rfl⟩ := Nat.exists_eq_add_of_le hq
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
  have hγ := Houses.lemma_C5_not_mem hI hne hc hΔI hcΔ hΔne
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
  have hw := wAux_le (I := I) hV' hp₀ hq₀ hsub
  rw [vPrime_high_eq hI hℓ hne hc hp₀, vPrime_high_eq hI hℓ hne hc hq₀]
  simp only [cHat, Houses.cHatH]
  rw [hγ, hΔ]; push_cast; linarith

/-- **(P1)** of Lemma P (`C8_theorem_F_potential.md`), arrows across the junction: for an arrow
`p → q` with `p ≥ M > q`, `v'(p) − v'(q) ≤ ĉ_H(p, q)`. (Uses `I ⊆ {0,…,k−1}`, `ℓ < 2^k` and (G)
for `V'`; not `α ≥ 1`.) -/
theorem lemma_P1_cross {p q : ℕ} (harr : IsArrow I p q) (hp : 2 ^ #(I.erase c) ≤ p)
    (hq : q < 2 ^ #(I.erase c)) :
    vPrime I k ℓ α c V' p - vPrime I k ℓ α c V' q ≤ cHat I k ℓ α p q := by
  have hN := card_erase_max hne hc
  obtain ⟨hpN, -, hss⟩ := harr
  obtain ⟨p₀, rfl⟩ := Nat.exists_eq_add_of_le hp
  have hp₀ : p₀ < 2 ^ #(I.erase c) := by omega
  have e1 := (lemma_0e hne hc hp₀).2
  have e2 := (lemma_0e hne hc hq).1
  have hcq := c_not_mem_dancer_erase (I := I) c q
  have hsub : dancer (I.erase c) q ⊆ dancer (I.erase c) p₀ := by
    intro x hx
    have := hss.subset (by rw [e2]; exact hx)
    rw [e1, mem_union, mem_singleton] at this
    rcases this with h | h
    · exact h
    · exact absurd (h ▸ hx) hcq
  have hΔ : dancer I (2 ^ #(I.erase c) + p₀) \ dancer I q =
      (dancer (I.erase c) p₀ \ dancer (I.erase c) q) ∪ {c} := by
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
  have hγ := Houses.lemma_C5_mem hI hne hc
    (Δ₀ := dancer (I.erase c) p₀ \ dancer (I.erase c) q) (sdiff_subset.trans (lemma_0a _ _))
  have hw := wAux_le (I := I) hV' hp₀ hq hsub
  rw [vPrime_high_eq hI hℓ hne hc hp₀, vPrime_low_eq hI hℓ hne hc hq]
  simp only [cHat, Houses.cHatH]
  rw [hΔ, hγ]; linarith

end P1

/-- **(P1)** of Lemma P (`C8_theorem_F_potential.md`), the remark «there is no arrow `p → q` with
`p < M ≤ q`». (Only `c = max I` is used.) -/
theorem lemma_P1_no_arrow (hne : I.Nonempty) (hc : c = I.max' hne) {p q : ℕ}
    (hp : p < 2 ^ #(I.erase c)) (hq : 2 ^ #(I.erase c) ≤ q) : ¬ IsArrow I p q := by
  rintro ⟨-, hqN, hss⟩
  have hN := card_erase_max hne hc
  obtain ⟨q₀, rfl⟩ := Nat.exists_eq_add_of_le hq
  have hq₀ : q₀ < 2 ^ #(I.erase c) := by omega
  have hc1 : c ∈ dancer I (2 ^ #(I.erase c) + q₀) := by
    rw [(lemma_0e hne hc hq₀).2]; simp
  have := hss.subset hc1
  rw [(lemma_0e hne hc hp).1] at this
  exact c_not_mem_dancer_erase c p this

/-- **(P2)** of Lemma P (`C8_theorem_F_potential.md`): for `p < M`,
`v'(p) − v'(N − 1 − p) = X_1(p)` and `v'(M + p) − v'(M − 1 − p) = −X_1(M − 1 − p)`.
(Uses only (E) for `V'` and `c ∈ I`; no house condition.) -/
theorem lemma_P2 (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') :
    (∀ p < 2 ^ #(I.erase c),
      vPrime I k ℓ α c V' p - vPrime I k ℓ α c V' (2 ^ #I - 1 - p) = X1 I k ℓ α c p) ∧
    (∀ p < 2 ^ #(I.erase c),
      vPrime I k ℓ α c V' (2 ^ #(I.erase c) + p) -
        vPrime I k ℓ α c V' (2 ^ #(I.erase c) - 1 - p) =
        -X1 I k ℓ α c (2 ^ #(I.erase c) - 1 - p)) := by
  have hN := card_erase_max hne hc
  constructor
  · intro p hp
    have e : 2 ^ #I - 1 - p = 2 ^ #(I.erase c) + (2 ^ #(I.erase c) - 1 - p) := by omega
    rw [e, vPrime_high, vPrime_low α c V' hp]
    have hE := hV'.E p hp
    simp only [X1]
    rw [dWalk_eq α c hp]
    linarith
  · intro p hp
    have hp' : 2 ^ #(I.erase c) - 1 - p < 2 ^ #(I.erase c) := by omega
    rw [vPrime_high, vPrime_low α c V' hp']
    have hE := hV'.E _ hp'
    have e : 2 ^ #(I.erase c) - 1 - (2 ^ #(I.erase c) - 1 - p) = p := by omega
    rw [e] at hE
    simp only [X1]
    rw [dWalk_eq α c hp', e]
    linarith

/-- **(P3)** of Lemma P (`C8_theorem_F_potential.md`): `v'` is non-increasing on `[0, M)` and on
`[M, N)`. (Uses only (M) for `V'` and `c ∈ I`; no house condition.) -/
theorem lemma_P3 (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') :
    (∀ p q, p ≤ q → q < 2 ^ #(I.erase c) → vPrime I k ℓ α c V' q ≤ vPrime I k ℓ α c V' p) ∧
    (∀ p q, 2 ^ #(I.erase c) ≤ p → p ≤ q → q < 2 ^ #I →
      vPrime I k ℓ α c V' q ≤ vPrime I k ℓ α c V' p) := by
  have hN := card_erase_max hne hc
  have hA : (0 : ℤ) ≤ if Houses.typ ℓ c = 1 then (Houses.kap I k ℓ c : ℤ) else 0 := by
    split_ifs <;> simp
  have hB : (0 : ℤ) ≤ if Houses.typ ℓ c = 0 then (Houses.kap I k ℓ c : ℤ) else 0 := by
    split_ifs <;> simp
  constructor
  · intro p q hpq hq
    rw [vPrime_low α c V' hq, vPrime_low α c V' (by omega)]
    have h1 := hV'.M p q hpq hq
    have h2 : (JHseq (I.erase c) c (ℓ % 2 ^ c) p : ℤ) ≤ JHseq (I.erase c) c (ℓ % 2 ^ c) q := by
      exact_mod_cast JHseq_mono hpq hq
    nlinarith [mul_le_mul_of_nonneg_left h2 hA]
  · intro p q hp hpq hq
    obtain ⟨p₀, rfl⟩ := Nat.exists_eq_add_of_le hp
    obtain ⟨q₀, rfl⟩ := Nat.exists_eq_add_of_le (hp.trans hpq)
    have hq₀ : q₀ < 2 ^ #(I.erase c) := by omega
    rw [vPrime_high, vPrime_high]
    have h1 := hV'.M p₀ q₀ (by omega) hq₀
    have h2 : (JHseq (I.erase c) c (ℓ % 2 ^ c) p₀ : ℤ) ≤ JHseq (I.erase c) c (ℓ % 2 ^ c) q₀ := by
      exact_mod_cast JHseq_mono (by omega) hq₀
    nlinarith [mul_le_mul_of_nonneg_left h2 hB]

/-- **(P4)** of Lemma P (`C8_theorem_F_potential.md`): `v'(M) − v'(M − 1) = −X_1(M − 1)` and
`−X_1(M − 1) ≤ h − α`, `h = k − c`. (Uses `I ⊆ {0,…,k−1}`, `α ≥ 1` (for (Λ) of `H'`) and (E) for
`V'`; not `ℓ < 2^k`.) -/
theorem lemma_P4 (hI : ∀ t ∈ I, t < k) (hα : 1 ≤ α) (hne : I.Nonempty) (hc : c = I.max' hne)
    (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') :
    vPrime I k ℓ α c V' (2 ^ #(I.erase c)) - vPrime I k ℓ α c V' (2 ^ #(I.erase c) - 1) =
      -X1 I k ℓ α c (2 ^ #(I.erase c) - 1) ∧
    -X1 I k ℓ α c (2 ^ #(I.erase c) - 1) ≤ ((k - c : ℕ) : ℤ) - α := by
  have hcI : c ∈ I := hc ▸ I.max'_mem hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ I.le_max' t ht
  have hI' : ∀ t ∈ I.erase c, t < c := fun t ht =>
    lt_of_le_of_ne (hcmax t (mem_of_mem_erase ht)) (ne_of_mem_erase ht)
  have hMpos : 0 < 2 ^ #(I.erase c) := Nat.two_pow_pos _
  constructor
  · have := (lemma_P2 (k := k) hne hc hV').2 0 hMpos
    simpa using this
  · have hM1 : 2 ^ #(I.erase c) - 1 < 2 ^ #(I.erase c) := by omega
    have hΛ := theorem_F1_Lambda hI' (Nat.mod_lt ℓ (Nat.two_pow_pos c)) hα _ hM1
    have hJ0 := lemma_0f_J0 (I.erase c) (Nat.mod_lt ℓ (Nat.two_pow_pos c))
    have hJ1 := JHseq_le_one (I.erase c) c (ℓ % 2 ^ c) (2 ^ #(I.erase c) - 1)
    have hh := Houses.h_max hI hcI hcmax
    simp only [X1, yhat]
    rw [dWalk_eq α c hM1, Nat.sub_self, hJ0]
    simp only [Houses.tau, hh]
    have hA : (0 : ℤ) ≤ if Houses.typ ℓ c = 1 then (Houses.kap I k ℓ c : ℤ) else 0 := by
      split_ifs <;> simp
    have hJ1' : (JHseq (I.erase c) c (ℓ % 2 ^ c) (2 ^ #(I.erase c) - 1) : ℤ) ≤ 1 := by
      exact_mod_cast hJ1
    have habs := neg_abs_le (ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α)
      (2 ^ #(I.erase c) - 1))
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hJ1' hA]

/-- **Lemma P** (`C8_theorem_F_potential.md`), all four parts together, for every house with
`I ≠ ∅` and every potential `V'` for `H'`: (P1)–(P4). -/
theorem lemma_P (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty)
    (hc : c = I.max' hne) (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') :
    -- (P1)
    ((∀ p q, IsArrow I p q → p < 2 ^ #(I.erase c) → q < 2 ^ #(I.erase c) →
        vPrime I k ℓ α c V' p - vPrime I k ℓ α c V' q + ((k - c : ℕ) : ℤ) ≤ cHat I k ℓ α p q) ∧
      (∀ p q, IsArrow I p q → 2 ^ #(I.erase c) ≤ p → 2 ^ #(I.erase c) ≤ q →
        vPrime I k ℓ α c V' p - vPrime I k ℓ α c V' q + ((k - c : ℕ) : ℤ) ≤ cHat I k ℓ α p q) ∧
      (∀ p q, IsArrow I p q → 2 ^ #(I.erase c) ≤ p → q < 2 ^ #(I.erase c) →
        vPrime I k ℓ α c V' p - vPrime I k ℓ α c V' q ≤ cHat I k ℓ α p q) ∧
      (∀ p q, p < 2 ^ #(I.erase c) → 2 ^ #(I.erase c) ≤ q → ¬ IsArrow I p q)) ∧
    -- (P2)
    ((∀ p < 2 ^ #(I.erase c),
      vPrime I k ℓ α c V' p - vPrime I k ℓ α c V' (2 ^ #I - 1 - p) = X1 I k ℓ α c p) ∧
    (∀ p < 2 ^ #(I.erase c),
      vPrime I k ℓ α c V' (2 ^ #(I.erase c) + p) -
        vPrime I k ℓ α c V' (2 ^ #(I.erase c) - 1 - p) =
        -X1 I k ℓ α c (2 ^ #(I.erase c) - 1 - p))) ∧
    -- (P3)
    ((∀ p q, p ≤ q → q < 2 ^ #(I.erase c) → vPrime I k ℓ α c V' q ≤ vPrime I k ℓ α c V' p) ∧
    (∀ p q, 2 ^ #(I.erase c) ≤ p → p ≤ q → q < 2 ^ #I →
      vPrime I k ℓ α c V' q ≤ vPrime I k ℓ α c V' p)) ∧
    -- (P4)
    (vPrime I k ℓ α c V' (2 ^ #(I.erase c)) - vPrime I k ℓ α c V' (2 ^ #(I.erase c) - 1) =
      -X1 I k ℓ α c (2 ^ #(I.erase c) - 1) ∧
    -X1 I k ℓ α c (2 ^ #(I.erase c) - 1) ≤ ((k - c : ℕ) : ℤ) - α) :=
  ⟨⟨fun _ _ ha hp hq => lemma_P1_low hI hℓ hne hc hV' ha hp hq,
    fun _ _ ha hp hq => lemma_P1_high hI hℓ hne hc hV' ha hp hq,
    fun _ _ ha hp hq => lemma_P1_cross hI hℓ hne hc hV' ha hp hq,
    fun _ _ hp hq => lemma_P1_no_arrow hne hc hp hq⟩,
    lemma_P2 hne hc hV', lemma_P3 hne hc hV', lemma_P4 hI hα hne hc hV'⟩

end Potential
