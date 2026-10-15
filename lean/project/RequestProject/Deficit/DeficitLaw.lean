module

public import RequestProject.Deficit.Polynomials

/-!
# Part A of `C10_deficit_law.md`, continued: Lemma 4.5 (the deficit law), (A4), (A5)

The deficit `δ` is `Rulers.delta k` and `min` (with `min ∅ = k`) is `Rulers.minOr k`
(piece C3).  The hypothesis `I ⊆ {0, …, k − 1}` is `hI : ∀ t ∈ I, t < k`.
-/

@[expose] public section

namespace Deficit

open Finset

lemma minOr_of_nonempty (k : ℕ) {Δ : Finset ℕ} (h : Δ.Nonempty) :
    Rulers.minOr k Δ = Δ.min' h := by
  simp [Rulers.minOr, h]

/-- **Lemma 4.5 (the deficit law)** (`C10_deficit_law.md`, Part A): for `k ≥ 1`,
`I ⊆ {0, …, k − 1}` and every `Δ ⊆ I`: `a_k(Δ) ≠ 0` and `v_2(a_k(Δ)) = δ(Δ)` as integers. -/
theorem lemma_4_5 {k : ℕ} (hk : 1 ≤ k) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) {Δ : Finset ℕ}
    (hΔ : Δ ⊆ I) : a I k Δ ≠ 0 ∧ (padicValInt 2 (a I k Δ) : ℤ) = Rulers.delta k Δ := by
  rcases Δ.eq_empty_or_nonempty with rfl | h
  · rw [A2_const I k hk]; simp [Rulers.delta]
  · obtain ⟨hle, hne, hv⟩ := A3_deficit I k Δ h hΔ (hI _ (hΔ (max'_mem Δ h)))
    refine ⟨hne, ?_⟩
    rw [hv, Rulers.delta, if_neg h.ne_empty, minOr_of_nonempty k h]
    omega

/-- **Lemma 4.5**, "in particular" (`C10_deficit_law.md`, Part A): `a_k(∅) = 1` for `k ≥ 1`
(the hypothesis `I ⊆ {0, …, k − 1}` is not needed). -/
theorem lemma_4_5_empty {k : ℕ} (hk : 1 ≤ k) (I : Finset ℕ) : a I k ∅ = 1 :=
  A2_const I k hk

/-- **Lemma 4.5**, "in particular" (`C10_deficit_law.md`, Part A): for `k ≥ 1`,
`I ⊆ {0, …, k − 1}` and non-empty `Δ ⊆ I`, `v_2(a_k(Δ)) = k − |Δ| − min Δ` (in `ℤ`). -/
theorem lemma_4_5_nonempty {k : ℕ} (hk : 1 ≤ k) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k)
    {Δ : Finset ℕ} (hΔ : Δ ⊆ I) (h : Δ.Nonempty) :
    (padicValInt 2 (a I k Δ) : ℤ) = (k : ℤ) - Δ.card - Δ.min' h := by
  rw [(lemma_4_5 hk hI hΔ).2, Rulers.delta, if_neg h.ne_empty, minOr_of_nonempty k h]

/-- **Lemma 4.5**, last sentence (`C10_deficit_law.md`, Part A): `v_2(a_k(Δ))` depends only on
`k` and `Δ`, not on the other elements of `I`: for two families `I, J ⊆ {0, …, k − 1}`
containing `Δ`, the valuations agree. -/
theorem lemma_4_5_indep {k : ℕ} (hk : 1 ≤ k) {I J : Finset ℕ} (hI : ∀ t ∈ I, t < k)
    (hJ : ∀ t ∈ J, t < k) {Δ : Finset ℕ} (hΔI : Δ ⊆ I) (hΔJ : Δ ⊆ J) :
    padicValInt 2 (a I k Δ) = padicValInt 2 (a J k Δ) := by
  have h1 := (lemma_4_5 hk hI hΔI).2
  have h2 := (lemma_4_5 hk hJ hΔJ).2
  omega

/-- **(A4) Strict subadditivity** (`C10_deficit_law.md`, Part A): for non-empty disjoint
`Δ₁, Δ₂ ⊆ {0, …, k − 1}`,
`δ(Δ₁) + δ(Δ₂) − δ(Δ₁ ∪ Δ₂) = k − max(min Δ₁, min Δ₂) ≥ 1` (in `ℤ`). -/
theorem A4_subadditivity {k : ℕ} {Δ₁ Δ₂ : Finset ℕ} (h1 : Δ₁.Nonempty) (h2 : Δ₂.Nonempty)
    (hd : Disjoint Δ₁ Δ₂) (hs1 : ∀ t ∈ Δ₁, t < k) (hs2 : ∀ t ∈ Δ₂, t < k) :
    Rulers.delta k Δ₁ + Rulers.delta k Δ₂ - Rulers.delta k (Δ₁ ∪ Δ₂) =
        (k : ℤ) - (max (Rulers.minOr k Δ₁) (Rulers.minOr k Δ₂) : ℕ) ∧
      1 ≤ (k : ℤ) - (max (Rulers.minOr k Δ₁) (Rulers.minOr k Δ₂) : ℕ) := by
  have h12 : (Δ₁ ∪ Δ₂).Nonempty := h1.mono subset_union_left
  have hmin : (Δ₁ ∪ Δ₂).min' h12 = min (Δ₁.min' h1) (Δ₂.min' h2) := by
    apply le_antisymm
    · rcases le_total (Δ₁.min' h1) (Δ₂.min' h2) with h | h
      · rw [min_eq_left h]; exact min'_le _ _ (mem_union_left _ (min'_mem _ _))
      · rw [min_eq_right h]; exact min'_le _ _ (mem_union_right _ (min'_mem _ _))
    · apply le_min'
      intro y hy
      rcases mem_union.1 hy with hy | hy
      · exact (min_le_left _ _).trans (min'_le _ _ hy)
      · exact (min_le_right _ _).trans (min'_le _ _ hy)
  have hm1 := hs1 _ (min'_mem Δ₁ h1)
  have hm2 := hs2 _ (min'_mem Δ₂ h2)
  simp only [Rulers.delta, if_neg h1.ne_empty, if_neg h2.ne_empty, if_neg h12.ne_empty,
    minOr_of_nonempty k h1, minOr_of_nonempty k h2, minOr_of_nonempty k h12, hmin,
    card_union_of_disjoint hd]
  constructor
  · rcases le_total (Δ₁.min' h1) (Δ₂.min' h2) with h | h
    · rw [min_eq_left h, max_eq_right h]; push_cast; ring
    · rw [min_eq_right h, max_eq_left h]; push_cast; ring
  · rcases le_total (Δ₁.min' h1) (Δ₂.min' h2) with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega

/-- **(A5) Example `λ = 6`** (`C10_deficit_law.md`, Part A), first half: for `I = {0, 1}`,
`a_1(∅) = 1` and `a_1({0}) = 1` (`q_1 = 1 + y_0`). -/
theorem A5_q1 : a {0, 1} 1 ∅ = 1 ∧ a {0, 1} 1 {0} = 1 := by decide

/-- **(A5) Example `λ = 6`** (`C10_deficit_law.md`, Part A), second half: for `I = {0, 1}`,
`a_2(∅) = 1`, `a_2({0}) = 2`, `a_2({1}) = −1`, `a_2({0, 1}) = −1`
(`q_2 = 1 + 2y_0 − y_1 − y_0 y_1`). -/
theorem A5_q2 : a {0, 1} 2 ∅ = 1 ∧ a {0, 1} 2 {0} = 2 ∧ a {0, 1} 2 {1} = -1 ∧
    a {0, 1} 2 {0, 1} = -1 := by decide

end Deficit
