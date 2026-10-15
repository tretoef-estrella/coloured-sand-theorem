module

public import RequestProject.AntitonicFit.Antisymmetry

/-!
# Lemma 7.3 (antisymmetric gluing)

This file formalizes **Lemma 7.3** of `C1_antitonic_fits.md`.  The antisymmetric sequence `x`
has length `2 * M` (`M` plays the role of `N'`), `Z_1 = fit M x` is `fit(x_{<N'})`,
`Z_2 = mirror M Z_1` its mirror-negative, `fit M (shift M x)` is `fit(x_{≥N'})`, and
`[max(Z_1, 0), min(Z_2, 0)]` is `concat M (fun i => max (Z_1 i) 0) (fun i => min (Z_2 i) 0)`.
-/

@[expose] public section

namespace AntitonicFit

open Finset

variable {M : ℕ}

lemma min_neg_zero_real (a : ℝ) : min (-a) 0 = -max a 0 := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, min_eq_right (by linarith), neg_zero]
  · rw [max_eq_left h, min_eq_left (by linarith)]

lemma min_neg_zero_int (a : ℤ) : min (-a) 0 = -max a 0 := by omega

/-- **Lemma 7.3** of `C1_antitonic_fits.md`, first claim: for `x` antisymmetric of length `2N'`,
`Z_2 = Z_1^* = fit(x_{≥N'})`. -/
theorem lemma_7_3_Z2 {x : ℕ → ℝ} (hx : IsAntisymm (2 * M) x) :
    ∀ j < M, mirror M (fit M x) j = fit M (shift M x) j := by
  have h1 : fit M (shift M x) = fit M (mirror M x) := fit_congr fun j hj => by
    have := hx (M - 1 - j) (by omega)
    rw [show 2 * M - 1 - (M - 1 - j) = M + j by omega] at this
    simp [shift, mirror, this]
  intro j hj
  rw [h1, fit_mirror x j hj]

/-- **Lemma 7.3** of `C1_antitonic_fits.md`, second claim: for `x` antisymmetric of length `2N'`,
`fit(x) = [max(Z_1, 0), min(Z_2, 0)]` (entrywise max and min). -/
theorem lemma_7_3_fit {x : ℕ → ℝ} (hx : IsAntisymm (2 * M) x) :
    ∀ j < 2 * M, fit (2 * M) x j =
      concat M (fun i => max (fit M x i) 0) (fun i => min (mirror M (fit M x) i) 0) j := by
  set Z1 := fit M x with hZ1_def
  set w := concat M (fun i => max (Z1 i) 0) (fun i => min (mirror M Z1 i) 0) with hw_def
  obtain ⟨hz, hle, htot, hdrop⟩ := fit_kkt M x
  have wlt : ∀ j < M, w j = max (Z1 j) 0 := fun j hj => by simp [hw_def, concat, hj]
  have wge : ∀ j, M ≤ j → w j = -max (Z1 (2 * M - 1 - j)) 0 := fun j hj => by
    simp only [hw_def, concat, if_neg (show ¬ j < M by omega), mirror]
    rw [show M - 1 - (j - M) = 2 * M - 1 - j by omega, min_neg_zero_real]
  have hw_anti : IsAntisymm (2 * M) w := by
    intro j hj
    by_cases hjM : j < M
    · rw [wge _ (by omega), wlt j hjM, show 2 * M - 1 - (2 * M - 1 - j) = j by omega]
    · rw [wlt _ (by omega), wge j (by omega), neg_neg]
  have hsum : ∀ n ≤ M, resid x w n = resid x Z1 n + ∑ j ∈ range n, (Z1 j - max (Z1 j) 0) := by
    intro n hn
    unfold resid
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [wlt j (by have := mem_range.1 hj; omega)]
    ring
  have hnonpos : ∀ n, ∑ j ∈ range n, (Z1 j - max (Z1 j) 0) ≤ 0 :=
    fun n => sum_nonpos fun j _ => by linarith [le_max_left (Z1 j) 0]
  have hsym : ∀ n ≤ 2 * M, resid x w (2 * M - n) = resid x w n :=
    fun n hn => resid_antisymm hx hw_anti hn
  have hlow : ∀ n ≤ M, resid x w n ≤ 0 := fun n hn => by
    rw [hsum n hn]; linarith [hle n hn, hnonpos n]
  -- drops in the first half
  have hdrop1 : ∀ s, s + 1 ≤ M → w (s + 1) < w s → resid x w (s + 1) = 0 := by
    intro s hs hlt
    rw [wlt s (by omega)] at hlt
    have hpos : 0 < Z1 s ∧ resid x Z1 (s + 1) = 0 := by
      rcases Nat.lt_or_ge (s + 1) M with h | h
      · rw [wlt _ h] at hlt
        have h1 : 0 < Z1 s := by
          by_contra hc; push_neg at hc
          rw [max_eq_right hc] at hlt; linarith [le_max_right (Z1 (s + 1)) 0]
        have h2 : Z1 (s + 1) < Z1 s := by
          by_contra hc; push_neg at hc
          linarith [max_le_max hc (le_refl (0 : ℝ))]
        exact ⟨h1, hdrop s h h2⟩
      · rw [wge _ (by omega), show 2 * M - 1 - (s + 1) = s by omega] at hlt
        have h1 : 0 < Z1 s := by
          by_contra hc; push_neg at hc
          rw [max_eq_right hc] at hlt; simp at hlt
        exact ⟨h1, by rw [show s + 1 = M by omega]; exact htot⟩
    rw [hsum _ hs, hpos.2, zero_add]
    refine sum_eq_zero fun j hj => ?_
    have : Z1 s ≤ Z1 j := hz.anti (by have := mem_range.1 hj; omega) (by omega)
    rw [max_eq_left (by linarith [hpos.1])]
    ring
  apply fit_eq_of_kkt
  refine ⟨fun i hi => ?_, fun n hn => ?_, ?_, fun s hs hlt => ?_⟩
  · -- `w` is non-increasing
    rcases lt_trichotomy (i + 1) M with h | h | h
    · rw [wlt _ h, wlt i (by omega)]
      exact max_le_max (hz i h) le_rfl
    · rw [wge _ h.ge, wlt i (by omega)]
      linarith [le_max_right (Z1 (2 * M - 1 - (i + 1))) 0, le_max_right (Z1 i) 0]
    · rw [wge _ (by omega), wge i (by omega), neg_le_neg_iff]
      exact max_le_max (hz.anti (by omega) (by omega)) le_rfl
  · by_cases hnM : n ≤ M
    · exact hlow n hnM
    · rw [← hsym n hn]; exact hlow _ (by omega)
  · rw [← hsym (2 * M) le_rfl, Nat.sub_self, resid_zero]
  · by_cases hsM : s + 1 ≤ M
    · exact hdrop1 s hsM hlt
    · have e1 := hw_anti s (by omega)
      have e2 := hw_anti (s + 1) (by omega)
      have h' := hdrop1 (2 * M - 2 - s) (by omega) (by
        rw [show 2 * M - 2 - s + 1 = 2 * M - 1 - s by omega, e1,
          show 2 * M - 2 - s = 2 * M - 1 - (s + 1) by omega, e2]
        linarith)
      rw [← hsym (s + 1) (by omega), show 2 * M - (s + 1) = 2 * M - 2 - s + 1 by omega]
      exact h'

theorem toR_antisymm {N : ℕ} {x : ℕ → ℤ} (hx : IsAntisymm N x) : IsAntisymm N (toR x) := by
  intro j hj; simp [toR, hx j hj]

/-- **Lemma 7.3** of `C1_antitonic_fits.md`, third claim: for an antisymmetric integer sequence
`x` of length `2N'`, with `X_1 = ifit(x_{<N'})` and `X_2 = X_1^*`,
`ifit(x) = [max(X_1, 0), min(X_2, 0)]`. -/
theorem lemma_7_3_ifit {x : ℕ → ℤ} (hx : IsAntisymm (2 * M) x) :
    ∀ j < 2 * M, ifit (2 * M) x j =
      concat M (fun i => max (ifit M x i) 0) (fun i => min (mirror M (ifit M x) i) 0) j := by
  have hxR := toR_antisymm hx
  set Z1 := fit M (toR x) with hZ1_def
  have hfit := lemma_7_3_fit hxR
  rw [← hZ1_def] at hfit
  have first : ∀ j < M, ifit (2 * M) x j = max (ifit M x j) 0 := by
    intro j hj
    by_cases hpos : 0 < Z1 j
    · have hL : levelSet (2 * M) (fit (2 * M) (toR x)) j = levelSet M Z1 j := by
        rw [levelSet_congr hfit (by omega)]
        ext i
        simp only [levelSet, mem_filter, mem_range, concat, if_pos hj, max_eq_left hpos.le]
        constructor
        · rintro ⟨hi, he⟩
          by_cases hiM : i < M
          · rw [if_pos hiM] at he
            refine ⟨hiM, ?_⟩
            by_contra hne
            have : Z1 i ≤ 0 := by
              by_contra hc; push_neg at hc; exact hne (by rw [max_eq_left hc.le] at he; exact he)
            rw [max_eq_right this] at he; linarith
          · rw [if_neg hiM] at he
            linarith [min_le_right (mirror M Z1 (i - M)) 0]
        · rintro ⟨hi, he⟩
          exact ⟨by omega, by rw [if_pos hi, he, max_eq_left hpos.le]⟩
      have heq : ifit (2 * M) x j = ifit M x j := by
        rw [ifit_of_lt (by omega), ifit_of_lt hj, hL]
      rw [heq, max_eq_left]
      rw [ifit_of_lt hj]
      apply blockF_nonneg
      have := sum_levelSet_fit_int (x := x) hj
      have h0 : (0 : ℝ) ≤ ((∑ i ∈ levelSet M (fit M (toR x)) j, x i : ℤ) : ℝ) := by
        rw [this]; exact mul_nonneg (Nat.cast_nonneg _) hpos.le
      exact_mod_cast h0
    · push_neg at hpos
      have hw : fit (2 * M) (toR x) j = 0 := by
        rw [hfit j (by omega)]; simp [concat, hj, max_eq_right hpos]
      have hS : (∑ i ∈ levelSet (2 * M) (fit (2 * M) (toR x)) j, x i) = 0 := by
        have := sum_levelSet_fit_int (x := x) (show j < 2 * M by omega)
        rw [hw, mul_zero] at this
        exact_mod_cast this
      have hX1 : ifit M x j ≤ 0 := by
        rw [ifit_of_lt hj]
        apply blockF_nonpos
        have := sum_levelSet_fit_int (x := x) hj
        have h0 : ((∑ i ∈ levelSet M (fit M (toR x)) j, x i : ℤ) : ℝ) ≤ 0 := by
          rw [this]; exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hpos
        exact_mod_cast h0
      rw [ifit_of_lt (by omega), hS, blockF_zero, max_eq_right hX1]
  intro j hj
  by_cases hjM : j < M
  · rw [first j hjM]; simp [concat, hjM]
  · have hA := A2 hx j hj
    rw [first _ (by omega)] at hA
    simp only [concat, if_neg hjM, mirror]
    rw [show M - 1 - (j - M) = 2 * M - 1 - j by omega, min_neg_zero_int, hA, neg_neg]

end AntitonicFit
