module

public import RequestProject.AntitonicFit.Cuts

/-!
# Antisymmetry: (A1), (A2), (A3)

This file formalizes the statements **(A1)**, **(A2)**, **(A3)** of the *Antisymmetry* paragraph
of `C1_antitonic_fits.md`.  We first prove the more general facts that `fit` and `ifit` commute
with the mirror-negation `u ↦ u^*` for *every* sequence (`fit_mirror`, `ifit_mirror`).
-/

@[expose] public section

namespace AntitonicFit

open Finset

variable {N : ℕ}

theorem mirror_mirror {α : Type*} [InvolutiveNeg α] (u : ℕ → α) {j : ℕ} (hj : j < N) :
    mirror N (mirror N u) j = u j := by
  simp [mirror, show N - 1 - (N - 1 - j) = j by omega]

theorem NonIncr.mirror {z : ℕ → ℝ} (hz : NonIncr N z) : NonIncr N (mirror N z) := by
  intro i hi
  simp only [AntitonicFit.mirror, neg_le_neg_iff]
  exact hz.anti (by omega) (by omega)

theorem sqDist_mirror (x y : ℕ → ℝ) : sqDist N (mirror N x) (mirror N y) = sqDist N x y := by
  unfold sqDist mirror
  rw [← sum_range_reflect (fun j => (x j - y j) ^ 2) N]
  exact sum_congr rfl fun j _ => by ring

theorem mirror_eq_of_antisymm {α : Type*} [InvolutiveNeg α] {x : ℕ → α} (hx : IsAntisymm N x) :
    ∀ j < N, mirror N x j = x j := by
  intro j hj
  have := hx (N - 1 - j) (by omega)
  rw [show N - 1 - (N - 1 - j) = j by omega] at this
  simp [mirror, this]

/-- General form of **(A1)** of `C1_antitonic_fits.md`: reversal plus negation commutes with
`fit`, i.e. `fit(x^*) = fit(x)^*`, for every sequence `x`. -/
theorem fit_mirror (x : ℕ → ℝ) : ∀ j < N, fit N (mirror N x) j = mirror N (fit N x) j := by
  apply fit_unique
  refine ⟨(fit_nonIncr N x).mirror, fun y hy => ?_⟩
  rw [sqDist_mirror,
    ← sqDist_congr (fun _ _ => rfl) (fun j hj => mirror_mirror y hj),
    sqDist_mirror (N := N) x (mirror N y)]
  exact (fit_isFit N x).2 _ hy.mirror

/-- **(A1)** of `C1_antitonic_fits.md`: if `x` is antisymmetric, then `fit(x)` is antisymmetric. -/
theorem A1 {x : ℕ → ℝ} (hx : IsAntisymm N x) : IsAntisymm N (fit N x) := by
  intro j hj
  have h1 : fit N (mirror N x) = fit N x := fit_congr (mirror_eq_of_antisymm hx)
  have := fit_mirror (N := N) x (N - 1 - j) (by omega)
  rw [h1] at this
  rw [this]
  simp [mirror, show N - 1 - (N - 1 - j) = j by omega]

theorem toR_mirror (x : ℕ → ℤ) : toR (mirror N x) = mirror N (toR x) := by
  funext j; simp [toR, mirror]

theorem IsLevelInterval.mirror {z : ℕ → ℝ} {p q : ℕ} (h : IsLevelInterval N z p q) :
    IsLevelInterval N (mirror N z) (N - 1 - q) (N - 1 - p) := by
  obtain ⟨hpq, hqN, hiff⟩ := h
  refine ⟨by omega, by omega, fun i hi => ?_⟩
  simp only [AntitonicFit.mirror, show N - 1 - (N - 1 - q) = q by omega, neg_inj]
  rw [(hiff q hqN).2 ⟨hpq, le_rfl⟩, hiff (N - 1 - i) (by omega)]
  omega

theorem sum_Icc_reflect (f : ℕ → ℤ) {p q : ℕ} (hpq : p ≤ q) (hqN : q < N) :
    ∑ i ∈ Icc (N - 1 - q) (N - 1 - p), f (N - 1 - i) = ∑ i ∈ Icc p q, f i := by
  apply sum_nbij' (fun i => N - 1 - i) (fun i => N - 1 - i)
  · intro a ha; simp only [mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [mem_Icc] at ha; omega
  · intro a ha; simp only [mem_Icc] at ha; omega
  · intro a _; rfl

/-- General form of **(A2)** of `C1_antitonic_fits.md`: for every integer sequence `x`,
`ifit(x^*) = ifit(x)^*`. -/
theorem ifit_mirror (x : ℕ → ℤ) : ∀ j < N, ifit N (mirror N x) j = mirror N (ifit N x) j := by
  intro j hj
  set j' := N - 1 - j with hj'
  obtain ⟨p, q, hpj, hjq, h⟩ := exists_levelInterval (fit_nonIncr N (toR x)) (show j' < N by omega)
  have hpq := h.1
  have hqN := h.2.1
  have hm : IsLevelInterval N (fit N (toR (mirror N x))) (N - 1 - q) (N - 1 - p) := by
    rw [toR_mirror]
    exact h.mirror.congr (fun i hi => (fit_mirror (toR x) i hi).symm)
  rw [ifit_eq_of_level hm (by omega) (by omega)]
  simp only [mirror]
  rw [ifit_eq_of_level h hpj hjq, sum_neg_distrib, sum_Icc_reflect x hpq hqN,
    show N - 1 - p - (N - 1 - q) + 1 = q - p + 1 by omega,
    show j - (N - 1 - q) = q - p + 1 - 1 - (j' - p) by omega]
  exact blockF_neg _ (by omega) (by omega)

/-- **(A2)** of `C1_antitonic_fits.md`: if `x` is an antisymmetric integer sequence, then
`ifit(x)` is antisymmetric. -/
theorem A2 {x : ℕ → ℤ} (hx : IsAntisymm N x) : IsAntisymm N (ifit N x) := by
  intro j hj
  have h1 : ifit N (mirror N x) = ifit N x := ifit_congr (mirror_eq_of_antisymm hx)
  have := ifit_mirror (N := N) x (N - 1 - j) (by omega)
  rw [h1] at this
  rw [this]
  simp [mirror, show N - 1 - (N - 1 - j) = j by omega]

/-- Prefix sums of an antisymmetric residual are symmetric: `Σ_{j<N−n} r_j = Σ_{j<n} r_j`. (Auxiliary result for (A3) and Lemma 7.3 of `C1_antitonic_fits.md`.) -/
theorem resid_antisymm {x z : ℕ → ℝ} (hx : IsAntisymm N x) (hz : IsAntisymm N z) {n : ℕ}
    (hn : n ≤ N) : resid x z (N - n) = resid x z n := by
  set r : ℕ → ℝ := fun j => x j - z j with hr
  have hr' : ∀ j < N, r (N - 1 - j) = -r j := by
    intro j hj; simp only [hr, hx j hj, hz j hj]; ring
  have htot : resid x z N = 0 := by
    have h1 : resid x z N = ∑ j ∈ range N, r (N - 1 - j) := (sum_range_reflect r N).symm
    rw [sum_congr rfl (fun j hj => hr' j (mem_range.1 hj)), sum_neg_distrib] at h1
    have : resid x z N = ∑ j ∈ range N, r j := rfl
    linarith
  have hsplit : resid x z N = resid x z (N - n) + ∑ k ∈ range n, r (N - n + k) := by
    unfold resid
    rw [← sum_range_add, show N - n + n = N by omega]
  have hlast : ∑ k ∈ range n, r (N - n + k) = -resid x z n := by
    rw [← sum_range_reflect, sum_congr rfl (fun k hk => by
      rw [show N - n + (n - 1 - k) = N - 1 - k by have := mem_range.1 hk; omega]),
      sum_congr rfl (fun k hk => hr' k (by have := mem_range.1 hk; omega)), sum_neg_distrib]
    rfl
  linarith

/-- **(A3)** of `C1_antitonic_fits.md`: let `x` be antisymmetric of length `N` and `0 < b < N`.
Then `x` is cut at `b` iff it is cut at `N − b`, and the cut at `b` is strict iff the cut at
`N − b` is. -/
theorem A3 {x : ℕ → ℝ} (hx : IsAntisymm N x) {b : ℕ} (hb0 : 0 < b) (hbN : b < N) :
    (IsCut N x b ↔ IsCut N x (N - b)) ∧ (IsStrictCut N x b ↔ IsStrictCut N x (N - b)) := by
  have hz := A1 hx
  have hres := resid_antisymm hx hz hbN.le
  have hcut : IsCut N x b ↔ IsCut N x (N - b) := by
    rw [isCut_iff_resid, isCut_iff_resid, hres]
    constructor
    · rintro ⟨-, -, h⟩; exact ⟨by omega, by omega, h⟩
    · rintro ⟨-, -, h⟩; exact ⟨hb0, hbN, h⟩
  refine ⟨hcut, ?_⟩
  have e1 := hz (b - 1) (by omega)
  have e2 := hz b hbN
  rw [show N - 1 - (b - 1) = N - b by omega] at e1
  rw [show N - 1 - b = N - b - 1 by omega] at e2
  unfold IsStrictCut
  rw [hcut, e1, e2]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

end AntitonicFit
