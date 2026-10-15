module

public import RequestProject.Deficit.DeficitLaw

/-!
# Part C of `C10_deficit_law.md`: the closed form (Theorem D, the valuations)

(C1) the window, (C2) integrality and valuation of `Mc(D, D')`.  `Mc I k α i D D'` is defined in
`RequestProject/Deficit/Basic.lean`; `K = 2^k`, `o_E = Rulers.oE E`, `δ = Rulers.delta k`,
`v_2(i + d) = Rulers.v2 (i + d)` (`= padicValNat 2 (i + d)`), and the valuation of the rational
`Mc(D, D')` is `padicValRat 2`.
-/

@[expose] public section

namespace Deficit

open Finset

/-- **(C1) Window** (`C10_deficit_law.md`, Part C): for `D' ⊆ D ⊆ I ⊆ {0, …, k − 1}`,
`o_{D'} + K − o_D = K − o(D ∖ D') ≥ 1` (in `ℤ`), so the window `[o_D, o_{D'} + K − 1]` is
non-empty.  (Uses Lemma 5.0 of C3, `Rulers.lemma_5_0_sdiff`.) -/
theorem C1_window {k : ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) {D D' : Finset ℕ}
    (hD' : D' ⊆ D) (hD : D ⊆ I) :
    (Rulers.oE D' : ℤ) + 2 ^ k - Rulers.oE D = 2 ^ k - Rulers.oE (D \ D') ∧
      1 ≤ (2 : ℤ) ^ k - Rulers.oE (D \ D') := by
  obtain ⟨h1, h2⟩ := Rulers.lemma_5_0_sdiff hI hD' hD
  exact ⟨by rw [h1]; ring, h2⟩

lemma padicValNat_prod_eq_sum (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ d ∈ s, f d ≠ 0) :
    padicValNat 2 (∏ d ∈ s, f d) = ∑ d ∈ s, padicValNat 2 (f d) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [prod_insert hx, sum_insert hx, padicValNat.mul (hf x (mem_insert_self _ _))
      (prod_ne_zero_iff.2 (fun d hd => hf d (mem_insert_of_mem hd))),
      ih (fun d hd => hf d (mem_insert_of_mem hd))]

/-- **(C2) Integrality and valuation** (`C10_deficit_law.md`, Part C): let `k ≥ 1`,
`I ⊆ {0, …, k − 1}`, `α ≥ 1`, `i ∈ ℕ` and `D' ⊆ D ⊆ I` with `0 < i + o_D`.  Then `Mc(D, D')` is a
non-zero integer (there is `z ∈ ℤ`, `z ≠ 0`, with `Mc(D, D') = z`), and
`v_2(Mc(D, D')) = 1 − K + o(D ∖ D') + δ(D ∖ D') + Σ_{d = o_D}^{o_{D'} + K − 1} (α + v_2(i + d))`
as integers, `v_2 = padicValRat 2` on the left. -/
theorem C2_integrality_valuation {k : ℕ} (hk : 1 ≤ k) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k)
    {α : ℤ} (hα : 1 ≤ α) (i : ℕ) {D D' : Finset ℕ} (hD' : D' ⊆ D) (hD : D ⊆ I)
    (hi : 0 < i + Rulers.oE D) :
    (∃ z : ℤ, z ≠ 0 ∧ Mc I k α i D D' = z) ∧
      padicValRat 2 (Mc I k α i D D') =
        1 - (2 : ℤ) ^ k + Rulers.oE (D \ D') + Rulers.delta k (D \ D') +
          ∑ d ∈ Ico (Rulers.oE D) (Rulers.oE D' + 2 ^ k), (α + (Rulers.v2 (i + d) : ℤ)) := by
  set Δ := D \ D' with hΔ
  set W := Ico (Rulers.oE D) (Rulers.oE D' + 2 ^ k) with hW
  set n : ℕ := Rulers.oE D' + 2 ^ k - Rulers.oE D with hn
  obtain ⟨hwin, hwin1⟩ := C1_window hI hD' hD
  have hle : Rulers.oE D ≤ Rulers.oE D' + 2 ^ k := by zify; omega
  have hnZ : (n : ℤ) = 2 ^ k - Rulers.oE Δ := by
    rw [hn, Nat.cast_sub hle]; push_cast; omega
  have hcard : W.card = n := by rw [hW, Nat.card_Ico]
  obtain ⟨ha0, hav⟩ := lemma_4_5 hk hI (sdiff_subset.trans hD : Δ ⊆ I)
  -- the product of the `i + d`
  set N : ℕ := ∏ d ∈ W, (i + d) with hN
  have hNd : ∀ d ∈ W, i + d ≠ 0 := by
    intro d hd; rw [hW, mem_Ico] at hd; omega
  have hN0 : N ≠ 0 := prod_ne_zero_iff.2 hNd
  have hprod : ∏ d ∈ W, pi0 α i d = (2 : ℚ) ^ (α * n) * (N : ℚ) := by
    simp only [pi0, prod_mul_distrib, prod_const, hcard, hN]
    push_cast
    rw [← zpow_natCast, ← zpow_mul]
  -- the exponent of `2`
  set E : ℤ := 1 + (α - 1) * (2 ^ k - Rulers.oE Δ) with hE
  have hE0 : 0 ≤ E := by
    have : 0 ≤ (α - 1) * (2 ^ k - Rulers.oE Δ) := mul_nonneg (by omega) (by omega)
    omega
  have hEexp : (1 : ℤ) - 2 ^ k + Rulers.oE Δ + α * n = (E.toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hE0, hE, hnZ]; ring
  have hMc : Mc I k α i D D' = (((-(2 ^ E.toNat * a I k Δ * (N : ℤ))) : ℤ) : ℚ) := by
    rw [Mc, ← hΔ, ← hW, hprod]
    have : (2 : ℚ) ^ ((1 : ℤ) - 2 ^ k + Rulers.oE Δ) * (2 : ℚ) ^ (α * n) =
        (2 : ℚ) ^ E.toNat := by
      rw [← zpow_add₀ (by norm_num), hEexp, zpow_natCast]
    push_cast
    linear_combination (-(↑(a I k Δ) * (N : ℚ))) * this
  have h2E : (2 : ℤ) ^ E.toNat ≠ 0 := pow_ne_zero _ two_ne_zero
  have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast hN0
  have hz0 : -(2 ^ E.toNat * a I k Δ * (N : ℤ)) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero h2E ha0) hNZ)
  refine ⟨⟨_, hz0, hMc⟩, ?_⟩
  rw [hMc, Int.cast_neg, padicValRat.neg, padicValRat.of_int, padicValInt.mul (mul_ne_zero h2E ha0) hNZ,
    padicValInt.mul h2E ha0, padicValInt.of_nat, hN, padicValNat_prod_eq_sum W _ hNd]
  have h1 : padicValInt 2 ((2 : ℤ) ^ E.toNat) = E.toNat := by
    have : ((2 : ℤ) ^ E.toNat) = ((2 ^ E.toNat : ℕ) : ℤ) := by push_cast; rfl
    rw [this, padicValInt.of_nat, padicValNat.prime_pow]
  rw [h1, sum_add_distrib, sum_const, hcard]
  simp only [Nat.cast_add, Nat.cast_sum]
  rw [← hav, ← hEexp]
  simp only [Rulers.v2, nsmul_eq_mul]
  ring

end Deficit
