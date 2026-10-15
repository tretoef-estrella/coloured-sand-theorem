module

public import RequestProject.Deficit.Basic

/-!
# Part B of `C10_deficit_law.md`: the rescaling (end of the proof of Theorem 4.4)

(B1): `c_h(Δ) = −2^{1 − 2^h} · 2^{o(Δ)} · a_h(Δ)` in `ℚ`, the power `2^{1 − 2^h}` an integer
power.  The encoding is described in `RequestProject/Deficit/Basic.lean`.
-/

@[expose] public section

namespace Deficit

open Finset

lemma two_zpow_one_sub (n : ℕ) : (2 : ℚ) ^ ((1 : ℤ) - (2 : ℤ) ^ n) = 2 * ((2 : ℚ) ^ (2 ^ n))⁻¹ := by
  rw [zpow_sub₀ (by norm_num), zpow_one, div_eq_mul_inv]
  congr 2

/-- **(B1)** (`C10_deficit_law.md`, Part B): for every `h` and every `Δ`,
`c_h(Δ) = −2^{1 − 2^h} · 2^{o(Δ)} · a_h(Δ)` in `ℚ` (no hypothesis on `I` is needed). -/
theorem B1_rescaling (I : Finset ℕ) (h : ℕ) (Δ : Finset ℕ) :
    c I h Δ = -(2 : ℚ) ^ ((1 : ℤ) - 2 ^ h) * 2 ^ (Rulers.oE Δ) * (a I h Δ : ℚ) := by
  induction h generalizing Δ with
  | zero =>
    by_cases hΔ : Δ = ∅
    · subst hΔ; simp [c, a, Rulers.oE]
    · simp [c, a, hΔ]
  | succ h ih =>
    set X : ℚ := (2 : ℚ) ^ (2 ^ h) with hX
    have hX0 : X ≠ 0 := pow_ne_zero _ two_ne_zero
    have hz : (2 : ℚ) ^ ((1 : ℤ) - 2 ^ h) = 2 * X⁻¹ := two_zpow_one_sub h
    have hz' : (2 : ℚ) ^ ((1 : ℤ) - 2 ^ (h + 1)) = 2 * (X ^ 2)⁻¹ := by
      rw [two_zpow_one_sub (h + 1), hX, ← pow_mul, pow_succ]
    have hstar : starMul (c I h) (c I h) Δ =
        (2 * X⁻¹) ^ 2 * 2 ^ (Rulers.oE Δ) * ((starMul (a I h) (a I h) Δ : ℤ) : ℚ) := by
      unfold starMul
      push_cast
      rw [mul_sum]
      apply sum_congr rfl
      intro Δ₁ hΔ₁
      rw [mem_powerset] at hΔ₁
      rw [ih, ih, hz, ← Rulers.oE_sdiff hΔ₁, pow_add]
      ring
    have hsing : (if h ∈ I then (1 : ℚ) else 0) * (if h ∈ Δ then 1 else 0) * c I h (Δ \ {h}) =
        -(2 * X⁻¹) * 2 ^ (Rulers.oE Δ) * X⁻¹ *
          (((if h ∈ I then (1 : ℤ) else 0) * (if h ∈ Δ then 1 else 0) * a I h (Δ \ {h}) : ℤ) : ℚ)
          := by
      by_cases hh : h ∈ Δ
      · rw [ih, hz, ← Rulers.oE_sdiff (singleton_subset_iff.2 hh)]
        simp only [Rulers.oE, sum_singleton, pow_add, if_pos hh]
        rw [← hX]
        push_cast
        field_simp
      · simp [hh]
    rw [c, a, hstar, hsing, hz']
    push_cast
    field_simp
    ring

end Deficit
