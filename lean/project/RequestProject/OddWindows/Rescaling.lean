module

public import RequestProject.OddWindows.General

/-!
# `CSI12_the_odd_windows.md` — **(C1) Rescaling**

Namespace `ColouredSand.OddTwist`.  The digits are CSI11's list `ds` (`d_t = ds.getD t 0`,
`I = Iod ds`, every digit `< p`), and `aP p ds h` is CSI11's `q_h` (starting at `+1`).

**(C1)** `c^{(h)}(Δ) = a^{(p^h−1)/(p−1)} · aP h Δ · ∏_{t ∈ Δ} (−b_t (−p)^{1 + d_t (p^t − 1)/(p−1)})`
with `a = −1/p`, `b_t = (−1)^{p − d_t + 1}` (`C1_rescaling`).  The exponents `(p^t − 1)/(p − 1)`
are natural-number divisions; they are exact (`= 1 + p + ⋯ + p^{t−1}`, Mathlib's
`Nat.geomSum_eq`).  The same statement for CSI10's digits of `λ + 1` is `C1_lambda`
(`cW p (Iset p λ) (digitL p λ) = cW p (Iod (dsL p λ)) (getD (dsL p λ))`, `cW_lambda`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Finset

/-- `(p^{h+1} − 1)/(p − 1) = p · (p^h − 1)/(p − 1) + 1` for `p ≥ 2`. -/
lemma geom_succ {p : ℕ} (hp : 2 ≤ p) (h : ℕ) :
    (p ^ (h + 1) - 1) / (p - 1) = p * ((p ^ h - 1) / (p - 1)) + 1 := by
  rw [← Nat.geomSum_eq hp, ← Nat.geomSum_eq hp, sum_range_succ', mul_sum]
  simp [pow_succ, mul_comm]

/-- Rescaling of powers by a multiplicative weight: if `g(Γ) = λ F(Γ) ∏_{t∈Γ} y_t` then
`g^{⋆n}(Δ) = λ^n F^{⋆n}(Δ) ∏_{t∈Δ} y_t`. -/
lemma starPow_scale (F : Finset ℕ → ℚ) (y : ℕ → ℚ) (lam : ℚ) :
    ∀ n Δ, starPow (fun Γ => lam * F Γ * ∏ t ∈ Γ, y t) n Δ =
      lam ^ n * starPow F n Δ * ∏ t ∈ Δ, y t := by
  intro n
  induction n with
  | zero =>
    intro Δ
    by_cases hΔ : Δ = ∅
    · subst hΔ; simp [starPow]
    · simp [starPow, hΔ]
  | succ n ih =>
    intro Δ
    change Deficit.starMul _ (starPow _ n) Δ = lam ^ (n + 1) * Deficit.starMul F (starPow F n) Δ *
      ∏ t ∈ Δ, y t
    unfold Deficit.starMul
    rw [mul_sum, sum_mul]
    apply sum_congr rfl
    intro Δ₁ hΔ₁
    rw [ih, ← prod_sdiff (mem_powerset.1 hΔ₁)]
    ring

lemma cast_starPow_int (f : Finset ℕ → ℤ) (n : ℕ) (Γ : Finset ℕ) :
    ((starPow f n Γ : ℤ) : ℚ) = starPow (fun Γ => (f Γ : ℚ)) n Γ := by
  have := map_starPow (Int.castRingHom ℚ) f n Γ
  simpa using this

/-- **(C1) Rescaling** (*Part C* of `CSI12_the_odd_windows.md`): for `p ≥ 2` and digits `< p`
(CSI11's list `ds`, `I = Iod ds`),
`c^{(h)}(Δ) = a^{(p^h−1)/(p−1)} · aP h Δ · ∏_{t ∈ Δ} (−b_t (−p)^{1 + d_t (p^t − 1)/(p−1)})`,
`a = −1/p`, `b_t = (−1)^{p − d_t + 1}`.  (Oddness of `p` is not needed.) -/
theorem C1_rescaling {p : ℕ} (hp : 2 ≤ p) (ds : List ℕ) (hds : ∀ d ∈ ds, d < p) (h : ℕ)
    (Δ : Finset ℕ) :
    cW p (Iod ds) (fun t => ds.getD t 0) h Δ =
      (-1 / (p : ℚ)) ^ ((p ^ h - 1) / (p - 1)) * (aP p ds h Δ : ℚ) *
        ∏ t ∈ Δ, (-(bW p (fun t => ds.getD t 0) t) *
          (-(p : ℚ)) ^ (1 + ds.getD t 0 * ((p ^ t - 1) / (p - 1)))) := by
  set y : ℕ → ℚ := fun t => -(bW p (fun t => ds.getD t 0) t) *
    (-(p : ℚ)) ^ (1 + ds.getD t 0 * ((p ^ t - 1) / (p - 1))) with hy
  set a : ℚ := -1 / (p : ℚ) with ha
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hap : a * (-(p : ℚ)) = 1 := by rw [ha]; field_simp
  induction h generalizing Δ with
  | zero =>
    by_cases hΔ : Δ = ∅
    · subst hΔ; simp [cW, Q0_zero]
    · simp [cW, Q0_zero, hΔ]
  | succ h ih =>
    set E := (p ^ h - 1) / (p - 1) with hE
    have hcW : cW p (Iod ds) (fun t => ds.getD t 0) h =
        fun Γ => a ^ E * (aP p ds h Γ : ℚ) * ∏ t ∈ Γ, y t := funext ih
    have hpow : ∀ n Γ, starPow (cW p (Iod ds) (fun t => ds.getD t 0) h) n Γ =
        (a ^ E) ^ n * ((starPow (aP p ds h) n Γ : ℤ) : ℚ) * ∏ t ∈ Γ, y t := by
      intro n Γ
      rw [hcW, starPow_scale, cast_starPow_int]
    rw [geom_succ hp, ← hE]
    simp only [cW]
    rw [Q0_succ_I, hpow, xMul]
    push_cast
    by_cases hc : h ∈ Iod ds ∧ h ∈ Δ
    · obtain ⟨hI, hΔ⟩ := hc
      rw [if_pos hI, if_pos hΔ, hpow]
      have hw : ∏ t ∈ Δ, y t = y h * ∏ t ∈ Δ \ {h}, y t := by
        rw [sdiff_singleton_eq_erase, mul_prod_erase _ _ hΔ]
      have hd : ds.getD h 0 < p := by
        rw [mem_Iod_iff] at hI
        exact hds _ (by rw [List.getD_eq_getElem _ _ hI.1]; exact List.getElem_mem _)
      set d := ds.getD h 0 with hdd
      have hexp : p * E + 1 = (p - d) * E + (d * E + 1) := by
        have : p = (p - d) + d := by omega
        conv_lhs => rw [this]
        ring
      have key : bW p (fun t => ds.getD t 0) h * (a ^ E) ^ (p - d) =
          -(a ^ (p * E + 1) * y h) := by
        rw [hy]
        simp only
        rw [hexp, pow_add, ← pow_mul, show 1 + d * E = d * E + 1 by ring]
        have : a ^ (d * E + 1) * (-(p : ℚ)) ^ (d * E + 1) = 1 := by
          rw [← mul_pow, hap, one_pow]
        rw [mul_comm E (p - d)]
        linear_combination (-(bW p (fun t => ds.getD t 0) h * a ^ ((p - d) * E))) * this
      rw [hw, if_pos hΔ, ← ha]
      linear_combination
        (((starPow (aP p ds h) (p - d) (Δ \ {h}) : ℤ) : ℚ) * ∏ t ∈ Δ \ {h}, y t) * key
    · rw [not_and_or] at hc
      rcases hc with hc | hc
      · simp only [hc, if_false]
        rw [pow_succ', ← pow_mul]
        ring
      · simp only [hc, if_false]
        rw [pow_succ', ← pow_mul]
        ring

end ColouredSand.OddTwist
