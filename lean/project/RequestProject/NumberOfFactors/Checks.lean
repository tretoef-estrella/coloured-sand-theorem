module

public import RequestProject.NumberOfFactors.TheoremD

/-!
# (D4) Checks

This file corresponds to **(D4) Checks** of `CS5_theorem_D_number_of_factors.md`.  The values are
computed from the closed forms `rho p m` (`ρ_p(m)`, `RequestProject/NumberOfFactors/RankModP.lean`)
and `nFactors p d q` (`N`, `RequestProject/NumberOfFactors/TheoremD.lean`) by `decide` (kernel
evaluation, no `native_decide`), not by computing groups.  Combined with `theorem_D`, the first
check gives the number of cyclic factors of `Syl_3 K(H(d,3))` for `d = 1, …, 6`
(`cyclic_factors_three`).
-/

@[expose] public section

open Finset Module

namespace ColouredSand.NumberOfFactors

open TensorProduct ColouredSand.Strings ColouredSand.TheoremB

/-- `q = p = 3`: `N = 1, 4, 12, 34, 96, 274` for `d = 1, …, 6`. -/
theorem nFactors_three :
    [nFactors 3 1 3, nFactors 3 2 3, nFactors 3 3 3, nFactors 3 4 3, nFactors 3 5 3,
      nFactors 3 6 3] = [1, 4, 12, 34, 96, 274] := by
  decide

/-- `ρ_3(m) = 1, 2, 5, 10, 21, 42` for `m = 1, …, 6`. -/
theorem rho_three :
    [rho 3 1, rho 3 2, rho 3 3, rho 3 4, rho 3 5, rho 3 6] = [1, 2, 5, 10, 21, 42] := by
  decide

/-- `ρ_2(m) = 1, 2, 4, 8, 16` for `m = 1, …, 5`. -/
theorem rho_two : [rho 2 1, rho 2 2, rho 2 3, rho 2 4, rho 2 5] = [1, 2, 4, 8, 16] := by
  decide

/-- With Theorem D: the number of cyclic factors of `Syl_3 K(H(d,3))`, i.e.
`dim_{𝔽_3} (𝔽_3 ⊗ Syl_3 K(H(d,3)))`, is `1, 4, 12, 34, 96, 274` for `d = 1, …, 6`. -/
theorem cyclic_factors_three :
    [finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile 1 3) 3),
      finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile 2 3) 3),
      finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile 3 3) 3),
      finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile 4 3) 3),
      finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile 5 3) 3),
      finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile 6 3) 3)] =
      [1, 4, 12, 34, 96, 274] := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simp only [theorem_D 3 _ 3 (by norm_num) dvd_rfl]
  exact nFactors_three

/-! ### `p > m` -/

/-- `∑_{i ≤ t} (C(m,i) − C(m,i−1)) = C(m,t)` for `2t + 1 ≤ m`. -/
lemma sum_strMult {m t : ℕ} (ht : 2 * t + 1 ≤ m) :
    ∑ i ∈ range (t + 1), strMult m i = m.choose t := by
  induction t with
  | zero => simp [strMult]
  | succ t ih =>
    rw [sum_range_succ, ih (by omega), strMult, if_neg (by omega), Nat.add_sub_cancel]
    have : m.choose t ≤ m.choose (t + 1) := Nat.choose_le_succ_of_lt_half_left (by omega)
    omega

lemma rPart_of_lt {p m s : ℕ} (hpm : m < p) (hs : s < m) :
    rPart p m s = if 2 * s ≤ m - 1 then m.choose s else m.choose (s + 1) := by
  unfold rPart
  dsimp only
  have hfilt : ∀ t, t + 1 ≤ m →
      (range (t + 1)).filter (fun i => ¬ p ∣ (t + 1 - i)) = range (t + 1) := by
    intro t ht
    rw [filter_eq_self]
    intro i hi hdvd
    have hi' := mem_range.mp hi
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  split_ifs with h
  · rw [hfilt s (by omega), sum_strMult (by omega)]
  · rw [hfilt (m - 1 - s) (by omega), sum_strMult (by omega),
      show m - 1 - s = m - (s + 1) by omega, Nat.choose_symm (by omega)]

/-- **(D4), `p > m`.**  If `p > m`, all diagonal entries `k − i` are units mod `p` and
`ρ_p(m) = 2^m − C(m, ⌊m/2⌋)`. -/
theorem rho_of_lt {p m : ℕ} (hpm : m < p) : rho p m = 2 ^ m - m.choose (m / 2) := by
  set n := (m + 1) / 2 with hn
  have hsplit : rho p m = ∑ s ∈ range n, m.choose s + ∑ x ∈ range (m - n), m.choose (n + x + 1) := by
    rw [rho, show m = n + (m - n) by omega, sum_range_add, ← show m = n + (m - n) by omega]
    congr 1
    · refine sum_congr rfl fun s hs => ?_
      have := mem_range.mp hs
      rw [rPart_of_lt hpm (by omega), if_pos (by omega)]
    · refine sum_congr rfl fun x hx => ?_
      have := mem_range.mp hx
      rw [rPart_of_lt hpm (by omega), if_neg (by omega)]
  have htot : 2 ^ m = ∑ s ∈ range n, m.choose s + m.choose n +
      ∑ x ∈ range (m - n), m.choose (n + x + 1) := by
    rw [← Nat.sum_range_choose, show m + 1 = (n + 1) + (m - n) by omega, sum_range_add,
      sum_range_succ]
    congr 1
    exact sum_congr rfl fun x _ => by rw [Nat.add_right_comm]
  have hmid : m.choose n = m.choose (m / 2) := by
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · congr 1; omega
    · rw [show m / 2 = m - n by omega, Nat.choose_symm (by omega)]
  rw [hsplit, htot, hmid]
  omega

end ColouredSand.NumberOfFactors
