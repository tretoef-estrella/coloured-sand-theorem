module

public import RequestProject.AntitonicFit.Characterization

/-!
# The integer fit and consequence (L)

This file formalizes the *Definition (integer fit)* of `C1_antitonic_fits.md` and the
consequence **(L)** of Lemma 7.1.

## Encoding of the integer fit

* An integer sequence is a function `x : ℕ → ℤ`; `toR x` is the same sequence viewed in `ℝ`,
  and `fit(x)` is `fit N (toR x)`.
* For a position `j < N`, let `L = levelSet N (fit N (toR x)) j` be its level set,
  `P = |L|` its number of positions and `S = Σ_{i ∈ L} x_i` (an integer).  The positions of
  `L` are ordered increasingly; the rank of `j` in `L` is `#{i ∈ L : i < j}`, so that "`j` is
  among the first `S mod P` positions of `L`" means `rank < S mod P`.  Then
  `ifit N x j = ⌈S/P⌉` if `rank < S mod P`, and `⌊S/P⌋` otherwise (`blockF S P rank`), where
  `S mod P = S % P` is the non-negative remainder (`Int.emod`) and `⌈S/P⌉, ⌊S/P⌋` are the ceiling
  and floor of the real number `S/P`.  At positions `j ≥ N`, `ifit N x j = 0`.
* By `levelSet_isInterval`, `L` is an interval `[p, q]` and the rank of `j` is `j − p`
  (`ifit_eq_of_level`), so this is exactly the rule of the file.  The integer fit is *not*
  claimed to be non-increasing (see `RequestProject/AntitonicFit/Examples.lean` for a
  counterexample).
-/

@[expose] public section

namespace AntitonicFit

open Finset

/-- *Definition (integer fit)* of `C1_antitonic_fits.md`: an integer sequence viewed as a real
sequence. -/
def toR (x : ℕ → ℤ) : ℕ → ℝ := fun j => (x j : ℝ)

/-- *Definition (integer fit)* of `C1_antitonic_fits.md`: on a level set with `P` positions and
sum `S`, the value at the position of rank `k` (counting from `0`) is `⌈S/P⌉` if
`k < S mod P` and `⌊S/P⌋` otherwise. -/
noncomputable def blockF (S : ℤ) (P k : ℕ) : ℤ :=
  if (k : ℤ) < S % (P : ℤ) then ⌈(S : ℝ) / P⌉ else ⌊(S : ℝ) / P⌋

/-- *Definition (integer fit)* of `C1_antitonic_fits.md`: `ifit N x` for an integer sequence `x`
of length `N`.  At `j < N`, with `L` the level set of `j` in `fit(x)`, `P = |L|`,
`S = Σ_{i∈L} x_i` and `rank = #{i ∈ L : i < j}`, the value is `blockF S P rank`. -/
noncomputable def ifit (N : ℕ) (x : ℕ → ℤ) (j : ℕ) : ℤ :=
  if j < N then
    blockF (∑ i ∈ levelSet N (fit N (toR x)) j, x i) (levelSet N (fit N (toR x)) j).card
      ((levelSet N (fit N (toR x)) j).filter (· < j)).card
  else 0

theorem toR_add (x δ : ℕ → ℤ) : toR (x + δ) = toR x + toR δ := by
  funext j; simp [toR]

lemma emod_facts (S : ℤ) {P : ℕ} (hP : 0 < P) :
    0 ≤ S % (P : ℤ) ∧ S % (P : ℤ) < P ∧ (P : ℤ) * (S / P) + S % P = S :=
  ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega), Int.mul_ediv_add_emod S P⟩

theorem floor_div_eq (S : ℤ) {P : ℕ} (hP : 0 < P) : ⌊(S : ℝ) / P⌋ = S / P := by
  obtain ⟨h2, h3, h1⟩ := emod_facts S hP
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have h1' : ((P : ℤ) : ℝ) * ((S / P : ℤ) : ℝ) + ((S % P : ℤ) : ℝ) = S := by exact_mod_cast h1
  have h2' : (0 : ℝ) ≤ ((S % P : ℤ) : ℝ) := by exact_mod_cast h2
  have h3' : ((S % P : ℤ) : ℝ) < ((P : ℤ) : ℝ) := by exact_mod_cast h3
  push_cast at h1' h3'
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hP']; nlinarith
  · rw [div_lt_iff₀ hP']; nlinarith

theorem ceil_div_eq (S : ℤ) {P : ℕ} (hP : 0 < P) :
    ⌈(S : ℝ) / P⌉ = S / P + if S % (P : ℤ) = 0 then 0 else 1 := by
  obtain ⟨h2, h3, h1⟩ := emod_facts S hP
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have h1' : ((P : ℤ) : ℝ) * ((S / P : ℤ) : ℝ) + ((S % P : ℤ) : ℝ) = S := by exact_mod_cast h1
  push_cast at h1'
  rw [Int.ceil_eq_iff]
  split_ifs with h
  · rw [h] at h1'
    push_cast at h1' ⊢
    constructor
    · rw [lt_div_iff₀ hP']; nlinarith
    · rw [div_le_iff₀ hP']; nlinarith
  · have h4 : (1 : ℤ) ≤ S % P := by omega
    have h4' : (1 : ℝ) ≤ ((S % P : ℤ) : ℝ) := by exact_mod_cast h4
    have h3' : ((S % P : ℤ) : ℝ) < ((P : ℤ) : ℝ) := by exact_mod_cast h3
    push_cast at h3' ⊢
    constructor
    · rw [lt_div_iff₀ hP']; nlinarith
    · rw [div_le_iff₀ hP']; nlinarith

/-- Arithmetic form of the block rule: `blockF S P k = ⌊S/P⌋ + [k < S mod P]`. (Auxiliary result for *Definition (integer fit)* of `C1_antitonic_fits.md`.) -/
theorem blockF_eq (S : ℤ) {P : ℕ} (hP : 0 < P) (k : ℕ) :
    blockF S P k = S / P + if (k : ℤ) < S % (P : ℤ) then 1 else 0 := by
  unfold blockF
  split_ifs with h
  · rw [ceil_div_eq S hP, if_neg (by omega)]
  · rw [floor_div_eq S hP, add_zero]

lemma sum_range_ite_lt (r : ℤ) (hr : 0 ≤ r) (n : ℕ) :
    ∑ k ∈ range n, (if (k : ℤ) < r then (1 : ℤ) else 0) = min (n : ℤ) r := by
  induction n with
  | zero => simp [hr]
  | succ n ih =>
    rw [sum_range_succ, ih]
    split_ifs with h <;> push_cast <;> omega

/-- The block rule has total `S` on a level set of `P` positions. (Auxiliary result for (L) of `C1_antitonic_fits.md`.) -/
theorem blockF_sum (S : ℤ) {P : ℕ} (hP : 0 < P) : ∑ k ∈ range P, blockF S P k = S := by
  obtain ⟨h2, h3, h1⟩ := emod_facts S hP
  simp_rw [blockF_eq S hP]
  rw [sum_add_distrib, sum_const, card_range, sum_range_ite_lt _ h2, nsmul_eq_mul,
    min_eq_right h3.le]
  linarith

theorem blockF_add_mul (S d : ℤ) {P : ℕ} (hP : 0 < P) (k : ℕ) :
    blockF (S + P * d) P k = blockF S P k + d := by
  rw [blockF_eq _ hP, blockF_eq _ hP, Int.add_mul_ediv_left _ _ (by omega),
    Int.add_mul_emod_self_left]
  ring

theorem blockF_neg (S : ℤ) {P k : ℕ} (hP : 0 < P) (hk : k < P) :
    blockF (-S) P (P - 1 - k) = -blockF S P k := by
  obtain ⟨h2, h3, h1⟩ := emod_facts S hP
  rw [blockF_eq _ hP, blockF_eq _ hP]
  by_cases hr : S % (P : ℤ) = 0
  · have e1 : -S / (P : ℤ) = -(S / P) ∧ -S % (P : ℤ) = 0 := by
      rw [Int.ediv_emod_unique (by omega)]
      refine ⟨by linarith, le_rfl, by omega⟩
    rw [e1.1, e1.2, hr, if_neg (by omega), if_neg (by omega)]
    ring
  · have e1 : -S / (P : ℤ) = -(S / P) - 1 ∧ -S % (P : ℤ) = P - S % P := by
      rw [Int.ediv_emod_unique (by omega)]
      refine ⟨by linarith, by omega, by omega⟩
    rw [e1.1, e1.2]
    split_ifs <;> omega

theorem blockF_nonneg {S : ℤ} (hS : 0 ≤ S) (P k : ℕ) : 0 ≤ blockF S P k := by
  have : (0 : ℝ) ≤ (S : ℝ) / P := div_nonneg (by exact_mod_cast hS) (Nat.cast_nonneg _)
  have h1 : 0 ≤ ⌊(S : ℝ) / P⌋ := Int.floor_nonneg.2 this
  unfold blockF
  split_ifs
  · exact h1.trans (Int.floor_le_ceil _)
  · exact h1

theorem blockF_nonpos {S : ℤ} (hS : S ≤ 0) (P k : ℕ) : blockF S P k ≤ 0 := by
  have : (S : ℝ) / P ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hS) (Nat.cast_nonneg _)
  have h1 : ⌈(S : ℝ) / P⌉ ≤ 0 := Int.ceil_le.2 (by simpa using this)
  unfold blockF
  split_ifs
  · exact h1
  · exact (Int.floor_le_ceil _).trans h1

theorem blockF_zero (P k : ℕ) : blockF 0 P k = 0 :=
  le_antisymm (blockF_nonpos le_rfl P k) (blockF_nonneg le_rfl P k)

variable {N : ℕ} {x : ℕ → ℤ}

theorem ifit_of_le {j : ℕ} (hj : N ≤ j) : ifit N x j = 0 := by
  simp [ifit, show ¬ j < N by omega]

theorem ifit_of_lt {j : ℕ} (hj : j < N) : ifit N x j =
    blockF (∑ i ∈ levelSet N (fit N (toR x)) j, x i) (levelSet N (fit N (toR x)) j).card
      ((levelSet N (fit N (toR x)) j).filter (· < j)).card := by
  simp [ifit, hj]

/-- The integer fit on a level interval `[p, q]` of `fit(x)`: at `j ∈ [p, q]` it equals
`⌈S/P⌉` if `j − p < S mod P` and `⌊S/P⌋` otherwise, where `S = Σ_{i=p}^{q} x_i` and
`P = q − p + 1` (the rule of *Definition (integer fit)* of `C1_antitonic_fits.md`). -/
theorem ifit_eq_of_level {p q j : ℕ} (h : IsLevelInterval N (fit N (toR x)) p q)
    (hpj : p ≤ j) (hjq : j ≤ q) :
    ifit N x j = blockF (∑ i ∈ Icc p q, x i) (q - p + 1) (j - p) := by
  have hjN : j < N := by have := h.2.1; omega
  rw [ifit_of_lt hjN, levelSet_eq_Icc h hpj hjq, Nat.card_Icc,
    show q + 1 - p = q - p + 1 by omega]
  congr 1
  rw [show (Icc p q).filter (· < j) = Ico p j by ext i; simp; omega, Nat.card_Ico]

/-- `ifit N x` only depends on the values of `x` at positions `< N`. (Auxiliary result for *Definition (integer fit)* and (A2) of `C1_antitonic_fits.md`.) -/
theorem ifit_congr {x' : ℕ → ℤ} (hx : ∀ j < N, x j = x' j) : ifit N x = ifit N x' := by
  have hf : fit N (toR x) = fit N (toR x') := fit_congr (fun j hj => by simp [toR, hx j hj])
  funext j
  by_cases hj : j < N
  · rw [ifit_of_lt hj, ifit_of_lt hj, hf]
    congr 1
    refine sum_congr rfl fun i hi => hx i ?_
    simp only [levelSet, mem_filter, mem_range] at hi
    exact hi.1
  · rw [ifit_of_le (by omega), ifit_of_le (by omega)]

/-- **(L)** of `C1_antitonic_fits.md`: if `x` is an integer sequence, then on every level set
`[p, q]` of `fit(x)` the (integer) sum `S = Σ_{j=p}^{q} x_j` satisfies
`S = (q − p + 1) · fit(x)_p`, and the sum of `ifit(x)` over `[p, q]` equals `S`.
(That `ifit(x)` is well defined is built into its definition, which is a total function.) -/
theorem consequence_L {p q : ℕ} (h : IsLevelInterval N (fit N (toR x)) p q) :
    ((∑ j ∈ Icc p q, x j : ℤ) : ℝ) = ((q - p + 1 : ℕ) : ℝ) * fit N (toR x) p ∧
      ∑ j ∈ Icc p q, ifit N x j = ∑ j ∈ Icc p q, x j := by
  refine ⟨by rw [Int.cast_sum]; exact sum_levelInterval_fit (x := toR x) h, ?_⟩
  rw [sum_congr rfl (fun j hj => ifit_eq_of_level h (mem_Icc.1 hj).1 (mem_Icc.1 hj).2),
    ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
    show q + 1 - p = q - p + 1 by have := h.1; omega]
  simp_rw [Nat.add_sub_cancel_left]
  exact blockF_sum _ (Nat.succ_pos _)

/-- Level-set version of the first half of **(L)**:
`Σ_{i ∈ levelSet j} x_i = |levelSet j| · fit(x)_j` for an integer sequence `x`. (Auxiliary result for (L) of `C1_antitonic_fits.md`.) -/
theorem sum_levelSet_fit_int {j : ℕ} (hj : j < N) :
    ((∑ i ∈ levelSet N (fit N (toR x)) j, x i : ℤ) : ℝ) =
      ((levelSet N (fit N (toR x)) j).card : ℝ) * fit N (toR x) j := by
  rw [Int.cast_sum]
  exact sum_levelSet_fit (x := toR x) hj

end AntitonicFit
