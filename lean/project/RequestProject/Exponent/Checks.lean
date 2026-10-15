module

public import RequestProject.Exponent.TheoremC

/-!
# (C5) Checks

This file corresponds to **(C5) Checks** of `CS4_theorem_C_exponent.md`.

## Encoding

As in `RequestProject/Exponent/TheoremC.lean`: `expE p q d` is the exponent `E` of Theorem C
(`E = max_{1 ≤ s ≤ d} (e s + v_p(s))` if `e = v_p(q) ≥ 1`, `E = ⌊log_p d⌋` if `e = 0`), the
`p`-primary component is `AddCommGroup.primaryComponent` and the exponent is
`AddMonoid.exponent`.

## Results

* `expE_three_three_ten`: for `q = p = 3`, `d = 10`, `E = 11`;
  `check_attained_nine`: the term `e s + v_3(s)` at `s = 9` is `11`;
  `check_not_attained_ten`: at `s = 10` it is `10 ≠ 11`;
  `exponent_three_three_ten`: so the exponent of `Syl_3 K(H(10,3))` is `3^11`.
* `expE_of_lt`: for `p > d`, `E = e d` (for every `e`, including `e = 0`);
  `exponent_of_lt`: the exponent of `Syl_p K(H(d,q))` is then `p^{e d}` (for `q ≥ 3`).
-/

@[expose] public section

open Finset ColouredSand.TheoremB

namespace ColouredSand.Exponent

/-- `v_p(n) = k` when `p^k ∣ n` and `p^{k+1} ∤ n`. -/
lemma padicValNat_eq_of_dvd {p : ℕ} [Fact p.Prime] {n k : ℕ} (hn : n ≠ 0) (h1 : p ^ k ∣ n)
    (h2 : ¬ p ^ (k + 1) ∣ n) : padicValNat p n = k := by
  apply le_antisymm
  · by_contra h
    exact h2 ((padicValNat_dvd_iff_le hn).mpr (by omega))
  · exact (padicValNat_dvd_iff_le hn).mp h1

lemma padicValNat_three_three : padicValNat 3 3 = 1 := padicValNat_self

/-- The values of `v_3(s)` for `1 ≤ s ≤ 10`. -/
lemma padicValNat_three_table (s : ℕ) (hs : s ∈ Icc 1 10) :
    padicValNat 3 s = if s = 9 then 2 else if s = 3 ∨ s = 6 then 1 else 0 := by
  rw [mem_Icc] at hs
  obtain ⟨h1, h2⟩ := hs
  interval_cases s <;> norm_num <;>
    first | exact padicValNat_eq_of_dvd (by norm_num) (by norm_num) (by norm_num)

/-- **(C5), `q = p = 3`, `d = 10`:** `E = 11`. -/
theorem expE_three_three_ten : expE 3 3 10 = 11 := by
  unfold expE
  rw [padicValNat_three_three, if_pos le_rfl]
  apply le_antisymm
  · refine Finset.sup_le fun s hs => ?_
    rw [padicValNat_three_table s hs]
    rw [mem_Icc] at hs
    split_ifs <;> omega
  · have h9 : (9 : ℕ) ∈ Icc 1 10 := mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    have : 1 * 9 + padicValNat 3 9 ≤ (Icc 1 10).sup (fun s => 1 * s + padicValNat 3 s) :=
      le_sup (f := fun s => 1 * s + padicValNat 3 s) h9
    rw [padicValNat_three_table 9 h9] at this
    simpa using this

/-- **(C5):** the maximum `11` is attained at `s = 9`: `e·9 + v_3(9) = 11` (here `e = 1`). -/
theorem check_attained_nine : padicValNat 3 3 * 9 + padicValNat 3 9 = 11 := by
  rw [padicValNat_three_three, padicValNat_three_table 9 (mem_Icc.mpr ⟨by norm_num, by norm_num⟩)]
  rfl

/-- **(C5):** the maximum is not attained at `s = 10`: `e·10 + v_3(10) = 10 ≠ 11`. -/
theorem check_not_attained_ten : padicValNat 3 3 * 10 + padicValNat 3 10 = 10 := by
  rw [padicValNat_three_three, padicValNat_three_table 10 (mem_Icc.mpr ⟨by norm_num, by norm_num⟩)]
  rfl

/-- **(C5), with Theorem C:** the exponent of `Syl_3 K(H(10,3))` is `3^11`. -/
theorem exponent_three_three_ten :
    AddMonoid.exponent (AddCommGroup.primaryComponent (sandpile 10 3) 3) = 3 ^ 11 := by
  rw [theorem_C' 10 3 3 le_rfl, expE_three_three_ten]

/-- **(C5), `p > d`:** `E = e d` (for every `e = v_p(q)`, including `e = 0`). -/
theorem expE_of_lt (p q d : ℕ) [Fact p.Prime] (hpd : d < p) :
    expE p q d = padicValNat p q * d := by
  unfold expE
  split_ifs with he
  · have hv : ∀ s ∈ Icc 1 d, padicValNat p s = 0 := fun s hs => by
      rw [mem_Icc] at hs
      exact padicValNat.eq_zero_of_not_dvd fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    apply le_antisymm
    · refine Finset.sup_le fun s hs => ?_
      rw [hv s hs]
      rw [mem_Icc] at hs
      simpa using Nat.mul_le_mul_left (padicValNat p q) hs.2
    · rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp
      · have : padicValNat p q * d + padicValNat p d ≤
            (Icc 1 d).sup (fun s => padicValNat p q * s + padicValNat p s) :=
          le_sup (f := fun s => padicValNat p q * s + padicValNat p s) (mem_Icc.mpr ⟨hd, le_rfl⟩)
        rw [hv d (mem_Icc.mpr ⟨hd, le_rfl⟩)] at this
        simpa using this
  · rw [show padicValNat p q = 0 by omega, zero_mul]
    exact Nat.log_of_lt hpd

/-- **(C5), `p > d`, with Theorem C:** for `q ≥ 3` and a prime `p > d`, the exponent of
`Syl_p K(H(d,q))` is `p^{e d}`, `e = v_p(q)`. -/
theorem exponent_of_lt (d q p : ℕ) [Fact p.Prime] (hq : 3 ≤ q) (hpd : d < p) :
    AddMonoid.exponent (AddCommGroup.primaryComponent (sandpile d q) p) =
      p ^ (padicValNat p q * d) := by
  rw [theorem_C' d q p hq, expE_of_lt p q d hpd]

end ColouredSand.Exponent
