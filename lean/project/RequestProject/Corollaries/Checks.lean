module

public import RequestProject.Corollaries.CorollarySix

/-!
# (Q5) Checks

This file corresponds to **(Q5) Checks** of `CS6_corollaries_1_and_6.md`.

The values are obtained from the closed forms, not by computing groups:

* `f(m)` (`fCoker m`, `RequestProject/Corollaries/JordanType.lean`) satisfies
  `3 f(m) + [m odd] = 2^m + 2` (`fCoker_closed`, from (Q3)), so
  `f(m) = (2^m + 2 − [m odd]) / 3`, which is evaluated by `decide` (`fCoker_values`).
* `corN q d = (6(q−1)^d + 2(q^d − (q−1)^d) − ((q−1)^d − (q−3)^d) − 6) / 6` is the closed form of
  (Q4); its values are evaluated by `decide` (`corN_values`).
* `cycFactors3 d q = dim_{𝔽_3} (𝔽_3 ⊗ Syl_3 K(H(d,q)))` is the number of cyclic factors; (Q4)
  (`corollary6`, in the form `cycFactors3_eq_corN`) and the previous item give its values (`cycFactors3_values`).
-/

@[expose] public section

open Finset Module TensorProduct

namespace ColouredSand.Corollaries

open ColouredSand.Strings ColouredSand.TheoremB

/-- `3 f(m) + [m odd] = 2^m + 2`. -/
lemma fCoker_closed (m : ℕ) : 3 * fCoker m + m % 2 = 2 ^ m + 2 := by
  have hf := fCoker_eq m
  rw [(rank_U_zmod_three m).1] at hf
  obtain ⟨-, h2, h3⟩ := jordanABC_closed m
  have hd := jordan_dim m
  have h4 := one_add_mod_two_le_two_pow m
  omega

lemma fCoker_eq_div (m : ℕ) : fCoker m = (2 ^ m + 2 - m % 2) / 3 := by
  have := fCoker_closed m
  omega

/-- `f(m) = 1, 1, 2, 3, 6, 11, 22, 43, 86, 171, 342` for `m = 0, …, 10`. -/
theorem fCoker_values :
    [fCoker 0, fCoker 1, fCoker 2, fCoker 3, fCoker 4, fCoker 5, fCoker 6, fCoker 7, fCoker 8,
      fCoker 9, fCoker 10] = [1, 1, 2, 3, 6, 11, 22, 43, 86, 171, 342] := by
  simp only [fCoker_eq_div]
  decide

/-- The closed form of (Q4):
`N = (6(q−1)^d + 2(q^d − (q−1)^d) − ((q−1)^d − (q−3)^d) − 6) / 6`. -/
def corN (q d : ℕ) : ℤ :=
  (6 * ((q : ℤ) - 1) ^ d + 2 * ((q : ℤ) ^ d - ((q : ℤ) - 1) ^ d) -
    (((q : ℤ) - 1) ^ d - ((q : ℤ) - 3) ^ d) - 6) / 6

/-- Values of the closed form: `q = 3`, `d = 1, …, 6`: `1, 4, 12, 34, 96, 274`;
`q = 6`, `d = 1, …, 4`: `4, 25, 138, 757`; `q = 9`, `d = 1, 2, 3`: `7, 64, 534`;
`q = 12`, `d = 2`: `121`. -/
theorem corN_values :
    [corN 3 1, corN 3 2, corN 3 3, corN 3 4, corN 3 5, corN 3 6] = [1, 4, 12, 34, 96, 274] ∧
    [corN 6 1, corN 6 2, corN 6 3, corN 6 4] = [4, 25, 138, 757] ∧
    [corN 9 1, corN 9 2, corN 9 3] = [7, 64, 534] ∧
    corN 12 2 = 121 := by
  decide

/-- The number of cyclic factors `N = dim_{𝔽_3} (𝔽_3 ⊗ Syl_3 K(H(d,q)))`. -/
noncomputable def cycFactors3 (d q : ℕ) : ℕ :=
  finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile d q) 3)

lemma cycFactors3_eq (d q : ℕ) (hq : 3 ≤ q) (h3 : 3 ∣ q) :
    6 * (cycFactors3 d q : ℤ) = 6 * ((q : ℤ) - 1) ^ d + 2 * ((q : ℤ) ^ d - ((q : ℤ) - 1) ^ d) -
      (((q : ℤ) - 1) ^ d - ((q : ℤ) - 3) ^ d) - 6 :=
  corollary6 d q hq h3

/-- (Q4) is the closed form: `N = corN q d`. -/
lemma cycFactors3_eq_corN (d q : ℕ) (hq : 3 ≤ q) (h3 : 3 ∣ q) :
    (cycFactors3 d q : ℤ) = corN q d := by
  rw [corN, ← cycFactors3_eq d q hq h3]
  omega

/-- **(Q5)** The number of cyclic factors of `Syl_3 K(H(d,q))`:
`q = 3`, `d = 1, …, 6`: `1, 4, 12, 34, 96, 274`; `q = 6`, `d = 1, …, 4`: `4, 25, 138, 757`;
`q = 9`, `d = 1, 2, 3`: `7, 64, 534`; `q = 12`, `d = 2`: `121`. -/
theorem cycFactors3_values :
    [cycFactors3 1 3, cycFactors3 2 3, cycFactors3 3 3, cycFactors3 4 3, cycFactors3 5 3,
      cycFactors3 6 3] = [1, 4, 12, 34, 96, 274] ∧
    [cycFactors3 1 6, cycFactors3 2 6, cycFactors3 3 6, cycFactors3 4 6] = [4, 25, 138, 757] ∧
    [cycFactors3 1 9, cycFactors3 2 9, cycFactors3 3 9] = [7, 64, 534] ∧
    cycFactors3 2 12 = 121 := by
  have hv := corN_values
  simp only [List.cons.injEq, and_true] at hv ⊢
  simp only [← cycFactors3_eq_corN _ _ (by norm_num : 3 ≤ 3) dvd_rfl,
    ← cycFactors3_eq_corN _ _ (by norm_num : 3 ≤ 6) (by norm_num : 3 ∣ 6),
    ← cycFactors3_eq_corN _ _ (by norm_num : 3 ≤ 9) (by norm_num : 3 ∣ 9),
    ← cycFactors3_eq_corN _ _ (by norm_num : 3 ≤ 12) (by norm_num : 3 ∣ 12)] at hv
  omega

end ColouredSand.Corollaries
