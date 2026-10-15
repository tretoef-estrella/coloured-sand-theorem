module

public import RequestProject.FamDec.Mult

/-!
# `CSH1_theorem_H_the_prime_two.md`, Part N — numbers

Namespace `ColouredSand.ThmH`.  `v_2(q)` is `padicValNat 2 q`; `FamDec.L m` is C31's list of the
summands `T(λ)` of `V^{⊗m}` (with repetitions); `(m − λ)/2` is natural subtraction and division,
computed for every entry of the list with `List.map`.  All proofs are by rewriting with the
defining equations (no `native_decide`).
-/

@[expose] public section

namespace ColouredSand.ThmH

open FamDec

/-- **(N1)** of `CSH1_theorem_H_the_prime_two.md`: `v_2(4) = 2`, `v_2(12) = 2`, `v_2(8) = 3`,
`v_2(6) = 1`. -/
theorem N1 : padicValNat 2 4 = 2 ∧ padicValNat 2 12 = 2 ∧ padicValNat 2 8 = 3 ∧
    padicValNat 2 6 = 1 := by
  have h3 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  · rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, h3]
  · rw [show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  · rw [show (6 : ℕ) = 2 * 3 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self, h3]

lemma Vdot_one : Vdot 1 = [2] := Vdot_odd 0

lemma Vdot_two : Vdot 2 = [1, 1, 3] := by
  rw [show (2 : ℕ) = 2 * 0 + 2 from rfl, Vdot_even, Vdot_zero]; rfl

lemma Vdot_three : Vdot 3 = [4] := Vdot_odd 1

/-- **(N2)** of `CSH1_theorem_H_the_prime_two.md`: `FamDec.L 2 = [2]`, `FamDec.L 3 = [1, 1, 3]`,
`FamDec.L 4 = [2, 2, 4]`. -/
theorem N2_lists : L 2 = [2] ∧ L 3 = [1, 1, 3] ∧ L 4 = [2, 2, 4] := by
  have h2 : L 2 = [2] := by
    rw [L_succ, L_succ, L_zero]
    simp [Vdot_zero, Vdot_one]
  have h3 : L 3 = [1, 1, 3] := by
    rw [L_succ, h2]
    simp [Vdot_two]
  have h4 : L 4 = [2, 2, 4] := by
    rw [L_succ, h3]
    simp [Vdot_one, Vdot_three]
  exact ⟨h2, h3, h4⟩

/-- **(N2)** of `CSH1_theorem_H_the_prime_two.md`, the values of `(m − λ)/2` along the lists:
`[0]` for `m = 2`, `[1, 1, 0]` for `m = 3` and `[1, 1, 0]` for `m = 4`. -/
theorem N2_halves : (L 2).map (fun lam => (2 - lam) / 2) = [0] ∧
    (L 3).map (fun lam => (3 - lam) / 2) = [1, 1, 0] ∧
    (L 4).map (fun lam => (4 - lam) / 2) = [1, 1, 0] := by
  obtain ⟨h2, h3, h4⟩ := N2_lists
  rw [h2, h3, h4]
  decide

end ColouredSand.ThmH
