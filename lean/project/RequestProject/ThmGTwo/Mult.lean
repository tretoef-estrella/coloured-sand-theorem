module

public import RequestProject.TiltDec.All
public import RequestProject.FamDec.All
public import RequestProject.ThmH.Numbers

/-!
# `CSX3_theorems_F_G_prime_two.md`, Part M — the multiplicities agree at `p = 2`

Namespace `ColouredSand.ThmGTwo`; every new name starts with `two`.

## Encodings

* `TiltDec.VdotP 2 l` (CSG5) and `FamDec.Vdot l` (the Dancing Sand rule, C31) are lists of
  weights, compared up to order with `List.Perm`.
* `TiltDec.LP 2 m` (CSG5) and `FamDec.L m` (C31) are the lists of the summands `T(λ)` of
  `V^{⊗m}` (each `λ` repeated with its multiplicity); "the multiplicities agree" is
  `(LP 2 m).Perm (L m)`.
* All lists are computed by rewriting with the defining equations; the final permutation checks
  are decided by `decide` on explicit lists of natural numbers (no `native_decide`).
-/

@[expose] public section

namespace ColouredSand.ThmGTwo

open ColouredSand.TiltP ColouredSand.TiltDec FamDec

/-- `VdotP 2 l` for `l ≤ 4`, explicitly (auxiliary for (M1) of
`CSX3_theorems_F_G_prime_two.md`). -/
lemma twoVdotP_zero : VdotP 2 0 = [1] := VdotP_zero 2

lemma twoVdotP_one : VdotP 2 1 = [2] := by
  unfold VdotP; simp [IsSimpleWt]

lemma twoVdotP_two : VdotP 2 2 = [3, 1, 1] := by
  unfold VdotP; simp [IsSimpleWt, rT]

lemma twoVdotP_three : VdotP 2 3 = [4] := by
  unfold VdotP; simp [IsSimpleWt]

lemma twoVdotP_four : VdotP 2 4 = [5, 3, 3] := by
  unfold VdotP; simp [IsSimpleWt, rT]

lemma twoVdot_four : Vdot 4 = [3, 3, 5] := by
  rw [show (4 : ℕ) = 2 * 1 + 2 from rfl, Vdot_even, ThmH.Vdot_one]; rfl

/-- **(M1)** of `CSX3_theorems_F_G_prime_two.md`: for `l ≤ 4`, `VdotP 2 l` and `Vdot l` are
permutations of each other (`l = 0`: `[1]`; `l = 1`: `[2]`; `l = 2`: `[3, 1, 1]`; `l = 3`:
`[4]`; `l = 4`: `[5, 3, 3]`). -/
theorem twoM1 {l : ℕ} (hl : l ≤ 4) : (VdotP 2 l).Perm (Vdot l) := by
  interval_cases l
  · rw [twoVdotP_zero, Vdot_zero]
  · rw [twoVdotP_one, ThmH.Vdot_one]
  · rw [twoVdotP_two, ThmH.Vdot_two]; decide
  · rw [twoVdotP_three, ThmH.Vdot_three]
  · rw [twoVdotP_four, twoVdot_four]; decide

/-- `LP 2 m` for `m ≤ 5`, explicitly (auxiliary for (M2)). -/
lemma twoLP_explicit :
    LP 2 0 = [0] ∧ LP 2 1 = [1] ∧ LP 2 2 = [2] ∧ LP 2 3 = [3, 1, 1] ∧ LP 2 4 = [4, 2, 2] ∧
      LP 2 5 = [5, 3, 3, 3, 1, 1, 3, 1, 1] := by
  have h1 : LP 2 1 = [1] := by rw [LP_succ, LP_zero]; simp [twoVdotP_zero]
  have h2 : LP 2 2 = [2] := by rw [LP_succ, h1]; simp [twoVdotP_one]
  have h3 : LP 2 3 = [3, 1, 1] := by rw [LP_succ, h2]; simp [twoVdotP_two]
  have h4 : LP 2 4 = [4, 2, 2] := by
    rw [LP_succ, h3]; simp [twoVdotP_three, twoVdotP_one]
  have h5 : LP 2 5 = [5, 3, 3, 3, 1, 1, 3, 1, 1] := by
    rw [LP_succ, h4]; simp [twoVdotP_four, twoVdotP_two]
  exact ⟨rfl, h1, h2, h3, h4, h5⟩

/-- `L m` for `m ≤ 5`, explicitly (auxiliary for (M2)). -/
lemma twoL_explicit :
    L 0 = [0] ∧ L 1 = [1] ∧ L 2 = [2] ∧ L 3 = [1, 1, 3] ∧ L 4 = [2, 2, 4] ∧
      L 5 = [1, 1, 3, 1, 1, 3, 3, 3, 5] := by
  obtain ⟨h2, h3, h4⟩ := ThmH.N2_lists
  have h1 : L 1 = [1] := by rw [L_succ, L_zero]; simp [Vdot_zero]
  have h5 : L 5 = [1, 1, 3, 1, 1, 3, 3, 3, 5] := by
    rw [L_succ, h4]; simp [ThmH.Vdot_two, twoVdot_four]
  exact ⟨rfl, h1, h2, h3, h4, h5⟩

/-- **(M2)** of `CSX3_theorems_F_G_prime_two.md`: `(LP 2 m).Perm (L m)` for `m ≤ 5`. -/
theorem twoM2 {m : ℕ} (hm : m ≤ 5) : (LP 2 m).Perm (L m) := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := twoLP_explicit
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := twoL_explicit
  interval_cases m
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]; decide
  · rw [a4, b4]; decide
  · rw [a5, b5]; decide

end ColouredSand.ThmGTwo
