module

public import RequestProject.Windows.Basic

/-!
# `C32_theorem_38_the_groups_of_the_families.md`: Part B0 — the digit list of a family

Encodings (namespace `Families`):

* `ds : ℕ → List Bool` is defined by well-founded recursion, in the same shape as C29's `Filt.T`:
  `ds 0 = []` and `ds (n + 1) = false :: ds (n / 2)` if `n` is even, `true :: ds (n / 2)` if `n`
  is odd.  The three equations of (B0) are the theorems `ds_zero`, `ds_odd`, `ds_even`.
* The family `I = Ids (ds λ)` is C14's `Windows.Ids`; sums over it are `Finset.sum`.
-/

@[expose] public section

namespace Families

open Finset

/-- **(B0)** of `C32_theorem_38_the_groups_of_the_families.md`: the digit list of a family,
by well-founded recursion: `ds 0 = []`, `ds (2l + 1) = false :: ds l`,
`ds (2l + 2) = true :: ds l` (written as `ds (n + 1) = false :: ds (n / 2)` for even `n` and
`true :: ds (n / 2)` for odd `n`). -/
def ds : ℕ → List Bool
  | 0 => []
  | n + 1 => if n % 2 = 0 then false :: ds (n / 2) else true :: ds (n / 2)
decreasing_by all_goals omega

/-- **(B0)** of `C32_theorem_38_the_groups_of_the_families.md`: `ds 0 = []`. -/
theorem ds_zero : ds 0 = [] := by rw [ds]

/-- **(B0)** of `C32_theorem_38_the_groups_of_the_families.md`: `ds (2l + 1) = false :: ds l`. -/
theorem ds_odd (l : ℕ) : ds (2 * l + 1) = false :: ds l := by
  rw [ds, if_pos (by omega), show 2 * l / 2 = l by omega]

/-- **(B0)** of `C32_theorem_38_the_groups_of_the_families.md`: `ds (2l + 2) = true :: ds l`. -/
theorem ds_even (l : ℕ) : ds (2 * l + 2) = true :: ds l := by
  rw [show 2 * l + 2 = (2 * l + 1) + 1 by omega, ds, if_neg (by omega),
    show (2 * l + 1) / 2 = l by omega]

/-- The three-way case split `n = 0`, `n = 2l + 1`, `n = 2l + 2` (auxiliary for Part B of
`C32_theorem_38_the_groups_of_the_families.md`). -/
lemma cases3 (n : ℕ) : n = 0 ∨ (∃ l, n = 2 * l + 1) ∨ ∃ l, n = 2 * l + 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rcases k with _ | k
    · left; rfl
    · right; right; exact ⟨k, by ring⟩
  · right; left; exact ⟨k, rfl⟩

/-- `Σ_{t ∈ I(d :: l)} 2^t = (if d then 1 else 0) + 2 · Σ_{t ∈ I(l)} 2^t` (auxiliary for (B0b) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
lemma sum_Ids_cons (d : Bool) (l : List Bool) :
    ∑ t ∈ Windows.Ids (d :: l), 2 ^ t =
      (if d = true then 1 else 0) + 2 * ∑ t ∈ Windows.Ids l, 2 ^ t := by
  rw [Windows.Ids_cons]
  have hdisj : Disjoint (if d = true then ({0} : Finset ℕ) else ∅)
      ((Windows.Ids l).image (· + 1)) := by
    split_ifs
    · simp
    · simp
  rw [sum_union hdisj, sum_image (fun a _ b _ h => by omega), mul_sum]
  congr 1
  · split_ifs <;> simp
  · exact sum_congr rfl fun t _ => by ring

/-- **(B0b)** of `C32_theorem_38_the_groups_of_the_families.md`: for every `λ`,
`λ + 1 = 2 ^ (ds λ).length + Σ_{t ∈ Ids (ds λ)} 2 ^ t`. -/
theorem B0b (lam : ℕ) :
    lam + 1 = 2 ^ (ds lam).length + ∑ t ∈ Windows.Ids (ds lam), 2 ^ t := by
  induction lam using Nat.strong_induction_on with
  | _ lam ih =>
    rcases cases3 lam with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
    · rw [ds_zero]; simp [Windows.Ids]
    · have := ih l (by omega)
      rw [ds_odd, sum_Ids_cons, List.length_cons, pow_succ]
      simp only [Bool.false_eq_true, if_false]
      linarith
    · have := ih l (by omega)
      rw [ds_even, sum_Ids_cons, List.length_cons, pow_succ]
      simp only [if_true]
      linarith

end Families
