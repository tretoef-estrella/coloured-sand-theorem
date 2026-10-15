module

public import RequestProject.Families.Digits

/-!
# `CSX2_theorem_I_prime_two.md`, (I6) — the digits

Namespace `ColouredSand.TwoI`.

`Families.ds λ` is the list of binary digits of `λ + 1` below the top digit, lowest first
(`false` for `0`, `true` for `1`).  We check that `k = (ds λ).length` and `|I| = Dance.mCount (ds λ)`
are the paper's: `k = ⌊log₂(λ + 1)⌋` (`Nat.log 2 (λ + 1)`) and `|I| + 1` is the number of digits `1`
of `λ + 1` (`(Nat.digits 2 (λ + 1)).count 1`, the `+ 1` being the top digit `d_k = 1`).
-/

@[expose] public section

namespace ColouredSand.TwoI

open Families

/-- **(I6)** of `CSX2_theorem_I_prime_two.md`, first half: `(ds λ).length = ⌊log₂(λ + 1)⌋`. -/
theorem twoI_ds_length (l : ℕ) : (ds l).length = Nat.log 2 (l + 1) := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    rcases cases3 l with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [ds_zero]; simp
    · rw [ds_odd, List.length_cons, ih m (by omega),
        show 2 * m + 1 + 1 = (m + 1) * 2 by ring, Nat.log_mul_base (by norm_num) (by omega)]
    · rw [ds_even, List.length_cons, ih m (by omega)]
      conv_rhs => rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega),
        show (2 * m + 2 + 1) / 2 = m + 1 by omega]

/-- **(I6)** of `CSX2_theorem_I_prime_two.md`, second half: `|I| + 1 = #{digits 1 of λ + 1}`,
i.e. `Dance.mCount (ds λ) + 1 = (Nat.digits 2 (λ + 1)).count 1`. -/
theorem twoI_mCount_ds (l : ℕ) :
    Dance.mCount (ds l) + 1 = (Nat.digits 2 (l + 1)).count 1 := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    rcases cases3 l with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [ds_zero]; simp [Dance.mCount]
    · rw [ds_odd, show 2 * m + 1 + 1 = 2 * (m + 1) by ring,
        Nat.digits_def' (by norm_num) (by omega), show 2 * (m + 1) % 2 = 0 by omega,
        show 2 * (m + 1) / 2 = m + 1 by omega, List.count_cons, ← ih m (by omega)]
      simp [Dance.mCount]
    · rw [ds_even, show 2 * m + 2 + 1 = 2 * (m + 1) + 1 by ring,
        Nat.digits_def' (by norm_num) (by omega), show (2 * (m + 1) + 1) % 2 = 1 by omega,
        show (2 * (m + 1) + 1) / 2 = m + 1 by omega, List.count_cons, ← ih m (by omega)]
      simp [Dance.mCount]

/-- **(I6)** of `CSX2_theorem_I_prime_two.md`: both digit identities together. -/
theorem twoI_I6 (l : ℕ) :
    (ds l).length = Nat.log 2 (l + 1) ∧
      Dance.mCount (ds l) + 1 = (Nat.digits 2 (l + 1)).count 1 :=
  ⟨twoI_ds_length l, twoI_mCount_ds l⟩

end ColouredSand.TwoI
