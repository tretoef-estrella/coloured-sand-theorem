import RequestProject.TwoTheoremI.All

/-!
# CheckCSX2 (Grepy Ship, 15 Oct 2026)

Hand restatement of CSX2 (`CSX2_theorem_I_prime_two.md`): Theorem I of the Coloured Sand at the
prime 2. Every type is written out by hand from the certified Dancing Sand definitions
(`FamilyGroup.X`, `SC`, `Q`; `Windows.finalMatrix`; `Families.ds`; `Dance.mCount`); the cokernel
`C = coker(2^k M)` is written out instead of using `CmodTwo`. Then `#print axioms`.
-/

namespace CheckCSX2

open FamilyGroup
open scoped Pointwise

/-- (E1): for `α ≥ 1` every entry of the final matrix is even (restated by hand). -/
theorem hE1 (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (s s' : Fin (2 ^ Dance.mCount ds)) :
    (2 : ℤ) ∣ Windows.finalMatrix ℤ ds α i s s' :=
  ColouredSand.TwoI.twoI_E1 ds α i hα s s'

/-- (I1), `k ≥ 1`, `i ≥ 1`: exponents `E j ≥ k + 1` for the `N` large summands. -/
theorem hI1 (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds, ds.length + 1 ≤ E j) ∧
      Nonempty (X ds α i ≃ₗ[ℤ_[2]] SC ds × ((j : Fin (2 ^ Dance.mCount ds)) → Q (E j))) :=
  ColouredSand.TwoI.twoI_I1_pos ds hk α i hα hi

/-- (I2): the small summands are killed by `2^k`. -/
theorem hI2 (ds : List Bool) (x : SC ds) : (2 : ℤ_[2]) ^ ds.length • x = 0 :=
  ColouredSand.TwoI.twoI_I2 ds x

/-- (I4), the invariant form, for every digit list. -/
theorem hI4 (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) :
    Nonempty ((X ds α i ⧸ (2 : ℤ_[2]) ^ (ds.length + 1) • (⊤ : Submodule ℤ_[2] (X ds α i)))
      ≃ₗ[ℤ_[2]] (SC ds × (Fin (2 ^ Dance.mCount ds) → Q (ds.length + 1)))) :=
  ColouredSand.TwoI.twoI_I4 ds α i hα

/-- (I3), with the cokernel `coker(2^k M)` written out by hand. -/
theorem hI3 (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) :
    Nonempty (X ds α i ≃ₗ[ℤ_[2]] SC ds × ((Fin (2 ^ Dance.mCount ds) → ℤ_[2]) ⧸
      LinearMap.range ((2 : ℤ_[2]) ^ ds.length •
        Matrix.toLin' ((Windows.finalMatrix ℤ ds α i).map (Int.castRingHom ℤ_[2]))))) :=
  ColouredSand.TwoI.twoI_I3_equiv ds α i hα

/-- (I5) on the family `λ`, invariant part, with `ds = Families.ds λ`. -/
theorem hI5 (l i α : ℕ) (hα : 1 ≤ α) :
    Nonempty ((X (Families.ds l) α i ⧸ (2 : ℤ_[2]) ^ ((Families.ds l).length + 1) •
        (⊤ : Submodule ℤ_[2] (X (Families.ds l) α i))) ≃ₗ[ℤ_[2]]
      (SC (Families.ds l) × (Fin (2 ^ Dance.mCount (Families.ds l)) →
        Q ((Families.ds l).length + 1)))) :=
  (ColouredSand.TwoI.twoI_theorem_I l i α hα).2.2.2.2

/-- (I6): `k = ⌊log₂(λ+1)⌋` and `|I| + 1` = number of binary digits 1 of `λ + 1`. -/
theorem hI6 (l : ℕ) :
    (Families.ds l).length = Nat.log 2 (l + 1) ∧
      Dance.mCount (Families.ds l) + 1 = (Nat.digits 2 (l + 1)).count 1 :=
  ColouredSand.TwoI.twoI_I6 l

/-- A concrete instance: `λ = 12`, `λ + 1 = 13 = 1101₂`, so `k = 3` and `|I| = 2`. -/
example : (Families.ds 12).length = 3 ∧ Dance.mCount (Families.ds 12) = 2 := by
  have h := hI6 12
  refine ⟨by rw [h.1]; decide, ?_⟩
  have h2 : (Nat.digits 2 (12 + 1)).count 1 = 3 := by decide
  omega

end CheckCSX2

#print axioms CheckCSX2.hE1
#print axioms CheckCSX2.hI1
#print axioms CheckCSX2.hI2
#print axioms CheckCSX2.hI3
#print axioms CheckCSX2.hI4
#print axioms CheckCSX2.hI5
#print axioms CheckCSX2.hI6
#print axioms ColouredSand.TwoI.twoI_theorem_I
#print axioms ColouredSand.TwoI.twoI_theorem_I_ds
#print axioms ColouredSand.TwoI.twoI_I1_zero
#print axioms ColouredSand.TwoI.twoI_I1_empty
#print axioms ColouredSand.TwoI.twoI_I1_nil_pos
#print axioms ColouredSand.TwoI.twoI_I1_nil_zero
#print axioms ColouredSand.TwoI.twoI_E2_pos
#print axioms ColouredSand.TwoI.twoI_E2_zero
