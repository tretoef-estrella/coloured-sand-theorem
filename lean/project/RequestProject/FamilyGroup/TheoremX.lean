module

public import RequestProject.FamilyGroup.Group
public import RequestProject.FamilyGroup.Raw

/-!
# `C16_the_family_group_over_Z2.md`, Part T: Theorem X

(T1) `T1`, (T2) `T2`, and the case `I = ∅` of (T2) (`T2_empty`, (X3) with `α = 1`).
-/

@[expose] public section

namespace FamilyGroup

open Windows

/-- **(T1)** of `C16_the_family_group_over_Z2.md` (Part T, `i ≥ 1`): for `k ≥ 1` and `i ≥ 1`
there is `E` with `(E p : ℤ) = ŷ_i(p)` for `p < N`, and
`X^{(1)}(ds, i) ≅ SC(ds) × Π_{p : Fin N} Q(E p)`. -/
theorem T1 (ds : List Bool) (hk : 1 ≤ ds.length) (i : ℕ) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ p < 2 ^ Dance.mCount ds, (E p : ℤ) = yPool ds i p) ∧
      Nonempty (X ds 1 i ≃ₗ[ℤ_[2]] SC ds × ((p : Fin (2 ^ Dance.mCount ds)) → Q (E p))) := by
  obtain ⟨E, hE, he⟩ := X1 ds hk 1 i le_rfl hi
  exact ⟨E, fun p hp => by rw [hE p hp, (R1 ds i hi p hp).2], he⟩

/-- **(T2)** of `C16_the_family_group_over_Z2.md` (Part T, `i = 0`): for `k ≥ 1` and `I ≠ ∅` there
is `E` with `(E q : ℤ) = ŷ_0(q)` for `q < N − 1`, and
`X^{(1)}(ds, 0) ≅ SC(ds) × (A × Π_{q : Fin (N − 1)} Q(E q))`. -/
theorem T2 (ds : List Bool) (hk : 1 ≤ ds.length) (hne : Ids ds ≠ ∅) :
    ∃ E : ℕ → ℕ, (∀ q < 2 ^ Dance.mCount ds - 1, (E q : ℤ) = yPool0 ds q) ∧
      Nonempty (X ds 1 0 ≃ₗ[ℤ_[2]]
        SC ds × (ℤ_[2] × ((q : Fin (2 ^ Dance.mCount ds - 1)) → Q (E q)))) := by
  obtain ⟨E, hE, he⟩ := X2 ds hk 1 le_rfl hne
  refine ⟨E, fun q hq => ?_, he⟩
  rw [hE q hq, ← (R2 ds q hq).2, Nat.cast_one, one_mul]

/-- The case `I = ∅` of **(T2)** of `C16_the_family_group_over_Z2.md` (Part T): (X3) with
`α = 1`, `X^{(1)}(ds, 0) ≅ SC(ds) × A`. -/
theorem T2_empty (ds : List Bool) (hI : Ids ds = ∅) :
    Nonempty (X ds 1 0 ≃ₗ[ℤ_[2]] SC ds × ℤ_[2]) :=
  X3 ds 1 le_rfl hI

end FamilyGroup
