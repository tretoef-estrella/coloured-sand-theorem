module

public import RequestProject.OddTwist.PartD2

/-!
# `CSI1_the_odd_twist.md`: Part D, (D3) — `Φ_p(𝟙) ≅ Δ_{ℤ_[p]}(p − 1)`

From (D1) with `μ = 0` and C18 (T5): `Δ_A(0) ≅ 𝟙` (equal data under `Fin 1 ≃ Unit`,
`T5_delta_zero`, turned into an isomorphism by C20's `Iso.ofDataEquiv`), together with the
functoriality (A2) of `Φ_p` (`Iso.twist`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset Doubling WeylFilt

variable (p : ℕ) [Fact p.Prime]

/-- (D3) the isomorphism `Φ_p(𝟙) ≅ Δ(p·0 + p − 1)`: `Φ_p` applied to `𝟙 ≅ Δ_A(0)` (C18 (T5)),
followed by (D1) for `μ = 0`. -/
def oneIso : Iso (twist p (one ℤ_[p])) (delta ℤ_[p] (lam p 0)) :=
  (Iso.twist p (Iso.ofDataEquiv finOneEquivUnit T5_delta_zero).symm).trans (deltaIso p 0).symm

/-- (D3) `Φ_p(one ℤ_[p]) ≅ Δ_{ℤ_[p]}(p − 1)` (the Steinberg lattice): there are morphisms both
ways whose composites are the identities. -/
theorem D3 : Nonempty (Iso (twist p (one ℤ_[p])) (delta ℤ_[p] (p - 1))) := by
  have h : lam p 0 = p - 1 := by simp [lam]
  rw [← h]
  exact ⟨oneIso p⟩

/-- (D3), explicit form: morphisms `Φ_p(𝟙) → Δ(p − 1)` and back whose composites are the
identities. -/
theorem D3' : ∃ (f : Hom (twist p (one ℤ_[p])) (delta ℤ_[p] (p - 1)))
    (g : Hom (delta ℤ_[p] (p - 1)) (twist p (one ℤ_[p]))),
    Hom.comp g f = Hom.id _ ∧ Hom.comp f g = Hom.id _ := by
  obtain ⟨u⟩ := D3 p
  exact ⟨u.hom, u.inv, u.hom_inv, u.inv_hom⟩

end ColouredSand.OddTwist
