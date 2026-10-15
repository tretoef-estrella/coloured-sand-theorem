module

public import RequestProject.Doubling.PartD2

/-!
# `C20_the_doubling_functor.md`: Part D, (D3) — `Φ(𝟙) ≅ V`

From (D1) with `μ = 0` and C18 (T5): `Δ_A(0) ≅ 𝟙` (equal data under `Fin 1 ≃ Unit`,
`T5_delta_zero`, turned into an isomorphism by `Iso.ofDataEquiv`) and `Δ_A(1) = V`
(`T5_delta_one`), together with the functoriality (A2) of `Φ` (`Iso.phi`).
-/

@[expose] public section

noncomputable section

namespace Doubling

open DPLattice Finset WeylFilt

variable {A : Type*} [CommRing A]

/-- The inverse of an isomorphism. -/
def Iso.symm {M N : DPLattice A} (u : Iso M N) : Iso N M :=
  ⟨u.inv, u.hom, u.inv_hom, u.hom_inv⟩

/-- (D3, from C18 (T5)) "equal data under a bijection `e : M.ι ≃ N.ι`" gives an isomorphism
`M ≅ N`, `f ↦ f ∘ e⁻¹`. -/
def Iso.ofDataEquiv {M N : DPLattice A} (e : M.ι ≃ N.ι) (h : DataEquiv M N e) : Iso M N :=
  Iso.ofInverse
    { toLin := LinearMap.funLeft A A e.symm
      comm_F := fun r => LinearMap.ext fun f => (h.Fd_eq r f).symm
      comm_E := fun r => LinearMap.ext fun f => (h.Ed_eq r f).symm
      comm_H := LinearMap.ext fun f => by
        funext j
        simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Hop_apply]
        rw [← h.wt_eq (e.symm j), Equiv.apply_symm_apply] }
    (LinearMap.funLeft A A e)
    (LinearMap.ext fun f => by funext i; simp [LinearMap.funLeft_apply])
    (LinearMap.ext fun f => by funext i; simp [LinearMap.funLeft_apply])

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- (D3) the isomorphism `Φ(𝟙) ≅ Δ_A(1)`: `Φ` applied to `𝟙 ≅ Δ_A(0)` (C18 (T5)), followed by
(D1) for `μ = 0`. -/
def oneIso : Iso (phi (one A)) (delta A (2 * 0 + 1)) :=
  ((Iso.ofDataEquiv finOneEquivUnit T5_delta_zero).symm.phi).trans (deltaIso 0).symm

/-- (D3) `Φ(one A) ≅ V A`: there are morphisms `Φ(𝟙) → V` and `V → Φ(𝟙)` whose composites are
the identities (from (D1) with `μ = 0`, C18 (T5) `Δ_A(0) ≅ 𝟙` and `Δ_A(1) = V`). -/
theorem D3 : Nonempty (Iso (phi (one A)) (V A)) := by
  rw [← T5_delta_one]
  exact ⟨oneIso⟩

/-- (D3), explicit form: morphisms both ways between `Φ(one A)` and `V A` whose composites are
the identities. -/
theorem D3' : ∃ (f : Hom (phi (one A)) (V A)) (g : Hom (V A) (phi (one A))),
    Hom.comp g f = Hom.id _ ∧ Hom.comp f g = Hom.id _ := by
  obtain ⟨u⟩ := D3 (A := A)
  exact ⟨u.hom, u.inv, u.hom_inv, u.inv_hom⟩

end Doubling
