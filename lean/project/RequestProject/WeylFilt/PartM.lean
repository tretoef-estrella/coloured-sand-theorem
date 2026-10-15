module

public import RequestProject.WeylFilt.Comm

/-!
# `C19_weyl_filtrations_of_V_tensor.md`: Part M — the maps are morphisms

* (M1) `M1_fDelta`, `M1_gDelta`, `M1_fNabla`, `M1_gNabla`: the four maps of "The four maps"
  (`fDeltaLin`, `gDeltaLin`, `fNablaLin`, `gNablaLin`, defined on basis vectors) commute with every
  `F^{(r)}`, every `E^{(s)}` and `H`. Hence they are morphisms of DP-lattices: `fDelta A m`,
  `gDelta A m hm`, `fNabla A m hm`, `gNabla A m` are the corresponding `Hom`s.
  For `fΔ` and `g∇` the statement holds for every `m` (more general than the file); for `gΔ` and
  `f∇` it is stated for `m ≥ 1` as in the file.
* (M2) `M2`: `Hom.id` and `Hom.comp` are morphisms (they are `Hom`s by construction, with underlying
  maps the identity and the composite), composition is associative and `Hom.id` is a unit.
-/

@[expose] public section

noncomputable section

namespace WeylFilt

open DPLattice Finset

variable {A : Type*} [CommRing A]

/-- (M1) for `fΔ : Δ_A(m+1) → V ⊗ Δ_A(m)`: it commutes with every `F^{(r)}`, every `E^{(s)}` and
`H` (for every `m`; the file asks for `m ≥ 1`). -/
theorem M1_fDelta (m : ℕ) :
    (∀ r, fDeltaLin m ∘ₗ (delta A (m + 1)).Fd r = (tensorV (delta A m)).Fd r ∘ₗ fDeltaLin m) ∧
    (∀ s, fDeltaLin m ∘ₗ (delta A (m + 1)).Ed s = (tensorV (delta A m)).Ed s ∘ₗ fDeltaLin m) ∧
    fDeltaLin m ∘ₗ H (delta A (m + 1)) = H (tensorV (delta A m)) ∘ₗ fDeltaLin m := by
  rw [fDeltaLin_eq]
  exact ⟨fun r => fDelta_F m r, fun s => fDelta_E m s, fDelta_H m⟩

/-- (M1) for `gΔ : V ⊗ Δ_A(m) → Δ_A(m−1)` (`m ≥ 1`): it commutes with every `F^{(r)}`, every
`E^{(s)}` and `H`. -/
theorem M1_gDelta (m : ℕ) (hm : 1 ≤ m) :
    (∀ r, gDeltaLin m ∘ₗ (tensorV (delta A m)).Fd r = (delta A (m - 1)).Fd r ∘ₗ gDeltaLin m) ∧
    (∀ s, gDeltaLin m ∘ₗ (tensorV (delta A m)).Ed s = (delta A (m - 1)).Ed s ∘ₗ gDeltaLin m) ∧
    gDeltaLin m ∘ₗ H (tensorV (delta A m)) = H (delta A (m - 1)) ∘ₗ gDeltaLin m := by
  rw [gDeltaLin_eq]
  exact ⟨fun r => gDelta_F m r hm, fun s => gDelta_E m s hm, gDelta_H m hm⟩

/-- (M1) for `f∇ : ∇_A(m−1) → V ⊗ ∇_A(m)` (`m ≥ 1`): it commutes with every `F^{(r)}`, every
`E^{(s)}` and `H`. -/
theorem M1_fNabla (m : ℕ) (hm : 1 ≤ m) :
    (∀ r, fNablaLin m ∘ₗ (nabla A (m - 1)).Fd r = (tensorV (nabla A m)).Fd r ∘ₗ fNablaLin m) ∧
    (∀ s, fNablaLin m ∘ₗ (nabla A (m - 1)).Ed s = (tensorV (nabla A m)).Ed s ∘ₗ fNablaLin m) ∧
    fNablaLin m ∘ₗ H (nabla A (m - 1)) = H (tensorV (nabla A m)) ∘ₗ fNablaLin m := by
  rw [fNablaLin_eq]
  exact ⟨fun r => fNabla_F m r hm, fun s => fNabla_E m s hm, fNabla_H m hm⟩

/-- (M1) for `g∇ : V ⊗ ∇_A(m) → ∇_A(m+1)`: it commutes with every `F^{(r)}`, every `E^{(s)}` and
`H` (for every `m`; the file asks for `m ≥ 1`). -/
theorem M1_gNabla (m : ℕ) :
    (∀ r, gNablaLin m ∘ₗ (tensorV (nabla A m)).Fd r = (nabla A (m + 1)).Fd r ∘ₗ gNablaLin m) ∧
    (∀ s, gNablaLin m ∘ₗ (tensorV (nabla A m)).Ed s = (nabla A (m + 1)).Ed s ∘ₗ gNablaLin m) ∧
    gNablaLin m ∘ₗ H (tensorV (nabla A m)) = H (nabla A (m + 1)) ∘ₗ gNablaLin m := by
  rw [gNablaLin_eq]
  exact ⟨fun r => gNabla_F m r, fun s => gNabla_E m s, gNabla_H m⟩

/-- (M1) the morphism `fΔ : Δ_A(m+1) → V ⊗ Δ_A(m)`. -/
def fDelta (A : Type*) [CommRing A] (m : ℕ) : Hom (delta A (m + 1)) (tensorV (delta A m)) where
  toLin := fDeltaLin m
  comm_F := (M1_fDelta m).1
  comm_E := (M1_fDelta m).2.1
  comm_H := (M1_fDelta m).2.2

/-- (M1) the morphism `gΔ : V ⊗ Δ_A(m) → Δ_A(m−1)` (`m ≥ 1`). -/
def gDelta (A : Type*) [CommRing A] (m : ℕ) (hm : 1 ≤ m) :
    Hom (tensorV (delta A m)) (delta A (m - 1)) where
  toLin := gDeltaLin m
  comm_F := (M1_gDelta m hm).1
  comm_E := (M1_gDelta m hm).2.1
  comm_H := (M1_gDelta m hm).2.2

/-- (M1) the morphism `f∇ : ∇_A(m−1) → V ⊗ ∇_A(m)` (`m ≥ 1`). -/
def fNabla (A : Type*) [CommRing A] (m : ℕ) (hm : 1 ≤ m) :
    Hom (nabla A (m - 1)) (tensorV (nabla A m)) where
  toLin := fNablaLin m
  comm_F := (M1_fNabla m hm).1
  comm_E := (M1_fNabla m hm).2.1
  comm_H := (M1_fNabla m hm).2.2

/-- (M1) the morphism `g∇ : V ⊗ ∇_A(m) → ∇_A(m+1)`. -/
def gNabla (A : Type*) [CommRing A] (m : ℕ) : Hom (tensorV (nabla A m)) (nabla A (m + 1)) where
  toLin := gNablaLin m
  comm_F := (M1_gNabla m).1
  comm_E := (M1_gNabla m).2.1
  comm_H := (M1_gNabla m).2.2

/-- (M2) `Hom.id` and `Hom.comp` are morphisms (with underlying maps the identity and the
composite), composition is associative, and `Hom.id` is a left and right unit. -/
theorem M2 {M N P Q : DPLattice A} (f : Hom M N) (g : Hom N P) (h : Hom P Q) :
    (Hom.id M).toLin = LinearMap.id ∧ (Hom.comp g f).toLin = g.toLin ∘ₗ f.toLin ∧
    Hom.comp h (Hom.comp g f) = Hom.comp (Hom.comp h g) f ∧
    Hom.comp (Hom.id N) f = f ∧ Hom.comp f (Hom.id M) = f :=
  ⟨rfl, rfl, Hom.ext' rfl, Hom.ext' rfl, Hom.ext' rfl⟩

end WeylFilt
