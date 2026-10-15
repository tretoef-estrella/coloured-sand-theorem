module

public import RequestProject.Lemma35.L1Comm

/-!
# `C22_lemma_35_over_F2.md`: Part L, (L1) `V^{⊗3} ≅ Δ(3) ⊕ (V ⊕ V)` — the isomorphism

Notation of `L1Defs.lean`: `T3 B = V^{⊗3}`, `D3 B = Δ(3) ⊕ (V ⊕ V)`, `gL`, `hL` the maps of the
file. `gHom h2`, `hHom h2` are the corresponding `Hom`s and `isoL1 h2` is the isomorphism
(`Doubling.Iso`), with `hom = h`, `inv = g`.
-/

@[expose] public section

noncomputable section

namespace Lemma35

open DPLattice Finset WeylFilt

variable {B : Type*} [CommRing B]

variable (h2 : (2 : B) = 0)

/-- (L1) `g : D → V^{⊗3}` is a `Hom` (when `2 = 0` in `B`). -/
def gHom : Hom (D3 B) (T3 B) :=
  homOfSmall (D3 B) (T3 B) gL 3 D3_wt_bound T3_wt_bound (g_comm_F h2) (g_comm_E h2) g_wt

include h2 in
lemma hL_comp_gL : hL ∘ₗ gL = (LinearMap.id : ((D3 B).ι → B) →ₗ[B] _) :=
  ext_single fun i => hg_single h2 i

include h2 in
lemma gL_comp_hL : gL ∘ₗ hL = (LinearMap.id : ((T3 B).ι → B) →ₗ[B] _) :=
  ext_single fun i => gh_single h2 i

/-- (L1) `h : V^{⊗3} → D` is a `Hom` (when `2 = 0` in `B`): the inverse of `g`. -/
def hHom : Hom (T3 B) (D3 B) :=
  Doubling.Hom.ofInverse (gHom h2) hL (hL_comp_gL h2) (gL_comp_hL h2)

@[simp] lemma gHom_toLin : (gHom h2).toLin = gL := rfl
@[simp] lemma hHom_toLin : (hHom h2).toLin = hL := rfl

/-- (L1) `h ∘ g = Hom.id`. -/
theorem hg_id : Hom.comp (hHom h2) (gHom h2) = Hom.id (D3 B) := Hom.ext' (hL_comp_gL h2)

/-- (L1) `g ∘ h = Hom.id`. -/
theorem gh_id : Hom.comp (gHom h2) (hHom h2) = Hom.id (T3 B) := Hom.ext' (gL_comp_hL h2)

/-- (L1) the isomorphism `V^{⊗3} ≅ Δ(3) ⊕ (V ⊕ V)`, with `hom = h` and `inv = g`. -/
def isoL1 : Doubling.Iso (T3 B) (D3 B) where
  hom := hHom h2
  inv := gHom h2
  hom_inv := gh_id h2
  inv_hom := hg_id h2

omit [CommRing B] in
/-- (L1) `g` sends `e_r` to `F^{(r)}(000)` (no hypothesis on `B` needed). -/
theorem g_eD_eq_Fd [CommRing B] (r : Fin 4) :
    gL (eD r) = (T3 B).Fd r (w (B := B) 0 0 0) := by
  funext ⟨a, b, c⟩
  fin_cases r <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [gL, ofImg_apply, gimg, tensorV, tensorFd, V, VFd, VmatF, dotProduct,
      Pi.single_apply, Matrix.toLin'_apply]

include h2 in
/-- (L1) Lemma 3.5, first isomorphism, over a commutative ring `B` with `2 = 0`:
`g : Δ(3) ⊕ (V ⊕ V) → V^{⊗3}` and `h : V^{⊗3} → Δ(3) ⊕ (V ⊕ V)` (given on basis vectors by the
tables of the file, `g_basis`, `h_basis`) are `Hom`s with `h ∘ g = Hom.id`, `g ∘ h = Hom.id`;
hence `V^{⊗3} ≅ Δ(3) ⊕ (V ⊕ V)`; and `g (e_r) = F^{(r)}(000)` for `r = 0, 1, 2, 3`. -/
theorem L1 :
    ∃ (g : Hom (D3 B) (T3 B)) (h : Hom (T3 B) (D3 B)),
      g.toLin = gL ∧ h.toLin = hL ∧
      Hom.comp h g = Hom.id (D3 B) ∧ Hom.comp g h = Hom.id (T3 B) ∧
      Nonempty (Doubling.Iso (tensorV (tensorV (V B))) (dsum (delta B 3) (dsum (V B) (V B)))) ∧
      ∀ r : Fin 4, g.toLin (eD r) = (T3 B).Fd r (w 0 0 0) :=
  ⟨gHom h2, hHom h2, rfl, rfl, hg_id h2, gh_id h2, ⟨isoL1 h2⟩, g_eD_eq_Fd⟩

end Lemma35
