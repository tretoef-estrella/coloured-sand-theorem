module

public import RequestProject.Twist.Basic

/-!
# `C21_reduction_mod_2_and_the_twist.md`: Part R, base change of a DP-lattice

Encodings:
* `baseChange φ M` is `M^φ`: same basis `M.ι`, same weights `M.wt`, and
  `F^{(r)} := (M.Fd r)^φ`, `E^{(r)} := (M.Ed r)^φ` (`bc`, see `Basic.lean`).
* `bcHom φ f` is `f^φ : Hom (M^φ) (N^φ)` for `f : Hom M N` (underlying map `bc φ f.toLin`).
* Isomorphisms are C20's `Doubling.Iso`; the statements of (R3) also record that both underlying
  linear maps are the identity.
-/

@[expose] public section

noncomputable section

namespace Twist

open DPLattice Finset WeylFilt Doubling

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)

/-- (R1) The data of `M^φ` (basis `M.ι`, weights `M.wt`, `F^{(r)} = (M.Fd r)^φ`,
`E^{(r)} = (M.Ed r)^φ`) satisfy `IsDP`: (W), (P0), (P1) and (K). -/
theorem R1 (M : DPLattice A) :
    IsDP M.wt (fun r => bc φ (M.Fd r)) (fun r => bc φ (M.Ed r)) where
  W_F i r j h := by
    rw [bc_single_apply, M.isDP.W_F i r j h, map_zero]
  W_E i r j h := by
    rw [bc_single_apply, M.isDP.W_E i r j h, map_zero]
  P0_F := by rw [M.isDP.P0_F, bc_one]
  P0_E := by rw [M.isDP.P0_E, bc_one]
  P1_F a b := by
    rw [← bc_comp, M.isDP.P1_F, bc_intCast_smul]
  P1_E a b := by
    rw [← bc_comp, M.isDP.P1_E, bc_intCast_smul]
  K i r s := by
    rw [← comp_single φ i, bc_apply_comp, bc_apply_comp, M.isDP.K i r s, comp_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [comp_smul, map_intCast, bc_apply_comp, bc_apply_comp]

/-- (R1) `M^φ` (`baseChange φ M`): the DP-lattice over `B` with basis `M.ι`, weights `M.wt`,
`F^{(r)} = (M.Fd r)^φ` and `E^{(r)} = (M.Ed r)^φ`. -/
def baseChange (M : DPLattice A) : DPLattice B where
  ι := M.ι
  wt := M.wt
  Fd r := bc φ (M.Fd r)
  Ed r := bc φ (M.Ed r)
  isDP := R1 φ M

@[simp] lemma baseChange_Fd (M : DPLattice A) (r : ℕ) :
    (baseChange φ M).Fd r = bc φ (M.Fd r) := rfl
@[simp] lemma baseChange_Ed (M : DPLattice A) (r : ℕ) :
    (baseChange φ M).Ed r = bc φ (M.Ed r) := rfl
@[simp] lemma baseChange_wt (M : DPLattice A) : (baseChange φ M).wt = M.wt := rfl

lemma H_baseChange (M : DPLattice A) : H (baseChange φ M) = bc φ (H M) := (bc_Hop φ M.wt).symm

/-- (R2) `f^φ : Hom (M^φ) (N^φ)` for a morphism `f : Hom M N` (underlying map `(f.toLin)^φ`). -/
def bcHom {M N : DPLattice A} (f : Hom M N) : Hom (baseChange φ M) (baseChange φ N) where
  toLin := bc φ f.toLin
  comm_F r := by
    show bc φ f.toLin ∘ₗ bc φ (M.Fd r) = bc φ (N.Fd r) ∘ₗ bc φ f.toLin
    rw [← bc_comp, f.comm_F, bc_comp]
  comm_E r := by
    show bc φ f.toLin ∘ₗ bc φ (M.Ed r) = bc φ (N.Ed r) ∘ₗ bc φ f.toLin
    rw [← bc_comp, f.comm_E, bc_comp]
  comm_H := by
    rw [H_baseChange, H_baseChange]
    show bc φ f.toLin ∘ₗ bc φ (H M) = bc φ (H N) ∘ₗ bc φ f.toLin
    rw [← bc_comp, f.comm_H, bc_comp]

/-- (R2) For `f : Hom M N`, `f^φ` is a `Hom (M^φ) (N^φ)` whose underlying map is `(f.toLin)^φ`;
`(Hom.id M)^φ = Hom.id (M^φ)` and `(g ∘ f)^φ = g^φ ∘ f^φ`. -/
theorem R2 :
    (∀ {M N : DPLattice A} (f : Hom M N), (bcHom φ f).toLin = bc φ f.toLin) ∧
    (∀ M : DPLattice A, bcHom φ (Hom.id M) = Hom.id (baseChange φ M)) ∧
    (∀ {M N P : DPLattice A} (g : Hom N P) (f : Hom M N),
      bcHom φ (Hom.comp g f) = Hom.comp (bcHom φ g) (bcHom φ f)) :=
  ⟨fun _ => rfl, fun _ => Hom.ext' (bc_id φ), fun g f => Hom.ext' (bc_comp φ g.toLin f.toLin)⟩

/-! ### (R3) -/

lemma bc_VFd (r : ℕ) : bc φ (VFd (A := A) r) = VFd r := by
  refine ext_single fun i => ?_
  funext j
  rw [bc_single_apply]
  rcases r with _ | _ | r
  · fin_cases i <;> fin_cases j <;> simp [VFd]
  · fin_cases i <;> fin_cases j <;> simp [VFd, VmatF]
  · fin_cases i <;> fin_cases j <;> simp [VFd]

lemma bc_VEd (r : ℕ) : bc φ (VEd (A := A) r) = VEd r := by
  refine ext_single fun i => ?_
  funext j
  rw [bc_single_apply]
  rcases r with _ | _ | r
  · fin_cases i <;> fin_cases j <;> simp [VEd]
  · fin_cases i <;> fin_cases j <;> simp [VEd, VmatE]
  · fin_cases i <;> fin_cases j <;> simp [VEd]

/-- (R3) the identity map `(V A)^φ → V B`, a morphism. -/
def VHom : Hom (baseChange φ (V A)) (V B) where
  toLin := LinearMap.id
  comm_F r := by
    show LinearMap.id ∘ₗ bc φ (VFd r) = VFd r ∘ₗ LinearMap.id
    rw [bc_VFd]; rfl
  comm_E r := by
    show LinearMap.id ∘ₗ bc φ (VEd r) = VEd r ∘ₗ LinearMap.id
    rw [bc_VEd]; rfl
  comm_H := rfl

/-- (R3) the identity map `V B → (V A)^φ`, a morphism. -/
def VHomInv : Hom (V B) (baseChange φ (V A)) where
  toLin := LinearMap.id
  comm_F r := by
    show LinearMap.id ∘ₗ VFd r = bc φ (VFd r) ∘ₗ LinearMap.id
    rw [bc_VFd]; rfl
  comm_E r := by
    show LinearMap.id ∘ₗ VEd r = bc φ (VEd r) ∘ₗ LinearMap.id
    rw [bc_VEd]; rfl
  comm_H := rfl

/-- (R3) `(V A)^φ ≅ V B`, by the identity of `Fin 2 → B`. -/
def VIso : Iso (baseChange φ (V A)) (V B) where
  hom := VHom φ
  inv := VHomInv φ
  hom_inv := Hom.ext' rfl
  inv_hom := Hom.ext' rfl

section tensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma bc_pred (F : ℕ → Module.End A (ι → A)) (r : ℕ) :
    bc φ (pred F r) = pred (fun r => bc φ (F r)) r := by
  rcases r with _ | r
  · simp [bc_zero]
  · rfl

lemma bc_tensorFd (F : ℕ → Module.End A (ι → A)) (r : ℕ) :
    bc φ (tensorFd F r) = tensorFd (fun r => bc φ (F r)) r :=
  ext_comp φ fun x => by
    simp only [tensorFd, ← bc_pred, LinearMap.add_apply, LinearMap.comp_apply, bc_apply_comp, comp_add,
      ← bvec_comp, slice_comp]

lemma bc_tensorEd (F : ℕ → Module.End A (ι → A)) (r : ℕ) :
    bc φ (tensorEd F r) = tensorEd (fun r => bc φ (F r)) r :=
  ext_comp φ fun x => by
    simp only [tensorEd, ← bc_pred, LinearMap.add_apply, LinearMap.comp_apply, bc_apply_comp, comp_add,
      ← bvec_comp, slice_comp]

end tensor

/-- (R3) the identity map `(tensorV M)^φ → tensorV (M^φ)`, a morphism. -/
def tensorHom (M : DPLattice A) : Hom (baseChange φ (tensorV M)) (tensorV (baseChange φ M)) where
  toLin := LinearMap.id
  comm_F r := by
    show LinearMap.id ∘ₗ bc φ (tensorFd M.Fd r) = tensorFd (fun r => bc φ (M.Fd r)) r ∘ₗ
      LinearMap.id
    rw [bc_tensorFd]; rfl
  comm_E r := by
    show LinearMap.id ∘ₗ bc φ (tensorEd M.Ed r) = tensorEd (fun r => bc φ (M.Ed r)) r ∘ₗ
      LinearMap.id
    rw [bc_tensorEd]; rfl
  comm_H := rfl

/-- (R3) the identity map `tensorV (M^φ) → (tensorV M)^φ`, a morphism. -/
def tensorHomInv (M : DPLattice A) :
    Hom (tensorV (baseChange φ M)) (baseChange φ (tensorV M)) where
  toLin := LinearMap.id
  comm_F r := by
    show LinearMap.id ∘ₗ tensorFd (fun r => bc φ (M.Fd r)) r =
      bc φ (tensorFd M.Fd r) ∘ₗ LinearMap.id
    rw [bc_tensorFd]; rfl
  comm_E r := by
    show LinearMap.id ∘ₗ tensorEd (fun r => bc φ (M.Ed r)) r =
      bc φ (tensorEd M.Ed r) ∘ₗ LinearMap.id
    rw [bc_tensorEd]; rfl
  comm_H := rfl

/-- (R3) `(tensorV M)^φ ≅ tensorV (M^φ)`, by the identity of `Fin 2 × M.ι → B`. -/
def tensorIso (M : DPLattice A) : Iso (baseChange φ (tensorV M)) (tensorV (baseChange φ M)) where
  hom := tensorHom φ M
  inv := tensorHomInv φ M
  hom_inv := Hom.ext' rfl
  inv_hom := Hom.ext' rfl

/-- (R3) `(V A)^φ ≅ V B` and `(tensorV M)^φ ≅ tensorV (M^φ)`, by isomorphisms (`Doubling.Iso`)
whose underlying linear maps, both ways, are the identity of `Fin 2 → B`, respectively of
`Fin 2 × M.ι → B`. -/
theorem R3 :
    (∃ u : Iso (baseChange φ (V A)) (V B),
      u.hom.toLin = (LinearMap.id : (Fin 2 → B) →ₗ[B] (Fin 2 → B)) ∧
      u.inv.toLin = (LinearMap.id : (Fin 2 → B) →ₗ[B] (Fin 2 → B))) ∧
    (∀ M : DPLattice A, ∃ u : Iso (baseChange φ (tensorV M)) (tensorV (baseChange φ M)),
      u.hom.toLin = (LinearMap.id : (Fin 2 × M.ι → B) →ₗ[B] (Fin 2 × M.ι → B)) ∧
      u.inv.toLin = (LinearMap.id : (Fin 2 × M.ι → B) →ₗ[B] (Fin 2 × M.ι → B))) :=
  ⟨⟨VIso φ, rfl, rfl⟩, fun M => ⟨tensorIso φ M, rfl, rfl⟩⟩

end Twist
