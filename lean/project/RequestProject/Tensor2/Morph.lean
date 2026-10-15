module

public import RequestProject.Tensor2.Basic

/-!
# `C23_the_tensor_product.md`: (P2) morphisms `f ⊠ g`, and (P7) `dsumIso`

Encodings (namespace `Tensor2`), reusing C18 (`Hom`, `H`), C19 (`WeylFilt.Hom.id`,
`WeylFilt.Hom.comp`), C20 (`Doubling.Iso`) and C22 (`Lemma35.dsum`, `Lemma35.dsumHom`):

* `kronHom f g : Hom (tensor M N) (tensor M' N')` is the morphism whose underlying linear map is
  `kron f.toLin g.toLin = f ⊠ g`, i.e. `δ_{(i,j)} ↦ f(δ_i) ⊗ g(δ_j)`.
* `tensorIso u v : Iso (tensor M N) (tensor M' N')` has `hom = u.hom ⊠ v.hom` and
  `inv = u.inv ⊠ v.inv`.
* `dsumIso u v : Iso (dsum M N) (dsum M' N')` has `hom = dsumHom u.hom v.hom` and
  `inv = dsumHom u.inv v.inv`.
-/

@[expose] public section

noncomputable section

namespace Tensor2

open DPLattice Finset WeylFilt Doubling Lemma35

variable {A : Type*} [CommRing A]

section P2

variable {M M' M'' N N' N'' : DPLattice A}

/-- (P2) For `f : Hom M M'` and `g : Hom N N'`, the linear map `f ⊠ g` is a morphism
`M ⊗ N → M' ⊗ N'`. -/
def kronHom (f : Hom M M') (g : Hom N N') : Hom (tensor M N) (tensor M' N') where
  toLin := kron f.toLin g.toLin
  comm_F r := by
    change kron _ _ ∘ₗ coFd M.Fd N.Fd r = coFd M'.Fd N'.Fd r ∘ₗ kron _ _
    simp only [coFd, lin_comp_sum, lin_sum_comp, kron_comp, f.comm_F, g.comm_F]
  comm_E r := by
    change kron _ _ ∘ₗ coFd M.Ed N.Ed r = coFd M'.Ed N'.Ed r ∘ₗ kron _ _
    simp only [coFd, lin_comp_sum, lin_sum_comp, kron_comp, f.comm_E, g.comm_E]
  comm_H := by
    rw [H_tensor, H_tensor, LinearMap.comp_add, LinearMap.add_comp, kron_comp, kron_comp,
      kron_comp, kron_comp, f.comm_H, g.comm_H]
    rfl

/-- (P2) the underlying linear map of `f ⊠ g`, on basis vectors:
`(f ⊠ g)(δ_{(i,j)}) (i', j') = f(δ_i)(i') · g(δ_j)(j')`. -/
theorem kronHom_single_apply (f : Hom M M') (g : Hom N N') (i : M.ι) (j : N.ι) (i' : M'.ι)
    (j' : N'.ι) : (kronHom f g).toLin (Pi.single (i, j) 1) (i', j') =
      f.toLin (Pi.single i 1) i' * g.toLin (Pi.single j 1) j' :=
  kron_single_apply _ _ i j i' j'

/-- (P2) `Hom.id M ⊠ Hom.id N = Hom.id (M ⊗ N)`. -/
theorem kronHom_id : kronHom (Hom.id M) (Hom.id N) = Hom.id (tensor M N) :=
  Hom.ext' kron_id

/-- (P2) `(f ∘ f') ⊠ (g ∘ g') = (f ⊠ g) ∘ (f' ⊠ g')`. -/
theorem kronHom_comp (f : Hom M' M'') (g : Hom N' N'') (f' : Hom M M') (g' : Hom N N') :
    kronHom (Hom.comp f f') (Hom.comp g g') = Hom.comp (kronHom f g) (kronHom f' g') :=
  Hom.ext' (kron_comp _ _ _ _).symm

/-- (P2) isomorphisms `M ≅ M'` and `N ≅ N'` give `M ⊗ N ≅ M' ⊗ N'`, with underlying maps
`u.hom ⊠ v.hom` and `u.inv ⊠ v.inv`. -/
def tensorIso (u : Iso M M') (v : Iso N N') : Iso (tensor M N) (tensor M' N') where
  hom := kronHom u.hom v.hom
  inv := kronHom u.inv v.inv
  hom_inv := by rw [← kronHom_comp, u.hom_inv, v.hom_inv, kronHom_id]
  inv_hom := by rw [← kronHom_comp, u.inv_hom, v.inv_hom, kronHom_id]

/-- (P2) the statement of the file: `f ⊠ g` is a morphism `M ⊗ N → M' ⊗ N'` (with underlying
linear map `f ⊠ g`); `Hom.id ⊠ Hom.id = Hom.id`; `(f ∘ f') ⊠ (g ∘ g') = (f ⊠ g) ∘ (f' ⊠ g')`;
and isomorphisms `u : M ≅ M'`, `v : N ≅ N'` give `tensorIso u v : M ⊗ N ≅ M' ⊗ N'` with
underlying maps `u.hom ⊠ v.hom` and `u.inv ⊠ v.inv`. -/
theorem P2 :
    (∀ {M M' N N' : DPLattice A} (f : Hom M M') (g : Hom N N'),
      (kronHom f g).toLin = kron f.toLin g.toLin) ∧
    (∀ M N : DPLattice A, kronHom (Hom.id M) (Hom.id N) = Hom.id (tensor M N)) ∧
    (∀ {M M' M'' N N' N'' : DPLattice A} (f : Hom M' M'') (g : Hom N' N'') (f' : Hom M M')
      (g' : Hom N N'),
      kronHom (Hom.comp f f') (Hom.comp g g') = Hom.comp (kronHom f g) (kronHom f' g')) ∧
    (∀ {M M' N N' : DPLattice A} (u : Iso M M') (v : Iso N N'),
      (tensorIso u v).hom.toLin = kron u.hom.toLin v.hom.toLin ∧
      (tensorIso u v).inv.toLin = kron u.inv.toLin v.inv.toLin) :=
  ⟨fun _ _ => rfl, fun _ _ => kronHom_id, fun f g f' g' => kronHom_comp f g f' g',
    fun _ _ => ⟨rfl, rfl⟩⟩

end P2

section P7

variable {M M' N N' : DPLattice A}

/-- (P7) isomorphisms `M ≅ M'` and `N ≅ N'` give `dsum M N ≅ dsum M' N'`, with underlying maps
`dsumHom u.hom v.hom` and `dsumHom u.inv v.inv`. -/
def dsumIso (u : Iso M M') (v : Iso N N') : Iso (dsum M N) (dsum M' N') where
  hom := dsumHom u.hom v.hom
  inv := dsumHom u.inv v.inv
  hom_inv := by rw [← dsumHom_comp, u.hom_inv, v.hom_inv, dsumHom_id]
  inv_hom := by rw [← dsumHom_comp, u.inv_hom, v.inv_hom, dsumHom_id]

/-- (P7) the statement of the file: `dsumIso u v : dsum M N ≅ dsum M' N'` has underlying
morphisms `dsumHom u.hom v.hom` and `dsumHom u.inv v.inv` (acting blockwise). -/
theorem P7 (u : Iso M M') (v : Iso N N') :
    (dsumIso u v).hom = dsumHom u.hom v.hom ∧ (dsumIso u v).inv = dsumHom u.inv v.inv ∧
    (∀ z : M.ι ⊕ N.ι → A, (dsumIso u v).hom.toLin z =
      Sum.elim (u.hom.toLin (z ∘ Sum.inl)) (v.hom.toLin (z ∘ Sum.inr))) ∧
    (∀ z : M'.ι ⊕ N'.ι → A, (dsumIso u v).inv.toLin z =
      Sum.elim (u.inv.toLin (z ∘ Sum.inl)) (v.inv.toLin (z ∘ Sum.inr))) :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

end P7

end Tensor2
