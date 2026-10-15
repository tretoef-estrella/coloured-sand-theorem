module

public import RequestProject.Tensor2.Morph

/-!
# `C23_the_tensor_product.md`: (P3) `tensorV M ≅ V A ⊗ M`, and (P6) `V ⊗ −` on morphisms

Encodings (namespace `Tensor2`), reusing C18 (`V`, `tensorV`, `bvec`, `slice`):

* Both `tensorV M` (C18) and `tensor (V A) M` have basis `Fin 2 × M.ι` and the same weights; the
  vector `b_e m` of `tensorV M` is `bvec e m`, and `bvec e m = δ_e ⊗ m` (`bvec_eq_tprod`).
* `tensorVIsoTensor M : Iso (tensorV M) (tensor (V A) M)` has both underlying linear maps equal
  to `LinearMap.id` (of `Fin 2 × M.ι → A`); this is (P3).
* `tensorVHom f : Hom (tensorV M) (tensorV N)` has underlying linear map
  `kron LinearMap.id f.toLin = id ⊠ f`, i.e. `bvec e m ↦ bvec e (f m)` (`tensorVHom_bvec`).
* `tensorVIso u : Iso (tensorV M) (tensorV N)` has `hom = tensorVHom u.hom`,
  `inv = tensorVHom u.inv`.
-/

@[expose] public section

noncomputable section

namespace Tensor2

open DPLattice Finset WeylFilt Doubling

variable {A : Type*} [CommRing A]

section P3

variable {ι : Type*}

lemma bvec_eq_tprod (e : Fin 2) (m : ι → A) :
    bvec e m = tprod (Pi.single e (1 : A)) m := by
  funext ⟨e', i⟩
  by_cases h : e' = e <;> simp [h]

variable (M : DPLattice A)

lemma V_tensor_sum (D : ℕ → Module.End A ((V A).ι → A)) (hD : ∀ a, 2 ≤ a → D a = 0)
    (G : ℕ → Module.End A (M.ι → A)) (e : Fin 2) (m : M.ι → A) (r : ℕ) :
    ∑ a ∈ range (r + 1), tprod (D a (Pi.single e (1 : A) : Fin 2 → A)) (G (r - a) m) =
      tprod (D 0 (Pi.single e (1 : A) : Fin 2 → A)) (G r m) +
        tprod (D 1 (Pi.single e (1 : A) : Fin 2 → A)) (pred G r m) := by
  rcases r with _ | k
  · simp
  · rw [sum_range_succ', sum_range_succ', sum_eq_zero fun a _ => by
      rw [hD (a + 1 + 1) (by omega)]; simp]
    simp only [zero_add, Nat.sub_zero, pred_succ]
    rw [show k + 1 - (0 + 1) = k by omega]
    abel

/-- (P3) `F^{(r)}` of `tensorV M` (C18's coproduct formulas) equals `F^{(r)}` of `V A ⊗ M`. -/
theorem tensorV_Fd_eq (r : ℕ) : (tensorV M).Fd r = (tensor (V A) M).Fd r := by
  refine ext_bvec (fun m => ?_) (fun m => ?_)
  · change tensorFd M.Fd r _ = coFd (V A).Fd M.Fd r _
    conv_rhs => rw [bvec_eq_tprod, coFd_tprod, V_tensor_sum M _ (V_Fd_ge_two (A := A)),
      (V A).isDP.P0_F, Module.End.one_apply, V_Fd_one_b0]
    rw [tensorFd_bvec0]
    simp only [bvec_eq_tprod]
  · change tensorFd M.Fd r _ = coFd (V A).Fd M.Fd r _
    conv_rhs => rw [bvec_eq_tprod, coFd_tprod, V_tensor_sum M _ (V_Fd_ge_two (A := A)),
      (V A).isDP.P0_F, Module.End.one_apply, V_Fd_one_b1]
    rw [tensorFd_bvec1]
    simp only [bvec_eq_tprod, tprod_zero_left, add_zero]

/-- (P3) `E^{(r)}` of `tensorV M` (C18's coproduct formulas) equals `E^{(r)}` of `V A ⊗ M`. -/
theorem tensorV_Ed_eq (r : ℕ) : (tensorV M).Ed r = (tensor (V A) M).Ed r := by
  refine ext_bvec (fun m => ?_) (fun m => ?_)
  · change tensorEd M.Ed r _ = coFd (V A).Ed M.Ed r _
    conv_rhs => rw [bvec_eq_tprod, coFd_tprod, V_tensor_sum M _ (V_Ed_ge_two (A := A)),
      (V A).isDP.P0_E, Module.End.one_apply, V_Ed_one_b0]
    rw [tensorEd_bvec0]
    simp only [bvec_eq_tprod, tprod_zero_left, add_zero]
  · change tensorEd M.Ed r _ = coFd (V A).Ed M.Ed r _
    conv_rhs => rw [bvec_eq_tprod, coFd_tprod, V_tensor_sum M _ (V_Ed_ge_two (A := A)),
      (V A).isDP.P0_E, Module.End.one_apply, V_Ed_one_b1]
    rw [tensorEd_bvec1]
    simp only [bvec_eq_tprod, add_comm]

/-- (P3) `H` of `tensorV M` equals `H` of `V A ⊗ M` (the weights agree). -/
theorem tensorV_H_eq : H (tensorV M) = H (tensor (V A) M) := rfl

/-- (P3) the identity of `Fin 2 × M.ι → A`, as a morphism `tensorV M → V A ⊗ M`. -/
def tensorVToTensor : Hom (tensorV M) (tensor (V A) M) where
  toLin := LinearMap.id
  comm_F r := by rw [tensorV_Fd_eq]; rfl
  comm_E r := by rw [tensorV_Ed_eq]; rfl
  comm_H := rfl

/-- (P3) `tensorV M ≅ V A ⊗ M`, with both underlying linear maps the identity of
`Fin 2 × M.ι → A`. -/
def tensorVIsoTensor : Iso (tensorV M) (tensor (V A) M) :=
  Iso.ofInverse (tensorVToTensor M) LinearMap.id rfl rfl

/-- (P3) the statement of the file: `tensorV M` and `V A ⊗ M` have the same basis
`Fin 2 × M.ι` and the same weights, and `tensorV M ≅ V A ⊗ M` with both underlying linear maps
the identity of `Fin 2 × M.ι → A` (so `δ_{(e,i)} ↦ δ_{(e,i)}` both ways). -/
theorem P3 :
    (tensorV M).ι = (Fin 2 × M.ι) ∧ (tensor (V A) M).ι = (Fin 2 × M.ι) ∧
    (∀ e i, (tensorV M).wt (e, i) = (tensor (V A) M).wt (e, i)) ∧
    (tensorVIsoTensor M).hom.toLin = LinearMap.id ∧
    (tensorVIsoTensor M).inv.toLin = LinearMap.id :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

end P3

section P6

variable {M N P : DPLattice A}

/-- (P6) For `f : Hom M N`, the linear map `id ⊠ f` of `Fin 2 × M.ι → A`
(`bvec e m ↦ bvec e (f m)`) is a morphism `tensorV M → tensorV N`. -/
def tensorVHom (f : Hom M N) : Hom (tensorV M) (tensorV N) where
  toLin := kron (LinearMap.id : (Fin 2 → A) →ₗ[A] (Fin 2 → A)) f.toLin
  comm_F r := by
    rw [tensorV_Fd_eq, tensorV_Fd_eq]
    exact (kronHom (Hom.id (V A)) f).comm_F r
  comm_E r := by
    rw [tensorV_Ed_eq, tensorV_Ed_eq]
    exact (kronHom (Hom.id (V A)) f).comm_E r
  comm_H := (kronHom (Hom.id (V A)) f).comm_H

/-- (P6) `(id ⊠ f)(b_e m) = b_e (f m)`. -/
theorem tensorVHom_bvec (f : Hom M N) (e : Fin 2) (m : M.ι → A) :
    (tensorVHom f).toLin (bvec e m) = bvec e (f.toLin m) := by
  change kron _ _ _ = _
  rw [bvec_eq_tprod, bvec_eq_tprod, kron_tprod]
  rfl

/-- (P6) `id ⊠ Hom.id = Hom.id`. -/
theorem tensorVHom_id : tensorVHom (Hom.id M) = Hom.id (tensorV M) :=
  Hom.ext' (by change kron _ _ = _; exact kron_id)

/-- (P6) `id ⊠ (g ∘ f) = (id ⊠ g) ∘ (id ⊠ f)`. -/
theorem tensorVHom_comp (g : Hom N P) (f : Hom M N) :
    tensorVHom (Hom.comp g f) = Hom.comp (tensorVHom g) (tensorVHom f) :=
  Hom.ext' (by
    change kron _ _ = kron _ _ ∘ₗ kron _ _
    rw [kron_comp]
    rfl)

/-- (P6) an isomorphism `M ≅ N` gives `tensorV M ≅ tensorV N`, with underlying maps
`id ⊠ u.hom` and `id ⊠ u.inv`. -/
def tensorVIso (u : Iso M N) : Iso (tensorV M) (tensorV N) where
  hom := tensorVHom u.hom
  inv := tensorVHom u.inv
  hom_inv := by rw [← tensorVHom_comp, u.hom_inv, tensorVHom_id]
  inv_hom := by rw [← tensorVHom_comp, u.inv_hom, tensorVHom_id]

/-- (P6) the statement of the file: for `f : Hom M N`, `id ⊠ f` (that is,
`bvec e m ↦ bvec e (f m)`) is a morphism `tensorV M → tensorV N`; it sends `Hom.id` to
`Hom.id` and composites to composites; and an isomorphism `u : M ≅ N` gives
`tensorVIso u : tensorV M ≅ tensorV N` with underlying maps `id ⊠ u.hom` and `id ⊠ u.inv`. -/
theorem P6 :
    (∀ {M N : DPLattice A} (f : Hom M N),
      (tensorVHom f).toLin = kron (LinearMap.id : (Fin 2 → A) →ₗ[A] (Fin 2 → A)) f.toLin ∧
      ∀ (e : Fin 2) (m : M.ι → A), (tensorVHom f).toLin (bvec e m) = bvec e (f.toLin m)) ∧
    (∀ M : DPLattice A, tensorVHom (Hom.id M) = Hom.id (tensorV M)) ∧
    (∀ {M N P : DPLattice A} (g : Hom N P) (f : Hom M N),
      tensorVHom (Hom.comp g f) = Hom.comp (tensorVHom g) (tensorVHom f)) ∧
    (∀ {M N : DPLattice A} (u : Iso M N),
      (tensorVIso u).hom = tensorVHom u.hom ∧ (tensorVIso u).inv = tensorVHom u.inv) :=
  ⟨fun f => ⟨rfl, tensorVHom_bvec f⟩, fun _ => tensorVHom_id, fun g f => tensorVHom_comp g f,
    fun _ => ⟨rfl, rfl⟩⟩

end P6

end Tensor2
