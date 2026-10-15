module

public import RequestProject.OddSES.PartS1

/-!
# `CSI4_the_short_exact_sequences.md`: Part S, (S1)–(S3) — the contraction and action maps

See the docstring of `RequestProject/OddSES/PartS1.lean` for the encodings:
`contrHom M = (unit) ∘ (ω ⊗ id) ∘ assoc⁻¹ : V ⊗ (V ⊗ M) → M`, `actHom M`, `pairHom f g`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

/-! ### The contraction `V ⊗ (V ⊗ M) → M` -/

section contr

variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A] (M : DPLattice A)

/-- The contraction `(unit) ∘ (ω ⊗ id_M) ∘ assoc⁻¹ : V ⊗ (V ⊗ M) → M`. -/
def contrHom : Hom (Tensor2.tensor (V A) (Tensor2.tensor (V A) M)) M :=
  WeylFilt.Hom.comp (Tensor2.unitLeftIso M).hom
    (WeylFilt.Hom.comp (Tensor2.kronHom (omegaHom A) (WeylFilt.Hom.id M))
      (Tensor2.assocIso (V A) (V A) M).inv)

omit [IsDomain A] [CharZero A] in
lemma funLeft_assoc_tprod' {ι κ μ : Type*} (x : ι → A) (y : κ → A) (z : μ → A) :
    LinearMap.funLeft A A (Equiv.prodAssoc ι κ μ) (Tensor2.tprod x (Tensor2.tprod y z)) =
      Tensor2.tprod (Tensor2.tprod x y) z := by
  funext ⟨⟨i, j⟩, k⟩
  simp [Tensor2.tprod_apply, mul_assoc]

lemma contr_tv (a b : Fin 2) (m : M.ι → A) :
    (contrHom M).toLin (tv a (tv b m)) =
      ((if a = 0 ∧ b = 1 then 1 else 0) - (if a = 1 ∧ b = 0 then 1 else 0) : A) • m := by
  have hω : (omegaHom A).toLin (Pi.single (a, b) 1) =
      ((if a = 0 ∧ b = 1 then 1 else 0) - (if a = 1 ∧ b = 0 then 1 else 0) : A) •
        (Pi.single () (1 : A) : (one A).ι → A) := by
    funext u
    exact (omegaL_single A a b u).trans
      (by change _ = _ * (Pi.single () (1 : A) : Unit → A) (); simp)
  have e1 : (tv a (tv b m) : (Tensor2.tensor (V A) (Tensor2.tensor (V A) M)).ι → A) =
      Tensor2.tprod (Pi.single a 1) (Tensor2.tprod (Pi.single b 1) m) := rfl
  simp only [contrHom, WeylFilt.Hom.comp, LinearMap.comp_apply, Tensor2.unitLeftIso,
    Tensor2.isoOfReindex_hom, Tensor2.assocIso, Tensor2.isoOfReindex_inv, Tensor2.kronHom]
  rw [e1]
  erw [funLeft_assoc_tprod']
  rw [← Tensor2.single_prod_eq_tprod]
  erw [Tensor2.kron_tprod]
  erw [hω]
  rw [Tensor2.tprod_smul_left, map_smul]
  erw [Tensor2.funLeft_uniqueProd_tprod]
  rfl

lemma contr_tv00 (m : M.ι → A) : (contrHom M).toLin (tv 0 (tv 0 m)) = 0 := by
  rw [contr_tv]; simp

lemma contr_tv01 (m : M.ι → A) : (contrHom M).toLin (tv 0 (tv 1 m)) = m := by
  rw [contr_tv]; simp

lemma contr_tv10 (m : M.ι → A) : (contrHom M).toLin (tv 1 (tv 0 m)) = -m := by
  rw [contr_tv]; simp

lemma contr_tv11 (m : M.ι → A) : (contrHom M).toLin (tv 1 (tv 1 m)) = 0 := by
  rw [contr_tv]; simp

end contr

/-! ### The action `V ⊗ (V ⊗ M) → M` of `Sym² V ≅ 𝔤`, times 2 -/

section act

variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A] (M : DPLattice A)

omit [IsDomain A] [CharZero A] in
lemma single_Wl' (a b : Fin 2) (i : M.ι) :
    (Pi.single (a, (b, i)) 1 : (Wl M).ι → A) =
      tv (ι := (Tensor2.tensor (V A) M).ι) a (tv (ι := M.ι) b (Pi.single i 1)) := by
  rw [Tensor2.single_prod_eq_tprod, Tensor2.single_prod_eq_tprod]
  rfl

/-- (S3) `z ↦ 2E z_{00} − H z_{01} − H z_{10} − 2F z_{11}`. -/
def actL : ((Tensor2.tensor (V A) (Tensor2.tensor (V A) M)).ι → A) →ₗ[A] (M.ι → A) :=
  (2 : A) • (M.Ed 1 ∘ₗ slot2 0 0) - H M ∘ₗ slot2 0 1 - H M ∘ₗ slot2 1 0 -
    (2 : A) • (M.Fd 1 ∘ₗ slot2 1 1)

lemma actL_apply (z : (Tensor2.tensor (V A) (Tensor2.tensor (V A) M)).ι → A) :
    actL M z = (2 : A) • M.Ed 1 (slot2 0 0 z) - H M (slot2 0 1 z) -
      H M (slot2 1 0 z) - (2 : A) • M.Fd 1 (slot2 1 1 z) := rfl

lemma actL_00 (m : M.ι → A) : actL M (tv 0 (tv 0 m)) = (2 : A) • M.Ed 1 m := by
  rw [actL_apply]; simp [slot2_Wl]

lemma actL_01 (m : M.ι → A) : actL M (tv 0 (tv 1 m)) = -H M m := by
  rw [actL_apply]; simp [slot2_Wl]

lemma actL_10 (m : M.ι → A) : actL M (tv 1 (tv 0 m)) = -H M m := by
  rw [actL_apply]; simp [slot2_Wl]

lemma actL_11 (m : M.ι → A) : actL M (tv 1 (tv 1 m)) = -((2 : A) • M.Fd 1 m) := by
  rw [actL_apply]; simp [slot2_Wl]

lemma actL_F : actL M ∘ₗ (Tensor2.tensor (V A) (Tensor2.tensor (V A) M)).Fd 1 =
    M.Fd 1 ∘ₗ actL M := by
  refine ext_single fun x => ?_
  obtain ⟨a, b, i⟩ := x
  rw [single_Wl' M a b i, LinearMap.comp_apply, LinearMap.comp_apply]
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl
  · rw [tensorV_Fd1_tv0, tensorV_Fd1_tv0, map_add, map_add, map_add, actL_10, actL_01, actL_00,
      actL_00, Doubling.dp_lie M, map_smul]
    module
  · rw [tensorV_Fd1_tv0, tensorV_Fd1_tv1, map_add, actL_11, actL_01, actL_01, H_F1, map_neg]
    module
  · rw [tensorV_Fd1_tv1, tensorV_Fd1_tv0, map_add, map_add, actL_11, actL_10, actL_10, H_F1,
      map_neg]
    module
  · rw [tensorV_Fd1_tv1, tensorV_Fd1_tv1, actL_11, actL_11, map_neg, map_smul]

lemma actL_E : actL M ∘ₗ (Tensor2.tensor (V A) (Tensor2.tensor (V A) M)).Ed 1 =
    M.Ed 1 ∘ₗ actL M := by
  refine ext_single fun x => ?_
  obtain ⟨a, b, i⟩ := x
  rw [single_Wl' M a b i, LinearMap.comp_apply, LinearMap.comp_apply]
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl
  · rw [tensorV_Ed1_tv0, tensorV_Ed1_tv0, actL_00, actL_00, map_smul]
  · rw [tensorV_Ed1_tv0, tensorV_Ed1_tv1, map_add, map_add, actL_00, actL_01, actL_01, H_E1, map_neg]
    module
  · rw [tensorV_Ed1_tv1, tensorV_Ed1_tv0, map_add, actL_00, actL_10, actL_10, H_E1, map_neg]
    module
  · rw [tensorV_Ed1_tv1, tensorV_Ed1_tv1, map_add, map_add, map_add, actL_01, actL_10, actL_11,
      actL_11, map_neg, map_smul, Doubling.dp_lie M]
    module

lemma actL_H : actL M ∘ₗ H (Tensor2.tensor (V A) (Tensor2.tensor (V A) M)) = H M ∘ₗ actL M := by
  refine ext_single fun x => ?_
  obtain ⟨a, b, i⟩ := x
  have hn := inWt_single (A := A) M.wt i
  have hW := inWt_tv (Tensor2.tensor (V A) M) a (inWt_tv M b hn)
  rw [single_Wl' M a b i, LinearMap.comp_apply, LinearMap.comp_apply, Doubling.Hop_of_inWt hW,
    map_smul]
  have hH : H M (Pi.single i 1) = ((M.wt i : ℤ) : A) • (Pi.single i 1 : M.ι → A) :=
    Doubling.Hop_of_inWt hn
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl
  · rw [actL_00, map_smul, H_E1, hH, map_smul]
    simp only [wtV_zero, smul_smul, smul_add]; push_cast; module
  · rw [actL_01, map_neg, hH, map_smul, hH]
    simp only [wtV_zero, wtV_one, smul_neg, smul_smul]; push_cast; module
  · rw [actL_10, map_neg, hH, map_smul, hH]
    simp only [wtV_zero, wtV_one, smul_neg, smul_smul]; push_cast; module
  · rw [actL_11, map_neg, map_smul, H_F1, hH, map_smul]
    simp only [wtV_one, smul_neg, smul_smul, smul_sub]; push_cast; module

/-- (S3) the action map `V ⊗ (V ⊗ M) → M` as a morphism (by (Q0c)). -/
def actHom : Hom (Tensor2.tensor (V A) (Tensor2.tensor (V A) M)) M :=
  Q0c (actL M) (actL_F M) (actL_E M) (actL_H M)

end act

/-! ### Pairs into a direct sum -/

section pair

variable {A : Type*} [CommRing A] {X Y Z : DPLattice A}

/-- `x ↦ (f x, g x)` as a morphism into `dsum Y Z`. -/
def pairHom (f : Hom X Y) (g : Hom X Z) : Hom X (Lemma35.dsum Y Z) where
  toLin :=
    { toFun := fun x => Sum.elim (f.toLin x) (g.toLin x)
      map_add' := fun x x' => by funext s; cases s <;> simp
      map_smul' := fun c x => by funext s; cases s <;> simp }
  comm_F r := LinearMap.ext fun x => funext fun s => by
    cases s with
    | inl i => exact congr_fun (LinearMap.congr_fun (f.comm_F r) x) i
    | inr i => exact congr_fun (LinearMap.congr_fun (g.comm_F r) x) i
  comm_E r := LinearMap.ext fun x => funext fun s => by
    cases s with
    | inl i => exact congr_fun (LinearMap.congr_fun (f.comm_E r) x) i
    | inr i => exact congr_fun (LinearMap.congr_fun (g.comm_E r) x) i
  comm_H := LinearMap.ext fun x => funext fun s => by
    cases s with
    | inl i => exact congr_fun (LinearMap.congr_fun f.comm_H x) i
    | inr i => exact congr_fun (LinearMap.congr_fun g.comm_H x) i

lemma pairHom_apply (f : Hom X Y) (g : Hom X Z) (x : X.ι → A) :
    (pairHom f g).toLin x = Sum.elim (f.toLin x) (g.toLin x) := rfl

end pair

end ColouredSand.OddTwist
