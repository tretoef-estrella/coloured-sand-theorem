module

public import RequestProject.OddSES.PartP3

/-!
# `CSI4_the_short_exact_sequences.md`: Part S, (S1) — the symplectic form `ω`, and the
contraction maps used for `π_r`

Encodings:

* For `z : Fin 2 × ι → A` (a vector of `V ⊗ M`), `slot e z : ι → A` is its component `y_e` in
  `z = b̂_0 ⊗ y_0 + b̂_1 ⊗ y_1` (`eq_tv_slot`). On `V ⊗ M` the single operators act on the
  components by `slot0_TF`, …, `slot_TH` (from C23's `tensor_Fd_tprod`, via CSI3's
  `tensorV_Fd1_tv0`, …).
* `omegaHom A : Hom (V ⊗ V) (one A)` is the symplectic form `ω` of (S1):
  `b̂_0 ⊗ b̂_1 ↦ 1`, `b̂_1 ⊗ b̂_0 ↦ −1`, `b̂_0 ⊗ b̂_0, b̂_1 ⊗ b̂_1 ↦ 0` (`S1`).
* `contrHom M : Hom (V ⊗ (V ⊗ M)) M` is the composite
  `(unit) ∘ (ω ⊗ id) ∘ assoc⁻¹` of C23's `Tensor2.assocIso`, `Tensor2.kronHom`,
  `Tensor2.unitLeftIso` (which identifies `one ⊗ M` with `M`), defined in `PartS1b.lean`; on
  basis tensors it is `b̂_a ⊗ b̂_b ⊗ m ↦ ω(b̂_a ⊗ b̂_b) m` (`contr_tv`, `contr_tv01`, …).
* `actHom M : Hom (V ⊗ (V ⊗ M)) M` (in `PartS1b.lean`) is "the `sl_2`-action of
  `Sym² V ≅ 𝔤`, times 2", used in (S3):
  `z ↦ 2E z_{00} − H z_{01} − H z_{10} − 2F z_{11}` (built with (Q0c) over any domain of
  characteristic zero).
* `pairHom f g : Hom X (dsum Y Z)` (in `PartS1b.lean`) is `x ↦ (f x, g x)` (C22's `Lemma35.dsum`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

section slots

variable {A : Type*} [CommRing A] {ι : Type*}

/-- The component `y_e` of `z = b̂_0 ⊗ y_0 + b̂_1 ⊗ y_1`. -/
def slot (e : Fin 2) : (Fin 2 × ι → A) →ₗ[A] (ι → A) where
  toFun z i := z (e, i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma slot_apply (e : Fin 2) (z : Fin 2 × ι → A) (i : ι) : slot e z i = z (e, i) := rfl

@[simp] lemma slot_tv_self (e : Fin 2) (y : ι → A) : slot e (tv e y) = y := by
  funext i; simp [tv_apply]

@[simp] lemma slot0_tv1 (y : ι → A) : slot 0 (tv 1 y) = 0 := by
  funext i; simp [tv_apply]

@[simp] lemma slot1_tv0 (y : ι → A) : slot 1 (tv 0 y) = 0 := by
  funext i; simp [tv_apply]

lemma eq_tv_slot (z : Fin 2 × ι → A) : z = tv 0 (slot 0 z) + tv 1 (slot 1 z) := by
  funext ⟨e, i⟩
  rcases fin2_cases e with rfl | rfl <;> simp [tv_apply]

lemma slot_ext {z z' : Fin 2 × ι → A} (h0 : slot 0 z = slot 0 z') (h1 : slot 1 z = slot 1 z') :
    z = z' := by
  rw [eq_tv_slot z, eq_tv_slot z', h0, h1]

end slots

section tensorV

variable {A : Type*} [CommRing A] (M : DPLattice A)

lemma TF_eq (w : (Tensor2.tensor (V A) M).ι → A) :
    (Tensor2.tensor (V A) M).Fd 1 w =
      tv 1 (slot 0 w) + tv 0 (M.Fd 1 (slot 0 w)) + tv 1 (M.Fd 1 (slot 1 w)) := by
  conv_lhs => rw [eq_tv_slot w]
  rw [map_add, tensorV_Fd1_tv0, tensorV_Fd1_tv1]

lemma TE_eq (w : (Tensor2.tensor (V A) M).ι → A) :
    (Tensor2.tensor (V A) M).Ed 1 w =
      tv 0 (M.Ed 1 (slot 0 w)) + tv 0 (slot 1 w) + tv 1 (M.Ed 1 (slot 1 w)) := by
  conv_lhs => rw [eq_tv_slot w]
  rw [map_add, tensorV_Ed1_tv0, tensorV_Ed1_tv1, add_assoc]

@[simp] lemma slot0_TF (w : (Tensor2.tensor (V A) M).ι → A) :
    slot 0 ((Tensor2.tensor (V A) M).Fd 1 w) = M.Fd 1 (slot 0 w) := by
  rw [TF_eq]; simp

@[simp] lemma slot1_TF (w : (Tensor2.tensor (V A) M).ι → A) :
    slot 1 ((Tensor2.tensor (V A) M).Fd 1 w) = slot 0 w + M.Fd 1 (slot 1 w) := by
  rw [TF_eq]; simp

@[simp] lemma slot0_TE (w : (Tensor2.tensor (V A) M).ι → A) :
    slot 0 ((Tensor2.tensor (V A) M).Ed 1 w) = M.Ed 1 (slot 0 w) + slot 1 w := by
  rw [TE_eq]; simp

@[simp] lemma slot1_TE (w : (Tensor2.tensor (V A) M).ι → A) :
    slot 1 ((Tensor2.tensor (V A) M).Ed 1 w) = M.Ed 1 (slot 1 w) := by
  rw [TE_eq]; simp

@[simp] lemma slot0_TH (w : (Tensor2.tensor (V A) M).ι → A) :
    slot 0 (H (Tensor2.tensor (V A) M) w) = H M (slot 0 w) + slot 0 w := by
  funext i
  simp only [slot_apply, Hop_apply, Pi.add_apply]
  change (((wtV 0 + M.wt i : ℤ)) : A) * w ((0 : Fin 2), i) = (M.wt i : A) * w ((0 : Fin 2), i) +
    w ((0 : Fin 2), i)
  simp; ring

@[simp] lemma slot1_TH (w : (Tensor2.tensor (V A) M).ι → A) :
    slot 1 (H (Tensor2.tensor (V A) M) w) = H M (slot 1 w) - slot 1 w := by
  funext i
  simp only [slot_apply, Hop_apply, Pi.sub_apply]
  change (((wtV 1 + M.wt i : ℤ)) : A) * w ((1 : Fin 2), i) = (M.wt i : A) * w ((1 : Fin 2), i) -
    w ((1 : Fin 2), i)
  simp; ring

/-- `slot e ((id ⊠ g) z) = g (slot e z)`. -/
lemma slot_kronHom_id {M' : DPLattice A} (g : Hom M M') (e : Fin 2)
    (z : (Tensor2.tensor (V A) M).ι → A) :
    slot e ((Tensor2.kronHom (WeylFilt.Hom.id (V A)) g).toLin z) = g.toLin (slot e z) := by
  have h : (Tensor2.kronHom (WeylFilt.Hom.id (V A)) g).toLin z =
      tv 0 (g.toLin (slot 0 z)) + tv 1 (g.toLin (slot 1 z)) := by
    conv_lhs => rw [eq_tv_slot z]
    rw [map_add]
    exact congrArg₂ (· + ·) (Tensor2.kron_tprod _ _ _ _) (Tensor2.kron_tprod _ _ _ _)
  rw [h]
  rcases fin2_cases e with rfl | rfl <;> simp

end tensorV

/-! ### `V` -/

section Vops

variable {A : Type*} [CommRing A]

lemma VF_apply0 (x : (V A).ι → A) : (V A).Fd 1 x (0 : Fin 2) = 0 := by
  simp [V, VFd, VmatF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma VF_apply1 (x : (V A).ι → A) : (V A).Fd 1 x (1 : Fin 2) = x (0 : Fin 2) := by
  simp [V, VFd, VmatF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma VE_apply0 (x : (V A).ι → A) : (V A).Ed 1 x (0 : Fin 2) = x (1 : Fin 2) := by
  simp [V, VEd, VmatE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma VE_apply1 (x : (V A).ι → A) : (V A).Ed 1 x (1 : Fin 2) = 0 := by
  simp [V, VEd, VmatE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma VH_apply0 (x : (V A).ι → A) : H (V A) x (0 : Fin 2) = x (0 : Fin 2) := by
  simp [Hop_apply, V, wtV]

lemma VH_apply1 (x : (V A).ι → A) : H (V A) x (1 : Fin 2) = -x (1 : Fin 2) := by
  simp [Hop_apply, V, wtV]

end Vops

/-! ### (S1) the symplectic form `ω` -/

section omega

variable (A : Type*) [CommRing A] [IsDomain A] [CharZero A]

/-- (S1) the linear map of `ω`: `z ↦ z(0,1) − z(1,0)`. -/
def omegaL : (Fin 2 × Fin 2 → A) →ₗ[A] (Unit → A) where
  toFun z _ := z (0, 1) - z (1, 0)
  map_add' z z' := by funext u; simp only [Pi.add_apply]; ring
  map_smul' c z := by funext u; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [IsDomain A] [CharZero A] in
lemma omegaL_apply (z : Fin 2 × Fin 2 → A) (u : (one A).ι) : omegaL A z u = z (0, 1) - z (1, 0) := rfl

omit [IsDomain A] [CharZero A] in
lemma omegaL_single (a b : Fin 2) (u : (one A).ι) :
    omegaL A (Pi.single (a, b) 1) u =
      (if a = 0 ∧ b = 1 then 1 else 0) - (if a = 1 ∧ b = 0 then 1 else 0) := by
  rw [omegaL_apply]
  simp only [Pi.single_apply, Prod.mk.injEq]
  congr 1 <;> simp only [eq_comm]

omit [IsDomain A] [CharZero A] in
lemma one_Fd1 : (one A).Fd 1 = 0 := by simp [one, oneFd]

omit [IsDomain A] [CharZero A] in
lemma one_Ed1 : (one A).Ed 1 = 0 := by simp [one, oneFd]

omit [IsDomain A] [CharZero A] in
lemma one_H : H (one A) = 0 := by
  refine LinearMap.ext fun x => funext fun u => ?_
  show (((one A).wt u : ℤ) : A) * x u = 0
  simp [one]

lemma omegaL_F : omegaL A ∘ₗ (Tensor2.tensor (V A) (V A)).Fd 1 = (one A).Fd 1 ∘ₗ omegaL A := by
  rw [one_Fd1, LinearMap.zero_comp]
  refine LinearMap.ext fun z => funext fun u => ?_
  have h0 := congr_fun (slot0_TF (V A) z) (1 : Fin 2)
  have h1 := congr_fun (slot1_TF (V A) z) (0 : Fin 2)
  simp only [slot_apply, Pi.add_apply, VF_apply0, VF_apply1] at h0 h1
  change ((Tensor2.tensor (V A) (V A)).Fd 1 z) ((0 : Fin 2), (1 : Fin 2)) -
    ((Tensor2.tensor (V A) (V A)).Fd 1 z) ((1 : Fin 2), (0 : Fin 2)) = 0
  rw [h0, h1]; ring

lemma omegaL_E : omegaL A ∘ₗ (Tensor2.tensor (V A) (V A)).Ed 1 = (one A).Ed 1 ∘ₗ omegaL A := by
  rw [one_Ed1, LinearMap.zero_comp]
  refine LinearMap.ext fun z => funext fun u => ?_
  have h0 := congr_fun (slot0_TE (V A) z) (1 : Fin 2)
  have h1 := congr_fun (slot1_TE (V A) z) (0 : Fin 2)
  simp only [slot_apply, Pi.add_apply, VE_apply0, VE_apply1] at h0 h1
  change ((Tensor2.tensor (V A) (V A)).Ed 1 z) ((0 : Fin 2), (1 : Fin 2)) -
    ((Tensor2.tensor (V A) (V A)).Ed 1 z) ((1 : Fin 2), (0 : Fin 2)) = 0
  rw [h0, h1]; ring

lemma omegaL_H : omegaL A ∘ₗ H (Tensor2.tensor (V A) (V A)) = H (one A) ∘ₗ omegaL A := by
  rw [one_H, LinearMap.zero_comp]
  refine LinearMap.ext fun z => funext fun u => ?_
  have h0 := congr_fun (slot0_TH (V A) z) (1 : Fin 2)
  have h1 := congr_fun (slot1_TH (V A) z) (0 : Fin 2)
  simp only [slot_apply, Pi.add_apply, Pi.sub_apply, VH_apply0, VH_apply1] at h0 h1
  change (H (Tensor2.tensor (V A) (V A)) z) ((0 : Fin 2), (1 : Fin 2)) -
    (H (Tensor2.tensor (V A) (V A)) z) ((1 : Fin 2), (0 : Fin 2)) = 0
  rw [h0, h1]; ring

/-- (S1) the symplectic form `ω : V ⊗ V → 𝟙` as a morphism (by (Q0c)). -/
def omegaHom : Hom (Tensor2.tensor (V A) (V A)) (one A) :=
  Q0c (omegaL A) (omegaL_F A) (omegaL_E A) (omegaL_H A)

/-- (S1) **The symplectic form.** `ω : V ⊗ V → 𝟙` is a morphism with
`ω(b̂_0 ⊗ b̂_1) = 1`, `ω(b̂_1 ⊗ b̂_0) = −1`, `ω(b̂_0 ⊗ b̂_0) = ω(b̂_1 ⊗ b̂_1) = 0`
(over any domain of characteristic zero, e.g. `ℤ_[p]`). -/
theorem S1 :
    (omegaHom A).toLin (Pi.single ((0 : Fin 2), (1 : Fin 2)) 1) = (fun _ => (1 : A)) ∧
    (omegaHom A).toLin (Pi.single ((1 : Fin 2), (0 : Fin 2)) 1) = (fun _ => (-1 : A)) ∧
    (omegaHom A).toLin (Pi.single ((0 : Fin 2), (0 : Fin 2)) 1) = 0 ∧
    (omegaHom A).toLin (Pi.single ((1 : Fin 2), (1 : Fin 2)) 1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [omegaHom, Q0c_toLin] <;> funext u
  · exact (omegaL_single A 0 1 u).trans (by simp)
  · exact (omegaL_single A 1 0 u).trans (by simp)
  · exact (omegaL_single A 0 0 u).trans (by simp)
  · exact (omegaL_single A 1 1 u).trans (by simp)

end omega

/-! ### Two-fold slots on `V ⊗ (V ⊗ M)` -/

section slot2

variable {A : Type*} [CommRing A] {ι : Type*}

/-- The component `z_{ab}` of `z = Σ b̂_a ⊗ b̂_b ⊗ z_{ab}` in `V ⊗ (V ⊗ M)`. -/
def slot2 (a b : Fin 2) : (Fin 2 × (Fin 2 × ι) → A) →ₗ[A] (ι → A) where
  toFun z i := z (a, (b, i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma slot2_apply (a b : Fin 2) (z : Fin 2 × (Fin 2 × ι) → A) (i : ι) :
    slot2 a b z i = z (a, (b, i)) := rfl

end slot2

section W

variable {A : Type*} [CommRing A] (M : DPLattice A)

/-- `W = V ⊗ (V ⊗ M)`. -/
abbrev Wl : DPLattice A := Tensor2.tensor (V A) (Tensor2.tensor (V A) M)

lemma single_Wl (a b : Fin 2) (i : M.ι) :
    (Pi.single (a, (b, i)) 1 : (Wl M).ι → A) = tv a (tv b (Pi.single i 1)) := by
  rw [Tensor2.single_prod_eq_tprod, Tensor2.single_prod_eq_tprod]
  rfl

lemma slot2_Wl (a b a' b' : Fin 2) (m : M.ι → A) :
    slot2 a b (tv a' (tv b' m) : (Wl M).ι → A) = if a = a' ∧ b = b' then m else 0 := by
  funext i
  simp only [slot2_apply, tv_apply]
  by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]

lemma Wl_F0 (x : (Tensor2.tensor (V A) M).ι → A) :
    (Wl M).Fd 1 (tv 0 x) = tv 1 x + tv 0 ((Tensor2.tensor (V A) M).Fd 1 x) :=
  tensorV_Fd1_tv0 _ x

end W

