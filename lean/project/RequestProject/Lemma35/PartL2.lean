module

public import RequestProject.Lemma35.Basic

/-!
# `C22_lemma_35_over_F2.md`: Part L, (L2) `Δ(3) ≅ V ⊗ V^{[1]}`

Encodings (namespace `Lemma35`), for a commutative ring `B` with `h2 : (2 : B) = 0`:

* `VV1 h2 := tensorV (Twist.frob h2 (V B))` is `V ⊗ V^{[1]}`, with basis `Fin 2 × Fin 2`; the
  basis vector `b_e b'_{e'}` is `bb e e' := Pi.single (e, e') 1`. Its weights are
  `wtV e + 2·wtV e'`.
* `Δ(3) = delta B 3` has basis `Fin 4` (`Fin (3 + 1)`); `e_r` is `eW r := Pi.single r 1`.
* `uL = ofImg uimg : Δ(3) → V ⊗ V^{[1]}` is given on basis vectors by the table of the file
  (`u_basis`), and `uinvL = ofImg uinvimg` is the reverse bijection of bases (`uinv_basis`).
* `uHom h2`, `uinvHom h2` are the corresponding `Hom`s and `isoL2 h2 : Doubling.Iso (delta B 3)
  (VV1 h2)` has `hom = u`, `inv = u⁻¹`.
-/

@[expose] public section

noncomputable section

namespace Lemma35

open DPLattice Finset WeylFilt

variable {B : Type*} [CommRing B] (h2 : (2 : B) = 0)

/-- (L2) `V ⊗ V^{[1]} = tensorV (Twist.frob h2 (V B))`, basis `Fin 2 × Fin 2`. -/
abbrev VV1 : DPLattice B := tensorV (Twist.frob h2 (V B))

/-- (L2) the index type `Fin 2 × Fin 2` of the basis of `V ⊗ V^{[1]}`. -/
abbrev IU : Type := Fin 2 × Fin 2

/-- (L2) the basis vector `b_e b'_{e'} = δ_{(e, e')}` of `V ⊗ V^{[1]}`. -/
abbrev bb (e e' : Fin 2) : IU → B := Pi.single (e, e') 1

/-- (L2) the basis vector `e_r` of `Δ(3)`. -/
abbrev eW (r : Fin 4) : Fin 4 → B := Pi.single r 1

/-- (L2) the images of the basis vectors of `Δ(3)` under `u` (the table of the file). -/
def uimg : Fin 4 → IU → B := ![bb 0 0, bb 1 0, bb 0 1, bb 1 1]

/-- (L2) the images of the basis vectors of `V ⊗ V^{[1]}` under `u⁻¹` (reverse bijection). -/
def uinvimg : IU → Fin 4 → B := fun p => ![![eW 0, eW 2], ![eW 1, eW 3]] p.1 p.2

/-- (L2) the linear map `u : Δ(3) → V ⊗ V^{[1]}`. -/
def uL : (Fin 4 → B) →ₗ[B] (IU → B) := ofImg uimg

/-- (L2) the linear map `u⁻¹ : V ⊗ V^{[1]} → Δ(3)`. -/
def uinvL : (IU → B) →ₗ[B] (Fin 4 → B) := ofImg uinvimg

/-- (L2) `u` on basis vectors, exactly as in the file. -/
theorem u_basis :
    uL (eW 0) = bb (B := B) 0 0 ∧ uL (eW 1) = bb (B := B) 1 0 ∧
    uL (eW 2) = bb (B := B) 0 1 ∧ uL (eW 3) = bb (B := B) 1 1 := by
  simp only [uL, ofImg_single]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- (L2) `u⁻¹` on basis vectors: the reverse bijection of bases. -/
theorem uinv_basis :
    uinvL (bb 0 0) = eW (B := B) 0 ∧ uinvL (bb 1 0) = eW (B := B) 1 ∧
    uinvL (bb 0 1) = eW (B := B) 2 ∧ uinvL (bb 1 1) = eW (B := B) 3 := by
  simp only [uinvL, ofImg_single]
  exact ⟨rfl, rfl, rfl, rfl⟩

lemma delta3_wt_bound : ∀ i, -((3 : ℕ) : ℤ) ≤ (delta B 3).wt i ∧ (delta B 3).wt i ≤ ((3 : ℕ) : ℤ) := by
  intro i; fin_cases i <;> simp [delta, weylWt]

lemma VV1_wt_bound : ∀ i, -((3 : ℕ) : ℤ) ≤ (VV1 h2).wt i ∧ (VV1 h2).wt i ≤ ((3 : ℕ) : ℤ) := by
  rintro ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> simp [tensorV, tensorWt, Twist.frob, V]

lemma u_wt : ∀ (i : Fin 4) (j : IU), (VV1 h2).wt j ≠ (delta B 3).wt i →
    uL (Pi.single i 1 : Fin 4 → B) j = 0 := by
  rintro i ⟨a, b⟩ hj
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [tensorV, tensorWt, Twist.frob, V, delta, weylWt] at hj <;>
    simp [uL, uimg]

set_option maxHeartbeats 1000000 in
include h2 in
lemma u_comm_F (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (i : Fin 4) :
    uL ((delta B 3).Fd r (Pi.single i 1 : Fin 4 → B)) =
      (VV1 h2).Fd r (uL (Pi.single i 1 : Fin 4 → B)) := by
  have h3 : (3 : B) = 1 := by linear_combination h2
  funext ⟨a, b⟩
  interval_cases r <;> fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [uL, ofImg_apply, uimg, tensorV, tensorFd, Twist.frob, Twist.frobOp, V, VFd, delta,
      deltaF, VmatF, dotProduct, Fin.sum_univ_succ, Pi.single_apply,
      Matrix.toLin'_apply, deltaMatF, one_add_one_eq_two, h2, h3]

set_option maxHeartbeats 1000000 in
include h2 in
lemma u_comm_E (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (i : Fin 4) :
    uL ((delta B 3).Ed r (Pi.single i 1 : Fin 4 → B)) =
      (VV1 h2).Ed r (uL (Pi.single i 1 : Fin 4 → B)) := by
  have h3 : (3 : B) = 1 := by linear_combination h2
  funext ⟨a, b⟩
  interval_cases r <;> fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [uL, ofImg_apply, uimg, tensorV, tensorEd, Twist.frob, Twist.frobOp, V, VEd, delta,
      deltaE, VmatE, dotProduct, Fin.sum_univ_succ, Pi.single_apply,
      Matrix.toLin'_apply, deltaMatE, one_add_one_eq_two, h2, h3]

lemma uinv_u_single (i : Fin 4) : uinvL (uL (Pi.single i 1 : Fin 4 → B)) = Pi.single i 1 := by
  fin_cases i <;> simp [uL, uinvL, uimg, uinvimg]

lemma u_uinv_single (i : IU) : uL (uinvL (Pi.single i 1 : IU → B)) = Pi.single i 1 := by
  obtain ⟨a, b⟩ := i
  fin_cases a <;> fin_cases b <;> simp [uL, uinvL, uimg, uinvimg]

/-- (L2) `u : Δ(3) → V ⊗ V^{[1]}` is a `Hom` (when `2 = 0` in `B`). -/
def uHom : Hom (delta B 3) (VV1 h2) :=
  homOfSmall (delta B 3) (VV1 h2) uL 3 delta3_wt_bound (VV1_wt_bound h2) (u_comm_F h2)
    (u_comm_E h2) (u_wt h2)

lemma uinvL_comp_uL : uinvL ∘ₗ uL = (LinearMap.id : (Fin 4 → B) →ₗ[B] _) :=
  ext_single fun i => uinv_u_single i

lemma uL_comp_uinvL : uL ∘ₗ uinvL = (LinearMap.id : (IU → B) →ₗ[B] _) :=
  ext_single fun i => u_uinv_single i

/-- (L2) `u⁻¹ : V ⊗ V^{[1]} → Δ(3)` is a `Hom` (when `2 = 0` in `B`). -/
def uinvHom : Hom (VV1 h2) (delta B 3) :=
  Doubling.Hom.ofInverse (uHom h2) uinvL uinvL_comp_uL uL_comp_uinvL

@[simp] lemma uHom_toLin : (uHom h2).toLin = uL := rfl
@[simp] lemma uinvHom_toLin : (uinvHom h2).toLin = uinvL := rfl

/-- (L2) `u⁻¹ ∘ u = Hom.id`. -/
theorem uinv_u_id : Hom.comp (uinvHom h2) (uHom h2) = Hom.id (delta B 3) :=
  Hom.ext' uinvL_comp_uL

/-- (L2) `u ∘ u⁻¹ = Hom.id`. -/
theorem u_uinv_id : Hom.comp (uHom h2) (uinvHom h2) = Hom.id (VV1 h2) :=
  Hom.ext' uL_comp_uinvL

/-- (L2) the isomorphism `Δ(3) ≅ V ⊗ V^{[1]}`, with `hom = u` and `inv = u⁻¹`. -/
def isoL2 : Doubling.Iso (delta B 3) (VV1 h2) where
  hom := uHom h2
  inv := uinvHom h2
  hom_inv := uinv_u_id h2
  inv_hom := u_uinv_id h2

/-- (L2) `u (e_r) = F^{(r)}(b_0 b'_0)` for `r = 0, 1, 2, 3`. -/
theorem u_eW_eq_Fd (r : Fin 4) : uL (eW r) = (VV1 h2).Fd r (bb (B := B) 0 0) := by
  funext ⟨a, b⟩
  fin_cases r <;> fin_cases a <;> fin_cases b <;>
    simp [uL, uimg, tensorV, tensorFd, Twist.frob, Twist.frobOp, V, VFd, VmatF,
      dotProduct, Pi.single_apply, Matrix.toLin'_apply]

/-- (L2) Lemma 3.5, second isomorphism, over a commutative ring `B` with `2 = 0`:
`u : Δ(3) → V ⊗ V^{[1]}` and `u⁻¹` (given on basis vectors by the table of the file, `u_basis`,
`uinv_basis`) are `Hom`s and mutually inverse; hence `Δ(3) ≅ V ⊗ V^{[1]}`; and
`u (e_r) = F^{(r)}(b_0 b'_0)` for `r = 0, 1, 2, 3`. -/
theorem L2 :
    ∃ (u : Hom (delta B 3) (VV1 h2)) (u' : Hom (VV1 h2) (delta B 3)),
      u.toLin = uL ∧ u'.toLin = uinvL ∧
      Hom.comp u' u = Hom.id (delta B 3) ∧ Hom.comp u u' = Hom.id (VV1 h2) ∧
      Nonempty (Doubling.Iso (delta B 3) (tensorV (Twist.frob h2 (V B)))) ∧
      ∀ r : Fin 4, u.toLin (eW r) = (VV1 h2).Fd r (bb 0 0) :=
  ⟨uHom h2, uinvHom h2, rfl, rfl, uinv_u_id h2, u_uinv_id h2, ⟨isoL2 h2⟩, u_eW_eq_Fd h2⟩

end Lemma35
