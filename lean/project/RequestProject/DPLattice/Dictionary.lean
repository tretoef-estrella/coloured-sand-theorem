module

public import RequestProject.DPLattice.Tensor
public import RequestProject.CubeLaplacian.Basic

/-!
# `C18_divided_power_lattices_and_the_dictionary.md`: Part L (Lemma 2.2, the dictionary)

Encodings:
* The basis of `V^{⊗n} = tensorPow A n` is `Fin 2 × (Fin 2 × ⋯ × Unit)`; the first coordinate is
  position `0` (the first tensor factor). The pure tensor `b_{e_0} ⊗ ⋯ ⊗ b_{e_{n−1}}` with letters
  `b_1` exactly on the positions of `S : Finset (Fin n)` is the basis vector
  `Pi.single (pt A n S) 1`, where `pt A (n+1) S = (e_0, pt A n S')` with `e_0 = 1` iff `0 ∈ S`, and
  `S' = {i | i + 1 ∈ S}`; `pt A n` is a bijection (`pt_bijective`), so a basis vector is determined
  by its set of positions.
* `G n`, `CubeLaplacian.e` and the Laplacian `CubeLaplacian.lap A n` are those of C17.
* `Tn A n = F^{(1)} + n − H` on `V^{⊗n}` (with `n` acting as `n • id`).
* The equivalence `Ψ = psi A n : (G n → A) ≃ₗ[A] V^{⊗n}` is built by recursion on `n`, through
  `G (n+1) ≃ Fin 2 × G n`, `g ↦ (g 0, g ∘ succ)`: on slots, `Ψ_{n+1} f = b_0 Ψ_n(u + v) − b_1 Ψ_n(v)`
  with `u = f(0, ·)`, `v = f(1, ·)`. (In the group ring this is the map `s_S ↦` pure tensor with
  `b_1` on `S` of the file's sketch; the proof here checks the intertwining relation directly.)
-/

@[expose] public section

noncomputable section

namespace DPLattice

open Finset CubeLaplacian

variable {A : Type*} [CommRing A]

/-! ### Pure tensors -/

/-- (L1) the basis index of the pure tensor of `V^{⊗n}` with letters `b_1` on the positions `S`. -/
def pt (A : Type*) [CommRing A] : (n : ℕ) → Finset (Fin n) → (tensorPow A n).ι
  | 0, _ => ()
  | n + 1, S => ((if (0 : Fin (n + 1)) ∈ S then 1 else 0 : Fin 2),
      pt A n (univ.filter fun i : Fin n => i.succ ∈ S))

lemma pt_succ (n : ℕ) (S : Finset (Fin (n + 1))) :
    pt A (n + 1) S = ((if (0 : Fin (n + 1)) ∈ S then 1 else 0 : Fin 2),
      pt A n (univ.filter fun i : Fin n => i.succ ∈ S)) := rfl

lemma card_succ_filter (n : ℕ) (S : Finset (Fin (n + 1))) :
    S.card = (if (0 : Fin (n + 1)) ∈ S then 1 else 0) +
      (univ.filter fun i : Fin n => i.succ ∈ S).card := by
  have h1 : S.card = (univ.filter fun i : Fin (n + 1) => i ∈ S).card := by
    congr 1; ext; simp
  rw [h1, card_filter, card_filter, Fin.sum_univ_succ]

lemma pt_injective (n : ℕ) : Function.Injective (pt A n) := by
  induction n with
  | zero => intro S T _; ext i; exact Fin.elim0 i
  | succ n ih =>
    intro S T h
    rw [pt_succ, pt_succ, Prod.mk.injEq] at h
    obtain ⟨h0, h1⟩ := h
    have h1' := ih h1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · by_cases hS : (0 : Fin (n + 1)) ∈ S <;> by_cases hT : (0 : Fin (n + 1)) ∈ T <;>
        simp_all
    · have := congrArg (fun U => j ∈ U) h1'
      simpa using this

lemma natCard_tensorPow (n : ℕ) : Nat.card (tensorPow A n).ι = 2 ^ n := by
  induction n with
  | zero => show Nat.card Unit = 1; simp
  | succ n ih =>
    show Nat.card (Fin 2 × (tensorPow A n).ι) = _
    rw [Nat.card_prod, ih, Nat.card_eq_fintype_card, Fintype.card_fin, pow_succ, mul_comm]

/-- (L1) pure tensors: `pt A n` is a bijection from subsets of positions to the basis of
`V^{⊗n}`. -/
theorem pt_bijective (n : ℕ) : Function.Bijective (pt A n) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨pt_injective n, ?_⟩
  rw [Fintype.card_finset, Fintype.card_fin, Fintype.card_eq_nat_card, natCard_tensorPow]

lemma wt_pt (n : ℕ) (S : Finset (Fin n)) : (tensorPow A n).wt (pt A n S) = n - 2 * S.card := by
  induction n with
  | zero =>
    obtain rfl : S = ∅ := Subsingleton.elim _ _
    simp [tensorPow, one]
  | succ n ih =>
    rw [pt_succ, card_succ_filter]
    show wtV _ + (tensorPow A n).wt _ = _
    rw [ih]
    by_cases h : (0 : Fin (n + 1)) ∈ S <;> simp [h] <;> ring

/-- (L1) `H` multiplies the pure tensor with letters `b_1` on `S` by `n − 2|S|`. -/
theorem L1_H (n : ℕ) (S : Finset (Fin n)) :
    H (tensorPow A n) (Pi.single (pt A n S) 1) =
      (((n : ℤ) - 2 * S.card : ℤ) : A) • (Pi.single (pt A n S) (1 : A) : (tensorPow A n).ι → A) := by
  funext i
  by_cases hi : i = pt A n S
  · subst hi; simp [wt_pt]
  · simp [hi]

lemma sum_compl_eq (n : ℕ) {X : Type*} [AddCommMonoid X] (S : Finset (Fin n)) (g : Fin n → X) :
    ∑ j ∈ Sᶜ, g j = ∑ j, if j ∈ S then 0 else g j := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  congr 1; ext; simp

lemma filter_insert_succ (n : ℕ) (S : Finset (Fin (n + 1))) (j : Fin n) :
    (univ.filter fun i : Fin n => i.succ ∈ insert j.succ S) =
      insert j (univ.filter fun i : Fin n => i.succ ∈ S) := by
  ext i; simp [Fin.succ_inj]

lemma filter_insert_zero (n : ℕ) (S : Finset (Fin (n + 1))) :
    (univ.filter fun i : Fin n => i.succ ∈ insert 0 S) =
      (univ.filter fun i : Fin n => i.succ ∈ S) := by
  ext i; simp [Fin.succ_ne_zero]

/-- (L1) `F^{(1)}` sends the pure tensor with letters `b_1` on `S` to the sum, over the positions
`j ∉ S`, of the pure tensor with letters `b_1` on `S ∪ {j}`. -/
theorem L1_F (n : ℕ) (S : Finset (Fin n)) :
    (tensorPow A n).Fd 1 (Pi.single (pt A n S) 1) =
      ∑ j ∈ Sᶜ, Pi.single (pt A n (insert j S)) 1 := by
  induction n with
  | zero =>
    have : Sᶜ = ∅ := by ext i; exact Fin.elim0 i
    rw [this, sum_empty]
    simp [tensorPow, one, oneFd]
  | succ n ih =>
    set S' := univ.filter fun i : Fin n => i.succ ∈ S with hS'
    rw [sum_compl_eq, Fin.sum_univ_succ]
    have hsucc : ∀ j : Fin n, (if j.succ ∈ S then (0 : (tensorPow A (n + 1)).ι → A) else
        Pi.single (pt A (n + 1) (insert j.succ S)) 1) =
        bvec (if (0 : Fin (n + 1)) ∈ S then 1 else 0)
          (if j ∈ S' then 0 else Pi.single (pt A n (insert j S')) 1) := by
      intro j
      have hj : j.succ ∈ S ↔ j ∈ S' := by simp [hS']
      by_cases h : j ∈ S'
      · rw [if_pos (hj.mpr h), if_pos h, map_zero]
      · rw [if_neg (mt hj.mp h), if_neg h, pt_succ, filter_insert_succ, ← hS']
        have : ((0 : Fin (n + 1)) ∈ insert j.succ S) ↔ (0 : Fin (n + 1)) ∈ S := by
          simp [(Fin.succ_ne_zero j).symm]
        simp only [this]
        exact single_eq_bvec _ _
    simp only [hsucc]
    rw [← map_sum (bvec (if (0 : Fin (n + 1)) ∈ S then 1 else 0))
      (fun x => if x ∈ S' then 0 else Pi.single (pt A n (insert x S')) 1) univ,
      ← sum_compl_eq, ← ih S']
    rw [pt_succ, ← hS', single_eq_bvec]
    by_cases h0 : (0 : Fin (n + 1)) ∈ S
    · simp only [h0, if_true, zero_add]
      exact tensorFd_bvec1 (tensorPow A n).Fd 1 _
    · simp only [h0, if_false]
      show tensorFd (tensorPow A n).Fd 1 _ = _
      rw [tensorFd_bvec0, pred_succ, (tensorPow A n).isDP.P0_F, pt_succ, filter_insert_zero,
        ← hS', single_eq_bvec]
      simp only [Finset.mem_insert, true_or, if_true]
      rw [add_comm]; rfl

/-! ### Lemma 2.2 -/

/-- (L2) the operator `F^{(1)} + n − H` on `V^{⊗n}` (`n` acts as `n • id`). -/
def Tn (A : Type*) [CommRing A] (n : ℕ) : Module.End A ((tensorPow A n).ι → A) :=
  (tensorPow A n).Fd 1 + (n : A) • LinearMap.id - H (tensorPow A n)

section slicewise

variable {α β : Type*}

/-- (L2, auxiliary) Apply a linear map in each slot of `V ⊗ −`. -/
def sliceMap (φ : (α → A) →ₗ[A] (β → A)) : (Fin 2 × α → A) →ₗ[A] (Fin 2 × β → A) :=
  bvec 0 ∘ₗ φ ∘ₗ slice 0 + bvec 1 ∘ₗ φ ∘ₗ slice 1

@[simp] lemma slice0_sliceMap (φ : (α → A) →ₗ[A] (β → A)) (h : Fin 2 × α → A) :
    slice 0 (sliceMap φ h) = φ (slice 0 h) := by simp [sliceMap]

@[simp] lemma slice1_sliceMap (φ : (α → A) →ₗ[A] (β → A)) (h : Fin 2 × α → A) :
    slice 1 (sliceMap φ h) = φ (slice 1 h) := by simp [sliceMap]

lemma sliceMap_comp {γ : Type*} (φ : (β → A) →ₗ[A] (γ → A)) (ψ : (α → A) →ₗ[A] (β → A)) :
    sliceMap φ ∘ₗ sliceMap ψ = sliceMap (φ ∘ₗ ψ) :=
  LinearMap.ext fun h => ext_slice (by simp) (by simp)

lemma sliceMap_id : sliceMap (LinearMap.id : (α → A) →ₗ[A] (α → A)) = LinearMap.id :=
  LinearMap.ext fun h => ext_slice (by simp) (by simp)

/-- (L2, auxiliary) Apply a linear equivalence in each slot of `V ⊗ −`. -/
def sliceEquiv (Φ : (α → A) ≃ₗ[A] (β → A)) : (Fin 2 × α → A) ≃ₗ[A] (Fin 2 × β → A) :=
  LinearEquiv.ofLinear (sliceMap Φ.toLinearMap) (sliceMap Φ.symm.toLinearMap)
    (by rw [sliceMap_comp, LinearEquiv.comp_symm, sliceMap_id])
    (by rw [sliceMap_comp, LinearEquiv.symm_comp, sliceMap_id])

/-- (L2, auxiliary) The shear `(h_0, h_1) ↦ (h_0 + h_1, −h_1)` on the slots (an involution). -/
def shear : Module.End A (Fin 2 × α → A) :=
  bvec 0 ∘ₗ (slice 0 + slice 1) - bvec 1 ∘ₗ slice 1

@[simp] lemma slice0_shear (h : Fin 2 × α → A) : slice 0 (shear h) = slice 0 h + slice 1 h := by
  simp [shear]

@[simp] lemma slice1_shear (h : Fin 2 × α → A) : slice 1 (shear h) = -slice 1 h := by
  simp [shear]

lemma shear_involutive : Function.Involutive (shear (α := α) (A := A)) :=
  fun h => ext_slice (by simp) (by simp)

/-- (L2, auxiliary) The shear as a linear equivalence. -/
def shearEquiv : (Fin 2 × α → A) ≃ₗ[A] (Fin 2 × α → A) :=
  LinearEquiv.ofInvolutive shear shear_involutive

end slicewise

/-- (L2, auxiliary) `G (n+1) ≃ Fin 2 × G n`, `g ↦ (g 0, g ∘ succ)`, on functions. -/
def gSplit (A : Type*) [CommRing A] (n : ℕ) : (G (n + 1) → A) ≃ₗ[A] (Fin 2 × G n → A) :=
  LinearEquiv.funCongrLeft A A
    (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod 2) : Fin 2 × G n ≃ G (n + 1))

lemma gSplit_apply (n : ℕ) (f : G (n + 1) → A) (a : Fin 2) (g : G n) :
    gSplit A n f (a, g) = f (Fin.cons (a : ZMod 2) g) := rfl

/-- (L2) the equivalence `Ψ : (G n → A) ≃ₗ[A] V^{⊗n}`, by recursion on `n`. -/
def psi (A : Type*) [CommRing A] : (n : ℕ) → (G n → A) ≃ₗ[A] ((tensorPow A n).ι → A)
  | 0 => LinearEquiv.funCongrLeft A A (Equiv.equivPUnit (G 0)).symm
  | n + 1 => ((gSplit A n).trans shearEquiv).trans (sliceEquiv (psi A n))

lemma slice0_psi_succ (n : ℕ) (f : G (n + 1) → A) :
    slice 0 (psi A (n + 1) f) =
      psi A n (slice 0 (gSplit A n f) + slice 1 (gSplit A n f)) := by
  show slice 0 (sliceMap _ (shear _)) = _
  rw [slice0_sliceMap, slice0_shear]; rfl

lemma slice1_psi_succ (n : ℕ) (f : G (n + 1) → A) :
    slice 1 (psi A (n + 1) f) = psi A n (-slice 1 (gSplit A n f)) := by
  show slice 1 (sliceMap _ (shear _)) = _
  rw [slice1_sliceMap, slice1_shear]; rfl

lemma cons_add_e_zero (n : ℕ) (a : ZMod 2) (g : G n) :
    (Fin.cons a g : G (n + 1)) + e (n + 1) 0 = Fin.cons (a + 1) g := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [e]
  · simp [e, Fin.succ_ne_zero]

lemma cons_add_e_succ (n : ℕ) (a : ZMod 2) (g : G n) (i : Fin n) :
    (Fin.cons a g : G (n + 1)) + e (n + 1) i.succ = Fin.cons a (g + e n i) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [e, (Fin.succ_ne_zero i).symm]
  · simp [e, Pi.single_apply, Fin.succ_inj]

lemma lap_cons (n : ℕ) (f : G (n + 1) → A) (a : ZMod 2) (g : G n) :
    lap A (n + 1) f (Fin.cons a g) = f (Fin.cons a g) - f (Fin.cons (a + 1) g) +
      lap A n (fun g' => f (Fin.cons a g')) g := by
  rw [lap_apply, lap_apply, Fin.sum_univ_succ, cons_add_e_zero]
  simp only [cons_add_e_succ]
  push_cast; ring

lemma slice0_gSplit_lap (n : ℕ) (f : G (n + 1) → A) :
    slice 0 (gSplit A n (lap A (n + 1) f)) = slice 0 (gSplit A n f) - slice 1 (gSplit A n f) +
      lap A n (slice 0 (gSplit A n f)) := by
  funext g
  exact lap_cons n f 0 g

lemma slice1_gSplit_lap (n : ℕ) (f : G (n + 1) → A) :
    slice 1 (gSplit A n (lap A (n + 1) f)) = slice 1 (gSplit A n f) - slice 0 (gSplit A n f) +
      lap A n (slice 1 (gSplit A n f)) := by
  funext g
  exact lap_cons n f 1 g

lemma slice0_Tn (n : ℕ) (h : (tensorPow A (n + 1)).ι → A) :
    slice 0 (Tn A (n + 1) h) = Tn A n (slice 0 h) := by
  funext i
  have : (tensorPow A (n + 1)).Fd 1 = tensorFd (tensorPow A n).Fd 1 := rfl
  simp only [Tn, this, tensorFd, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, slice_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Hop_apply,
    smul_eq_mul]
  simp [tensorPow, tensorV, tensorWt]
  ring

lemma slice1_Tn (n : ℕ) (h : (tensorPow A (n + 1)).ι → A) :
    slice 1 (Tn A (n + 1) h) = Tn A n (slice 1 h) + (slice 1 h + slice 1 h) + slice 0 h := by
  funext i
  have : (tensorPow A (n + 1)).Fd 1 = tensorFd (tensorPow A n).Fd 1 := rfl
  have hP0 := (tensorPow A n).isDP.P0_F
  simp only [Tn, this, tensorFd, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, slice_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Hop_apply,
    smul_eq_mul]
  simp [tensorPow, tensorV, tensorWt, hP0]
  ring

/-- (L2) `Ψ ∘ lap A n = (F^{(1)} + n − H) ∘ Ψ` for the explicit `Ψ = psi A n`. -/
theorem psi_comm (n : ℕ) :
    (psi A n).toLinearMap ∘ₗ lap A n = Tn A n ∘ₗ (psi A n).toLinearMap := by
  induction n with
  | zero =>
    refine LinearMap.ext fun f => ?_
    funext u
    simp [Tn, lap_apply, tensorPow, one, oneFd, psi]
  | succ n ih =>
    have ih' : ∀ x, psi A n (lap A n x) = Tn A n (psi A n x) := fun x => LinearMap.congr_fun ih x
    refine LinearMap.ext fun f => ext_slice ?_ ?_
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [slice0_psi_succ, slice0_Tn, slice0_psi_succ, slice0_gSplit_lap, slice1_gSplit_lap,
        ← ih', (lap A n).map_add]
      congr 1; abel
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [slice1_psi_succ, slice1_Tn, slice1_psi_succ, slice0_psi_succ, slice1_gSplit_lap,
        ← ih', ← map_add, ← map_add, ← map_add]
      congr 1
      rw [map_neg]; abel

/-- (L2) Lemma 2.2: there is an `A`-linear equivalence `Ψ : (G n → A) ≃ₗ[A] V^{⊗n}` with
`Ψ ∘ lap A n = (F^{(1)} + n − H) ∘ Ψ`. -/
theorem L2 (n : ℕ) : ∃ Ψ : (G n → A) ≃ₗ[A] ((tensorPow A n).ι → A),
    Ψ.toLinearMap ∘ₗ lap A n = Tn A n ∘ₗ Ψ.toLinearMap :=
  ⟨psi A n, psi_comm n⟩

end DPLattice
