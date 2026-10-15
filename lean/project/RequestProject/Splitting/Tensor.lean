module

public import RequestProject.Splitting.Basic

/-!
# Tensor powers, encoded on functions

Auxiliary material for the proof of **(A2) The splitting** of `CS2_theorem_A_splitting.md`
(the first bullet of its proof: `L = Σᵢ 1 ⊗ ⋯ ⊗ K^{(i)} ⊗ ⋯ ⊗ 1` on `(ℤ^q)^{⊗ d}`).

## Encoding

`(R^α)^{⊗ d}` is encoded directly as `(Fin d → α) → R` (the pure tensor `h₁ ⊗ ⋯ ⊗ h_d` is the
function `x ↦ ∏ᵢ hᵢ (xᵢ)`, `prodFun h`).

* `coordOp A i` is `1 ⊗ ⋯ ⊗ A^{(i)} ⊗ ⋯ ⊗ 1`, i.e. `(coordOp A i f) x = Σₐ A (xᵢ) a f(x[i ↦ a])`;
  `coordOp_prodFun` shows it acts on pure tensors by applying `A` in the `i`-th factor.
* For a basis `b` of `α → R`, `tensorEquiv b` is the change of basis to the tensor basis
  `B_z = b_{z₁} ⊗ ⋯ ⊗ b_{z_d}`: it is the linear equivalence of `(Fin d → α) → R` sending the
  coefficient vector `e_z` to `B_z` (`tensorEquiv_single`).
-/

@[expose] public section

open Finset Matrix

namespace ColouredSand.Splitting

variable {R : Type*} [CommRing R] {d : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

/-- The pure tensor `h₁ ⊗ ⋯ ⊗ h_d`, as the function `x ↦ ∏ᵢ hᵢ (xᵢ)`. -/
def prodFun (h : Fin d → α → R) : (Fin d → α) → R := fun x => ∏ i, h i (x i)

/-- `1 ⊗ ⋯ ⊗ A^{(i)} ⊗ ⋯ ⊗ 1`: `(coordOp A i f) x = Σₐ A (xᵢ) a · f (x[i ↦ a])`. -/
def coordOp (A : Matrix α α R) (i : Fin d) : ((Fin d → α) → R) →ₗ[R] ((Fin d → α) → R) where
  toFun f x := ∑ a, A (x i) a * f (Function.update x i a)
  map_add' f g := by ext x; simp [mul_add, sum_add_distrib]
  map_smul' c f := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

omit [DecidableEq α] in
lemma coordOp_apply (A : Matrix α α R) (i : Fin d) (f : (Fin d → α) → R) (x : Fin d → α) :
    coordOp A i f x = ∑ a, A (x i) a * f (Function.update x i a) := rfl

omit [Fintype α] [DecidableEq α] in
lemma prodFun_eq_mul_erase (h : Fin d → α → R) (x : Fin d → α) (i : Fin d) :
    prodFun h x = h i (x i) * ∏ j ∈ univ.erase i, h j (x j) :=
  (Finset.mul_prod_erase univ (fun j => h j (x j)) (mem_univ i)).symm

omit [DecidableEq α] in
/-- `A^{(i)}` acts on a pure tensor by applying `A` to its `i`-th factor. -/
lemma coordOp_prodFun (A : Matrix α α R) (i : Fin d) (h : Fin d → α → R) :
    coordOp A i (prodFun h) = prodFun (Function.update h i (A *ᵥ h i)) := by
  ext x
  rw [coordOp_apply, prodFun_eq_mul_erase _ x i]
  simp only [Function.update_self]
  have hrest : ∀ a, ∏ j ∈ univ.erase i, h j (Function.update x i a j) =
      ∏ j ∈ univ.erase i, Function.update h i (A *ᵥ h i) j (x j) := by
    intro a
    refine Finset.prod_congr rfl fun j hj => ?_
    have hji : j ≠ i := ne_of_mem_erase hj
    simp [hji]
  simp only [fun a => prodFun_eq_mul_erase h (Function.update x i a) i, Function.update_self,
    hrest, mulVec, dotProduct, sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

omit [Fintype α] [DecidableEq α] in
lemma prodFun_update_smul (h : Fin d → α → R) (i : Fin d) (c : R) :
    prodFun (Function.update h i (c • h i)) = c • prodFun h := by
  ext x
  rw [prodFun_eq_mul_erase _ x i, Pi.smul_apply, prodFun_eq_mul_erase h x i]
  simp only [Function.update_self, Pi.smul_apply, smul_eq_mul]
  rw [mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun j hj => ?_
  simp [ne_of_mem_erase hj]

/-! ### Kronecker powers and the tensor basis -/

/-- The `d`-th Kronecker power of a square matrix: entries `∏ᵢ P (xᵢ) (yᵢ)`. -/
def kronPow (d : ℕ) (P : Matrix α α R) : Matrix (Fin d → α) (Fin d → α) R :=
  Matrix.of fun x y => ∏ i, P (x i) (y i)

omit [DecidableEq α] in
lemma kronPow_mul (P Q : Matrix α α R) : kronPow d P * kronPow d Q = kronPow d (P * Q) := by
  ext x z
  simp only [kronPow, mul_apply, of_apply]
  rw [Finset.prod_univ_sum (fun _ => (univ : Finset α))]
  simp only [Fintype.piFinset_univ, ← Finset.prod_mul_distrib]

omit [Fintype α] in
lemma kronPow_one : kronPow d (1 : Matrix α α R) = 1 := by
  ext x z
  simp only [kronPow, of_apply, one_apply, Finset.prod_boole, mem_univ, true_implies]
  by_cases h : x = z
  · simp [h]
  · rw [if_neg (fun h' => h (funext h')), if_neg h]

/-- The matrix whose columns are the vectors of `b`: `P a k = b k a`. -/
noncomputable def basisMat (b : Module.Basis α R (α → R)) : Matrix α α R := Matrix.of fun a k => b k a

/-- The inverse matrix: `Q k a` is the `k`-th coordinate of `e_a`. -/
noncomputable def basisMatInv (b : Module.Basis α R (α → R)) : Matrix α α R :=
  Matrix.of fun k a => b.repr (Pi.single a 1) k

lemma basisMat_mul_inv (b : Module.Basis α R (α → R)) : basisMat b * basisMatInv b = 1 := by
  ext a a'
  have h := congrFun (b.sum_repr (Pi.single a' 1)) a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [basisMat, basisMatInv, mul_apply, of_apply]
  rw [one_apply]
  simp_rw [mul_comm (b _ a)]
  rw [h, Pi.single_apply]

/-- The change of basis to the tensor basis `B_z = b_{z₁} ⊗ ⋯ ⊗ b_{z_d}`. -/
noncomputable def tensorEquiv (d : ℕ) (b : Module.Basis α R (α → R)) :
    ((Fin d → α) → R) ≃ₗ[R] ((Fin d → α) → R) :=
  LinearEquiv.ofLinear (kronPow d (basisMat b)).mulVecLin (kronPow d (basisMatInv b)).mulVecLin
    (by rw [← mulVecLin_mul, kronPow_mul, basisMat_mul_inv, kronPow_one, mulVecLin_one])
    (by rw [← mulVecLin_mul, kronPow_mul, mul_eq_one_comm.mp (basisMat_mul_inv b), kronPow_one,
      mulVecLin_one])

lemma tensorEquiv_apply (b : Module.Basis α R (α → R)) (c : (Fin d → α) → R) :
    tensorEquiv d b c = kronPow d (basisMat b) *ᵥ c := rfl

/-- `tensorEquiv` sends `e_z` to `B_z = b_{z₁} ⊗ ⋯ ⊗ b_{z_d}`. -/
lemma tensorEquiv_single (b : Module.Basis α R (α → R)) (z : Fin d → α) :
    tensorEquiv d b (Pi.single z 1) = prodFun (fun i => b (z i)) := by
  ext x
  rw [tensorEquiv_apply, mulVec_single_one]
  simp [kronPow, basisMat, prodFun]

end ColouredSand.Splitting
