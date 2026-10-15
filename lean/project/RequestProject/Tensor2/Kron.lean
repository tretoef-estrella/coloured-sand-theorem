module

public import RequestProject.Lemma35.Sum

/-!
# `C23_the_tensor_product.md`: Setting — the Kronecker product `f ⊠ g`

Encodings (namespace `Tensor2`), for a commutative ring `A`:

* A vector of `ι × κ → A` with `ι`, `κ` finite; the basis vector `δ_{(i,j)}` is
  `Pi.single (i, j) 1`.
* `tprod m n` is the "pure tensor" `m ⊗ n : ι × κ → A`, `(m ⊗ n) (i, j) = m i * n j`; in
  particular `δ_{(i,j)} = tprod δ_i δ_j` (`single_prod_eq_tprod`).
* `kron f g` is `f ⊠ g` of the Setting: the linear map `(ι × κ → A) → (ι' × κ' → A)` whose matrix
  is the Kronecker product of the matrices of `f` and `g`, so that
  `(f ⊠ g)(δ_{(i,j)}) (i', j') = f(δ_i)(i') · g(δ_j)(j')` (`kron_single_apply`).
-/

@[expose] public section

noncomputable section

namespace Tensor2

open Finset

variable {A : Type*} [CommRing A]

section tprod

variable {ι κ : Type*}

/-- Setting: the pure tensor `m ⊗ n`, `(m ⊗ n) (i, j) = m i * n j`. -/
def tprod (m : ι → A) (n : κ → A) : ι × κ → A := fun p => m p.1 * n p.2

@[simp] lemma tprod_apply (m : ι → A) (n : κ → A) (p : ι × κ) : tprod m n p = m p.1 * n p.2 :=
  rfl

lemma tprod_add_left (m m' : ι → A) (n : κ → A) : tprod (m + m') n = tprod m n + tprod m' n := by
  funext p; simp [add_mul]

lemma tprod_add_right (m : ι → A) (n n' : κ → A) : tprod m (n + n') = tprod m n + tprod m n' := by
  funext p; simp [mul_add]

lemma tprod_smul_left (c : A) (m : ι → A) (n : κ → A) : tprod (c • m) n = c • tprod m n := by
  funext p; simp [mul_assoc]

lemma tprod_smul_right (c : A) (m : ι → A) (n : κ → A) : tprod m (c • n) = c • tprod m n := by
  funext p; simp; ring

@[simp] lemma tprod_zero_left (n : κ → A) : tprod (0 : ι → A) n = 0 := by funext p; simp
@[simp] lemma tprod_zero_right (m : ι → A) : tprod m (0 : κ → A) = 0 := by funext p; simp

lemma tprod_sum_left {α : Type*} (s : Finset α) (m : α → ι → A) (n : κ → A) :
    tprod (∑ a ∈ s, m a) n = ∑ a ∈ s, tprod (m a) n := by
  funext p; simp [Finset.sum_apply, Finset.sum_mul]

lemma tprod_sum_right {α : Type*} (s : Finset α) (m : ι → A) (n : α → κ → A) :
    tprod m (∑ a ∈ s, n a) = ∑ a ∈ s, tprod m (n a) := by
  funext p; simp [Finset.sum_apply, Finset.mul_sum]

lemma single_prod_eq_tprod [DecidableEq ι] [DecidableEq κ] (i : ι) (j : κ) :
    (Pi.single (i, j) (1 : A) : ι × κ → A) = tprod (Pi.single i 1) (Pi.single j 1) := by
  funext ⟨i', j'⟩
  by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [Pi.single_apply, hi, hj]

end tprod

section kron

variable {ι ι' ι'' κ κ' κ'' : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Setting: the Kronecker product `f ⊠ g` of linear maps `f : (ι → A) → (ι' → A)` and
`g : (κ → A) → (κ' → A)`: the linear map `(ι × κ → A) → (ι' × κ' → A)` whose matrix is the
Kronecker product of the matrices of `f` and `g`. -/
def kron (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    (ι × κ → A) →ₗ[A] (ι' × κ' → A) :=
  Matrix.toLin' (Matrix.kroneckerMap (· * ·) (LinearMap.toMatrix' f) (LinearMap.toMatrix' g))

/-- Setting: `(f ⊠ g)(δ_{(i,j)}) (i', j') = f(δ_i)(i') · g(δ_j)(j')`. -/
theorem kron_single_apply (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A))
    (i : ι) (j : κ) (i' : ι') (j' : κ') :
    kron f g (Pi.single (i, j) 1) (i', j') = f (Pi.single i 1) i' * g (Pi.single j 1) j' := by
  simp [kron, Matrix.toLin'_apply, LinearMap.toMatrix'_apply]

/-- `(f ⊠ g)(m ⊗ n) = f m ⊗ g n`. -/
theorem kron_tprod (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A))
    (m : ι → A) (n : κ → A) : kron f g (tprod m n) = tprod (f m) (g n) := by
  conv_rhs => rw [← Matrix.toLin'_toMatrix' f, ← Matrix.toLin'_toMatrix' g]
  funext ⟨i', j'⟩
  simp only [kron, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, tprod_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma kron_comp [Fintype ι'] [Fintype κ'] [DecidableEq ι'] [DecidableEq κ'] (f : (ι' → A) →ₗ[A] (ι'' → A)) (g : (κ' → A) →ₗ[A] (κ'' → A))
    (f' : (ι → A) →ₗ[A] (ι' → A)) (g' : (κ → A) →ₗ[A] (κ' → A)) :
    kron f g ∘ₗ kron f' g' = kron (f ∘ₗ f') (g ∘ₗ g') := by
  simp only [kron, LinearMap.toMatrix'_comp, Matrix.mul_kronecker_mul, Matrix.toLin'_mul]

lemma kron_comp_apply [Fintype ι'] [Fintype κ'] [DecidableEq ι'] [DecidableEq κ'] (f : (ι' → A) →ₗ[A] (ι'' → A)) (g : (κ' → A) →ₗ[A] (κ'' → A))
    (f' : (ι → A) →ₗ[A] (ι' → A)) (g' : (κ → A) →ₗ[A] (κ' → A)) (x : ι × κ → A) :
    kron f g (kron f' g' x) = kron (f ∘ₗ f') (g ∘ₗ g') x := by
  rw [← kron_comp]; rfl

lemma kron_id : kron (LinearMap.id : (ι → A) →ₗ[A] (ι → A)) (LinearMap.id : (κ → A) →ₗ[A] _) =
    LinearMap.id := by
  simp [kron]

lemma kron_one : kron (1 : Module.End A (ι → A)) (1 : Module.End A (κ → A)) = 1 := kron_id

lemma kron_add_left (f f' : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    kron (f + f') g = kron f g + kron f' g := by
  simp [kron, Matrix.add_kronecker]

lemma kron_add_right (f : (ι → A) →ₗ[A] (ι' → A)) (g g' : (κ → A) →ₗ[A] (κ' → A)) :
    kron f (g + g') = kron f g + kron f g' := by
  simp [kron, Matrix.kronecker_add]

lemma kron_smul_left (c : A) (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    kron (c • f) g = c • kron f g := by
  simp [kron, Matrix.smul_kronecker]

lemma kron_smul_right (c : A) (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    kron f (c • g) = c • kron f g := by
  simp [kron, Matrix.kronecker_smul]

lemma kron_zero_left (g : (κ → A) →ₗ[A] (κ' → A)) :
    kron (0 : (ι → A) →ₗ[A] (ι' → A)) g = 0 := by
  simp [kron]

lemma kron_zero_right (f : (ι → A) →ₗ[A] (ι' → A)) :
    kron f (0 : (κ → A) →ₗ[A] (κ' → A)) = 0 := by
  simp [kron]

lemma kron_sum_left {α : Type*} (s : Finset α) (f : α → (ι → A) →ₗ[A] (ι' → A))
    (g : (κ → A) →ₗ[A] (κ' → A)) : kron (∑ a ∈ s, f a) g = ∑ a ∈ s, kron (f a) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [kron_zero_left]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, kron_add_left, ih]

lemma kron_sum_right {α : Type*} (s : Finset α) (f : (ι → A) →ₗ[A] (ι' → A))
    (g : α → (κ → A) →ₗ[A] (κ' → A)) : kron f (∑ a ∈ s, g a) = ∑ a ∈ s, kron f (g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [kron_zero_right]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, kron_add_right, ih]

/-- `H`-type diagonal operators: `Hop wt ⊠ 1 + 1 ⊠ Hop wt' = Hop (wt i + wt' j)`. -/
lemma kron_Hop (wt : ι → ℤ) (wt' : κ → ℤ) :
    kron (DPLattice.Hop (A := A) wt) 1 + kron 1 (DPLattice.Hop wt') =
      DPLattice.Hop (fun p : ι × κ => wt p.1 + wt' p.2) := by
  refine DPLattice.ext_single fun ⟨i, j⟩ => ?_
  rw [single_prod_eq_tprod, LinearMap.add_apply, kron_tprod, kron_tprod]
  funext ⟨i', j'⟩
  by_cases hi : i' = i <;> by_cases hj : j' = j <;>
    simp [hi, hj]

end kron

end Tensor2
