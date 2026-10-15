module

public import RequestProject.Splitting.Laplacian

/-!
# The Laplacian of `H(d,q)` in the tensor basis

Part of the proof of **(A2) The splitting** of `CS2_theorem_A_splitting.md` (second to fourth
bullets of its proof).  We write `q = n + 2`.

We use the basis `b_0 = e_0`, `b_1 = −σ`, `b_{k} = f_{k−1}` (`2 ≤ k ≤ q − 1`) of `ℤ^q`
(the basis of (A1) with `σ` replaced by `−σ`, which absorbs the sign change `(−1)^{|S|}` of the
file), so that `K b_0 = b_1` and `K b_k = q b_k` for `k ≥ 1`.  In the tensor basis
`B_z = b_{z_1} ⊗ ⋯ ⊗ b_{z_d}` (`z : Fin d → Fin q`) the Laplacian becomes the operator `Nop`:
`L B_z = q·#{i | zᵢ ≠ 0} B_z + Σ_{i : zᵢ = 0} B_{z[i ↦ 1]}`, i.e. on coefficients
`(Nop c)(y) = q·#{i | yᵢ ≠ 0} c(y) + Σ_{i : yᵢ = 1} c(y[i ↦ 0])` (`laplacian_conj`).
-/

@[expose] public section

open Finset Matrix

namespace ColouredSand.Splitting

variable (n d : ℕ)

/-- The basis `e_0, −σ, f_1, …, f_{q−2}` of `ℤ^q`, `q = n + 2`. -/
noncomputable def hamBasis : Module.Basis (Fin (n + 2)) ℤ (Fin (n + 2) → ℤ) :=
  (Classical.choose (basisVec_isBasis (q := n + 2) (by omega))).unitsSMul
    (fun k => if k = 1 then -1 else 1)

variable {n d}

lemma hamBasis_apply (k : Fin (n + 2)) :
    hamBasis n k = (if k = 1 then (-1 : ℤ) else 1) • basisVec (n + 2) k := by
  rw [hamBasis, Module.Basis.unitsSMul_apply,
    Classical.choose_spec (basisVec_isBasis (q := n + 2) (by omega))]
  split_ifs <;> simp

lemma hamBasis_K (k : Fin (n + 2)) :
    Kmat (n + 2) *ᵥ hamBasis n k =
      if k = 0 then hamBasis n 1 else (((n + 2 : ℕ) : ℤ)) • hamBasis n k := by
  rw [hamBasis_apply, hamBasis_apply 1, if_pos rfl, mulVec_smul]
  by_cases h0 : k = 0
  · subst h0
    rw [if_pos rfl, if_neg (by simp), basisVec_zero _ rfl, basisVec_one _ rfl, one_smul,
      K_ev_zero (by omega)]
    simp
  · rw [if_neg h0]
    by_cases h1 : k = 1
    · subst h1
      rw [basisVec_one _ rfl, K_sigma, smul_comm]
    · rw [basisVec_ge_two _ (by
        have h0' : (k : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
        have h1' : (k : ℕ) ≠ 1 := fun h => h1 (Fin.ext h)
        omega), K_fv (by omega), smul_comm]

variable (n d)

/-- The Laplacian in the tensor basis, on coefficients:
`(Nop c)(y) = q·#{i | yᵢ ≠ 0} c(y) + Σ_{i : yᵢ = 1} c(y[i ↦ 0])`, `q = n + 2`. -/
def Nop : ((Fin d → Fin (n + 2)) → ℤ) →ₗ[ℤ] ((Fin d → Fin (n + 2)) → ℤ) where
  toFun c y := ((n + 2 : ℕ) : ℤ) * (univ.filter fun i => y i ≠ 0).card * c y +
    ∑ i ∈ univ.filter (fun i => y i = 1), c (Function.update y i 0)
  map_add' f g := by ext y; simp [sum_add_distrib]; ring
  map_smul' a f := by
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add, Finset.mul_sum]
    ring

variable {n d}

lemma Nop_apply (c : (Fin d → Fin (n + 2)) → ℤ) (y : Fin d → Fin (n + 2)) :
    Nop n d c y = ((n + 2 : ℕ) : ℤ) * (univ.filter fun i => y i ≠ 0).card * c y +
      ∑ i ∈ univ.filter (fun i => y i = 1), c (Function.update y i 0) := rfl

lemma update_iff (y z : Fin d → Fin (n + 2)) (i : Fin d) :
    (y i = 1 ∧ Function.update y i 0 = z) ↔ (z i = 0 ∧ y = Function.update z i 1) := by
  constructor
  · rintro ⟨hy, rfl⟩
    refine ⟨by simp, ?_⟩
    rw [Function.update_idem, ← hy, Function.update_eq_self]
  · rintro ⟨hz, rfl⟩
    refine ⟨by simp, ?_⟩
    rw [Function.update_idem, ← hz, Function.update_eq_self]

lemma Nop_single (z : Fin d → Fin (n + 2)) :
    Nop n d (Pi.single z 1) =
      (((n + 2 : ℕ) : ℤ) * (univ.filter fun i => z i ≠ 0).card) • Pi.single z 1 +
        ∑ i ∈ univ.filter (fun i => z i = 0), Pi.single (Function.update z i 1) 1 := by
  ext y
  rw [Nop_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1
  · by_cases h : y = z
    · subst h; rfl
    · simp [h]
  · simp only [Pi.single_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ite_and, ← ite_and]
    exact if_congr (update_iff y z i) rfl rfl

lemma update_hamBasis_comp (z : Fin d → Fin (n + 2)) (i : Fin d) (a : Fin (n + 2)) :
    Function.update (fun j => hamBasis n (z j)) i (hamBasis n a) =
      fun j => hamBasis n (Function.update z i a j) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

lemma laplacian_tensor_single (z : Fin d → Fin (n + 2)) :
    laplacian d (n + 2) (prodFun fun i => hamBasis n (z i)) =
      ∑ i, if z i = 0 then prodFun (fun j => hamBasis n (Function.update z i 1 j))
        else ((n + 2 : ℕ) : ℤ) • prodFun (fun j => hamBasis n (z j)) := by
  rw [laplacian_eq_sum_coordOp, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordOp_prodFun, hamBasis_K]
  split_ifs with h
  · rw [update_hamBasis_comp]
  · exact prodFun_update_smul _ _ _

/-- **The Laplacian in the tensor basis.**  `L ∘ Ψ = Ψ ∘ Nop`, where `Ψ = tensorEquiv` is the
change of basis to `B_z = b_{z_1} ⊗ ⋯ ⊗ b_{z_d}`. -/
theorem laplacian_conj (c : (Fin d → Fin (n + 2)) → ℤ) :
    laplacian d (n + 2) (tensorEquiv d (hamBasis n) c) =
      tensorEquiv d (hamBasis n) (Nop n d c) := by
  have h : laplacian d (n + 2) ∘ₗ (tensorEquiv d (hamBasis n)).toLinearMap =
      (tensorEquiv d (hamBasis n)).toLinearMap ∘ₗ Nop n d := by
    refine (Pi.basisFun ℤ (Fin d → Fin (n + 2))).ext fun z => ?_
    simp only [LinearMap.comp_apply, Pi.basisFun_apply, LinearEquiv.coe_coe]
    rw [Nop_single, map_add, map_sum, map_smul, tensorEquiv_single, laplacian_tensor_single,
      Finset.sum_ite]
    simp only [tensorEquiv_single, sum_const]
    module
  exact congrArg (fun φ => φ c) h

end ColouredSand.Splitting
