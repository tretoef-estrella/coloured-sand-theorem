module

public import RequestProject.CubeLaplacian.GroupRing

/-!
# `C17_the_laplacian_in_the_group_ring.md`: Part B — the Laplacian is multiplication by `σ`

Under the identification `R = ℤ^G` (`toFun n`, `f ↦ (g ↦ f g)`), left multiplication by
`σ` is the Laplacian `L` of the cube.
-/

@[expose] public section

noncomputable section

namespace CubeLaplacian

open Finset

lemma neg_e (n : ℕ) (i : Fin n) : -e n i = e n i :=
  neg_eq_of_add_eq_zero_left (e_add_self n i)

lemma x_mul_apply (n : ℕ) (i : Fin n) (f : R n) (g : G n) :
    (x n i * f) g = f (g + e n i) := by
  rw [x, AddMonoidAlgebra.single_mul_apply, one_mul, neg_e, add_comm]

lemma R_sub_apply {n : ℕ} (a b : R n) (g : G n) : (a - b) g = a g - b g :=
  Finsupp.sub_apply a b g

/-- Part B, (B1): for every `f ∈ R` and `g ∈ G`, `(σ · f)(g) = n · f(g) − Σ_{i<n} f(g + e_i)`. -/
theorem B1 (n : ℕ) (f : R n) (g : G n) :
    (sigma n * f) g = n * f g - ∑ i, f (g + e n i) := by
  rw [sigma, Finset.sum_mul, Finsupp.finset_sum_apply]
  simp only [s, sub_mul, one_mul, R_sub_apply, x_mul_apply,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Part B, (B1), second form: under the identification `R = ℤ^G` (`toFun n`), multiplication by
`σ` is `L`. -/
theorem B1' (n : ℕ) :
    (toFun n).toLinearMap ∘ₗ mulSigma n = L n ∘ₗ (toFun n).toLinearMap := by
  refine LinearMap.ext fun f => funext fun g => ?_
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, toFun_apply,
    mulSigma, LinearMap.mulLeft_apply, lap_apply]
  exact B1 n f g

lemma range_L_eq (n : ℕ) :
    (LinearMap.range (mulSigma n)).map (toFun n).toLinearMap = LinearMap.range (L n) := by
  rw [← LinearMap.range_comp, B1', LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 (toFun n).surjective

/-- Part B, (B2): `(G → ℤ) ⧸ range L ≃ₗ[ℤ] R ⧸ range (σ · −)`. -/
def B2equiv (n : ℕ) : coker n ≃ₗ[ℤ] R n ⧸ LinearMap.range (mulSigma n) :=
  (Submodule.Quotient.equiv _ _ (toFun n) (range_L_eq n)).symm

/-- Part B, (B2): `(G → ℤ) ⧸ range L ≃ₗ[ℤ] R ⧸ range (σ · −)`. -/
theorem B2 (n : ℕ) : Nonempty (coker n ≃ₗ[ℤ] R n ⧸ LinearMap.range (mulSigma n)) :=
  ⟨B2equiv n⟩

end CubeLaplacian
