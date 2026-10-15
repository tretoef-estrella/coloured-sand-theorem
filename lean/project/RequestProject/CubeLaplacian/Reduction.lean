module

public import RequestProject.CubeLaplacian.TwoAdic

/-!
# `C17_the_laplacian_in_the_group_ring.md`: Part D, (D2) — the `2`-adic reduction

`σ_A` is `lap ℤ_[2] n : (G n → ℤ_[2]) →ₗ[ℤ_[2]] (G n → ℤ_[2])`,
`(σ_A f)(g) = n · f(g) − Σ_{i<n} f(g + e_i)`; the quotient `(G → ℤ_[2]) ⧸ range σ_A` is the
quotient by the `ℤ_[2]`-submodule `range σ_A`.
-/

@[expose] public section

noncomputable section

namespace CubeLaplacian

open TensorProduct

/-- `(G → ℤ) ⊗[ℤ] ℤ_[2] ≃ₗ[ℤ] (G → ℤ_[2])`, `f ⊗ a ↦ (g ↦ f(g) • a)`. -/
def psi (n : ℕ) : (G n → ℤ) ⊗[ℤ] ℤ_[2] ≃ₗ[ℤ] (G n → ℤ_[2]) :=
  (TensorProduct.comm ℤ _ _).trans (TensorProduct.piScalarRight ℤ ℤ ℤ_[2] (G n))

lemma psi_tmul (n : ℕ) (f : G n → ℤ) (a : ℤ_[2]) : psi n (f ⊗ₜ a) = fun g => f g • a := by
  simp [psi]

lemma psi_comm (n : ℕ) :
    (psi n).toLinearMap ∘ₗ (L n).rTensor ℤ_[2] =
      (lap ℤ_[2] n).restrictScalars ℤ ∘ₗ (psi n).toLinearMap := by
  refine TensorProduct.ext' fun f a => ?_
  funext g
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.rTensor_tmul, psi_tmul, LinearMap.coe_restrictScalars, lap_apply]
  simp only [zsmul_eq_mul, Finset.sum_mul, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Int.cast_sum, sub_mul, mul_assoc]

lemma range_tensor_eq (n : ℕ) :
    (LinearMap.range (TensorProduct.map (LinearMap.range (L n)).subtype
      (LinearMap.id : ℤ_[2] →ₗ[ℤ] ℤ_[2]))).map (psi n).toLinearMap =
      (LinearMap.range (lap ℤ_[2] n)).restrictScalars ℤ := by
  have h1 : LinearMap.range (TensorProduct.map (LinearMap.range (L n)).subtype
      (LinearMap.id : ℤ_[2] →ₗ[ℤ] ℤ_[2])) = LinearMap.range ((L n).rTensor ℤ_[2]) := by
    have hL : L n = (LinearMap.range (L n)).subtype ∘ₗ (L n).rangeRestrict :=
      LinearMap.ext fun _ => rfl
    conv_rhs => rw [hL, LinearMap.rTensor_comp]
    rw [LinearMap.range_comp_of_range_eq_top]
    · rfl
    · exact LinearMap.range_eq_top.2
        (LinearMap.rTensor_surjective _ (LinearMap.surjective_rangeRestrict _))
  rw [h1, ← LinearMap.range_comp, psi_comm, LinearMap.range_comp_of_range_eq_top,
    LinearMap.range_restrictScalars]
  exact LinearMap.range_eq_top.2 (psi n).surjective

/-- Right exactness of `⊗_ℤ ℤ_[2]`: `((G → ℤ) ⧸ range L) ⊗ ℤ_[2] ≅ (G → ℤ_[2]) ⧸ range σ_A`. -/
def cokerTensorEquiv (n : ℕ) :
    coker n ⊗[ℤ] ℤ_[2] ≃ₗ[ℤ] (G n → ℤ_[2]) ⧸ (LinearMap.range (lap ℤ_[2] n)).restrictScalars ℤ :=
  (TensorProduct.quotientTensorEquiv ℤ_[2] (LinearMap.range (L n))).trans
    (Submodule.Quotient.equiv _ _ (psi n) (range_tensor_eq n))

/-- Part D, (D2) (the last claim of §2.1):
`(G → ℤ_[2]) ⧸ range σ_A ≃+ ℤ_[2] × Syl_2 K(Q_n)`. -/
theorem D2 (n : ℕ) :
    Nonempty ((G n → ℤ_[2]) ⧸ LinearMap.range (lap ℤ_[2] n) ≃+ ℤ_[2] × Syl2 (K n)) := by
  haveI := K_finite n
  obtain ⟨d1⟩ := D1 (K n)
  let e1 := (Submodule.Quotient.restrictScalarsEquiv ℤ (LinearMap.range (lap ℤ_[2] n))).symm
  let e2 := (cokerTensorEquiv n).symm
  let e3 : coker n ⊗[ℤ] ℤ_[2] ≃ₗ[ℤ] (ℤ × K n) ⊗[ℤ] ℤ_[2] :=
    TensorProduct.congr (cokerEquivK n) (LinearEquiv.refl ℤ ℤ_[2])
  let e4 := TensorProduct.prodLeft ℤ ℤ ℤ (K n) ℤ_[2]
  let e5 : (ℤ ⊗[ℤ] ℤ_[2]) × (K n ⊗[ℤ] ℤ_[2]) ≃+ ℤ_[2] × Syl2 (K n) :=
    AddEquiv.prodCongr (TensorProduct.lid ℤ ℤ_[2]).toAddEquiv d1
  exact ⟨((((e1.trans e2).trans e3).trans e4).toAddEquiv).trans e5⟩

end CubeLaplacian
