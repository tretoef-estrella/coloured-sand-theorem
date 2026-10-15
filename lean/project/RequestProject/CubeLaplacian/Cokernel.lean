module

public import RequestProject.CubeLaplacian.Triangular

/-!
# `C17_the_laplacian_in_the_group_ring.md`: Part C, (C3) and (C4)

One free summand and a finite rest: `R ⧸ range (σ · −) ≃ ℤ × T(n)`, `K(Q_n) ≃ T(n)`.
-/

@[expose] public section

noncomputable section

namespace CubeLaplacian

open Finset

/-- The submodule `range (σ · −)` of `R`, pulled back to `R_+`. -/
abbrev Wp (n : ℕ) : Submodule ℤ (Rplus n) := (LinearMap.range (mulSigma n)).comap (Rplus n).subtype

/-- The coordinate of `s_∅` (in the basis (A4)). -/
abbrev coord0 (n : ℕ) : R n →ₗ[ℤ] ℤ := (sBasis n).coord ∅

lemma coord0_one (n : ℕ) : coord0 n 1 = 1 := by
  have : (1 : R n) = sS n ∅ := by simp [sS]
  rw [Module.Basis.coord_apply, this, repr_sS, if_pos rfl]

/-- The projection `f ↦ f − (coefficient of s_∅) · 1` of `R` onto `R_+`. -/
def projPlus (n : ℕ) : R n →ₗ[ℤ] Rplus n :=
  LinearMap.codRestrict (Rplus n)
    (LinearMap.id - (LinearMap.toSpanSingleton ℤ (R n) 1) ∘ₗ coord0 n) fun f => by
      rw [mem_Rplus_iff]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, map_sub, map_zsmul, Finsupp.sub_apply,
        Finsupp.smul_apply]
      have h1 : (sBasis n).repr (1 : R n) ∅ = 1 := coord0_one n
      rw [h1, smul_eq_mul, mul_one, Module.Basis.coord_apply, sub_self]

@[simp] lemma projPlus_coe (n : ℕ) (f : R n) : (projPlus n f : R n) = f - coord0 n f • 1 := rfl

/-- The map `R → ℤ × T(n)`, `f ↦ (coefficient of s_∅, class of the R_+-part)`. -/
def splitMap (n : ℕ) : R n →ₗ[ℤ] ℤ × T n :=
  (coord0 n).prod ((Wp n).mkQ ∘ₗ projPlus n)

lemma splitMap_surjective (n : ℕ) : Function.Surjective (splitMap n) := by
  rintro ⟨a, q⟩
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (Wp n) q
  have hy : coord0 n (y : R n) = 0 := by
    rw [Module.Basis.coord_apply]; exact (mem_Rplus_iff n _).1 y.2
  have hc : coord0 n (a • 1 + (y : R n)) = a := by
    rw [map_add, map_zsmul, coord0_one, hy, smul_eq_mul, mul_one, add_zero]
  refine ⟨a • 1 + (y : R n), Prod.ext hc ?_⟩
  simp only [splitMap, LinearMap.prod_apply, Pi.prod, LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  rw [projPlus_coe, hc, add_sub_cancel_left]

lemma splitMap_ker (n : ℕ) : LinearMap.ker (splitMap n) = LinearMap.range (mulSigma n) := by
  ext f
  simp only [LinearMap.mem_ker, splitMap, LinearMap.prod_apply, Pi.prod, LinearMap.comp_apply,
    Prod.mk_eq_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype, projPlus_coe]
  constructor
  · rintro ⟨h0, h1⟩
    rwa [h0, zero_smul, sub_zero] at h1
  · intro hf
    have h0 : coord0 n f = 0 := by
      rw [Module.Basis.coord_apply]; exact (mem_Rplus_iff n f).1 (C1_range n hf)
    refine ⟨h0, ?_⟩
    rwa [h0, zero_smul, sub_zero]

/-- Part C, (C3): `R ⧸ range (σ · −) ≃ₗ[ℤ] ℤ × T(n)` (the `ℤ` is the coefficient of `s_∅ = 1`). -/
def C3equiv (n : ℕ) : (R n ⧸ LinearMap.range (mulSigma n)) ≃ₗ[ℤ] ℤ × T n :=
  (Submodule.quotEquivOfEq _ _ (splitMap_ker n).symm).trans
    ((splitMap n).quotKerEquivOfSurjective (splitMap_surjective n))

/-- Part C, (C3): `T(n) = R_+ ⧸ range (σ · −)` is finite. -/
theorem T_finite (n : ℕ) : Finite (T n) :=
  finite_quotient_of_sigma_mem n _ fun S _ => ⟨sS n S, rfl⟩

/-- Part C, (C3): `R ⧸ range (σ · −) ≃ₗ[ℤ] ℤ × (R_+ ⧸ range (σ · −))`, and
`T(n) := R_+ ⧸ range (σ · −)` is finite. -/
theorem C3 (n : ℕ) :
    Nonempty ((R n ⧸ LinearMap.range (mulSigma n)) ≃ₗ[ℤ] ℤ × T n) ∧ Finite (T n) :=
  ⟨⟨C3equiv n⟩, T_finite n⟩

/-- The torsion of a `ℤ`-module `M ≃ ℤ × T` with `T` finite is `T`. -/
def torsionEquivOfProd {M T : Type*} [AddCommGroup M] [AddCommGroup T] [Finite T]
    (E : M ≃ₗ[ℤ] ℤ × T) : Submodule.torsion ℤ M ≃ₗ[ℤ] T := by
  refine (LinearEquiv.ofBijective
    (LinearMap.codRestrict (Submodule.torsion ℤ M)
      (E.symm.toLinearMap ∘ₗ LinearMap.inr ℤ ℤ T) fun t => ?_) ⟨?_, ?_⟩).symm
  · have hpos := (isOfFinAddOrder_of_finite t).addOrderOf_pos
    refine (Submodule.mem_torsion_iff _).2 ⟨⟨(addOrderOf t : ℤ),
      mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hpos.ne')⟩, ?_⟩
    rw [Submonoid.mk_smul, LinearMap.comp_apply, LinearEquiv.coe_coe, ← map_zsmul,
      LinearMap.inr_apply, Prod.smul_mk, smul_zero, natCast_zsmul, addOrderOf_nsmul_eq_zero]
    simp
  · intro t t' h
    have := congrArg Subtype.val h
    simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.inr_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq, true_and] at this
    exact this
  · rintro ⟨m, hm⟩
    obtain ⟨⟨r, hr⟩, hrm⟩ := (Submodule.mem_torsion_iff _).1 hm
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have h1 : r • E m = 0 := by
      rw [Submonoid.mk_smul] at hrm
      rw [← map_zsmul, hrm, map_zero]
    have ha : (E m).1 = 0 := by
      have := congrArg Prod.fst h1
      simp only [Prod.smul_fst, smul_eq_mul, Prod.fst_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hr0
    refine ⟨(E m).2, Subtype.ext ?_⟩
    simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.inr_apply]
    rw [LinearEquiv.symm_apply_eq]
    exact Prod.ext ha.symm rfl

/-- `coker L ≃ₗ[ℤ] ℤ × T(n)`, combining (B2) and (C3). -/
def cokerEquiv (n : ℕ) : coker n ≃ₗ[ℤ] ℤ × T n := (B2equiv n).trans (C3equiv n)

/-- Part C, (C4): `K(Q_n) ≃ₗ[ℤ] T(n)`. -/
def C4equiv (n : ℕ) : K n ≃ₗ[ℤ] T n :=
  haveI := T_finite n
  torsionEquivOfProd (cokerEquiv n)

/-- Part C, (C4): `K(Q_n)` is finite. -/
theorem K_finite (n : ℕ) : Finite (K n) :=
  haveI := T_finite n
  Finite.of_equiv _ (C4equiv n).symm.toEquiv

/-- Part C, (C4): `(G → ℤ) ⧸ range L ≃ₗ[ℤ] ℤ × K(Q_n)`. -/
def cokerEquivK (n : ℕ) : coker n ≃ₗ[ℤ] ℤ × K n :=
  (cokerEquiv n).trans (LinearEquiv.prodCongr (LinearEquiv.refl ℤ ℤ) (C4equiv n).symm)

/-- Part C, (C4): `K(Q_n) ≃ₗ[ℤ] T(n)`; in particular `K(Q_n)` is finite, and
`(G → ℤ) ⧸ range L ≃ₗ[ℤ] ℤ × K(Q_n)`. -/
theorem C4 (n : ℕ) :
    Nonempty (K n ≃ₗ[ℤ] T n) ∧ Finite (K n) ∧ Nonempty (coker n ≃ₗ[ℤ] ℤ × K n) :=
  ⟨⟨C4equiv n⟩, K_finite n, ⟨cokerEquivK n⟩⟩

end CubeLaplacian
