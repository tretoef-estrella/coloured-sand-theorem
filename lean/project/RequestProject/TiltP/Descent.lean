module

public import RequestProject.Doubling.All
public import RequestProject.Lemma35.All
public import RequestProject.LemmaW.All
public import RequestProject.Glue.All

/-!
# Descent from `ℚ_[p]` to `ℤ_[p]` (auxiliary for `CSG3_tilting_lattices_and_clebsch_gordan.md`)

This file contains the general tools behind the hint of (T1) of
`CSG3_tilting_lattices_and_clebsch_gordan.md`: "the axioms are linear identities between operators,
so they transport along a linear change of basis and descend to the `ℤ_[p]`-coordinates
(injectivity of `ℤ_[p] → ℚ_[p]`)".

## Encoding

* `A → K` is an algebra with injective structure map (in the applications `ℤ_[p] → ℚ_[p]`).
  `coeL ι : (ι → A) →ₗ[A] (ι → K)` applies `algebraMap A K` coordinatewise.
* `Models Fd FK` says that the `A`-linear operators `Fd t` on `ι → A` are the restrictions of the
  `K`-linear operators `FK t` on `ι → K`: `coeL (Fd t v) = FK t (coeL v)`.
* `IsDP.descend`: if `(wt, FK, EK)` satisfies (W), (P0), (P1), (K) over `K` and is modelled by
  `(Fd, Ed)`, then `(wt, Fd, Ed)` satisfies them over `A`.
* `IsDP.conj`: conjugating DP data by a `K`-linear automorphism that preserves weight vectors
  gives DP data.
* `homOfModel`, `iso_of_model`: morphisms and isomorphisms of DP-lattices obtained from
  `K`-linear intertwiners (an isomorphism when the intertwiner maps the standard lattice
  `range coeL` onto the standard lattice).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltP

open DPLattice WeylFilt Doubling LemmaW Finset

section general

variable {A K : Type*} [CommRing A] [CommRing K] [Algebra A K]

variable (A K) in
/-- The coordinatewise map `(ι → A) → (ι → K)`, `v ↦ algebraMap A K ∘ v`. -/
def coeL (ι : Type*) : (ι → A) →ₗ[A] (ι → K) :=
  LinearMap.pi fun i => (Algebra.linearMap A K).comp (LinearMap.proj i)

@[simp] lemma coeL_apply {ι : Type*} (v : ι → A) (i : ι) :
    coeL A K ι v i = algebraMap A K (v i) := rfl

lemma coeL_injective (hinj : Function.Injective (algebraMap A K)) (ι : Type*) :
    Function.Injective (coeL A K ι) := fun _ _ h => funext fun i => hinj (congrFun h i)

lemma coeL_single {ι : Type*} [DecidableEq ι] (i : ι) :
    coeL A K ι (Pi.single i 1) = Pi.single i 1 := by
  funext j; by_cases h : j = i <;> simp [Pi.single_apply, h]

lemma coeL_smul_int {ι : Type*} (c : ℤ) (v : ι → A) :
    coeL A K ι (((c : A)) • v) = ((c : K)) • coeL A K ι v := by
  rw [map_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

/-- `Models Fd FK`: the `A`-operators `Fd t` are the restrictions of the `K`-operators `FK t`. -/
def Models {ι : Type*} (Fd : ℕ → Module.End A (ι → A)) (FK : ℕ → Module.End K (ι → K)) : Prop :=
  ∀ t v, coeL A K ι (Fd t v) = FK t (coeL A K ι v)

/-- **Descent of (W), (P0), (P1), (K)** along an injective `A → K`. -/
theorem IsDP.descend (hinj : Function.Injective (algebraMap A K)) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {wt : ι → ℤ} {Fd Ed : ℕ → Module.End A (ι → A)}
    {FK EK : ℕ → Module.End K (ι → K)} (hK : IsDP wt FK EK) (hF : Models Fd FK)
    (hE : Models Ed EK) : IsDP wt Fd Ed := by
  have inj := coeL_injective hinj ι
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i r j hj
    apply hinj
    have := congrFun (hF r (Pi.single i 1)) j
    rw [coeL_single, hK.W_F i r j hj] at this
    rw [map_zero, ← this]; rfl
  · intro i r j hj
    apply hinj
    have := congrFun (hE r (Pi.single i 1)) j
    rw [coeL_single, hK.W_E i r j hj] at this
    rw [map_zero, ← this]; rfl
  · refine LinearMap.ext fun v => ?_; apply inj; rw [hF, hK.P0_F]; rfl
  · refine LinearMap.ext fun v => ?_; apply inj; rw [hE, hK.P0_E]; rfl
  · intro a b; refine LinearMap.ext fun v => ?_; apply inj
    rw [LinearMap.comp_apply, hF, hF, LinearMap.smul_apply, coeL_smul_int, hF,
      ← LinearMap.comp_apply, hK.P1_F]; rfl
  · intro a b; refine LinearMap.ext fun v => ?_; apply inj
    rw [LinearMap.comp_apply, hE, hE, LinearMap.smul_apply, coeL_smul_int, hE,
      ← LinearMap.comp_apply, hK.P1_E]; rfl
  · intro i r s
    apply inj
    rw [hE, hF, coeL_single, hK.K, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeL_smul_int, hF, hE, coeL_single]

/-- (K) for an arbitrary weight vector (not only for basis vectors). -/
theorem IsDP.K_inWt {ι : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ}
    {Fd Ed : ℕ → Module.End K (ι → K)} (h : IsDP wt Fd Ed) {w : ℤ} {v : ι → K}
    (hv : InWt wt w v) (r s : ℕ) :
    Ed s (Fd r v) = ∑ j ∈ range (min r s + 1),
      ((Ring.choose (w + s - r) j : ℤ) : K) • Fd (r - j) (Ed (s - j) v) := by
  have hv' : v = ∑ i, v i • (Pi.single i (1 : K) : ι → K) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  have key : ∀ i, v i • Ed s (Fd r (Pi.single i 1)) = ∑ j ∈ range (min r s + 1),
      ((Ring.choose (w + s - r) j : ℤ) : K) • (v i • Fd (r - j) (Ed (s - j) (Pi.single i 1))) := by
    intro i
    by_cases hi : wt i = w
    · rw [h.K, Finset.smul_sum, hi]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_comm]
    · rw [hv i hi]; simp
  rw [hv']
  simp only [map_sum, map_smul]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]

/-- **Conjugation of DP data** by a `K`-linear automorphism `T` such that `T` and `T⁻¹` map weight
vectors to weight vectors of the same weight. -/
theorem IsDP.conj {ι : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ}
    {Fd Ed : ℕ → Module.End K (ι → K)} (h : IsDP wt Fd Ed) (T : (ι → K) ≃ₗ[K] (ι → K))
    (hT : ∀ w v, InWt wt w v → InWt wt w (T v))
    (hT' : ∀ w v, InWt wt w v → InWt wt w (T.symm v)) :
    IsDP wt (fun t => T.toLinearMap ∘ₗ Fd t ∘ₗ T.symm.toLinearMap)
      (fun t => T.toLinearMap ∘ₗ Ed t ∘ₗ T.symm.toLinearMap) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i r j hj
    exact hT _ _ (h.inWt_Fd r (hT' _ _ (inWt_single wt i))) j hj
  · intro i r j hj
    exact hT _ _ (h.inWt_Ed r (hT' _ _ (inWt_single wt i))) j hj
  · refine LinearMap.ext fun v => ?_; simp [h.P0_F]
  · refine LinearMap.ext fun v => ?_; simp [h.P0_E]
  · intro a b; refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.smul_apply]
    rw [← LinearMap.comp_apply (Fd a) (Fd b), h.P1_F]; simp
  · intro a b; refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.smul_apply]
    rw [← LinearMap.comp_apply (Ed a) (Ed b), h.P1_E]; simp
  · intro i r s
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [IsDP.K_inWt h (hT' _ _ (inWt_single wt i)) r s, map_sum]
    simp [map_smul]

/-- A weight-preserving linear map commutes with `H`. -/
lemma comm_H_of_wtPres {M N : DPLattice A} (φ : (M.ι → A) →ₗ[A] (N.ι → A)) (hφ : IsWtPres φ) :
    φ ∘ₗ H M = H N ∘ₗ φ := by
  refine ext_single fun i => ?_
  have hH : H M (Pi.single i 1) = ((M.wt i : ℤ) : A) • (Pi.single i 1 : M.ι → A) := by
    funext k; by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  funext j
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hH, map_smul]
  show ((M.wt i : ℤ) : A) • φ (Pi.single i 1) j = ((N.wt j : ℤ) : A) * φ (Pi.single i 1) j
  by_cases hw : M.wt i = N.wt j
  · rw [hw, smul_eq_mul]
  · rw [hφ i j hw]; simp

/-- A morphism of DP-lattices from a `K`-linear intertwiner of the models. -/
def homOfModel (hinj : Function.Injective (algebraMap A K)) {M N : DPLattice A}
    {FMK EMK : ℕ → Module.End K (M.ι → K)} {FNK ENK : ℕ → Module.End K (N.ι → K)}
    (hMF : Models M.Fd FMK) (hME : Models M.Ed EMK) (hNF : Models N.Fd FNK)
    (hNE : Models N.Ed ENK) (φ : (M.ι → A) →ₗ[A] (N.ι → A)) (φK : (M.ι → K) →ₗ[K] (N.ι → K))
    (hφ : ∀ v, coeL A K N.ι (φ v) = φK (coeL A K M.ι v))
    (hcF : ∀ t, φK ∘ₗ FMK t = FNK t ∘ₗ φK) (hcE : ∀ t, φK ∘ₗ EMK t = ENK t ∘ₗ φK)
    (hW : IsWtPres φ) : Hom M N where
  toLin := φ
  comm_F t := by
    refine LinearMap.ext fun v => ?_; apply coeL_injective hinj
    simp only [LinearMap.comp_apply]
    rw [hφ, hMF, ← LinearMap.comp_apply φK, hcF, LinearMap.comp_apply, ← hφ, hNF]
  comm_E t := by
    refine LinearMap.ext fun v => ?_; apply coeL_injective hinj
    simp only [LinearMap.comp_apply]
    rw [hφ, hME, ← LinearMap.comp_apply φK, hcE, LinearMap.comp_apply, ← hφ, hNE]
  comm_H := comm_H_of_wtPres φ hW

@[simp] lemma homOfModel_toLin (hinj : Function.Injective (algebraMap A K)) {M N : DPLattice A}
    {FMK EMK : ℕ → Module.End K (M.ι → K)} {FNK ENK : ℕ → Module.End K (N.ι → K)}
    (hMF : Models M.Fd FMK) (hME : Models M.Ed EMK) (hNF : Models N.Fd FNK)
    (hNE : Models N.Ed ENK) (φ : (M.ι → A) →ₗ[A] (N.ι → A)) (φK : (M.ι → K) →ₗ[K] (N.ι → K))
    (hφ hcF hcE hW) :
    (homOfModel hinj hMF hME hNF hNE φ φK hφ hcF hcE hW).toLin = φ := rfl

/-- The `A`-linear map induced by a `K`-linear map preserving the standard lattices. -/
def latMap (hinj : Function.Injective (algebraMap A K)) {ι κ : Type*}
    (ψ : (ι → K) →ₗ[K] (κ → K))
    (hint : ∀ v, v ∈ LinearMap.range (coeL A K ι) → ψ v ∈ LinearMap.range (coeL A K κ)) :
    (ι → A) →ₗ[A] (κ → A) :=
  (LinearEquiv.ofInjective _ (coeL_injective hinj κ)).symm.toLinearMap ∘ₗ
    (ψ.restrictScalars A).restrict hint ∘ₗ
    (LinearEquiv.ofInjective _ (coeL_injective hinj ι)).toLinearMap

lemma coeL_latMap (hinj : Function.Injective (algebraMap A K)) {ι κ : Type*}
    (ψ : (ι → K) →ₗ[K] (κ → K))
    (hint : ∀ v, v ∈ LinearMap.range (coeL A K ι) → ψ v ∈ LinearMap.range (coeL A K κ))
    (v : ι → A) : coeL A K κ (latMap hinj ψ hint v) = ψ (coeL A K ι v) := by
  simp only [latMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← LinearEquiv.ofInjective_apply (h := coeL_injective hinj κ), LinearEquiv.apply_symm_apply]
  rfl

/-- **Isomorphisms from `K`-linear intertwiners.**  If `ψ` is a `K`-linear isomorphism between the
models of `M` and `N`, intertwining the divided powers, preserving weights, and mapping the
standard lattice onto the standard lattice, then `M ≅ N`. -/
theorem iso_of_model (hinj : Function.Injective (algebraMap A K)) {M N : DPLattice A}
    {FMK EMK : ℕ → Module.End K (M.ι → K)} {FNK ENK : ℕ → Module.End K (N.ι → K)}
    (hMF : Models M.Fd FMK) (hME : Models M.Ed EMK) (hNF : Models N.Fd FNK)
    (hNE : Models N.Ed ENK) (ψ : (M.ι → K) ≃ₗ[K] (N.ι → K))
    (hcF : ∀ t, ψ.toLinearMap ∘ₗ FMK t = FNK t ∘ₗ ψ.toLinearMap)
    (hcE : ∀ t, ψ.toLinearMap ∘ₗ EMK t = ENK t ∘ₗ ψ.toLinearMap)
    (hW : ∀ i j, M.wt i ≠ N.wt j → ψ (Pi.single i 1) j = 0)
    (hint : ∀ v, v ∈ LinearMap.range (coeL A K M.ι) ↔ ψ v ∈ LinearMap.range (coeL A K N.ι)) :
    Nonempty (Iso M N) := by
  have h1 : ∀ v, v ∈ LinearMap.range (coeL A K M.ι) →
      ψ.toLinearMap v ∈ LinearMap.range (coeL A K N.ι) := fun v hv => (hint v).1 hv
  have h2 : ∀ w, w ∈ LinearMap.range (coeL A K N.ι) →
      ψ.symm.toLinearMap w ∈ LinearMap.range (coeL A K M.ι) := fun w hw => by
    rw [hint]; simpa using hw
  set φ := latMap hinj ψ.toLinearMap h1
  set φ' := latMap hinj ψ.symm.toLinearMap h2
  have hφW : IsWtPres (M := M) (N := N) φ := by
    intro i j hij
    apply hinj
    have := congrFun (coeL_latMap hinj ψ.toLinearMap h1 (Pi.single i 1)) j
    rw [coeL_single] at this
    rw [map_zero, ← coeL_apply, this]
    exact hW i j hij
  let f : Hom M N := homOfModel hinj hMF hME hNF hNE φ ψ.toLinearMap
    (coeL_latMap hinj _ h1) hcF hcE hφW
  refine ⟨Iso.ofInverse f φ' ?_ ?_⟩
  · refine LinearMap.ext fun v => ?_; apply coeL_injective hinj
    show coeL A K M.ι (φ' (φ v)) = coeL A K M.ι v
    rw [coeL_latMap, coeL_latMap]; simp
  · refine LinearMap.ext fun v => ?_; apply coeL_injective hinj
    show coeL A K N.ι (φ (φ' v)) = coeL A K N.ι v
    rw [coeL_latMap, coeL_latMap]; simp

end general

/-! ### The standard lattice of `ι → ℚ_[p]` -/

section padic

variable {p : ℕ} [Fact p.Prime]

lemma padic_algebraMap_injective : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := by
  intro x y h
  rw [PadicInt.algebraMap_apply, PadicInt.algebraMap_apply] at h
  exact Subtype.ext h

/-- A vector of `ι → ℚ_[p]` lies in the standard lattice iff all its coordinates are integral. -/
lemma mem_range_coeL_iff {ι : Type*} (v : ι → ℚ_[p]) :
    v ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] ι) ↔ ∀ i, ‖v i‖ ≤ 1 := by
  constructor
  · rintro ⟨z, rfl⟩ i
    rw [coeL_apply, PadicInt.algebraMap_apply]
    exact PadicInt.norm_le_one _
  · intro h
    refine ⟨fun i => ⟨v i, h i⟩, ?_⟩
    funext i
    rw [coeL_apply, PadicInt.algebraMap_apply]

end padic

end ColouredSand.TiltP
