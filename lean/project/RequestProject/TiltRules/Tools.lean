module

public import RequestProject.TiltP.All

/-!
# Tools for the tensor rules (auxiliary for `CSG4_tensor_rules.md`, §3)

This file contains the general machinery used to prove the isomorphisms of Parts S and R of
`CSG4_tensor_rules.md`.  Throughout `K = ℚ_[p]`, `A = ℤ_[p]`.

## Encoding

* `isDP_H_eq`: in any DP datum, `H = E^{(1)} F^{(1)} − F^{(1)} E^{(1)}` (Kostant's formula with
  `r = s = 1`).  Hence (`wt_of_comm`) a `K`-linear map intertwining `F^{(1)}` and `E^{(1)}` of two
  DP data is automatically weight-preserving, and `iso_of_model'` is the descent tool
  `TiltP.iso_of_model` without the weight hypothesis.
* `Untw M X` ("untwisted model" of a DP-lattice `M` over `ℤ_[p]`): a `K`-model `(FK, EK)` of the
  divided powers of `M` (satisfying (W), (P0), (P1), (K)), a `K`-linear isomorphism
  `θ : (M.ι → K) ≃ (X → K)` onto a second coordinate space `X → K` carrying operators
  `FX t`, `EX t` with `θ ∘ FK t = FX t ∘ θ`, and the image `Λ = θ(M_{ℤ_p})` of the standard lattice
  of `M` (as a `ℤ_[p]`-submodule of `X → K`).  The instances are in `RequestProject/TiltRules/Untw.lean`.
* `iso_of_untw`: if `ψ : (X → K) ≃ (Y → K)` intertwines the untwisted operators of `M` and `N`
  and maps `Λ_M` onto `Λ_N`, then `M ≅ N` as DP-lattices over `ℤ_[p]`.
* `IsGen F Λ g`: the vectors `g i` lie in `Λ` and `Λ` is contained in the `ℤ_[p]`-span of all
  `F t (g i)`.  `lat_of_gen` reduces "`ψ` maps `Λ_M` onto `Λ_N`" to finitely many membership
  checks on generators.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltRules

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP

/-! ### `H` is determined by `F^{(1)}` and `E^{(1)}` -/

lemma Hop_single {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι] (wt : ι → ℤ) (i : ι) :
    Hop (A := A) wt (Pi.single i 1) = ((wt i : ℤ) : A) • (Pi.single i 1 : ι → A) := by
  funext k; by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

/-- In any DP datum, `H = E^{(1)} F^{(1)} − F^{(1)} E^{(1)}`. -/
lemma isDP_H_eq {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ}
    {Fd Ed : ℕ → Module.End A (ι → A)} (h : IsDP wt Fd Ed) :
    Hop wt = Ed 1 ∘ₗ Fd 1 - Fd 1 ∘ₗ Ed 1 := by
  refine ext_single fun i => ?_
  have hK := h.K i 1 1
  rw [show min 1 1 + 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one] at hK
  simp only [Nat.sub_zero, Nat.sub_self, h.P0_F, h.P0_E, Ring.choose_zero_right,
    Ring.choose_one_right, Int.cast_one, one_smul, Module.End.one_apply] at hK
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, hK, Hop_single]
  rw [show wt i + ((1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) = wt i by push_cast; ring]
  abel

/-- A linear map intertwining `F^{(1)}` and `E^{(1)}` of two DP data over a field of
characteristic zero is weight-preserving. -/
lemma wt_of_comm {K : Type*} [Field K] [CharZero K] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {wt : ι → ℤ} {wt' : κ → ℤ} {F E : ℕ → Module.End K (ι → K)}
    {F' E' : ℕ → Module.End K (κ → K)} (h : IsDP wt F E) (h' : IsDP wt' F' E')
    (ψ : (ι → K) →ₗ[K] (κ → K)) (hF : ψ ∘ₗ F 1 = F' 1 ∘ₗ ψ) (hE : ψ ∘ₗ E 1 = E' 1 ∘ₗ ψ) :
    ∀ i j, wt i ≠ wt' j → ψ (Pi.single i 1) j = 0 := by
  have hH : ψ ∘ₗ Hop wt = Hop wt' ∘ₗ ψ := by
    rw [isDP_H_eq h, isDP_H_eq h', LinearMap.comp_sub, LinearMap.sub_comp]
    congr 1
    · rw [← LinearMap.comp_assoc, hE, LinearMap.comp_assoc, hF, LinearMap.comp_assoc]
    · rw [← LinearMap.comp_assoc, hF, LinearMap.comp_assoc, hE, LinearMap.comp_assoc]
  intro i j hij
  have := congrFun (LinearMap.congr_fun hH (Pi.single i 1)) j
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Hop_single, map_smul, DPLattice.Hop_apply,
    Pi.smul_apply, smul_eq_mul] at this
  have hne : ((wt i : ℤ) : K) - ((wt' j : ℤ) : K) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hij
  have h2 : (((wt i : ℤ) : K) - ((wt' j : ℤ) : K)) * ψ (Pi.single i 1) j = 0 := by
    rw [sub_mul, this, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left hne

variable {p : ℕ} [Fact p.Prime]

/-- `TiltP.iso_of_model` without the weight hypothesis (it follows from the intertwining, since
both `K`-models satisfy (K)). -/
theorem iso_of_model' {M N : DPLattice ℤ_[p]}
    {FMK EMK : ℕ → Module.End ℚ_[p] (M.ι → ℚ_[p])} {FNK ENK : ℕ → Module.End ℚ_[p] (N.ι → ℚ_[p])}
    (hMF : Models M.Fd FMK) (hME : Models M.Ed EMK) (hNF : Models N.Fd FNK)
    (hNE : Models N.Ed ENK) (hMK : IsDP M.wt FMK EMK) (hNK : IsDP N.wt FNK ENK)
    (ψ : (M.ι → ℚ_[p]) ≃ₗ[ℚ_[p]] (N.ι → ℚ_[p]))
    (hcF : ∀ t, ψ.toLinearMap ∘ₗ FMK t = FNK t ∘ₗ ψ.toLinearMap)
    (hcE : ∀ t, ψ.toLinearMap ∘ₗ EMK t = ENK t ∘ₗ ψ.toLinearMap)
    (hint : ∀ v, v ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] M.ι) ↔
      ψ v ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] N.ι)) :
    Nonempty (Iso M N) :=
  iso_of_model padic_algebraMap_injective hMF hME hNF hNE ψ hcF hcE
    (wt_of_comm hMK hNK ψ.toLinearMap (hcF 1) (hcE 1)) hint

/-! ### Untwisted models -/

/-- An untwisted model of a DP-lattice `M` over `ℤ_[p]` on the coordinate space `X → ℚ_[p]`. -/
structure Untw (M : DPLattice ℤ_[p]) (X : Type) where
  /-- the `ℚ_[p]`-model of `F^{(t)}` on `M.ι → ℚ_[p]` -/
  FK : ℕ → Module.End ℚ_[p] (M.ι → ℚ_[p])
  /-- the `ℚ_[p]`-model of `E^{(t)}` on `M.ι → ℚ_[p]` -/
  EK : ℕ → Module.End ℚ_[p] (M.ι → ℚ_[p])
  mF : Models M.Fd FK
  mE : Models M.Ed EK
  dp : IsDP M.wt FK EK
  /-- the change of coordinates -/
  θ : (M.ι → ℚ_[p]) ≃ₗ[ℚ_[p]] (X → ℚ_[p])
  /-- the operators `F^{(t)}` on `X → ℚ_[p]` -/
  FX : ℕ → Module.End ℚ_[p] (X → ℚ_[p])
  /-- the operators `E^{(t)}` on `X → ℚ_[p]` -/
  EX : ℕ → Module.End ℚ_[p] (X → ℚ_[p])
  θF : ∀ t v, θ (FK t v) = FX t (θ v)
  θE : ∀ t v, θ (EK t v) = EX t (θ v)
  /-- the image of the standard lattice -/
  Λ : Submodule ℤ_[p] (X → ℚ_[p])
  hΛ : ∀ v, v ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] M.ι) ↔ θ v ∈ Λ

/-- **Isomorphisms from untwisted models.** -/
theorem iso_of_untw {M N : DPLattice ℤ_[p]} {X Y : Type} (U : Untw M X) (W : Untw N Y)
    (ψ : (X → ℚ_[p]) ≃ₗ[ℚ_[p]] (Y → ℚ_[p]))
    (hF : ∀ t x, ψ (U.FX t x) = W.FX t (ψ x)) (hE : ∀ t x, ψ (U.EX t x) = W.EX t (ψ x))
    (hlat : ∀ x, x ∈ U.Λ ↔ ψ x ∈ W.Λ) : Nonempty (Iso M N) := by
  refine iso_of_model' U.mF U.mE W.mF W.mE U.dp W.dp ((U.θ.trans ψ).trans W.θ.symm) ?_ ?_ ?_
  · intro t; refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
    apply W.θ.injective
    rw [LinearEquiv.apply_symm_apply, W.θF, LinearEquiv.apply_symm_apply, U.θF, hF]
  · intro t; refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
    apply W.θ.injective
    rw [LinearEquiv.apply_symm_apply, W.θE, LinearEquiv.apply_symm_apply, U.θE, hE]
  · intro v
    simp only [LinearEquiv.trans_apply]
    rw [U.hΛ, hlat, W.hΛ, LinearEquiv.apply_symm_apply]

/-- The image of the standard lattice is stable under the untwisted `F^{(t)}`. -/
lemma Untw.stabF {M : DPLattice ℤ_[p]} {X : Type} (U : Untw M X) (t : ℕ) (x : X → ℚ_[p])
    (hx : x ∈ U.Λ) : U.FX t x ∈ U.Λ := by
  obtain ⟨v, rfl⟩ := U.θ.surjective x
  rw [← U.hΛ] at hx
  obtain ⟨z, rfl⟩ := hx
  rw [← U.θF, ← U.hΛ, ← U.mF]
  exact ⟨_, rfl⟩

/-! ### Generators -/

/-- `IsGen F Λ g`: the `g i` lie in `Λ`, and `Λ` is in the `ℤ_[p]`-span of all `F t (g i)`. -/
def IsGen {X I : Type} (F : ℕ → Module.End ℚ_[p] (X → ℚ_[p])) (Λ : Submodule ℤ_[p] (X → ℚ_[p]))
    (g : I → X → ℚ_[p]) : Prop :=
  (∀ i, g i ∈ Λ) ∧ Λ ≤ Submodule.span ℤ_[p] (Set.range fun q : ℕ × I => F q.1 (g q.2))

/-- **Lattice equality from generators.** -/
theorem lat_of_gen {X Y I J : Type} {FX : ℕ → Module.End ℚ_[p] (X → ℚ_[p])}
    {FY : ℕ → Module.End ℚ_[p] (Y → ℚ_[p])} {ΛX : Submodule ℤ_[p] (X → ℚ_[p])}
    {ΛY : Submodule ℤ_[p] (Y → ℚ_[p])} (ψ : (X → ℚ_[p]) ≃ₗ[ℚ_[p]] (Y → ℚ_[p]))
    (hF : ∀ t x, ψ (FX t x) = FY t (ψ x)) (sY : ∀ t, ∀ y ∈ ΛY, FY t y ∈ ΛY)
    (sX : ∀ t, ∀ x ∈ ΛX, FX t x ∈ ΛX) {gX : I → X → ℚ_[p]} {gY : J → Y → ℚ_[p]}
    (hX : IsGen FX ΛX gX) (hY : IsGen FY ΛY gY) (himg : ∀ i, ψ (gX i) ∈ ΛY)
    (hpre : ∀ j, ∃ x ∈ ΛX, ψ x = gY j) : ∀ x, x ∈ ΛX ↔ ψ x ∈ ΛY := by
  intro x
  constructor
  · intro hx
    have key : ∀ w ∈ Submodule.span ℤ_[p] (Set.range fun q : ℕ × I => FX q.1 (gX q.2)),
        ψ w ∈ ΛY := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨⟨t, i⟩, rfl⟩ := hw
        rw [hF]; exact sY t _ (himg i)
      | zero => rw [map_zero]; exact ΛY.zero_mem
      | add v w _ _ hv hw => rw [map_add]; exact ΛY.add_mem hv hw
      | smul c v _ hv =>
        rw [show ψ (c • v) = c • ψ v from LinearMap.map_smul_of_tower ψ.toLinearMap c v]
        exact ΛY.smul_mem c hv
    exact key x (hX.2 hx)
  · intro hx
    have key : Submodule.span ℤ_[p] (Set.range fun q : ℕ × J => FY q.1 (gY q.2)) ≤
        ΛX.map (ψ.toLinearMap.restrictScalars ℤ_[p]) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨t, j⟩, rfl⟩
      obtain ⟨x', hx', hψ⟩ := hpre j
      refine ⟨FX t x', sX t x' hx', ?_⟩
      simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
      rw [hF, hψ]
    obtain ⟨x', hx', hψ⟩ := key (hY.2 hx)
    simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe] at hψ
    rw [← ψ.injective hψ]; exact hx'

end ColouredSand.TiltRules
