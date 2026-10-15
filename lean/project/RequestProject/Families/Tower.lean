module

public import RequestProject.Families.Digits
public import RequestProject.Filt.PartT
public import RequestProject.Dance.Basic

/-!
# `C32_theorem_38_the_groups_of_the_families.md`: Part B1 — the lattice `T(λ)` is the tower
# `T(ds λ)`

Encodings (namespace `Families`):

* A vector of a DP-lattice `M` is `M.ι → A` (C18); a vector of the tower `T(ds)` is an element of
  `⨁ _ : Dance.Idx ds, A` (C13).  Coordinates of a direct-sum vector `v` are `v q`.
* `TowerRel M d lam Θ` bundles the two properties (a), (b) of (B1) for a linear equivalence
  `Θ : (M.ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx d, A)`.
* The odd step `phiEquiv` sends `b_e n` (C18 `bvec e n`) to `embΦ e (Θ n)` (C11 `embΦ`); the even
  step `vEquiv` sends `b_a ⊗ b_e n` to `embVΦ a e (Θ n)` (C12 `embVΦ`) and is followed by C12's
  change of basis `thetaEquiv` (whose underlying map is `theta`).
* `Theta A lam` is a chosen equivalence satisfying (B1) (`Classical.choose` of the existence
  statement `B1`).
-/

@[expose] public section

noncomputable section

namespace Families

open DirectSum DPLattice Doubling Payment Split Filt

universe u

variable {A : Type u} [CommRing A]

/-! ### Coordinates of the placement maps -/

section coords

variable {κ : Type} [DecidableEq κ]

omit [DecidableEq κ] in
/-- Coordinates of a `DirectSum.lof` vector with constant fibres (auxiliary for (B1) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
lemma lof_apply_const {ι : Type} [DecidableEq ι] (i j : ι) (x : A) :
    (DirectSum.lof A ι (fun _ => A) i x) j = if j = i then x else 0 := by
  rw [DirectSum.lof_eq_of, DirectSum.of_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Coordinates of `b_e v` in the double (auxiliary for (B1) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
lemma embΦ_apply (e : Fin 2) (v : ⨁ _ : κ, A) (q : κ) (e' : Fin 2) :
    (embΦ A (fun _ : κ => A) e v) (q, e') = if e' = e then v q else 0 := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← DirectSum.lof_eq_of A, embΦ, DirectSum.toModule_lof, lof_apply_const, lof_apply_const]
    by_cases h1 : q = i <;> by_cases h2 : e' = e <;> simp [h1, h2]
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy]; split_ifs <;> simp

/-- Coordinates of `b_a b_e v` in the tensor model (auxiliary for (B1) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
lemma embVΦ_apply (a e : Fin 2) (v : ⨁ _ : κ, A) (q : κ) (a' e' : Fin 2) :
    (embVΦ A (fun _ : κ => A) a e v) (q, a', e') = if a' = a ∧ e' = e then v q else 0 := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← DirectSum.lof_eq_of A, embVΦ, DirectSum.toModule_lof, lof_apply_const, lof_apply_const]
    by_cases h1 : q = i <;> by_cases h2 : a' = a <;> by_cases h3 : e' = e <;> simp [h1, h2, h3]
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy]; split_ifs <;> simp

/-- Coordinates of `J v` in the split model (auxiliary for (B1) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
lemma embΨ_apply (j : Fin 4) (v : ⨁ _ : κ, A) (q : κ) (k : Fin 4) :
    (embΨ A (fun _ : κ => A) j v) (q, k) = if k = j then v q else 0 := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← DirectSum.lof_eq_of A, embΨ, DirectSum.toModule_lof, lof_apply_const, lof_apply_const]
    by_cases h1 : q = i <;> by_cases h2 : k = j <;> simp [h1, h2]
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy]; split_ifs <;> simp

end coords

/-! ### The relation of (B1) -/

/-- The two properties (a), (b) of (B1) of `C32_theorem_38_the_groups_of_the_families.md` for a
linear equivalence `Θ : M ≃ T(d)`: (a) `Θ ∘ F^{(1)} = F_d ∘ Θ`; (b) `Θ δ_j` has coordinate `0` at
every `q` with `2 fl(q) + wt(j) ≠ lam`. -/
def TowerRel (M : DPLattice A) (d : List Bool) (lam : ℤ)
    (Θ : (M.ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx d, A)) : Prop :=
  Θ.toLinearMap ∘ₗ M.Fd 1 = Dance.F A d ∘ₗ Θ.toLinearMap ∧
    ∀ (j : M.ι) (q : Dance.Idx d),
      2 * (Dance.fl d q : ℤ) + M.wt j ≠ lam → Θ (Pi.single j 1) q = 0

/-! ### The odd step -/

section odd

variable {κ : Type} [DecidableEq κ] {ι : Type} [DecidableEq ι]

/-- The projection of the double onto the layer `e` (auxiliary for (B1) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
def prΦ (e : Fin 2) : (⨁ _ : κ × Fin 2, A) →ₗ[A] (⨁ _ : κ, A) :=
  DirectSum.toModule A (κ × Fin 2) _ (fun q =>
    if q.2 = e then DirectSum.lof A κ (fun _ => A) q.1 else 0)

lemma prΦ_embΦ (e e' : Fin 2) (v : ⨁ _ : κ, A) :
    prΦ e (embΦ A (fun _ : κ => A) e' v) = if e' = e then v else 0 := by
  have : (prΦ e ∘ₗ embΦ A (fun _ : κ => A) e' : (⨁ _ : κ, A) →ₗ[A] _) =
      if e' = e then LinearMap.id else 0 := by
    apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, embΦ, DirectSum.toModule_lof, prΦ]
    split_ifs <;> simp
  have h := LinearMap.congr_fun this v
  simp only [LinearMap.comp_apply] at h
  rw [h]; split_ifs <;> simp

lemma embΦ_prΦ (v : ⨁ _ : κ × Fin 2, A) :
    embΦ A (fun _ : κ => A) 0 (prΦ 0 v) + embΦ A (fun _ : κ => A) 1 (prΦ 1 v) = v := by
  have : (embΦ A (fun _ : κ => A) 0 ∘ₗ prΦ 0 + embΦ A (fun _ : κ => A) 1 ∘ₗ prΦ 1 :
      (⨁ _ : κ × Fin 2, A) →ₗ[A] _) = LinearMap.id := by
    apply DirectSum.linearMap_ext; rintro ⟨i, e⟩; refine LinearMap.ext fun x => ?_
    fin_cases e <;> simp [prΦ, embΦ, DirectSum.toModule_lof]
  simpa using LinearMap.congr_fun this v

/-- The odd step of (B1) of `C32_theorem_38_the_groups_of_the_families.md`:
`b_e n ↦ embΦ e (Θ n)`. -/
def phiTo (Θ : (ι → A) ≃ₗ[A] (⨁ _ : κ, A)) : (Fin 2 × ι → A) →ₗ[A] (⨁ _ : κ × Fin 2, A) :=
  embΦ A (fun _ : κ => A) 0 ∘ₗ Θ.toLinearMap ∘ₗ slice 0 +
    embΦ A (fun _ : κ => A) 1 ∘ₗ Θ.toLinearMap ∘ₗ slice 1

/-- The inverse of the odd step (auxiliary for (B1) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
def phiInv (Θ : (ι → A) ≃ₗ[A] (⨁ _ : κ, A)) : (⨁ _ : κ × Fin 2, A) →ₗ[A] (Fin 2 × ι → A) :=
  bvec 0 ∘ₗ Θ.symm.toLinearMap ∘ₗ prΦ 0 + bvec 1 ∘ₗ Θ.symm.toLinearMap ∘ₗ prΦ 1

omit [DecidableEq ι] in
lemma phiTo_bvec (Θ : (ι → A) ≃ₗ[A] (⨁ _ : κ, A)) (e : Fin 2) (m : ι → A) :
    phiTo Θ (bvec e m) = embΦ A (fun _ : κ => A) e (Θ m) := by
  fin_cases e <;> simp [phiTo]

/-- The odd step as a linear equivalence (auxiliary for (B1) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
def phiEquiv (Θ : (ι → A) ≃ₗ[A] (⨁ _ : κ, A)) : (Fin 2 × ι → A) ≃ₗ[A] (⨁ _ : κ × Fin 2, A) :=
  LinearEquiv.ofLinear (phiTo Θ) (phiInv Θ)
    (by
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.comp_apply, phiInv, LinearMap.add_apply, map_add, phiTo_bvec,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.id_apply]
      exact embΦ_prΦ v)
    (by
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.comp_apply, phiTo, LinearMap.add_apply, phiInv, map_add,
        prΦ_embΦ, LinearEquiv.coe_coe, LinearMap.id_apply]
      simp
      exact (eq_bvec_slice f).symm)

omit [DecidableEq ι] in
lemma phiEquiv_bvec (Θ : (ι → A) ≃ₗ[A] (⨁ _ : κ, A)) (e : Fin 2) (m : ι → A) :
    phiEquiv Θ (bvec e m) = embΦ A (fun _ : κ => A) e (Θ m) := phiTo_bvec Θ e m

lemma FΦ_embΦ0 (F : (⨁ _ : κ, A) →ₗ[A] (⨁ _ : κ, A)) (v : ⨁ _ : κ, A) :
    FΦ F (embΦ A (fun _ : κ => A) 0 v) = embΦ A (fun _ : κ => A) 1 v := by
  have : (FΦ F ∘ₗ embΦ A (fun _ : κ => A) 0 : (⨁ _ : κ, A) →ₗ[A] _) =
      embΦ A (fun _ : κ => A) 1 := by
    apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, embΦ, DirectSum.toModule_lof]
    exact FΦ_lof0 F i x
  exact LinearMap.congr_fun this v

lemma FΦ_embΦ1 (F : (⨁ _ : κ, A) →ₗ[A] (⨁ _ : κ, A)) (v : ⨁ _ : κ, A) :
    FΦ F (embΦ A (fun _ : κ => A) 1 v) = (2 : A) • embΦ A (fun _ : κ => A) 0 (F v) := by
  have : (FΦ F ∘ₗ embΦ A (fun _ : κ => A) 1 : (⨁ _ : κ, A) →ₗ[A] _) =
      (2 : A) • (embΦ A (fun _ : κ => A) 0 ∘ₗ F) := by
    apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [show embΦ A (fun _ : κ => A) 1 (DirectSum.lof A κ (fun _ => A) i x) =
      DirectSum.lof A (κ × Fin 2) (NΦ (fun _ : κ => A)) (i, 1) x by
        simp [embΦ, DirectSum.toModule_lof]]
    exact FΦ_lof1 F i x
  exact LinearMap.congr_fun this v

end odd

/-! ### The even step -/

section even

variable {κ : Type} [DecidableEq κ] {ι : Type} [DecidableEq ι]

/-- The projection of the tensor model onto the slot `(a, e)` (auxiliary for (B1) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
def prV (a e : Fin 2) : (⨁ _ : κ × Fin 2 × Fin 2, A) →ₗ[A] (⨁ _ : κ, A) :=
  DirectSum.toModule A (κ × Fin 2 × Fin 2) _ (fun q =>
    if q.2.1 = a ∧ q.2.2 = e then DirectSum.lof A κ (fun _ => A) q.1 else 0)

lemma prV_embVΦ (a e a' e' : Fin 2) (v : ⨁ _ : κ, A) :
    prV a e (embVΦ A (fun _ : κ => A) a' e' v) = if a' = a ∧ e' = e then v else 0 := by
  have : (prV a e ∘ₗ embVΦ A (fun _ : κ => A) a' e' : (⨁ _ : κ, A) →ₗ[A] _) =
      if a' = a ∧ e' = e then LinearMap.id else 0 := by
    apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, embVΦ, DirectSum.toModule_lof, prV]
    split_ifs <;> simp
  have h := LinearMap.congr_fun this v
  simp only [LinearMap.comp_apply] at h
  rw [h]; split_ifs <;> simp

lemma embVΦ_prV (v : ⨁ _ : κ × Fin 2 × Fin 2, A) :
    embVΦ A (fun _ : κ => A) 0 0 (prV 0 0 v) + embVΦ A (fun _ : κ => A) 0 1 (prV 0 1 v) +
      embVΦ A (fun _ : κ => A) 1 0 (prV 1 0 v) + embVΦ A (fun _ : κ => A) 1 1 (prV 1 1 v) =
      v := by
  have : (embVΦ A (fun _ : κ => A) 0 0 ∘ₗ prV 0 0 + embVΦ A (fun _ : κ => A) 0 1 ∘ₗ prV 0 1 +
      embVΦ A (fun _ : κ => A) 1 0 ∘ₗ prV 1 0 + embVΦ A (fun _ : κ => A) 1 1 ∘ₗ prV 1 1 :
      (⨁ _ : κ × Fin 2 × Fin 2, A) →ₗ[A] _) = LinearMap.id := by
    apply DirectSum.linearMap_ext; rintro ⟨i, a, e⟩; refine LinearMap.ext fun x => ?_
    fin_cases a <;> fin_cases e <;> simp [prV, embVΦ, DirectSum.toModule_lof]
  simpa using LinearMap.congr_fun this v

/-- The even step of (B1) of `C32_theorem_38_the_groups_of_the_families.md`:
`b_a ⊗ b_e n ↦ embVΦ a e (Θ n)`. -/
def vTo (Θ : (ι → A) ≃ₗ[A] (⨁ _ : κ, A)) :
    (Fin 2 × (Fin 2 × ι) → A) →ₗ[A] (⨁ _ : κ × Fin 2 × Fin 2, A) :=
  embVΦ A (fun _ : κ => A) 0 0 ∘ₗ Θ.toLinearMap ∘ₗ slice 0 ∘ₗ slice 0 +
    embVΦ A (fun _ : κ => A) 0 1 ∘ₗ Θ.toLinearMap ∘ₗ slice 1 ∘ₗ slice 0 +
    embVΦ A (fun _ : κ => A) 1 0 ∘ₗ Θ.toLinearMap ∘ₗ slice 0 ∘ₗ slice 1 +
    embVΦ A (fun _ : κ => A) 1 1 ∘ₗ Θ.toLinearMap ∘ₗ slice 1 ∘ₗ slice 1

/-- The inverse of the even step (auxiliary for (B1) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
def vInv (Θ : (ι → A) ≃ₗ[A] (⨁ _ : κ, A)) :
    (⨁ _ : κ × Fin 2 × Fin 2, A) →ₗ[A] (Fin 2 × (Fin 2 × ι) → A) :=
  bvec 0 ∘ₗ bvec 0 ∘ₗ Θ.symm.toLinearMap ∘ₗ prV 0 0 +
    bvec 0 ∘ₗ bvec 1 ∘ₗ Θ.symm.toLinearMap ∘ₗ prV 0 1 +
    bvec 1 ∘ₗ bvec 0 ∘ₗ Θ.symm.toLinearMap ∘ₗ prV 1 0 +
    bvec 1 ∘ₗ bvec 1 ∘ₗ Θ.symm.toLinearMap ∘ₗ prV 1 1

omit [DecidableEq ι] in
lemma vTo_bvec (Θ : (ι → A) ≃ₗ[A] (⨁ _ : κ, A)) (a e : Fin 2) (m : ι → A) :
    vTo Θ (bvec a (bvec e m)) = embVΦ A (fun _ : κ => A) a e (Θ m) := by
  fin_cases a <;> fin_cases e <;> simp [vTo]

/-- The even step as a linear equivalence (auxiliary for (B1) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
def vEquiv (Θ : (ι → A) ≃ₗ[A] (⨁ _ : κ, A)) :
    (Fin 2 × (Fin 2 × ι) → A) ≃ₗ[A] (⨁ _ : κ × Fin 2 × Fin 2, A) :=
  LinearEquiv.ofLinear (vTo Θ) (vInv Θ)
    (by
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.comp_apply, vInv, LinearMap.add_apply, map_add, vTo_bvec,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.id_apply]
      exact embVΦ_prV v)
    (by
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.comp_apply, vTo, LinearMap.add_apply, vInv, map_add,
        prV_embVΦ, LinearEquiv.coe_coe, LinearMap.id_apply]
      simp
      apply ext_slice
      · rw [eq_bvec_slice (slice 0 f)]; simp
      · rw [eq_bvec_slice (slice 1 f)]; simp)

omit [DecidableEq ι] in
lemma vEquiv_bvec (Θ : (ι → A) ≃ₗ[A] (⨁ _ : κ, A)) (a e : Fin 2) (m : ι → A) :
    vEquiv Θ (bvec a (bvec e m)) = embVΦ A (fun _ : κ => A) a e (Θ m) := vTo_bvec Θ a e m

variable (F : (⨁ _ : κ, A) →ₗ[A] (⨁ _ : κ, A))

lemma embVΦ_lof (a e : Fin 2) (i : κ) (x : A) :
    embVΦ A (fun _ : κ => A) a e (DirectSum.lof A κ (fun _ => A) i x) =
      DirectSum.lof A (κ × Fin 2 × Fin 2) (NVΦ (fun _ : κ => A)) (i, a, e) x := by
  simp [embVΦ, DirectSum.toModule_lof]

lemma FVΦ_embVΦ00 (v : ⨁ _ : κ, A) :
    FVΦ F (embVΦ A (fun _ : κ => A) 0 0 v) =
      embVΦ A (fun _ : κ => A) 1 0 v + embVΦ A (fun _ : κ => A) 0 1 v := by
  have : (FVΦ F ∘ₗ embVΦ A (fun _ : κ => A) 0 0 : (⨁ _ : κ, A) →ₗ[A] _) =
      embVΦ A (fun _ : κ => A) 1 0 + embVΦ A (fun _ : κ => A) 0 1 := by
    apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, embVΦ_lof]
    exact FVΦ_lof00 F i x
  exact LinearMap.congr_fun this v

lemma FVΦ_embVΦ01 (v : ⨁ _ : κ, A) :
    FVΦ F (embVΦ A (fun _ : κ => A) 0 1 v) =
      embVΦ A (fun _ : κ => A) 1 1 v + (2 : A) • embVΦ A (fun _ : κ => A) 0 0 (F v) := by
  have : (FVΦ F ∘ₗ embVΦ A (fun _ : κ => A) 0 1 : (⨁ _ : κ, A) →ₗ[A] _) =
      embVΦ A (fun _ : κ => A) 1 1 + (2 : A) • (embVΦ A (fun _ : κ => A) 0 0 ∘ₗ F) := by
    apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, embVΦ_lof]
    exact FVΦ_lof01 F i x
  exact LinearMap.congr_fun this v

lemma FVΦ_embVΦ10 (v : ⨁ _ : κ, A) :
    FVΦ F (embVΦ A (fun _ : κ => A) 1 0 v) = embVΦ A (fun _ : κ => A) 1 1 v := by
  have : (FVΦ F ∘ₗ embVΦ A (fun _ : κ => A) 1 0 : (⨁ _ : κ, A) →ₗ[A] _) =
      embVΦ A (fun _ : κ => A) 1 1 := by
    apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, embVΦ_lof]
    exact FVΦ_lof10 F i x
  exact LinearMap.congr_fun this v

lemma FVΦ_embVΦ11 (v : ⨁ _ : κ, A) :
    FVΦ F (embVΦ A (fun _ : κ => A) 1 1 v) = (2 : A) • embVΦ A (fun _ : κ => A) 1 0 (F v) := by
  have : (FVΦ F ∘ₗ embVΦ A (fun _ : κ => A) 1 1 : (⨁ _ : κ, A) →ₗ[A] _) =
      (2 : A) • (embVΦ A (fun _ : κ => A) 1 0 ∘ₗ F) := by
    apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, embVΦ_lof]
    exact FVΦ_lof11 F i x
  exact LinearMap.congr_fun this v

/-- The coordinates of `θ (b_a b_e v)` (auxiliary for (B1) of
`C32_theorem_38_the_groups_of_the_families.md`): `θ(b_0b_0 v) = A v`,
`θ(b_0b_1 v) = B v + C v`, `θ(b_1b_0 v) = C v`, `θ(b_1b_1 v) = Dd v`. -/
lemma theta_embVΦ (a e : Fin 2) (v : ⨁ _ : κ, A) :
    theta (A := A) (N := fun _ : κ => A) (embVΦ A (fun _ : κ => A) a e v) =
      if a = 0 then (if e = 0 then embΨ A (fun _ : κ => A) 0 v
        else embΨ A (fun _ : κ => A) 1 v + embΨ A (fun _ : κ => A) 2 v)
      else (if e = 0 then embΨ A (fun _ : κ => A) 2 v else embΨ A (fun _ : κ => A) 3 v) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [← DirectSum.lof_eq_of A, embVΦ_lof]
    fin_cases a <;> fin_cases e <;> simp [embΨ, DirectSum.toModule_lof]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    split_ifs <;> (simp only [map_add]; try abel)

end even

/-! ### (B1) -/

section B1

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- The odd case of the induction of (B1) of `C32_theorem_38_the_groups_of_the_families.md`: from
`Θ : N ≃ T(d)` with (a), (b) at `l`, an equivalence `Φ(N) ≃ T(false :: d)` with (a), (b) at
`2l + 1`. -/
lemma towerRel_phi (N : DPLattice A) (d : List Bool) (l : ℤ)
    (Θ : (N.ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx d, A)) (h : TowerRel N d l Θ) :
    ∃ Θ' : ((phi N).ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx (false :: d), A),
      TowerRel (phi N) (false :: d) (2 * l + 1) Θ' := by
  refine ⟨phiEquiv Θ, ?_, ?_⟩
  · have hF : ∀ m, Θ (N.Fd 1 m) = Dance.F A d (Θ m) := fun m => LinearMap.congr_fun h.1 m
    refine ext_bvec (fun m => ?_) (fun m => ?_)
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [(Doubling.B1 N).1 m, phiEquiv_bvec, phiEquiv_bvec]
      exact (FΦ_embΦ0 _ _).symm
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [(Doubling.B1 N).2.1 m, map_smul, phiEquiv_bvec, phiEquiv_bvec, hF]
      exact (FΦ_embΦ1 _ _).symm
  · rintro ⟨e, i⟩ ⟨q, e'⟩ hne
    erw [single_eq_bvec, phiEquiv_bvec]
    change (embΦ A (fun _ : Dance.Idx d => A) e (Θ (Pi.single i 1))) (q, e') = 0
    rw [embΦ_apply]
    split_ifs with he
    · subst he
      apply h.2
      change 2 * ((flΦ (Dance.fl d) (q, e') : ℕ) : ℤ) + phiWt N (e', i) ≠ 2 * l + 1 at hne
      simp only [flΦ, phiWt] at hne
      intro hc
      apply hne
      fin_cases e' <;> simp at hc ⊢ <;> omega
    · rfl

/-- The even case of the induction of (B1) of `C32_theorem_38_the_groups_of_the_families.md`:
from `Θ : N ≃ T(d)` with (a), (b) at `l`, an equivalence `V ⊗ Φ(N) ≃ T(true :: d)` with (a), (b)
at `2l + 2` (the even step followed by C12's `theta`). -/
lemma towerRel_tensorV_phi (N : DPLattice A) (d : List Bool) (l : ℤ)
    (Θ : (N.ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx d, A)) (h : TowerRel N d l Θ) :
    ∃ Θ' : ((tensorV (phi N)).ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx (true :: d), A),
      TowerRel (tensorV (phi N)) (true :: d) (2 * l + 2) Θ' := by
  have hF : ∀ m, Θ (N.Fd 1 m) = Dance.F A d (Θ m) := fun m => LinearMap.congr_fun h.1 m
  have hP0 : (phi N).Fd 0 = 1 := (phi N).isDP.P0_F
  -- the even step intertwines `F^{(1)}` with `F^{VΦ}` on the vectors `b_a ⊗ b_e m`
  have k00 : ∀ m : N.ι → A,
      vEquiv Θ ((tensorV (phi N)).Fd 1 (bvec (ι := (phi N).ι) 0 (bvec 0 m))) =
        FVΦ (Dance.F A d) (vEquiv Θ (bvec 0 (bvec 0 m))) := by
    intro m
    have h1 := tensorV_Fd_b0 (phi N) 1 le_rfl (bvec 0 m)
    rw [Nat.sub_self, hP0, (Doubling.B1 N).1 m, Module.End.one_apply] at h1
    rw [h1, map_add]
    erw [vEquiv_bvec, vEquiv_bvec, vEquiv_bvec]
    rw [FVΦ_embVΦ00, add_comm]
  have k01 : ∀ m : N.ι → A,
      vEquiv Θ ((tensorV (phi N)).Fd 1 (bvec (ι := (phi N).ι) 0 (bvec 1 m))) =
        FVΦ (Dance.F A d) (vEquiv Θ (bvec 0 (bvec 1 m))) := by
    intro m
    have h1 := tensorV_Fd_b0 (phi N) 1 le_rfl (bvec 1 m)
    rw [Nat.sub_self, hP0, (Doubling.B1 N).2.1 m, Module.End.one_apply] at h1
    rw [h1, map_add, map_smul, map_smul]
    erw [vEquiv_bvec, vEquiv_bvec, vEquiv_bvec]
    rw [FVΦ_embVΦ01, hF, add_comm]
  have k10 : ∀ m : N.ι → A,
      vEquiv Θ ((tensorV (phi N)).Fd 1 (bvec (ι := (phi N).ι) 1 (bvec 0 m))) =
        FVΦ (Dance.F A d) (vEquiv Θ (bvec 1 (bvec 0 m))) := by
    intro m
    have h1 := tensorV_Fd_b1 (phi N) 1 (bvec 0 m)
    rw [(Doubling.B1 N).1 m] at h1
    rw [h1]
    erw [vEquiv_bvec, vEquiv_bvec]
    rw [FVΦ_embVΦ10]
  have k11 : ∀ m : N.ι → A,
      vEquiv Θ ((tensorV (phi N)).Fd 1 (bvec (ι := (phi N).ι) 1 (bvec 1 m))) =
        FVΦ (Dance.F A d) (vEquiv Θ (bvec 1 (bvec 1 m))) := by
    intro m
    have h1 := tensorV_Fd_b1 (phi N) 1 (bvec 1 m)
    rw [(Doubling.B1 N).2.1 m] at h1
    rw [h1, map_smul, map_smul]
    erw [vEquiv_bvec, vEquiv_bvec]
    rw [FVΦ_embVΦ11, hF]
  have hV : ∀ x, vEquiv Θ ((tensorV (phi N)).Fd 1 x) =
      FVΦ (Dance.F A d) (vEquiv Θ x) := by
    intro x
    have hx : x = bvec (ι := (phi N).ι) 0 (bvec 0 (slice 0 (slice 0 x))) +
        bvec (ι := (phi N).ι) 0 (bvec 1 (slice 1 (slice 0 x))) +
        bvec (ι := (phi N).ι) 1 (bvec 0 (slice 0 (slice 1 x))) +
        bvec (ι := (phi N).ι) 1 (bvec 1 (slice 1 (slice 1 x))) := by
      funext ⟨a, e, i⟩
      fin_cases a <;> fin_cases e <;> simp
    rw [hx]
    simp only [map_add]
    rw [k00, k01, k10, k11]
    rfl
  refine ⟨(vEquiv Θ).trans (thetaEquiv (A := A) (N := fun _ : Dance.Idx d => A)), ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
    have h2 := LinearMap.congr_fun
      (A2_theta_comp_F (A := A) (N := fun _ : Dance.Idx d => A) (Dance.F A d)) (vEquiv Θ x)
    simp only [LinearMap.comp_apply] at h2
    exact (congrArg (theta (A := A) (N := fun _ : Dance.Idx d => A)) (hV x)).trans h2
  · rintro ⟨a, e, i⟩ ⟨q, k⟩ hne
    erw [LinearEquiv.trans_apply, single_eq_bvec, single_eq_bvec, vEquiv_bvec]
    change (theta (embVΦ A (fun _ : Dance.Idx d => A) a e (Θ (Pi.single i 1)))) (q, k) = 0
    change 2 * ((flΨ (Dance.fl d) (q, k) : ℕ) : ℤ) +
      (wtV a + phiWt N (e, i)) ≠ 2 * l + 2 at hne
    simp only [flΨ, phiWt] at hne
    have key : 2 * (Dance.fl d q : ℤ) + N.wt i ≠ l → Θ (Pi.single i 1) q = 0 := h.2 i q
    rw [theta_embVΦ]
    fin_cases a <;> fin_cases e <;> fin_cases k <;>
      simp [embΨ_apply] at hne ⊢ <;> apply key <;> omega

omit [IsDomain A] [CharZero A] [OddUnits A] in
/-- The base case of (B1) of `C32_theorem_38_the_groups_of_the_families.md`:
`𝟙 ≃ T([])`, both one-dimensional with `F = 0`. -/
lemma towerRel_one : ∃ Θ : ((one A).ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx [], A),
    TowerRel (one A) [] 0 Θ := by
  let Θ : ((one A).ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx [], A) :=
    (DirectSum.linearEquivFunOnFintype A Unit (fun _ => A)).symm
  refine ⟨Θ, ?_, ?_⟩
  · refine LinearMap.ext fun x => ?_
    change Θ (oneFd A 1 x) = (0 : (⨁ _ : Dance.Idx [], A) →ₗ[A] _) (Θ x)
    simp [oneFd]
  · intro j q hne
    exact absurd (by simp [Dance.fl, one]) hne

/-- **(B1)** of `C32_theorem_38_the_groups_of_the_families.md` (existence form): for every `λ`
there is an `A`-linear equivalence `Θ : (T A λ).ι → A ≃ ⨁ _ : Dance.Idx (ds λ), A` with
(a) `Θ ∘ₗ (T A λ).Fd 1 = Dance.F A (ds λ) ∘ₗ Θ` and
(b) `Θ (Pi.single j 1) q = 0` whenever `2 * fl q + wt j ≠ λ`.
Proof by strong induction on `λ`, following the recursions of `T` and `ds`. -/
theorem B1 (lam : ℕ) : ∃ Θ : ((T A lam).ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx (ds lam), A),
    Θ.toLinearMap ∘ₗ (T A lam).Fd 1 = Dance.F A (ds lam) ∘ₗ Θ.toLinearMap ∧
    ∀ (j : (T A lam).ι) (q : Dance.Idx (ds lam)),
      2 * (Dance.fl (ds lam) q : ℤ) + (T A lam).wt j ≠ lam → Θ (Pi.single j 1) q = 0 := by
  induction lam using Nat.strong_induction_on with
  | _ lam ih =>
    rcases cases3 lam with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
    · rw [T_zero, ds_zero]
      exact towerRel_one
    · obtain ⟨Θ, hΘ⟩ := ih l (by omega)
      rw [T_odd, ds_odd]
      obtain ⟨Θ', h'⟩ := towerRel_phi (T A l) (ds l) l Θ hΘ
      exact ⟨Θ', h'.1, fun j q hq => h'.2 j q (by push_cast at hq; exact hq)⟩
    · obtain ⟨Θ, hΘ⟩ := ih l (by omega)
      rw [T_even, ds_even]
      obtain ⟨Θ', h'⟩ := towerRel_tensorV_phi (T A l) (ds l) l Θ hΘ
      exact ⟨Θ', h'.1, fun j q hq => h'.2 j q (by push_cast at hq; exact hq)⟩

variable (A) in
/-- **(B1)** of `C32_theorem_38_the_groups_of_the_families.md`: the chosen equivalence
`Θ λ : ((T A λ).ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx (ds λ), A)` (a choice of the equivalence given by
`B1`). -/
def Theta (lam : ℕ) : ((T A lam).ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx (ds lam), A) :=
  Classical.choose (B1 (A := A) lam)

/-- **(B1)(a)** of `C32_theorem_38_the_groups_of_the_families.md`:
`Θ λ ∘ₗ (T A λ).Fd 1 = Dance.F A (ds λ) ∘ₗ Θ λ`. -/
theorem B1a (lam : ℕ) :
    (Theta A lam).toLinearMap ∘ₗ (T A lam).Fd 1 = Dance.F A (ds lam) ∘ₗ (Theta A lam).toLinearMap :=
  (Classical.choose_spec (B1 (A := A) lam)).1

/-- **(B1)(b)** of `C32_theorem_38_the_groups_of_the_families.md` (weights become floors): if
`2 * fl q + wt j ≠ λ` then `Θ λ (Pi.single j 1) q = 0`. -/
theorem B1b (lam : ℕ) (j : (T A lam).ι) (q : Dance.Idx (ds lam))
    (h : 2 * (Dance.fl (ds lam) q : ℤ) + (T A lam).wt j ≠ lam) :
    Theta A lam (Pi.single j 1) q = 0 :=
  (Classical.choose_spec (B1 (A := A) lam)).2 j q h

end B1

end Families
