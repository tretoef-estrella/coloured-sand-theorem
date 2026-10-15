module

public import RequestProject.Families.Tower
public import RequestProject.FamilyGroup.Basic

/-!
# `C32_theorem_38_the_groups_of_the_families.md`: Part B2 — the group of a family is the group
# of its tower

Encodings (namespace `Families`):

* `sigL A λ α i := (T A λ).Fd 1 + (2 ^ (α − 1) : A) • (((λ : A) + 2 * i) • id − H (T A λ))` is the
  operator `σ^{(α)}_i = F + 2^α (D + i)` of §3.4 on `T(λ)`, written with `2D = λ − H`.
* `slotE ds : (⨁ _ : Dance.Idx ds, A) ≃ₗ[A] Dance.SysT A ds (Fin 1)` is the identification
  `M ≃ M^{Fin 1}`, `m ↦ m ι_0` (C11 `slotEmb`).
* The cokernel of an endomorphism `f` of `X` is `X ⧸ LinearMap.range f`; the equivalence of (B2)
  is the explicit `sigEquiv`, induced by `slotE ∘ Θ λ` (Part B1).
* `ℤ_[2]` is `PadicInt 2`; `FamilyGroup.X ds α i` is C16's group of the tower.
-/

@[expose] public section

noncomputable section

namespace Families

open DirectSum DPLattice Doubling Payment Split Filt

universe u

variable {A : Type u} [CommRing A]

/-! ### The identification `M ≃ M^{Fin 1}` -/

section slot

variable (ds : List Bool)

/-- The inverse of `m ↦ m ι_0` (auxiliary for (B2) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
def slotProj : Dance.SysT A ds (Fin 1) →ₗ[A] (⨁ _ : Dance.Idx ds, A) :=
  DirectSum.toModule A (Fin 1 × Dance.Idx ds) _ (fun q =>
    DirectSum.lof A (Dance.Idx ds) (fun _ => A) q.2)

variable (A) in
/-- The identification `M ≃ M^{Fin 1}`, `m ↦ m ι_0` (C11 `slotEmb`) (auxiliary for (B2) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
def slotE : (⨁ _ : Dance.Idx ds, A) ≃ₗ[A] Dance.SysT A ds (Fin 1) :=
  LinearEquiv.ofLinear (slotEmb A (fun _ : Dance.Idx ds => A) (Fin 1) 0) (slotProj ds)
    (by
      apply DirectSum.linearMap_ext; rintro ⟨s, q⟩; refine LinearMap.ext fun x => ?_
      have hs : s = 0 := Subsingleton.elim _ _
      subst hs
      simp [slotProj, DirectSum.toModule_lof, slotLof])
    (by
      apply DirectSum.linearMap_ext; intro q; refine LinearMap.ext fun x => ?_
      simp [slotProj, DirectSum.toModule_lof, slotLof])

lemma slotE_apply (v : ⨁ _ : Dance.Idx ds, A) :
    slotE A ds v = slotEmb A (fun _ : Dance.Idx ds => A) (Fin 1) 0 v := rfl

/-- The diagonal part `x at q ↦ (2 · pσ(fl q)) x at q` of `σ` (auxiliary for (B2) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
def diagσ (α i : ℕ) : (⨁ _ : Dance.Idx ds, A) →ₗ[A] (⨁ _ : Dance.Idx ds, A) :=
  DirectSum.toModule A (Dance.Idx ds) _ (fun q =>
    (2 * Dance.pσ (A := A) α i 0 (Dance.fl ds q)) • DirectSum.lof A (Dance.Idx ds) (fun _ => A) q)

lemma diagσ_apply (α i : ℕ) (v : ⨁ _ : Dance.Idx ds, A) (q : Dance.Idx ds) :
    diagσ ds α i v q = 2 * Dance.pσ (A := A) α i 0 (Dance.fl ds q) * v q := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of k x =>
    rw [← DirectSum.lof_eq_of A, diagσ, DirectSum.toModule_lof, LinearMap.smul_apply,
      DFinsupp.smul_apply, lof_apply_const]
    by_cases h : q = k
    · subst h; simp [smul_eq_mul]
    · simp [h]
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy, mul_add]

/-- `σ (m ι_0) = (F m + diagσ m) ι_0` (auxiliary for (B2) of
`C32_theorem_38_the_groups_of_the_families.md`): the slot type `Fin 1` has no coupling. -/
lemma sigma_slotE (α i : ℕ) (v : ⨁ _ : Dance.Idx ds, A) :
    Dance.sigma A ds α i (slotE A ds v) = slotE A ds (Dance.F A ds v + diagσ ds α i v) := by
  have : (Dance.sigma A ds α i ∘ₗ (slotE A ds).toLinearMap : (⨁ _ : Dance.Idx ds, A) →ₗ[A] _) =
      (slotE A ds).toLinearMap ∘ₗ (Dance.F A ds + diagσ ds α i) := by
    apply DirectSum.linearMap_ext; intro q; refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, slotE_apply, slotEmb_lof,
      LinearMap.add_apply, map_add]
    rw [Dance.sigma, G_eq, LinearMap.add_apply, FS_slotLof, DS_slotLof]
    have hempty : Finset.univ.filter (fun s : Fin 1 => (0 : Fin 1) < s) = ∅ := by
      ext s; simp [Fin.lt_def, Subsingleton.elim s 0]
    rw [hempty, Finset.sum_empty, add_zero]
    congr 1
    simp [diagσ, DirectSum.toModule_lof, slotLof]
  exact LinearMap.congr_fun this v

end slot

/-! ### (B2) -/

section B2

variable [IsDomain A] [CharZero A] [OddUnits A]

variable (A) in
/-- The operator `σ^{(α)}_i = F + 2^α (D + i)` of §3.4 on `T(λ)`, written with `2D = λ − H`:
`sigL A λ α i := (T A λ).Fd 1 + (2 ^ (α − 1) : A) • (((λ : A) + 2 * i) • id − H (T A λ))`
(Part B2 of `C32_theorem_38_the_groups_of_the_families.md`). -/
def sigL (lam α i : ℕ) : Module.End A ((T A lam).ι → A) :=
  (T A lam).Fd 1 + (2 ^ (α - 1) : A) • (((lam : A) + 2 * i) • LinearMap.id - H (T A lam))

/-- On the image of a basis vector, `diagσ` is the scalar `2^{α−1}(λ + 2i − wt j)` (auxiliary for
(B2) of `C32_theorem_38_the_groups_of_the_families.md`; this is where (B1)(b) is used). -/
lemma diagσ_Theta (lam α i : ℕ) (j : (T A lam).ι) :
    diagσ (ds lam) α i (Theta A lam (Pi.single j 1)) =
      ((2 : A) ^ (α - 1) * ((lam : A) + 2 * i - ((T A lam).wt j : A))) •
        Theta A lam (Pi.single j 1) := by
  refine DFinsupp.ext fun q => ?_
  rw [diagσ_apply, DFinsupp.smul_apply, smul_eq_mul]
  by_cases h : 2 * (Dance.fl (ds lam) q : ℤ) + (T A lam).wt j = lam
  · have h' : ((T A lam).wt j : A) = (lam : A) - 2 * (Dance.fl (ds lam) q : A) := by
      have := congrArg (fun z : ℤ => (z : A)) h
      push_cast at this
      linear_combination this
    rw [h', Dance.pσ]
    ring
  · rw [B1b lam j q h, mul_zero, mul_zero]

/-- The intertwining `slotE ∘ Θ λ ∘ sigL = σ ∘ slotE ∘ Θ λ` (auxiliary for (B2) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
lemma sigL_intertwine (lam α i : ℕ) :
    ((Theta A lam).trans (slotE A (ds lam))).toLinearMap ∘ₗ sigL A lam α i =
      Dance.sigma A (ds lam) α i ∘ₗ ((Theta A lam).trans (slotE A (ds lam))).toLinearMap := by
  have hF : ∀ x, Theta A lam ((T A lam).Fd 1 x) = Dance.F A (ds lam) (Theta A lam x) :=
    fun x => LinearMap.congr_fun (B1a lam) x
  refine ext_single fun j => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, sigma_slotE]
  congr 1
  have hH : H (T A lam) (Pi.single j (1 : A)) =
      ((T A lam).wt j : A) • (Pi.single j (1 : A) : (T A lam).ι → A) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  simp only [sigL, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, hH, map_add, map_smul, map_sub, hF, diagσ_Theta]
  rw [← sub_smul, smul_smul]

/-- **(B2)** of `C32_theorem_38_the_groups_of_the_families.md` (explicit equivalence): the
cokernel of `sigL A λ α i` on `T(λ)` is the cokernel of `σ^{(α)}_i = Dance.sigma A (ds λ) α i` on
`Sys(T(ds λ), Fin 1)`, through `slotE ∘ Θ λ`. -/
def sigEquiv (lam α i : ℕ) :
    (((T A lam).ι → A) ⧸ LinearMap.range (sigL A lam α i)) ≃ₗ[A]
      (Dance.SysT A (ds lam) (Fin 1) ⧸ LinearMap.range (Dance.sigma A (ds lam) α i)) :=
  let Φ := (Theta A lam).trans (slotE A (ds lam))
  Submodule.Quotient.equiv _ _ Φ (by
    rw [← LinearMap.range_comp, sigL_intertwine, LinearMap.range_comp_of_range_eq_top]
    exact LinearEquiv.range Φ)

/-- **(B2)** of `C32_theorem_38_the_groups_of_the_families.md`: for every `λ`, `α ≥ 1` and `i`,
`((T A λ).ι → A) ⧸ range (sigL A λ α i) ≃ₗ[A] SysT A (ds λ) (Fin 1) ⧸ range (sigma A (ds λ) α i)`.
The hypothesis `1 ≤ α` is kept as in the file but is not used: both `sigL` and `Dance.pσ` carry the
same factor `2 ^ (α − 1)`, so the statement holds for every `α` (see `sigEquiv`). -/
theorem B2 (lam α i : ℕ) (_hα : 1 ≤ α) :
    Nonempty ((((T A lam).ι → A) ⧸ LinearMap.range (sigL A lam α i)) ≃ₗ[A]
      (Dance.SysT A (ds lam) (Fin 1) ⧸ LinearMap.range (Dance.sigma A (ds lam) α i))) :=
  ⟨sigEquiv lam α i⟩

/-- **(B2Z)** of `C32_theorem_38_the_groups_of_the_families.md` (explicit equivalence): for
`A = ℤ_[2]`, the cokernel of `sigL` on `T(λ)` is C16's group `FamilyGroup.X (ds λ) α i`. -/
def sigEquivZ (lam α i : ℕ) :
    (((T ℤ_[2] lam).ι → ℤ_[2]) ⧸ LinearMap.range (sigL ℤ_[2] lam α i)) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (ds lam) α i :=
  sigEquiv lam α i

/-- **(B2Z)** of `C32_theorem_38_the_groups_of_the_families.md`: for `A = ℤ_[2]`,
`((T ℤ_[2] λ).ι → ℤ_[2]) ⧸ range (sigL ℤ_[2] λ α i) ≃ₗ[ℤ_[2]] FamilyGroup.X (ds λ) α i`
(for `α ≥ 1`; as in (B2), the hypothesis `1 ≤ α` is not used). -/
theorem B2Z (lam α i : ℕ) (_hα : 1 ≤ α) :
    Nonempty ((((T ℤ_[2] lam).ι → ℤ_[2]) ⧸ LinearMap.range (sigL ℤ_[2] lam α i)) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (ds lam) α i) :=
  ⟨sigEquivZ lam α i⟩

end B2

end Families
