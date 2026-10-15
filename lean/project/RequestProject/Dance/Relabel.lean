module

public import RequestProject.Dance.Basic

/-!
# Part R of `C13_the_dance.md`: relabelling slots

* `cokerEquivOfIntertwine`: a linear equivalence `E` with `E ∘ f = g ∘ E` induces
  `coker(c · f) ≅ coker(c · g)` for every `c`.
* `relabSys e : Sys N S ≃ₗ[A] Sys N S'` is the slotwise relabelling `x ι_{s,i} ↦ x ι_{e s, i}`
  (`relabSys_slotLof`).
* **(R1)** `R1_intertwine`: for `e : S ≃o S'`, `relabSys e ∘ G[fl, F, p' ∘ e, κ' ∘ (e × e)] =
  G[fl, F, p', κ'] ∘ relabSys e`; `R1_coker`: the cokernels of `c · G` are equivalent.
-/

@[expose] public section

universe u

namespace Dance

open DirectSum Payment
open scoped Pointwise

variable {A : Type u} [CommRing A]

/-- A linear equivalence `E : M ≃ M'` with `E ∘ f = g ∘ E` induces, for every `c ∈ A`, an
equivalence `M ⧸ range (c • f) ≃ M' ⧸ range (c • g)` (used for *Part R*, (R1), and *Part D*, (D3),
of `C13_the_dance.md`). -/
noncomputable def cokerEquivOfIntertwine {M M' : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (E : M ≃ₗ[A] M') (f : M →ₗ[A] M) (g : M' →ₗ[A] M')
    (h : (E : M →ₗ[A] M') ∘ₗ f = g ∘ₗ (E : M →ₗ[A] M')) (c : A) :
    (M ⧸ LinearMap.range (c • f)) ≃ₗ[A] (M' ⧸ LinearMap.range (c • g)) :=
  Submodule.Quotient.equiv _ _ E (by
    change (LinearMap.range (c • f)).map (E : M →ₗ[A] M') = _
    rw [← LinearMap.range_comp, LinearMap.comp_smul, h, ← LinearMap.smul_comp,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 E.surjective)])

variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable {S S' : Type*} [Fintype S] [LinearOrder S] [Fintype S'] [LinearOrder S']

variable (A N) in
/-- The slotwise relabelling map `x ι_{s,i} ↦ x ι_{e s, i}` (*Part R*, (R1), of
`C13_the_dance.md`). -/
noncomputable def relabMap (e : S ≃ S') : Sys N S →ₗ[A] Sys N S' :=
  DirectSum.toModule A (S × ι) _ (fun q => slotLof A N S' (e q.1) q.2)

omit [Fintype S] [Fintype S'] in
/-- `relabMap e (x ι_{s,i}) = x ι_{e s, i}` (*Part R*, (R1), of `C13_the_dance.md`). -/
@[simp] lemma relabMap_slotLof (e : S ≃ S') (s : S) (i : ι) (x : N i) :
    relabMap A N e (slotLof A N S s i x) = slotLof A N S' (e s) i x := by
  simp [relabMap, slotLof, DirectSum.toModule_lof]

variable (A N) in
/-- The slotwise relabelling `Sys N S ≃ₗ[A] Sys N S'`, `x ι_{s,i} ↦ x ι_{e s, i}` (*Part R*, (R1),
of `C13_the_dance.md`). -/
noncomputable def relabSys (e : S ≃ S') : Sys N S ≃ₗ[A] Sys N S' :=
  LinearEquiv.ofLinear (relabMap A N e) (relabMap A N e.symm)
    (by
      apply DirectSum.linearMap_ext
      rintro ⟨s, i⟩
      refine LinearMap.ext fun x => ?_
      change relabMap A N e (relabMap A N e.symm (slotLof A N S' s i x)) = slotLof A N S' s i x
      simp)
    (by
      apply DirectSum.linearMap_ext
      rintro ⟨s, i⟩
      refine LinearMap.ext fun x => ?_
      change relabMap A N e.symm (relabMap A N e (slotLof A N S s i x)) = slotLof A N S s i x
      simp)

omit [Fintype S] [Fintype S'] in
/-- `relabSys e (x ι_{s,i}) = x ι_{e s, i}` (*Part R*, (R1), of `C13_the_dance.md`). -/
@[simp] lemma relabSys_slotLof (e : S ≃ S') (s : S) (i : ι) (x : N i) :
    relabSys A N e (slotLof A N S s i x) = slotLof A N S' (e s) i x :=
  relabMap_slotLof e s i x

omit [Fintype S] [Fintype S'] in
/-- `relabSys e (m ι_s) = m ι_{e s}` (*Part R*, (R1), of `C13_the_dance.md`). -/
lemma relabSys_slotEmb (e : S ≃ S') (s : S) (m : ⨁ i, N i) :
    relabSys A N e (slotEmb A N S s m) = slotEmb A N S' (e s) m := by
  induction m using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    change relabSys A N e (slotEmb A N S s (DirectSum.lof A ι N i x)) =
      slotEmb A N S' (e s) (DirectSum.lof A ι N i x)
    simp
  | add x y hx hy => simp [map_add, hx, hy]

/-- **(R1)** of `C13_the_dance.md`, intertwining: for an order isomorphism `e : S ≃o S'` and
halved data `(p', κ')` on `S'`, with `p := p' ∘ e` and `κ s u := κ' (e s) (e u)`, the slotwise
relabelling intertwines `G[fl, F, p, κ]` and `G[fl, F, p', κ']`. -/
theorem R1_intertwine (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (e : S ≃o S')
    (p' : S' → ℕ → A) (κ' : S' → S' → ℕ → A) :
    (relabSys A N e.toEquiv : Sys N S →ₗ[A] Sys N S') ∘ₗ G fl F (relabP e p') (relabK e κ') =
      G fl F p' κ' ∘ₗ (relabSys A N e.toEquiv : Sys N S →ₗ[A] Sys N S') := by
  apply DirectSum.linearMap_ext
  rintro ⟨s', i⟩
  refine LinearMap.ext fun x => ?_
  change relabSys A N e.toEquiv (G fl F (relabP e p') (relabK e κ') (slotLof A N S s' i x)) =
    G fl F p' κ' (relabSys A N e.toEquiv (slotLof A N S s' i x))
  rw [G_eq, G_eq]
  simp only [LinearMap.add_apply, FS_slotLof, DS_slotLof, map_add, map_sum, map_smul,
    relabSys_slotLof, relabSys_slotEmb, relabSys_slotLof]
  simp only [relabP, relabK]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp e.toEquiv]
  simp [e.lt_iff_lt]

/-- **(R1)** of `C13_the_dance.md`, cokernels: for an order isomorphism `e : S ≃o S'`, halved data
`(p', κ')` on `S'` and every `c ∈ A`,
`coker(c · G[fl, F, p' ∘ e, κ' ∘ (e × e)]) ≅ coker(c · G[fl, F, p', κ'])`. -/
theorem R1_coker (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (e : S ≃o S')
    (p' : S' → ℕ → A) (κ' : S' → S' → ℕ → A) (c : A) :
    Nonempty ((Sys N S ⧸ LinearMap.range (c • G fl F (relabP e p') (relabK e κ'))) ≃ₗ[A]
      (Sys N S' ⧸ LinearMap.range (c • G fl F p' κ'))) :=
  ⟨cokerEquivOfIntertwine _ _ _ (R1_intertwine fl F e p' κ') c⟩

end Dance
