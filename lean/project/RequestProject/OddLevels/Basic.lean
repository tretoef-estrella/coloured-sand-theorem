module

public import RequestProject.OddPayment.Basic
public import RequestProject.DPLattice.Basic

/-!
# `CSI9_last_level_and_floors.md`: common encodings, and Part G (G3)

Namespace `ColouredSand.OddTwist`. Reuses C11's `Payment.Sys`, CSI7's system `Gp p fl F Q`
(`RequestProject/OddPayment/`) and C18's `DPLattice` (`RequestProject/DPLattice/`).

## Encodings

* **Lattices as graded families.** A DP-lattice `M : DPLattice A` acts on the module of functions
  `M.ι → A` (C18), while a graded family of CSI7 acts on a direct sum `⨁ i, N i`. For a lattice all
  modules are `N i = A`, and the identification of `(κ → A)` with `⨁ _ : κ, A` is the standard
  finite one, `dsE A κ := DirectSum.linearEquivFunOnFintype` (the generator `lof i 1` is the basis
  vector `Pi.single i 1`).
* **Reindexing.** For an equivalence of index types `e : κ ≃ ι` and an endomorphism `T` of
  `ι → A`, `opDS e T` is the endomorphism of `⨁ _ : κ, A` obtained by transporting `T` along `e`
  and `dsE`: on functions it is `f ↦ (T (f ∘ e.symm)) ∘ e` (`dsE_opDS`). With `e = Equiv.refl`,
  `famF M := opDS (Equiv.refl _) (M.Fd 1)` is the operator `F = F^{(1)}` of `M` read as the
  operator of a graded family (with `N i = A`).
* **One slot.** For (G3) the slot type is `Unit`; the module of a one-slot system,
  `Payment.Sys (fun _ : ι => A) Unit = ⨁ q : Unit × ι, A`, is identified with `ι → A` by
  `sysUnitE A ι` (`x ↦ (i ↦ x ((), i))`).
* **(G3)** `Dop fl` is the diagonal operator `(Dop fl x) j = fl j · x j` (the file's `D_fl`);
  `Q0 p e i φ` is the `1 × 1` matrix `p^{e−1} (φ + i)`; the operator of the file is
  `σ = F + p^e • (D_fl + i)`, written `T + (p : A)^e • (Dop fl + (i : A) • 1)`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DirectSum

variable (A : Type*) [CommRing A]

/-- The standard finite identification `(⨁ _ : κ, A) ≃ (κ → A)` (Part G (G2) of
`CSI9_last_level_and_floors.md`: "the identification of `(ι → ℤ_[p])` with `⨁ i, ℤ_[p]` is the
standard finite one"). -/
def dsE (κ : Type*) [Fintype κ] [DecidableEq κ] : (⨁ _ : κ, A) ≃ₗ[A] (κ → A) :=
  DirectSum.linearEquivFunOnFintype A κ (fun _ => A)

variable {A}

lemma dsE_lof {κ : Type*} [Fintype κ] [DecidableEq κ] (i : κ) (a : A) :
    dsE A κ (DirectSum.lof A κ (fun _ => A) i a) = Pi.single i a :=
  DirectSum.linearEquivFunOnFintype_lof ..

lemma dsE_symm_single {κ : Type*} [Fintype κ] [DecidableEq κ] (i : κ) (a : A) :
    (dsE A κ).symm (Pi.single i a) = DirectSum.lof A κ (fun _ => A) i a := by
  rw [LinearEquiv.symm_apply_eq, dsE_lof]

/-- An endomorphism `T` of `ι → A` transported to `⨁ _ : κ, A` along an equivalence of index
types `e : κ ≃ ι` (Part G (G2) of `CSI9_last_level_and_floors.md`, "equality of linear maps after
the reindexing equivalence of index types"): on functions, `f ↦ (T (f ∘ e.symm)) ∘ e`. -/
def opDS {κ ι : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (T : Module.End A (ι → A)) :
    Module.End A (⨁ _ : κ, A) :=
  (dsE A κ).symm.toLinearMap ∘ₗ LinearMap.funLeft A A e ∘ₗ T ∘ₗ
    LinearMap.funLeft A A e.symm ∘ₗ (dsE A κ).toLinearMap

lemma dsE_opDS {κ ι : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (T : Module.End A (ι → A))
    (x : ⨁ _ : κ, A) : dsE A κ (opDS e T x) = (T (dsE A κ x ∘ e.symm)) ∘ e := by
  simp [opDS]; rfl

/-- The operator `F = F^{(1)}` of a DP-lattice read as the operator of a graded family on
`⨁ _ : M.ι, A` (Part G of `CSI9_last_level_and_floors.md`: "`danceL p λ`'s `Fd 1`, read as a
graded family"; Part L: "the `Fd 1` of `delta ℤ_[p] (d−1)`"). -/
def famF (M : DPLattice A) : Module.End A (⨁ _ : M.ι, A) := opDS (Equiv.refl M.ι) (M.Fd 1)

lemma dsE_famF (M : DPLattice A) (x : ⨁ _ : M.ι, A) :
    dsE A M.ι (famF M x) = M.Fd 1 (dsE A M.ι x) := by
  rw [famF, dsE_opDS]; rfl

lemma famF_lof (M : DPLattice A) (i : M.ι) (a : A) :
    famF M (DirectSum.lof A M.ι (fun _ => A) i a) = (dsE A M.ι).symm (M.Fd 1 (Pi.single i a)) := by
  rw [LinearEquiv.eq_symm_apply, dsE_famF, dsE_lof]

variable (A) in
/-- The module of a one-slot system, `Payment.Sys (fun _ : ι => A) Unit = ⨁ q : Unit × ι, A`,
identified with `ι → A`: `x ↦ (i ↦ x ((), i))` (Part G (G3) of
`CSI9_last_level_and_floors.md`, "with one slot"). -/
def sysUnitE (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Payment.Sys (fun _ : ι => A) Unit ≃ₗ[A] (ι → A) :=
  (DirectSum.linearEquivFunOnFintype A (Unit × ι) (fun _ => A)).trans
    (LinearEquiv.funCongrLeft A A (Equiv.punitProd ι).symm)

lemma sysUnitE_lof {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) (a : A) :
    sysUnitE A ι (DirectSum.lof A (Unit × ι) (fun q => (fun _ : ι => A) q.2) ((), k) a) =
      Pi.single k a := by
  funext j
  simp only [sysUnitE, LinearEquiv.trans_apply]
  rw [DirectSum.linearEquivFunOnFintype_lof]
  simp [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Pi.single_apply]

/-- The diagonal operator `D_fl x := fl · x` coordinatewise (Part G (G3) of
`CSI9_last_level_and_floors.md`). -/
def Dop {ι : Type*} (fl : ι → ℕ) : Module.End A (ι → A) where
  toFun x j := (fl j : A) * x j
  map_add' x y := by funext j; simp [mul_add]
  map_smul' c x := by funext j; simp; ring

@[simp] lemma Dop_apply {ι : Type*} (fl : ι → ℕ) (x : ι → A) (j : ι) :
    Dop fl x j = (fl j : A) * x j := rfl

variable (A) in
/-- The one-slot data of (G3): the `1 × 1` matrix `Q₀ φ = p^{e−1} (φ + i)` (Part G (G3) of
`CSI9_last_level_and_floors.md`). -/
def Q0 (p e i : ℕ) (φ : ℕ) : Matrix Unit Unit A := fun _ _ => (p : A) ^ (e - 1) * ((φ : A) + i)

/-- **(G3), general form** (Part G (G3) of `CSI9_last_level_and_floors.md`, for an arbitrary
endomorphism `T` of `ι → A` and an arbitrary floor `fl`; the file's case is `T = Fd 1` of
`danceL p λ` and `fl = flL p λ`, see `G3_operator`): for `e ≥ 1` and `i : ℕ`, the one-slot system
`Gp p fl T Q₀` is `σ = T + p^e • (D_fl + i)`, i.e.
`sysUnitE ∘ Gp p fl T Q₀ = σ ∘ sysUnitE`. -/
theorem Gp_Q0_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (p e i : ℕ) (he : 1 ≤ e) (fl : ι → ℕ)
    (T : Module.End A (ι → A)) :
    (sysUnitE A ι).toLinearMap ∘ₗ Gp p fl (opDS (Equiv.refl ι) T) (Q0 A p e i) =
      (T + (p : A) ^ e • (Dop fl + (i : A) • (1 : Module.End A (ι → A)))) ∘ₗ
        (sysUnitE A ι).toLinearMap := by
  refine DirectSum.linearMap_ext A fun q => LinearMap.ext_ring ?_
  obtain ⟨⟨⟩, k⟩ := q
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Gp, DirectSum.toModule_lof,
    LinearMap.add_apply, Fintype.univ_unit, Finset.sum_singleton, LinearMap.smul_apply]
  rw [map_add, map_smul]
  have h2 : sysUnitE A ι (oslot A (fun _ : ι => A) Unit () k 1) = Pi.single k 1 :=
    sysUnitE_lof k 1
  have h3 : ∀ y : ⨁ _ : ι, A, sysUnitE A ι (oslotE A (fun _ : ι => A) Unit () y) = dsE A ι y := by
    intro y
    have : (sysUnitE A ι).toLinearMap ∘ₗ oslotE A (fun _ : ι => A) Unit () =
        (dsE A ι).toLinearMap := by
      refine DirectSum.linearMap_ext A fun k' => LinearMap.ext_ring ?_
      simp only [LinearMap.comp_apply, oslotE, DirectSum.toModule_lof, LinearEquiv.coe_coe]
      rw [dsE_lof]; exact sysUnitE_lof k' 1
    exact LinearMap.congr_fun this y
  rw [h2, h3, dsE_opDS]
  rw [dsE_lof]
  rw [show sysUnitE A ι (DirectSum.lof A (Unit × ι) (fun _ => A) ((), k) 1) = Pi.single k 1 from
    sysUnitE_lof k 1]
  funext j
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Dop_apply, Module.End.one_apply, Q0]
  by_cases hj : j = k
  · subst hj
    simp only [Pi.single_eq_same, mul_one]
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  · simp [Pi.single_eq_of_ne hj]

end ColouredSand.OddTwist
