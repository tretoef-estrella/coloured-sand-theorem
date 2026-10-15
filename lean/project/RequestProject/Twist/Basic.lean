module

public import RequestProject.Doubling.All

/-!
# `C21_reduction_mod_2_and_the_twist.md`: Part R, base change of linear maps (R0)

Encodings (namespace `Twist`), reusing C18 (`DPLattice`), C19 (`WeylFilt.Hom.id`,
`WeylFilt.Hom.comp`) and C20 (`Doubling`):

* `A`, `B` are commutative rings and `φ : A →+* B` is a ring homomorphism.
* For an `A`-linear map `f : (ι → A) →ₗ[A] (κ → A)` (in particular an endomorphism), its base
  change `f^φ` is `bc φ f := Matrix.toLin' ((LinearMap.toMatrix' f).map φ)`: the `B`-linear map
  whose matrix is the matrix of `f` with `φ` applied to every entry, i.e.
  `f^φ (δ_i) j = φ (f (δ_i) j)` (`bc_single_apply`).
* The reduction of a vector `x : ι → A` is `φ ∘ x` (written `⇑φ ∘ x`).
-/

@[expose] public section

noncomputable section

namespace Twist

open DPLattice Finset

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)

section bc

variable {ι κ μ : Type*} [Fintype ι] [DecidableEq ι]

/-- Part R: the base change `f^φ` of an `A`-linear map `f : (ι → A) → (κ → A)`: the `B`-linear
map whose matrix is the matrix of `f` with `φ` applied entrywise. -/
def bc (f : (ι → A) →ₗ[A] (κ → A)) : (ι → B) →ₗ[B] (κ → B) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map φ)

/-- (R0) `f^φ (φ ∘ x) = φ ∘ (f x)` for every `x : ι → A`. -/
theorem bc_apply_comp (f : (ι → A) →ₗ[A] (κ → A)) (x : ι → A) :
    bc φ f (⇑φ ∘ x) = ⇑φ ∘ (f x) := by
  rw [bc, Matrix.toLin'_apply]
  have := RingHom.map_mulVec φ (LinearMap.toMatrix' f) x
  funext j
  rw [Function.comp_apply, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix'] at *
  rw [this]; rfl

omit [Fintype ι] in
lemma comp_single (i : ι) : (⇑φ ∘ (Pi.single i (1 : A) : ι → A)) = Pi.single i 1 := by
  funext j; by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- Part R: `f^φ (δ_i) j = φ (f (δ_i) j)`. -/
theorem bc_single_apply (f : (ι → A) →ₗ[A] (κ → A)) (i : ι) (j : κ) :
    bc φ f (Pi.single i 1) j = φ (f (Pi.single i 1) j) := by
  rw [← comp_single φ i, bc_apply_comp]; rfl

/-- Part R (auxiliary): two `B`-linear maps agreeing on all reduced vectors `φ ∘ x` are equal. -/
lemma ext_comp {N : Type*} [AddCommGroup N] [Module B N] {f g : (ι → B) →ₗ[B] N}
    (h : ∀ x : ι → A, f (⇑φ ∘ x) = g (⇑φ ∘ x)) : f = g :=
  ext_single fun i => by rw [← comp_single φ i]; exact h _

omit [Fintype ι] [DecidableEq ι] in
lemma comp_add (x y : ι → A) : (⇑φ ∘ (x + y)) = ⇑φ ∘ x + ⇑φ ∘ y := by
  funext j; simp

omit [Fintype ι] [DecidableEq ι] in
lemma comp_smul (c : A) (x : ι → A) : (⇑φ ∘ (c • x)) = φ c • (⇑φ ∘ x) := by
  funext j; simp

omit [Fintype ι] [DecidableEq ι] in
lemma comp_zero : (⇑φ ∘ (0 : ι → A)) = 0 := by funext j; simp

omit [Fintype ι] [DecidableEq ι] in
lemma comp_sum {J : Type*} (S : Finset J) (x : J → ι → A) :
    (⇑φ ∘ (∑ j ∈ S, x j)) = ∑ j ∈ S, ⇑φ ∘ x j := by
  funext k; simp [Finset.sum_apply]

/-- (R0) `(f ∘ g)^φ = f^φ ∘ g^φ`. -/
theorem bc_comp [Fintype κ] [DecidableEq κ] (f : (κ → A) →ₗ[A] (μ → A)) (g : (ι → A) →ₗ[A] (κ → A)) :
    bc φ (f ∘ₗ g) = bc φ f ∘ₗ bc φ g :=
  ext_comp φ fun x => by
    rw [LinearMap.comp_apply, bc_apply_comp, bc_apply_comp, bc_apply_comp]; rfl

/-- (R0) `1^φ = 1`. -/
theorem bc_one : bc φ (1 : Module.End A (ι → A)) = 1 :=
  ext_comp φ fun x => by rw [bc_apply_comp]; rfl

theorem bc_id : bc φ (LinearMap.id : (ι → A) →ₗ[A] (ι → A)) = LinearMap.id := bc_one φ

/-- (R0) `(c • f)^φ = φ(c) • f^φ`. -/
theorem bc_smul (c : A) (f : (ι → A) →ₗ[A] (κ → A)) : bc φ (c • f) = φ c • bc φ f :=
  ext_comp φ fun x => by
    rw [bc_apply_comp, LinearMap.smul_apply, LinearMap.smul_apply, bc_apply_comp, comp_smul]

theorem bc_add (f g : (ι → A) →ₗ[A] (κ → A)) : bc φ (f + g) = bc φ f + bc φ g :=
  ext_comp φ fun x => by
    rw [bc_apply_comp, LinearMap.add_apply, LinearMap.add_apply, bc_apply_comp, bc_apply_comp,
      comp_add]

theorem bc_zero : bc φ (0 : (ι → A) →ₗ[A] (κ → A)) = 0 :=
  ext_comp φ fun x => by rw [bc_apply_comp]; simp

theorem bc_mul (f g : Module.End A (ι → A)) : bc φ (f * g) = bc φ f * bc φ g := bc_comp φ f g

/-- Part R: base change as a ring homomorphism `Module.End A (ι → A) →+* Module.End B (ι → B)`
(from (R0): it preserves `1`, composites, `0` and sums). -/
def bcRingHom : Module.End A (ι → A) →+* Module.End B (ι → B) where
  toFun := bc φ
  map_one' := bc_one φ
  map_mul' := bc_mul φ
  map_zero' := bc_zero φ
  map_add' := bc_add φ

@[simp] lemma bcRingHom_apply (f : Module.End A (ι → A)) : bcRingHom φ f = bc φ f := rfl

theorem bc_intCast_smul (k : ℤ) (f : (ι → A) →ₗ[A] (κ → A)) :
    bc φ (((k : ℤ) : A) • f) = ((k : ℤ) : B) • bc φ f := by
  rw [bc_smul, map_intCast]

/-- (R0) The weight operator: `(Hop wt)^φ = Hop wt`. -/
theorem bc_Hop (wt : ι → ℤ) : bc φ (Hop (A := A) wt) = Hop wt :=
  ext_comp φ fun x => by
    rw [bc_apply_comp]; funext j; simp

omit [Fintype ι] [DecidableEq ι] in
/-- (R3), auxiliary: the slot maps `b_e` and `slice e` commute with reduction. -/
lemma bvec_comp (e : Fin 2) (m : ι → A) : bvec e (⇑φ ∘ m) = ⇑φ ∘ bvec e m := by
  funext p; by_cases h : p.1 = e <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
lemma slice_comp (e : Fin 2) (x : Fin 2 × ι → A) : slice e (⇑φ ∘ x) = ⇑φ ∘ slice e x := rfl

/-- (R0) Base change of linear maps: `f^φ (φ ∘ x) = φ ∘ (f x)` for every `x : ι → A`;
`(f ∘ g)^φ = f^φ ∘ g^φ`; `1^φ = 1`; `(c • f)^φ = φ(c) • f^φ`. -/
theorem R0 [Fintype κ] [DecidableEq κ] :
    (∀ (f : (ι → A) →ₗ[A] (κ → A)) (x : ι → A), bc φ f (⇑φ ∘ x) = ⇑φ ∘ (f x)) ∧
    (∀ (f : (κ → A) →ₗ[A] (μ → A)) (g : (ι → A) →ₗ[A] (κ → A)),
      bc φ (f ∘ₗ g) = bc φ f ∘ₗ bc φ g) ∧
    bc φ (1 : Module.End A (ι → A)) = 1 ∧
    (∀ (c : A) (f : (ι → A) →ₗ[A] (κ → A)), bc φ (c • f) = φ c • bc φ f) :=
  ⟨bc_apply_comp φ, bc_comp φ, bc_one φ, bc_smul φ⟩

end bc

end Twist
