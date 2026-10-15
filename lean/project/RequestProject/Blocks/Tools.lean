module

public import Mathlib

/-!
# Tools for computing cokernels (CSG1, §3 "Elimination")

Generic linear algebra used throughout the formalization of `CSG1_lemma_8_the_blocks.md`
(§3, "the proof in the paper"): this file contains no statement of the document itself.

* `quotEquivOfSection`: if `π : V → W` has a linear section `σ` (`π ∘ σ = id`) with
  `v − σ (π v) ∈ N` for all `v`, then `V ⧸ N ≃ W ⧸ π(N)`.  This is the formal version of
  "eliminating generators" (solving relations with unit coefficients, or changing generators).
* `quotProdEquiv`: `(V × W) ⧸ (A × B) ≃ (V ⧸ A) × (W ⧸ B)`.
* `ev i : Fin m → R`: the basis vector `e_i`, indexed by a natural number, and `0` when `i ≥ m`
  (this makes the columns of bidiagonal matrices uniform: the last column has no subdiagonal
  entry because `e_{n+1} = 0` in `R^{n+1}`).
-/

@[expose] public section

open Submodule

namespace ColouredSand.Blocks

section general

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Quotients are preserved by a map with a linear section that is the identity modulo `N`. -/
noncomputable def quotEquivOfSection (N : Submodule R V) (N' : Submodule R W) (π : V →ₗ[R] W)
    (σ : W →ₗ[R] V) (hπσ : ∀ w, π (σ w) = w) (hσπ : ∀ v, v - σ (π v) ∈ N)
    (hN : N.map π = N') : (V ⧸ N) ≃ₗ[R] (W ⧸ N') := by
  subst hN
  have hσ : N.map π ≤ (N).comap σ := by
    rintro _ ⟨n, hn, rfl⟩
    show σ (π n) ∈ N
    have h2 : σ (π n) = n - (n - σ (π n)) := by abel
    rw [h2]; exact N.sub_mem hn (hσπ n)
  refine LinearEquiv.ofLinear (N.mapQ (N.map π) π (le_comap_map π N))
    ((N.map π).mapQ N σ hσ) ?_ ?_
  · ext w
    simp [hπσ]
  · ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.id_comp]
    rw [Submodule.Quotient.eq]
    have := N.neg_mem (hσπ v)
    simpa using this

/-- Quotient of a product by a product of submodules. -/
noncomputable def quotProdEquiv (A : Submodule R V) (B : Submodule R W) :
    ((V × W) ⧸ A.prod B) ≃ₗ[R] (V ⧸ A) × (W ⧸ B) := by
  have h1 : A.prod B ≤ LinearMap.ker (LinearMap.prodMap A.mkQ B.mkQ) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [LinearMap.mem_ker, LinearMap.prodMap_apply, Submodule.mkQ_apply,
      Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
    exact ⟨hx, hy⟩
  have h2 : A ≤ (A.prod B).comap (LinearMap.inl R V W) := fun x hx => ⟨hx, B.zero_mem⟩
  have h3 : B ≤ (A.prod B).comap (LinearMap.inr R V W) := fun x hx => ⟨A.zero_mem, hx⟩
  refine LinearEquiv.ofLinear ((A.prod B).liftQ _ h1)
    (LinearMap.coprod (A.mapQ _ (LinearMap.inl R V W) h2) (B.mapQ _ (LinearMap.inr R V W) h3))
    ?_ ?_
  · apply LinearMap.ext
    rintro ⟨x, y⟩
    induction x using Submodule.Quotient.induction_on
    induction y using Submodule.Quotient.induction_on
    simp
  · apply LinearMap.ext
    intro z
    induction z using Submodule.Quotient.induction_on
    rename_i z
    obtain ⟨x, y⟩ := z
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.liftQ_apply,
      LinearMap.prodMap_apply, LinearMap.coprod_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.id_apply]
    rw [← Submodule.Quotient.mk_add]
    simp

lemma map_span_range {ι : Type*} (π : V →ₗ[R] W) (f : ι → V) :
    (Submodule.span R (Set.range f)).map π = Submodule.span R (Set.range (π ∘ f)) := by
  rw [Submodule.map_span, Set.range_comp]

end general

section ev

variable {R : Type*} [CommRing R]

/-- The basis vector `e_i` of `R^m = Fin m → R`, indexed by `i : ℕ` (zero if `i ≥ m`). -/
def ev {m : ℕ} (i : ℕ) : Fin m → R := fun j => if (j : ℕ) = i then 1 else 0

@[simp] lemma ev_apply {m : ℕ} (i : ℕ) (j : Fin m) :
    (ev i : Fin m → R) j = if (j : ℕ) = i then 1 else 0 := rfl

lemma ev_eq_zero {m : ℕ} {i : ℕ} (h : m ≤ i) : (ev i : Fin m → R) = 0 := by
  ext j; simp only [ev_apply, Pi.zero_apply]; rw [if_neg]; have := j.2; omega

lemma ev_eq_single {m : ℕ} (j : Fin m) : (ev j : Fin m → R) = Pi.single j 1 := by
  ext i; simp only [ev_apply, Pi.single_apply, Fin.ext_iff]

/-- A linear map out of `R^m` sends everything into `N` once it sends each `e_j` there. -/
lemma mem_of_forall_ev {V : Type*} [AddCommGroup V] [Module R V] {m : ℕ}
    (f : (Fin m → R) →ₗ[R] V) (N : Submodule R V) (h : ∀ j < m, f (ev j) ∈ N)
    (x : Fin m → R) : f x ∈ N := by
  have hx : x = ∑ j : Fin m, x j • (ev j : Fin m → R) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, ev_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; rw [if_neg]; intro h'; exact hb (Fin.ext h'.symm)
    · simp
  rw [hx, map_sum]
  exact Submodule.sum_mem _ (fun j _ => by rw [map_smul]; exact N.smul_mem _ (h j j.2))

/-- Two linear maps out of `R^m` agree once they agree on each `e_j`. -/
lemma ext_ev {V : Type*} [AddCommGroup V] [Module R V] {m : ℕ}
    (f g : (Fin m → R) →ₗ[R] V) (h : ∀ j < m, f (ev j) = g (ev j)) : f = g := by
  apply LinearMap.pi_ext'
  intro j
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
  have := h j j.2
  rwa [ev_eq_single] at this

/-- The linear map `R^m → V` sending `e_j` to `f j`. -/
noncomputable def linOfFun {V : Type*} [AddCommGroup V] [Module R V] {m : ℕ}
    (f : ℕ → V) : (Fin m → R) →ₗ[R] V :=
  ∑ j : Fin m, (LinearMap.proj j : (Fin m → R) →ₗ[R] R).smulRight (f j)

lemma linOfFun_ev {V : Type*} [AddCommGroup V] [Module R V] {m : ℕ} (f : ℕ → V) {i : ℕ}
    (hi : i < m) : linOfFun (m := m) (R := R) f (ev i) = f i := by
  simp only [linOfFun, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.coe_proj, Function.eval, ev]
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp
  · intro b _ hb; rw [if_neg, zero_smul]; intro h; exact hb (Fin.ext h)
  · simp

lemma linOfFun_ev_of_le {V : Type*} [AddCommGroup V] [Module R V] {m : ℕ} (f : ℕ → V) {i : ℕ}
    (hi : m ≤ i) : linOfFun (m := m) (R := R) f (ev i) = 0 := by
  rw [ev_eq_zero hi, map_zero]

end ev

end ColouredSand.Blocks
