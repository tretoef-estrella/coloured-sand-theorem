module

public import RequestProject.Strings.StringCoker

/-!
# Theorem A: objects and general cokernel lemmas

This file corresponds to **§0 (Objects)** of `CS2_theorem_A_splitting.md`; it also contains
two general facts about cokernels used in the proof of **(A2)** and **(A3)**.

## Encoding

* The Hamming graph `H(d,q)` is `hammingGraph d q : SimpleGraph (Fin d → Fin q)`; two vertices
  are adjacent iff `hammingDist x y = 1`, i.e. they differ in exactly one coordinate.
* Its Laplacian `L` is the `ℤ`-linear map `f ↦ (lapMatrix ℤ) *ᵥ f` on `(Fin d → Fin q) → ℤ`,
  where `lapMatrix = degMatrix − adjMatrix` is Mathlib's Laplacian matrix; so
  `(L f)(x) = deg(x) f(x) − ∑_{y ∼ x} f(y)` (`laplacian_apply`).
* `B_m`, `H`, `U` are those of `RequestProject/Strings/Basic.lean` (with `R = ℤ`), and
  `M_q(m,c) = q (c + H) + U` is `opM m ℤ q c` of `RequestProject/Strings/StringCoker.lean`,
  i.e. `(q : ℤ) • ((c : ℤ) • id + H) + U`.
* A cokernel `coker f` is the quotient `N ⧸ LinearMap.range f`; so
  `X_q(m,c) = B_m ⧸ range M_q(m,c)` is `Xq q m c`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Splitting

open ColouredSand.Strings

/-! ### General cokernel lemmas -/

section general

variable {R : Type*} [CommRing R]

/-- Cokernels of conjugate maps are isomorphic: if `f' ∘ e₁ = e₂ ∘ f` with `e₁, e₂` linear
equivalences, then `coker f ≅ coker f'`. -/
noncomputable def cokerEquivOfConj {M N M' N' : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M'] [AddCommGroup N']
    [Module R N'] (f : M →ₗ[R] N) (f' : M' →ₗ[R] N') (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (h : ∀ x, f' (e₁ x) = e₂ (f x)) :
    (N ⧸ LinearMap.range f) ≃ₗ[R] (N' ⧸ LinearMap.range f') :=
  Submodule.Quotient.equiv _ _ e₂ (by
    have hc : f' ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f := LinearMap.ext h
    calc (LinearMap.range f).map (e₂ : N →ₗ[R] N')
        = LinearMap.range (e₂.toLinearMap ∘ₗ f) := (LinearMap.range_comp f _).symm
      _ = LinearMap.range (f' ∘ₗ e₁.toLinearMap) := by rw [hc]
      _ = LinearMap.range f' := LinearMap.range_comp_of_range_eq_top _ e₁.range)

/-- The range of a "diagonal" map `∏ Nₖ` on a product is the product of the ranges. -/
lemma range_pi_comp_proj {K : Type*} {M N : K → Type*} [∀ k, AddCommGroup (M k)]
    [∀ k, Module R (M k)] [∀ k, AddCommGroup (N k)] [∀ k, Module R (N k)]
    (F : ∀ k, M k →ₗ[R] N k) :
    LinearMap.range (LinearMap.pi (fun k => F k ∘ₗ LinearMap.proj k)) =
      Submodule.pi Set.univ (fun k => LinearMap.range (F k)) := by
  ext y
  simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨x, rfl⟩ k
    exact ⟨x k, rfl⟩
  · intro hy
    choose x hx using hy
    exact ⟨x, funext fun k => by simpa using hx k⟩

/-- **Block decomposition of a cokernel.**  Let `e : (Σ k, κ k) ≃ ι` and let `N` be an
endomorphism of `ι → R` which is block diagonal along `e`, with blocks `Nₖ`
(hypothesis `h`).  Then `coker N ≅ ∏ₖ coker Nₖ`. -/
noncomputable def cokerEquivPi {ι K : Type*} [Fintype K] [DecidableEq K] {κ : K → Type*}
    (e : (Σ k, κ k) ≃ ι) (N : (ι → R) →ₗ[R] (ι → R)) (Nk : ∀ k, (κ k → R) →ₗ[R] (κ k → R))
    (h : ∀ f k s, N f (e ⟨k, s⟩) = Nk k (fun s' => f (e ⟨k, s'⟩)) s) :
    ((ι → R) ⧸ LinearMap.range N) ≃ₗ[R] ∀ k, ((κ k → R) ⧸ LinearMap.range (Nk k)) :=
  let Φ : (ι → R) ≃ₗ[R] ∀ k, κ k → R :=
    (LinearEquiv.funCongrLeft R R e).trans (LinearEquiv.piCurry R (fun _ _ => R))
  (cokerEquivOfConj N (LinearMap.pi (fun k => Nk k ∘ₗ LinearMap.proj k)) Φ Φ (by
    intro f
    funext k s
    exact (h f k s).symm)).trans
  ((Submodule.quotEquivOfEq _ _ (range_pi_comp_proj Nk)).trans
    (Submodule.quotientPi _))

end general

/-! ### The Hamming graph and its Laplacian -/

/-- The Hamming graph `H(d,q)` (§0): vertex set `Fin d → Fin q`, two vertices adjacent iff they
differ in exactly one coordinate (`hammingDist x y = 1`). -/
def hammingGraph (d q : ℕ) : SimpleGraph (Fin d → Fin q) where
  Adj x y := hammingDist x y = 1
  symm x y h := by
    change hammingDist y x = 1
    rwa [hammingDist_comm]
  loopless := ⟨fun x h => by simp at h⟩

instance (d q : ℕ) : DecidableRel (hammingGraph d q).Adj :=
  fun x y => decEq (hammingDist x y) 1

/-- The Laplacian `L` of `H(d,q)` (§0), acting on `(Fin d → Fin q) → ℤ` by the Laplacian matrix
`lapMatrix = degMatrix − adjMatrix`. -/
noncomputable def laplacian (d q : ℕ) :
    ((Fin d → Fin q) → ℤ) →ₗ[ℤ] ((Fin d → Fin q) → ℤ) :=
  ((hammingGraph d q).lapMatrix ℤ).mulVecLin

/-- `(L f)(x) = deg(x) f(x) − ∑_{y ∼ x} f(y)`. -/
lemma laplacian_apply (d q : ℕ) (f : (Fin d → Fin q) → ℤ) (x : Fin d → Fin q) :
    laplacian d q f x =
      (hammingGraph d q).degree x * f x - ∑ y ∈ (hammingGraph d q).neighborFinset x, f y :=
  SimpleGraph.lapMatrix_mulVec_apply _ _ _

/-! ### The pieces `X_q(m,c)` -/

/-- `M_q(m,c) = q (c + H) + U` on `B_m = Finset (Fin m) → ℤ` (§0). -/
noncomputable abbrev Mq (q m c : ℕ) : B m ℤ →ₗ[ℤ] B m ℤ := opM m ℤ (q : ℤ) (c : ℤ)

/-- `X_q(m,c) = coker M_q(m,c) = B_m ⧸ range M_q(m,c)` (§0). -/
abbrev Xq (q m c : ℕ) : Type := B m ℤ ⧸ LinearMap.range (Mq q m c)

lemma Mq_apply (q m c : ℕ) (f : B m ℤ) (S : Finset (Fin m)) :
    Mq q m c f S = q * (c + S.card) * f S + ∑ x ∈ S, f (S.erase x) := by
  simp [opM]
  ring

end ColouredSand.Splitting
