module

public import Mathlib

/-!
# `C17_the_laplacian_in_the_group_ring.md`: Setting

Encodings (namespace `CubeLaplacian`), all for a fixed `n : ℕ`:

* `G n := Fin n → ZMod 2` (the group `(ℤ/2)^n`, written additively), with generators
  `e n i := Pi.single i 1`.
* `R n := AddMonoidAlgebra ℤ (G n)` (the group ring `ℤ[G]`; `single g 1 * single h 1 = single (g+h) 1`).
  As a type, `AddMonoidAlgebra ℤ (G n)` is `G n →₀ ℤ`; the identification `R = ℤ^G` of the file is
  `toFun n : R n ≃ₗ[ℤ] (G n → ℤ)`, `f ↦ (g ↦ f g)` (Mathlib's `Finsupp.linearEquivFunOnFinite`).
* `x n i := single (e n i) 1`, `s n i := 1 - x n i`, `sS n S := ∏ i ∈ S, s n i` for
  `S : Finset (Fin n)` (so `sS n ∅ = 1`), `sigma n := ∑ i, s n i`.
* `mulSigma n : R n →ₗ[ℤ] R n` is left multiplication `f ↦ σ * f` (`σ · −`).
* `lap A n : (G n → A) →ₗ[A] (G n → A)` is the Laplacian of `Q_n` with coefficients in a commutative
  ring `A`: `(lap A n f) g = n * f g - ∑ i, f (g + e n i)`. The Laplacian `L` of the file is
  `L n := lap ℤ n`, and `σ_A` of Part D is `lap ℤ_[2] n`.
* `coker n := (G n → ℤ) ⧸ LinearMap.range (L n)`, and the sandpile group is
  `K n := Submodule.torsion ℤ (coker n)` (Mathlib's torsion submodule).
* For an additive commutative group `T`, `Syl2 T` is the subgroup `{x | ∃ e : ℕ, 2 ^ e • x = 0}`.
* `Rplus n := Submodule.span ℤ {sS n S | S ≠ ∅}` (`R_+`), and
  `T n := Rplus n ⧸ (LinearMap.range (mulSigma n)).comap (Rplus n).subtype`
  (`R_+ ⧸ range (σ · −)`; note `range (σ · −) ⊆ R_+` by (C1)).
-/

@[expose] public section

noncomputable section

namespace CubeLaplacian

open Finset

/-- Setting: the group `G = (ℤ/2)^n`. -/
abbrev G (n : ℕ) := Fin n → ZMod 2

/-- Setting: the generator `e_i = Pi.single i 1` of `G`. -/
def e (n : ℕ) (i : Fin n) : G n := Pi.single i 1

/-- Setting: the group ring `R = ℤ[G]`, encoded as `AddMonoidAlgebra ℤ G`. -/
abbrev R (n : ℕ) := AddMonoidAlgebra ℤ (G n)

/-- Setting: `x_i := x_{e_i}`, the basis element of `R` attached to the generator `e_i`. -/
def x (n : ℕ) (i : Fin n) : R n := AddMonoidAlgebra.single (e n i) 1

/-- Setting: `s_i := 1 - x_i`. -/
def s (n : ℕ) (i : Fin n) : R n := 1 - x n i

/-- Setting: `s_S := ∏_{i ∈ S} s_i` (so `s_∅ = 1`). -/
def sS (n : ℕ) (S : Finset (Fin n)) : R n := ∏ i ∈ S, s n i

/-- Setting: `σ := Σ_{i<n} (1 - x_i) = Σ_i s_i`. -/
def sigma (n : ℕ) : R n := ∑ i, s n i

/-- Setting: left multiplication by `σ` on `R`, `σ · −`, as a `ℤ`-linear map. -/
def mulSigma (n : ℕ) : R n →ₗ[ℤ] R n := LinearMap.mulLeft ℤ (sigma n)

/-- Setting (and Part D): the Laplacian of the cube `Q_n` with coefficients in a commutative ring
`A`, `(L f)(g) = n · f(g) − Σ_{i<n} f(g + e_i)`. -/
def lap (A : Type*) [CommRing A] (n : ℕ) : (G n → A) →ₗ[A] (G n → A) where
  toFun f g := (n : A) * f g - ∑ i, f (g + e n i)
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

/-- Setting: the Laplacian `L` of `Q_n` on `ℤ^G = (G → ℤ)`. -/
abbrev L (n : ℕ) : (G n → ℤ) →ₗ[ℤ] (G n → ℤ) := lap ℤ n

lemma lap_apply (A : Type*) [CommRing A] (n : ℕ) (f : G n → A) (g : G n) :
    lap A n f g = (n : A) * f g - ∑ i, f (g + e n i) := rfl

/-- Setting: the cokernel `(G → ℤ) ⧸ range L`. -/
abbrev coker (n : ℕ) := (G n → ℤ) ⧸ LinearMap.range (L n)

/-- Setting: the sandpile group `K(Q_n)`, the torsion of the `ℤ`-module `(G → ℤ) ⧸ range L`. -/
abbrev K (n : ℕ) := Submodule.torsion ℤ (coker n)

/-- Setting (and Part D): the `2`-part `Syl_2 T := {x : 2^e • x = 0 for some e}` of an abelian
group `T`, as an additive subgroup. -/
def Syl2 (T : Type*) [AddCommGroup T] : AddSubgroup T where
  carrier := {y | ∃ k : ℕ, (2 ^ k : ℕ) • y = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    show (2 ^ (k + l) : ℕ) • (a + b) = 0
    have h1 : (2 ^ (k + l) : ℕ) • a = 0 := by
      rw [pow_add, mul_nsmul, hk, nsmul_zero]
    have h2 : (2 ^ (k + l) : ℕ) • b = 0 := by
      rw [pow_add, mul_comm, mul_nsmul, hl, nsmul_zero]
    rw [smul_add, h1, h2, add_zero]
  neg_mem' := by
    rintro a ⟨k, hk⟩
    exact ⟨k, by rw [smul_neg, hk, neg_zero]⟩

/-- Setting: the identification `R = ℤ^G`, `f ↦ (g ↦ f(g))`. -/
def toFun (n : ℕ) : R n ≃ₗ[ℤ] (G n → ℤ) := Finsupp.linearEquivFunOnFinite ℤ ℤ (G n)

@[simp] lemma toFun_apply (n : ℕ) (f : R n) (g : G n) : toFun n f g = f g := rfl

/-- Part C: the augmentation ideal `R_+ := span_ℤ {s_S : S ≠ ∅}`. -/
def Rplus (n : ℕ) : Submodule ℤ (R n) := Submodule.span ℤ (sS n '' {S | S ≠ ∅})

/-- Part C: `T(n) := R_+ ⧸ range (σ · −)` (the range, contained in `R_+`, pulled back to `R_+`). -/
abbrev T (n : ℕ) := Rplus n ⧸ (LinearMap.range (mulSigma n)).comap (Rplus n).subtype

end CubeLaplacian
