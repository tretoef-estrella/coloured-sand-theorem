module

public import Mathlib

/-!
# `CSI5_the_splitting.md`: Part H — algebraic tools (auxiliary)

Namespace `ColouredSand.OddTwist`. Three generic facts used in the finite proof of Part H
(steps 1–3 of "A finite proof (no limits)"):

* `exists_annihilating_poly`: **Cayley–Hamilton in the form used in step 1.** If `N`, `R` are
  endomorphisms of a finite free module `ι → A` with `N ∘ N = q • R`, then there are `k` and a
  polynomial `h` with `N^{2k} + q • h(N) = 0`, i.e. `N` is killed by a monic polynomial
  `≡ X^{2k} (mod q)`. (Proof: if `χ = X^k + Σ_{i<k} c_i X^i` is the characteristic polynomial of
  `R`, then `q^k χ(R) = N^{2k} + Σ_{i<k} c_i q^{k-i} N^{2i} = 0`.) This replaces the
  characteristic polynomial of `Ω` in the file by the one of `R`; the effect is the same (a monic
  polynomial killing `Ω_Q − b` and congruent to a power of `X` modulo `p`).
* `modP` / `isUnit_of_isUnit_modP`: **units are detected modulo `p`** (step 3). `modP p ι` is the
  ring morphism `End_{ℤ_p}(ι → ℤ_p) → Matrix ι ι (ZMod p)` (matrix in the standard basis, reduced
  modulo `p`); if the reduction of `x` is invertible, then `det x` is a unit of the local ring
  `ℤ_[p]`, so `x` is invertible.
* `intertwine_aeval`: if `f ∘ A = B ∘ f` then `f ∘ g(A) = g(B) ∘ f` for every polynomial `g`
  (steps 3–5: polynomials in `Ω` commute with every morphism and every `F^{(r)}`, `E^{(r)}`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Polynomial

/-- Part H, step 1 (Cayley–Hamilton): if `N ∘ N = q • R` on a finite free module, then
`N^{2k} + q • h(N) = 0` for some `k` and some polynomial `h`. -/
theorem exists_annihilating_poly {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι] (q : A)
    (N R : Module.End A (ι → A)) (hNR : N * N = q • R) :
    ∃ (k : ℕ) (h : A[X]), N ^ (2 * k) + q • aeval N h = 0 := by
  set c := LinearMap.charpoly R
  have hc : c.Monic := LinearMap.charpoly_monic R
  have hcR : aeval R c = 0 := LinearMap.aeval_self_charpoly R
  obtain ⟨k, hk⟩ : ∃ k, k = c.natDegree := ⟨_, rfl⟩
  have hsum : c = X ^ k + ∑ i ∈ Finset.range k, C (c.coeff i) * X ^ i := by
    rw [hk]; exact hc.as_sum
  refine ⟨k, ∑ i ∈ Finset.range k, C (c.coeff i * q ^ (k - 1 - i)) * X ^ (2 * i), ?_⟩
  have hpow : ∀ i, N ^ (2 * i) = q ^ i • R ^ i := by
    intro i; rw [pow_mul, sq, hNR, _root_.smul_pow]
  have key := congrArg (fun z => q ^ k • z) hcR
  simp only [smul_zero] at key
  rw [hsum] at key
  simp only [map_add, map_sum, map_mul, aeval_C, map_pow, aeval_X, smul_add,
    Finset.smul_sum] at key
  rw [← key]
  simp only [map_sum, map_mul, aeval_C, map_pow, aeval_X, Finset.smul_sum, hpow]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi := Finset.mem_range.mp hi
  simp only [Algebra.algebraMap_eq_smul_one, _root_.smul_pow, one_pow, smul_mul_assoc, one_mul,
    mul_smul_comm, mul_one, smul_smul]
  congr 1
  rw [show k = (k - 1 - i) + 1 + i by omega]
  simp only [pow_add, pow_one]
  rw [show k - 1 - i + 1 + i - 1 - i = k - 1 - i by omega]
  ring

/-- Part H, step 3 (auxiliary): reduction modulo `p`, `End_{ℤ_p}(ι → ℤ_p) → Matrix ι ι (ZMod p)`
(the matrix in the standard basis, with entries reduced modulo `p`). A ring morphism. -/
def modP (p : ℕ) [Fact p.Prime] (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Module.End ℤ_[p] (ι → ℤ_[p]) →+* Matrix ι ι (ZMod p) :=
  (PadicInt.toZMod (p := p)).mapMatrix.comp
    (LinearMap.toMatrixAlgEquiv' :
      Module.End ℤ_[p] (ι → ℤ_[p]) ≃ₐ[ℤ_[p]] Matrix ι ι ℤ_[p]).toRingEquiv.toRingHom

/-- Part H, step 3: an endomorphism of `ι → ℤ_[p]` whose reduction modulo `p` is invertible is
invertible (its determinant is a unit of the local ring `ℤ_[p]`). -/
theorem isUnit_of_isUnit_modP {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Module.End ℤ_[p] (ι → ℤ_[p])) (h : IsUnit (modP p ι x)) : IsUnit x := by
  rw [← MulEquiv.isUnit_map (LinearMap.toMatrixAlgEquiv' (R := ℤ_[p]) (n := ι)).toMulEquiv]
  change IsUnit (LinearMap.toMatrix' x)
  change IsUnit ((PadicInt.toZMod (p := p)).mapMatrix (LinearMap.toMatrix' x)) at h
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det] at h
  by_contra hd
  have hm : (LinearMap.toMatrix' x).det ∈ IsLocalRing.maximalIdeal ℤ_[p] := hd
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm
  rw [hm] at h
  exact not_isUnit_zero h

/-- Part H, step 3 (auxiliary): `p • x` reduces to `0` modulo `p`. -/
lemma modP_p_smul {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Module.End ℤ_[p] (ι → ℤ_[p])) : modP p ι ((p : ℤ_[p]) • x) = 0 := by
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, map_mul, map_natCast]
  rw [← Matrix.diagonal_natCast', show ((p : ι → ZMod p)) = 0 from funext fun _ => by simp]
  simp

/-- Part H, steps 3–5 (auxiliary): if `f ∘ A = B ∘ f` then `f ∘ g(A) = g(B) ∘ f` for every
polynomial `g`. -/
theorem intertwine_aeval {R X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (A : Module.End R X) (B : Module.End R Y)
    (h : f ∘ₗ A = B ∘ₗ f) (g : R[X]) : f ∘ₗ aeval A g = aeval B g ∘ₗ f := by
  induction g using Polynomial.induction_on' with
  | add g₁ g₂ h₁ h₂ => rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, h₁, h₂]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul,
      LinearMap.comp_smul, LinearMap.smul_comp,
      (Module.End.commute_pow_left_of_commute h.symm n).symm]

end ColouredSand.OddTwist
