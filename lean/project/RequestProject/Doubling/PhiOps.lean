module

public import RequestProject.Doubling.Phi

/-!
# `C20_the_doubling_functor.md`: computations with the closed formulas (Parts A, B)

Auxiliary computations: the closed formulas on arbitrary vectors (for `F`) and on weight vectors
(for `E`), the operators `Π_{c}`, and the commutation of `E` with polynomials in `FE` on `N`
(proof sketch of (A1)).
-/

@[expose] public section

noncomputable section

namespace Doubling

open DPLattice Finset Polynomial

variable {A : Type*} [CommRing A] (N : DPLattice A)

/-! ### The closed formulas as linear maps -/

lemma phiFd_comp_bvec (r : ℕ) (e : Fin 2) : phiFd N r ∘ₗ bvec e = phiFdL N r e := by
  refine ext_single fun i => ?_
  rw [LinearMap.comp_apply, ← single_eq_bvec, phiFd_single]; rfl

lemma phiFd_bvec (r : ℕ) (e : Fin 2) (n : N.ι → A) : phiFd N r (bvec e n) = phiFdL N r e n :=
  LinearMap.congr_fun (phiFd_comp_bvec N r e) n

lemma phiEd_bvec_of_inWt (r : ℕ) (e : Fin 2) {w : ℤ} {x : N.ι → A} (hx : InWt N.wt w x) :
    phiEd N r (bvec e x) = phiEdL N r e w x :=
  eq_on_inWt (phiEd N r ∘ₗ bvec e) (phiEdL N r e w)
    (fun i hi => by rw [LinearMap.comp_apply, ← single_eq_bvec, phiEd_single, phiEdB, hi]) hx

lemma phiFdL_even (s : ℕ) (e : Fin 2) (n : N.ι → A) :
    phiFdL N (2 * s) e n = dfi (A := A) s • bvec e (N.Fd s n) := by
  rw [phiFdL, if_pos (two_mul_mod s), two_mul_div]; rfl

lemma phiFdL_odd0 (s : ℕ) (n : N.ι → A) :
    phiFdL N (2 * s + 1) 0 n = dfi (A := A) (s + 1) • bvec 1 (N.Fd s n) := by
  rw [phiFdL, two_mul_add_one_mod, two_mul_add_one_div]; rfl

lemma phiFdL_odd1 (s : ℕ) (n : N.ι → A) :
    phiFdL N (2 * s + 1) 1 n =
      (((2 * s + 2 : ℕ) : A) * dfi (s + 1)) • bvec 0 (N.Fd (s + 1) n) := by
  rw [phiFdL, two_mul_add_one_mod, two_mul_add_one_div]; rfl

lemma phiEdL_even1 (s : ℕ) (w : ℤ) (n : N.ι → A) :
    phiEdL N (2 * s) 1 w n = dfi (A := A) s • bvec 1 (piOp N (range s) (cE w s) (N.Ed s n)) := by
  rw [phiEdL, if_pos (two_mul_mod s), two_mul_div]; rfl

lemma phiEdL_even0 (s : ℕ) (w : ℤ) (n : N.ι → A) :
    phiEdL N (2 * s) 0 w n = dfi (A := A) s • bvec 0 (piOp N (Icc 1 s) (cE w s) (N.Ed s n)) := by
  rw [phiEdL, if_pos (two_mul_mod s), two_mul_div, if_neg (show ((0 : Fin 2) ≠ 1) by decide)]
  rfl

lemma phiEdL_odd1 (s : ℕ) (w : ℤ) (n : N.ι → A) :
    phiEdL N (2 * s + 1) 1 w n =
      dfi (A := A) (s + 1) • bvec 0 (piOp N (range (s + 1)) (cE w s) (N.Ed s n)) := by
  rw [phiEdL, two_mul_add_one_mod, two_mul_add_one_div]; rfl

lemma phiEdL_odd0 (s : ℕ) (w : ℤ) (n : N.ι → A) :
    phiEdL N (2 * s + 1) 0 w n = (((2 * (s + 1) : ℕ) : A) * dfi (s + 1)) •
      bvec 1 (piOp N (Icc 1 s) (cE w (s + 1)) (N.Ed (s + 1) n)) := by
  rw [phiEdL, two_mul_add_one_mod, two_mul_add_one_div,
    if_neg (show ((0 : Fin 2) ≠ 1) by decide)]; rfl

@[simp] lemma dfi_one : dfi (A := A) 1 = 1 := by simp [dfi]

/-! ### The operators `Π_c` -/

lemma piOp_empty (c : ℕ → ℤ) : piOp N ∅ c = 1 := by simp [piOp]

lemma piOp_apply_aeval (S : Finset ℕ) (c : ℕ → ℤ) (q : A[X]) (x : N.ι → A) :
    aeval (N.Fd 1 * N.Ed 1) q (piOp N S c x) =
      aeval (N.Fd 1 * N.Ed 1) (q * ∏ j ∈ S, (4 * X + C ((c j : ℤ) : A))) x := by
  rw [map_mul, Module.End.mul_apply]; rfl

lemma aeval_lin_apply (a : A) (x : N.ι → A) :
    aeval (N.Fd 1 * N.Ed 1) (4 * X + C a) x = (4 : A) • N.Fd 1 (N.Ed 1 x) + a • x := by
  rw [map_add, map_mul, aeval_X, aeval_C, map_ofNat, LinearMap.add_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, Module.End.mul_apply]
  congr 1
  rw [← Nat.cast_ofNat, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul A]
  rfl

lemma aeval_piOp_range (s : ℕ) (c : ℕ → ℤ) (a : ℤ) (ha : a = c s) (x : N.ι → A) :
    aeval (N.Fd 1 * N.Ed 1) (4 * X + C ((a : ℤ) : A)) (piOp N (range s) c x) =
      piOp N (range (s + 1)) c x := by
  rw [piOp_apply_aeval, piOp, prod_range_succ, mul_comm, ha]

lemma aeval_piOp_Icc (s : ℕ) (c : ℕ → ℤ) (a : ℤ) (ha : a = c (s + 1)) (x : N.ι → A) :
    aeval (N.Fd 1 * N.Ed 1) (4 * X + C ((a : ℤ) : A)) (piOp N (Icc 1 s) c x) =
      piOp N (Icc 1 (s + 1)) c x := by
  rw [piOp_apply_aeval, piOp, prod_Icc_succ_top (by omega), mul_comm, ha]

/-! ### Weights on `N` -/

lemma inWt_FE {μ : ℤ} {x : N.ι → A} (hx : InWt N.wt μ x) :
    InWt N.wt μ ((N.Fd 1 * N.Ed 1) x) := by
  have := N.isDP.inWt_Fd 1 (N.isDP.inWt_Ed 1 hx)
  rw [Module.End.mul_apply]
  exact inWt_congr (by ring) this

lemma inWt_aeval (p : A[X]) {μ : ℤ} {x : N.ι → A} (hx : InWt N.wt μ x) :
    InWt N.wt μ (aeval (N.Fd 1 * N.Ed 1) p x) := by
  induction p using Polynomial.induction_on generalizing x with
  | C a => simpa using inWt_smul a hx
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact inWt_add (hp hx) (hq hx)
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact ih (inWt_FE N hx)

lemma inWt_piOp (S : Finset ℕ) (c : ℕ → ℤ) {μ : ℤ} {x : N.ι → A} (hx : InWt N.wt μ x) :
    InWt N.wt μ (piOp N S c x) := inWt_aeval N _ hx

/-! ### `[E, F] = H` on `N` and `E · f(FE) = f(FE + μ + 2) · E` -/

/-- The Lie relation `EF = FE + H` on a DP-lattice (from (K) with `r = s = 1`). -/
lemma dp_lie (x : N.ι → A) : N.Ed 1 (N.Fd 1 x) = N.Fd 1 (N.Ed 1 x) + H N x := by
  have : N.Ed 1 ∘ₗ N.Fd 1 = N.Fd 1 ∘ₗ N.Ed 1 + H N := by
    refine ext_single fun i => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [N.isDP.K i 1 1, Hop_of_inWt (inWt_single _ i)]
    simp [Finset.sum_range_succ, N.isDP.P0_F, N.isDP.P0_E]
  exact LinearMap.congr_fun this x

lemma Ed_FE {μ : ℤ} {z : N.ι → A} (hz : InWt N.wt μ z) :
    N.Ed 1 ((N.Fd 1 * N.Ed 1) z) =
      (N.Fd 1 * N.Ed 1 + algebraMap A _ ((μ + 2 : ℤ) : A)) (N.Ed 1 z) := by
  rw [Module.End.mul_apply, dp_lie, Hop_of_inWt (N.isDP.inWt_Ed 1 hz), LinearMap.add_apply,
    Module.End.mul_apply, Module.algebraMap_end_apply]
  congr 2

lemma Ed_aeval (p : A[X]) {μ : ℤ} {y : N.ι → A} (hy : InWt N.wt μ y) :
    N.Ed 1 (aeval (N.Fd 1 * N.Ed 1) p y) =
      aeval (N.Fd 1 * N.Ed 1 + algebraMap A _ ((μ + 2 : ℤ) : A)) p (N.Ed 1 y) := by
  induction p using Polynomial.induction_on generalizing y with
  | C a => simp
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp hy, hq hy]
  | monomial n a ih =>
    have e2 : ∀ T : Module.End A (N.ι → A), aeval T (C a * X ^ (n + 1)) =
        aeval T (C a * X ^ n) * T := fun T => by rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    rw [e2, e2, Module.End.mul_apply, ih (inWt_FE N hy), Ed_FE N hy, Module.End.mul_apply]

/-- `E Π_{c}(y) = Π_{c'}(E y)` with `c'_j = 4(μ+2) + c_j`, for `y` of weight `μ`. -/
lemma Ed_piOp (S : Finset ℕ) (c : ℕ → ℤ) {μ : ℤ} {y : N.ι → A} (hy : InWt N.wt μ y) :
    N.Ed 1 (piOp N S c y) = piOp N S (fun j => 4 * (μ + 2) + c j) (N.Ed 1 y) := by
  rw [piOp, Ed_aeval N _ hy]
  have h : (N.Fd 1 * N.Ed 1 + algebraMap A _ ((μ + 2 : ℤ) : A)) =
      aeval (N.Fd 1 * N.Ed 1) (X + C ((μ + 2 : ℤ) : A)) := by simp
  rw [h, ← aeval_comp, Polynomial.prod_comp, piOp]
  congr 2
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [add_comp, mul_comp, X_comp, C_comp, ofNat_comp]
  push_cast
  simp only [C_add, C_mul, C_ofNat]
  ring

/-! ### Weights on `Φ(N)` -/

lemma inWt_bvec (e : Fin 2) {μ : ℤ} {x : N.ι → A} (hx : InWt N.wt μ x) :
    InWt (phiWt N) (2 * μ + wtV e) (bvec e x) := by
  intro ⟨e', j⟩ hj
  simp only [bvec_apply]
  split_ifs with he
  · subst he
    refine hx j fun h => hj ?_
    simp [phiWt, h]
  · rfl

end Doubling
