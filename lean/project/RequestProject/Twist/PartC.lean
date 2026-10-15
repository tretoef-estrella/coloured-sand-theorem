module

public import RequestProject.Twist.PartT

/-!
# `C21_reduction_mod_2_and_the_twist.md`: Part C, Proposition 3.1 (c)

Setting: `A` is a commutative ring with `[IsDomain A] [CharZero A] [Doubling.OddUnits A]` (C20),
`B` a commutative ring with `h2 : (2 : B) = 0`, and `φ : A →+* B` a ring homomorphism.
`Doubling.phi N` is `Φ(N)` (C20), `baseChange φ` is `(·)^φ`, `frob h2` is `(·)^{[1]}`.
-/

@[expose] public section

noncomputable section

namespace Twist

open DPLattice Finset WeylFilt Doubling Polynomial

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)

/-! ### Parity helpers -/

section parity

variable (h2 : (2 : B) = 0)

include h2 in
lemma natCast_of_odd {n : ℕ} (hn : Odd n) : (n : B) = 1 := by
  obtain ⟨k, rfl⟩ := hn; push_cast; rw [h2]; ring

include h2 in
lemma intCast_of_odd {n : ℤ} (hn : Odd n) : (n : B) = 1 := by
  obtain ⟨k, rfl⟩ := hn; push_cast; rw [h2]; ring

include h2 in
lemma natCast_two_mul (k : ℕ) : ((2 * k : ℕ) : B) = 0 := by
  push_cast; rw [h2, zero_mul]

lemma odd_doubleFactorial (s : ℕ) : Odd (Nat.doubleFactorial (2 * s - 1)) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rcases s with _ | s
    · simp
    · have : 2 * (s + 1 + 1) - 1 = (2 * s + 1) + 2 := by omega
      rw [this, Nat.doubleFactorial_add_two]
      have h2' : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
      rw [h2'] at ih
      exact (show Odd (2 * s + 1 + 2) from ⟨s + 1, by ring⟩).mul ih

end parity

/-! ### (C0) -/

section C0

variable {φ} (h2 : (2 : B) = 0)

include h2 in
lemma phi_dfi [OddUnits A] (s : ℕ) : φ (dfi s) = 1 := by
  have h := congrArg φ (dfi_mul (A := A) s)
  rw [map_mul, map_one, map_natCast, natCast_of_odd h2 (odd_doubleFactorial s), mul_one] at h
  exact h

lemma odd_cE (w : ℤ) (s j : ℕ) : Odd ((w + 2 * s + 1) ^ 2 - (w + 2 * j) ^ 2) :=
  ⟨2 * s ^ 2 - 2 * j ^ 2 + 2 * w * s - 2 * w * j + w + 2 * s, by ring⟩

lemma odd_cE' (w : ℤ) (s j : ℕ) : Odd ((w + 2 * s + 3) ^ 2 - (w + 2 * (j + 1)) ^ 2) :=
  ⟨2 * s ^ 2 + 2 * w * s + w + 6 * s + 2 - 2 * w * j - 2 * j ^ 2 - 4 * j, by ring⟩

lemma bc_aeval {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Module.End A (ι → A)) (p : A[X]) :
    bc φ (aeval T p) = aeval (bc φ T) (p.map φ) := by
  have hc : (bcRingHom (ι := ι) φ).comp (algebraMap A (Module.End A (ι → A))) =
      (algebraMap B (Module.End B (ι → B))).comp φ := by
    ext a : 1
    simp only [RingHom.comp_apply, bcRingHom_apply, Module.algebraMap_end_eq_smul_id, bc_smul,
      bc_id]
  rw [aeval_def, aeval_def, ← bcRingHom_apply, hom_eval₂, hc, eval₂_map]; rfl

include h2 in
/-- (C0) `(Doubling.piOp N S c)^φ = 1` whenever every `c j`, `j ∈ S`, is odd. -/
theorem bc_piOp (N : DPLattice A) (S : Finset ℕ) (c : ℕ → ℤ) (hc : ∀ j ∈ S, Odd (c j)) :
    bc φ (piOp N S c) = 1 := by
  rw [piOp, bc_aeval, Polynomial.map_prod]
  have h2' : (2 : B[X]) = 0 := by
    rw [← map_ofNat C 2, h2, C_0]
  have h4 : (4 : B[X]) = 0 := by
    rw [show (4 : B[X]) = 2 * 2 by norm_num, h2', zero_mul]
  rw [prod_congr rfl (g := fun _ => (1 : B[X])) fun j hj => ?_]
  · simp
  · simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_ofNat, map_X,
      map_intCast, h4, zero_mul, zero_add, Polynomial.map_intCast]
    rw [intCast_of_odd h2' (hc j hj)]

include h2 in
/-- (C0) The constants become `1` (or `0`) modulo 2:
`φ(⅟(2s−1)!!) = 1`; `φ(2s + 2) = 0`; `φ(2(s + 1)) = 0`; for every integer `w` the integers
`c_j = (w + 2s + 1)² − (w + 2j)²` and `(w + 2s + 3)² − (w + 2(j + 1))²` are odd (for every `j`,
more generally than the ranges `0 ≤ j ≤ s`, `0 ≤ j ≤ s − 1` of the file), so `φ(c_j) = 1`; and
`(piOp N S c)^φ = 1` whenever every `c j` (`j ∈ S`) is odd. -/
theorem C0 [OddUnits A] :
    (∀ s : ℕ, φ (dfi s) = 1) ∧
    (∀ s : ℕ, φ ((2 * s + 2 : ℕ) : A) = 0) ∧
    (∀ s : ℕ, φ ((2 * (s + 1) : ℕ) : A) = 0) ∧
    (∀ (w : ℤ) (s j : ℕ), Odd ((w + 2 * s + 1) ^ 2 - (w + 2 * j) ^ 2) ∧
      φ (((w + 2 * s + 1) ^ 2 - (w + 2 * j) ^ 2 : ℤ) : A) = 1) ∧
    (∀ (w : ℤ) (s j : ℕ), Odd ((w + 2 * s + 3) ^ 2 - (w + 2 * (j + 1)) ^ 2) ∧
      φ (((w + 2 * s + 3) ^ 2 - (w + 2 * (j + 1)) ^ 2 : ℤ) : A) = 1) ∧
    (∀ (N : DPLattice A) (S : Finset ℕ) (c : ℕ → ℤ), (∀ j ∈ S, Odd (c j)) →
      bc φ (piOp N S c) = 1) := by
  refine ⟨phi_dfi h2, fun s => ?_, fun s => ?_, fun w s j => ⟨odd_cE w s j, ?_⟩,
    fun w s j => ⟨odd_cE' w s j, ?_⟩, fun N S c hc => bc_piOp h2 N S c hc⟩
  · rw [map_natCast, show 2 * s + 2 = 2 * (s + 1) by ring, natCast_two_mul h2]
  · rw [map_natCast, natCast_two_mul h2]
  · rw [map_intCast, intCast_of_odd h2 (odd_cE w s j)]
  · rw [map_intCast, intCast_of_odd h2 (odd_cE' w s j)]

end C0

end Twist
