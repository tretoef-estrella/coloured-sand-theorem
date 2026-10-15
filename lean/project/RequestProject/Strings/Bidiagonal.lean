module

public import Mathlib

/-!
# The bidiagonal lemma (S4)

This file corresponds to **(S4) Bidiagonal lemma** of `CS1_strings_and_theorem_E.md`.

## Encoding

* `R^n` is `Fin n → R`; the matrix `M : Matrix (Fin n) (Fin n) R` acts on column vectors via
  `Matrix.mulVecLin M` (`x ↦ M *ᵥ x`).
* "Lower bidiagonal with diagonal `d_0, …, d_{n−1}` and unit subdiagonal" is:
  `M i i = d i`, `M i j` a unit when `i = j + 1`, and `M i j = 0` otherwise.
* The cokernel of `M` is the quotient `(Fin n → R) ⧸ LinearMap.range (Matrix.mulVecLin M)`, and
  "`≅`" is the existence of an `R`-linear equivalence.
-/

@[expose] public section

open Finset Matrix

namespace ColouredSand.Strings

namespace Bidiagonal

variable {R : Type*} [CommRing R] {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) R)

/-- The diagonal of `M`, indexed by `ℕ`. -/
def dg (j : ℕ) : R := if h : j < N + 1 then M ⟨j, h⟩ ⟨j, h⟩ else 0

/-- The subdiagonal of `M`, indexed by `ℕ` (`1` outside the matrix). -/
def sd (j : ℕ) : R := if h : j + 1 < N + 1 then M ⟨j + 1, h⟩ ⟨j, by omega⟩ else 1

/-- The coefficients `c_j` with `[e_j] = c_j [e_0]` in the cokernel. -/
noncomputable def cf : ℕ → R
  | 0 => 1
  | j + 1 => -(dg M j) * Ring.inverse (sd M j) * cf j

variable {M}

lemma isUnit_sd (hsub : ∀ i j : Fin (N + 1), (i : ℕ) = j + 1 → IsUnit (M i j)) (j : ℕ) :
    IsUnit (sd M j) := by
  unfold sd
  split_ifs with h
  · exact hsub _ _ rfl
  · exact isUnit_one

lemma cf_mul_eq (hsub : ∀ i j : Fin (N + 1), (i : ℕ) = j + 1 → IsUnit (M i j)) (j : ℕ) :
    cf M j * ((-1) ^ j * ∏ i ∈ range j, sd M i) = ∏ i ∈ range j, dg M i := by
  induction j with
  | zero => simp [cf]
  | succ j ih =>
    rw [cf, prod_range_succ, prod_range_succ, ← ih]
    have := Ring.inverse_mul_cancel _ (isUnit_sd hsub j)
    linear_combination (cf M j * (-1) ^ j * (∏ i ∈ range j, sd M i) * dg M j) * this

lemma column_eq (hsub : ∀ i j : Fin (N + 1), (i : ℕ) = j + 1 → IsUnit (M i j))
    (hzero : ∀ i j : Fin (N + 1), i ≠ j → (i : ℕ) ≠ j + 1 → M i j = 0) (j : Fin (N + 1)) :
    ∑ i : Fin (N + 1), cf M i * M i j = if (j : ℕ) = N then cf M N * dg M N else 0 := by
  have hM : ∀ i, M i j = (if i = j then M j j else 0) + (if (i : ℕ) = j + 1 then M i j else 0) := by
    intro i
    by_cases h1 : i = j
    · subst h1; rw [if_pos rfl, if_neg (by omega), add_zero]
    · by_cases h2 : (i : ℕ) = j + 1
      · rw [if_neg h1, if_pos h2, zero_add]
      · rw [if_neg h1, if_neg h2, add_zero, hzero i j h1 h2]
  rw [sum_congr rfl (fun (i : Fin (N + 1)) _ => congrArg (cf M i * ·) (hM i))]
  simp_rw [mul_add, sum_add_distrib, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  by_cases hj : (j : ℕ) = N
  · rw [if_pos hj, sum_eq_zero, add_zero]
    · obtain rfl : j = ⟨N, Nat.lt_succ_self N⟩ := Fin.ext hj
      rw [dg, dif_pos (by omega)]
    · intro i _
      rw [if_neg]
      have := i.2
      omega
  · rw [if_neg hj, sum_eq_single ⟨j + 1, by omega⟩]
    · simp only [if_true]
      have hs : sd M j = M ⟨j + 1, by omega⟩ j := by rw [sd, dif_pos (by omega)]
      have hd : dg M j = M j j := by rw [dg, dif_pos j.2]
      rw [cf, ← hs, ← hd]
      have := Ring.inverse_mul_cancel _ (isUnit_sd hsub j)
      linear_combination (-(dg M j * cf M j)) * this
    · intro i _ hi
      rw [if_neg]
      intro h; exact hi (Fin.ext h)
    · intro h; exact absurd (mem_univ _) h

variable (M) in
/-- The linear form `x ↦ ∑_j c_j x_j`. -/
noncomputable def phi : (Fin (N + 1) → R) →ₗ[R] R where
  toFun x := ∑ j : Fin (N + 1), cf M (j : ℕ) * x j
  map_add' x y := by simp [mul_add, sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    exact sum_congr rfl (fun _ _ => by ring)

lemma phi_apply (x : Fin (N + 1) → R) : phi M x = ∑ j : Fin (N + 1), cf M (j : ℕ) * x j := rfl

lemma phi_mulVec (hsub : ∀ i j : Fin (N + 1), (i : ℕ) = j + 1 → IsUnit (M i j))
    (hzero : ∀ i j : Fin (N + 1), i ≠ j → (i : ℕ) ≠ j + 1 → M i j = 0) (x : Fin (N + 1) → R) :
    phi M (M *ᵥ x) = cf M N * dg M N * x (Fin.last N) := by
  simp only [phi_apply, Matrix.mulVec, dotProduct, mul_sum]
  rw [sum_comm]
  simp_rw [← mul_assoc, ← sum_mul, column_eq hsub hzero]
  rw [sum_eq_single (Fin.last N)]
  · simp
  · intro j _ hj
    rw [if_neg, zero_mul]
    intro h; exact hj (Fin.ext (by simpa using h))
  · intro h; exact absurd (mem_univ _) h

lemma prod_diag_eq : ∏ i, M i i = ∏ i ∈ range (N + 1), dg M i := by
  rw [← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl (fun i _ => ?_)
  rw [dg, dif_pos i.2]

lemma mulVec_single_eq (hzero : ∀ i j : Fin (N + 1), i ≠ j → (i : ℕ) ≠ j + 1 → M i j = 0)
    (j : Fin (N + 1)) : M *ᵥ (Pi.single j 1 : Fin (N + 1) → R) =
      dg M j • (Pi.single j 1 : Fin (N + 1) → R) + (if h : (j : ℕ) + 1 < N + 1 then
        sd M j • (Pi.single (⟨j + 1, h⟩ : Fin (N + 1)) 1 : Fin (N + 1) → R) else 0) := by
  ext i
  rw [Matrix.mulVec_single_one, Pi.add_apply, Pi.smul_apply]
  change M i j = _
  by_cases h1 : i = j
  · subst h1
    have : dg M i = M i i := by rw [dg, dif_pos i.2]
    rw [this, Pi.single_eq_same, smul_eq_mul, mul_one]
    split_ifs with h
    · rw [Pi.smul_apply, Pi.single_eq_of_ne, smul_zero, add_zero]
      intro h'; have := congrArg Fin.val h'; simp at this
    · simp
  · by_cases h2 : (i : ℕ) = j + 1
    · have h3 : (j : ℕ) + 1 < N + 1 := by have := i.2; omega
      rw [dif_pos h3]
      have : i = ⟨j + 1, h3⟩ := Fin.ext h2
      subst this
      have hs : sd M j = M ⟨j + 1, h3⟩ j := by rw [sd, dif_pos h3]
      rw [Pi.single_eq_of_ne h1, smul_zero, zero_add, Pi.smul_apply, Pi.single_eq_same, hs,
        smul_eq_mul, mul_one]
    · rw [hzero i j h1 h2, Pi.single_eq_of_ne h1, smul_zero, zero_add]
      split_ifs with h
      · have : i ≠ ⟨j + 1, h⟩ := fun h' => h2 (by rw [h'])
        rw [Pi.smul_apply, Pi.single_eq_of_ne this, smul_zero]
      · rfl

theorem coker_equiv_aux (hsub : ∀ i j : Fin (N + 1), (i : ℕ) = j + 1 → IsUnit (M i j))
    (hzero : ∀ i j : Fin (N + 1), i ≠ j → (i : ℕ) ≠ j + 1 → M i j = 0) :
    Nonempty (((Fin (N + 1) → R) ⧸ LinearMap.range (Matrix.mulVecLin M)) ≃ₗ[R]
      (R ⧸ Ideal.span {∏ i, M i i})) := by
  set I : Ideal R := Ideal.span {∏ i, M i i}
  set Q := LinearMap.range (Matrix.mulVecLin M)
  set w : R := (-1) ^ N * ∏ i ∈ range N, sd M i
  have hw : IsUnit w := by
    refine ((isUnit_neg_one (α := R)).pow N).mul ?_
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => isUnit_sd hsub i)
  have hprod : cf M N * dg M N * w = ∏ i, M i i := by
    rw [prod_diag_eq, prod_range_succ, ← cf_mul_eq hsub N]
    ring
  -- the forward map
  have hφ : Q ≤ LinearMap.ker (I.mkQ ∘ₗ phi M) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Matrix.mulVecLin_apply, phi_mulVec hsub hzero]
    refine Ideal.mul_mem_right _ _ ?_
    have : cf M N * dg M N = ((hw.unit⁻¹ : Rˣ) : R) * ∏ i, M i i := by
      rw [← hprod, mul_comm _ (cf M N * dg M N * w), mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  let F : ((Fin (N + 1) → R) ⧸ Q) →ₗ[R] R ⧸ I := Q.liftQ _ hφ
  have hcol := mulVec_single_eq hzero
  let e0 : (Fin (N + 1) → R) ⧸ Q := Q.mkQ (Pi.single 0 1)
  have hrel : ∀ j : Fin (N + 1), Q.mkQ (M *ᵥ Pi.single j (1 : R)) = 0 := by
    intro j
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨_, rfl⟩
  have he : ∀ j (hj : j < N + 1),
      Q.mkQ (Pi.single (⟨j, hj⟩ : Fin (N + 1)) (1 : R)) = cf M j • e0 := by
    intro j
    induction j with
    | zero => intro _; rw [show cf M 0 = 1 from rfl, one_smul]; rfl
    | succ j ih =>
      intro hj
      have h := hrel ⟨j, by omega⟩
      rw [hcol, dif_pos (show j + 1 < N + 1 from hj), map_add, map_smul, map_smul,
        ih (by omega)] at h
      have h' : sd M j • Q.mkQ (Pi.single (⟨j + 1, hj⟩ : Fin (N + 1)) (1 : R)) =
          -(dg M j • cf M j • e0) := eq_neg_of_add_eq_zero_right h
      have hinv := Ring.inverse_mul_cancel _ (isUnit_sd hsub j)
      calc Q.mkQ (Pi.single (⟨j + 1, hj⟩ : Fin (N + 1)) (1 : R))
          = (Ring.inverse (sd M j) * sd M j) •
              Q.mkQ (Pi.single (⟨j + 1, hj⟩ : Fin (N + 1)) (1 : R)) := by rw [hinv, one_smul]
        _ = Ring.inverse (sd M j) • -(dg M j • cf M j • e0) := by rw [← smul_smul, h']
        _ = cf M (j + 1) • e0 := by
          rw [show cf M (j + 1) = -(dg M j) * Ring.inverse (sd M j) * cf M j from rfl, smul_neg,
            smul_smul, smul_smul, ← neg_smul]
          congr 1
          ring
  have hlast : dg M N • Q.mkQ (Pi.single (Fin.last N) (1 : R)) = 0 := by
    have h := hrel (Fin.last N)
    rw [hcol, dif_neg (by simp), add_zero, map_smul] at h
    exact h
  -- the backward map
  have hψ : I ≤ LinearMap.ker (LinearMap.toSpanSingleton R _ e0) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.toSpanSingleton_apply, ← hprod]
    have h : Q.mkQ (Pi.single (Fin.last N) (1 : R)) = cf M N • e0 := he N (by omega)
    rw [h, smul_smul] at hlast
    rw [show cf M N * dg M N * w = w * (dg M N * cf M N) by ring, ← smul_smul, hlast, smul_zero]
  let G : (R ⧸ I) →ₗ[R] ((Fin (N + 1) → R) ⧸ Q) := I.liftQ _ hψ
  have hphi : ∀ j : Fin (N + 1), phi M (Pi.single j 1) = cf M j := by
    intro j
    rw [phi_apply, sum_eq_single j]
    · simp
    · intro i _ hi; rw [Pi.single_eq_of_ne hi, mul_zero]
    · intro h; exact absurd (mem_univ _) h
  refine ⟨LinearEquiv.ofLinear F G ?_ ?_⟩
  · refine Submodule.linearMap_qext _ (LinearMap.ext_ring ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.id_apply, G, F,
      Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul, e0]
    rw [hphi]
    rfl
  · refine Submodule.linearMap_qext _ (LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.id_apply, G, F,
      LinearMap.coe_single, Submodule.liftQ_apply, hphi]
    rw [LinearMap.toSpanSingleton_apply, ← he j j.2]
    rfl

end Bidiagonal

/-- **(S4) Bidiagonal lemma.**  Let `R` be a commutative ring, `n ≥ 1`, and let
`M : R^n → R^n` be lower bidiagonal: diagonal entries `d_0, …, d_{n−1}`, subdiagonal entries
`M (j+1) j` units, all other entries `0`.  Then `coker M ≅ R / (d_0 d_1 ⋯ d_{n−1})` as
`R`-modules.  Here `R^n = Fin n → R`, `M` acts by `Matrix.mulVecLin`, and the cokernel is
`(Fin n → R) ⧸ LinearMap.range (Matrix.mulVecLin M)`. -/
theorem bidiagonal_coker {R : Type*} [CommRing R] (n : ℕ) (hn : 1 ≤ n)
    (M : Matrix (Fin n) (Fin n) R) (d : Fin n → R) (hdiag : ∀ i, M i i = d i)
    (hsub : ∀ i j : Fin n, (i : ℕ) = j + 1 → IsUnit (M i j))
    (hzero : ∀ i j : Fin n, i ≠ j → (i : ℕ) ≠ j + 1 → M i j = 0) :
    Nonempty (((Fin n → R) ⧸ LinearMap.range (Matrix.mulVecLin M)) ≃ₗ[R]
      (R ⧸ Ideal.span {∏ i, d i})) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [show ∏ i, d i = ∏ i, M i i from prod_congr rfl (fun i _ => (hdiag i).symm)]
  exact Bidiagonal.coker_equiv_aux hsub hzero

end ColouredSand.Strings
