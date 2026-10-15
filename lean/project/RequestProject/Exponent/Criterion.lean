module

public import Mathlib

/-!
# (C2) The exponent criterion

This file corresponds to **(C2) The exponent criterion** of `CS4_theorem_C_exponent.md`.

## Encoding

* For a square matrix `M : Matrix ι ι R`, `coker M` is `(ι → R) ⧸ LinearMap.range M.mulVecLin`.
* `M^{−1}` is the inverse, over a fraction field `K` of `R`, of the matrix `M.map (algebraMap R K)`.
  "`x ∈ K` is integral" means `x` lies in the image of `R`, i.e. `∃ r : R, algebraMap R K r = x`;
  "`p^n M^{−1}` is integral" means that this holds for every entry of `p^n M^{−1}`.
* **Exponent.**  Over a discrete valuation ring `R` (which need not be a `ℤ`-algebra of finite
  characteristic) the exponent of an `R`-module `X` is encoded by its annihilator ideal
  `Module.annihilator R X`: "the exponent of `coker M` is `p^ε`" means
  `Module.annihilator R (coker M) = (p^ε)`.  Over `ℤ_[p]` we also state it with Mathlib's
  `AddMonoid.exponent` (the least positive `n` with `n • x = 0` for all `x`), as in the file.

## Results

* `kills_coker_iff_integral` (any domain, more general than the file): `a ∈ R` kills `coker M`
  iff `a M^{−1}` is integral.  Its abstract form `kills_coker_iff_integral'` (for linear maps) is
  what is used in the proof of Theorem C.
* `exponent_criterion` (discrete valuation ring with uniformizer `p`): there is `ε` such that
  `p^n M^{−1}` is integral exactly for `n ≥ ε` (so `ε` is the least such `n`), and the annihilator
  of `coker M` is `(p^ε)`.
* `exponent_criterion_padic` (`R = ℤ_[p]`): `AddMonoid.exponent (coker M) = p^ε`, where `−ε` is the
  least `p`-adic valuation of an entry of `M^{−1}` (all entries have valuation `≥ −ε` and some
  nonzero entry has valuation exactly `−ε`).
* `exponent_eq_pow_of_kills_iff`: a group in which `p^n` kills everything exactly when `n ≥ E` has
  exponent `p^E` (used again in Theorem C).
-/

@[expose] public section

open Finset

namespace ColouredSand.Exponent

/-! ### Exponent of a group from the powers of `p` killing it -/

/-- If `p` is prime and `p^n • x = 0` for all `x` exactly when `E ≤ n`, then the exponent of `G`
is `p^E`. -/
theorem exponent_eq_pow_of_kills_iff {G : Type*} [AddMonoid G] {p : ℕ} (hp : p.Prime) {E : ℕ}
    (h : ∀ n : ℕ, (∀ x : G, p ^ n • x = 0) ↔ E ≤ n) : AddMonoid.exponent G = p ^ E := by
  have hdvd : AddMonoid.exponent G ∣ p ^ E :=
    AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero ((h E).mpr le_rfl)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have : E ≤ k := (h k).mp fun x => hk' ▸ AddMonoid.exponent_nsmul_eq_zero x
  rw [hk', le_antisymm hk this]

/-! ### The abstract criterion -/

section core

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- `a` kills `coker M` iff `a e_j ∈ range M` for every basis vector `e_j`. -/
lemma kills_coker_iff_single (MR : (ι → R) →ₗ[R] (ι → R)) (a : R) :
    (∀ x : (ι → R) ⧸ LinearMap.range MR, a • x = 0) ↔
      ∀ j, a • (Pi.single j 1 : ι → R) ∈ LinearMap.range MR := by
  constructor
  · intro h j
    have := h (Submodule.Quotient.mk (Pi.single j 1))
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  · intro h x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      have hf : f = ∑ j, f j • (Pi.single j 1 : ι → R) := by
        conv_lhs => rw [← Finset.univ_sum_single f]
        refine sum_congr rfl fun j _ => ?_
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [hf, smul_sum]
      exact Submodule.sum_mem _ fun j _ => by
        rw [smul_comm]
        exact Submodule.smul_mem _ _ (h j)

omit [Fintype ι] in
/-- If `M_K w = e_j` and `a w` is integral, then `a e_j ∈ range M_R`. -/
lemma smul_single_mem_range (hinj : Function.Injective (algebraMap R K))
    (MR : (ι → R) →ₗ[R] (ι → R)) (MK : (ι → K) →ₗ[K] (ι → K))
    (hcomp : ∀ f, MK (fun i => algebraMap R K (f i)) = fun i => algebraMap R K (MR f i))
    {j : ι} {w : ι → K} (hw : MK w = Pi.single j 1) {a : R}
    (hint : ∀ i, ∃ r, algebraMap R K r = algebraMap R K a * w i) :
    a • (Pi.single j 1 : ι → R) ∈ LinearMap.range MR := by
  choose r hr using hint
  refine ⟨r, funext fun i => hinj ?_⟩
  have h1 := congrFun (hcomp r) i
  have h2 : (fun i => algebraMap R K (r i)) = algebraMap R K a • w := funext fun i => by
    simp [hr]
  rw [← h1, h2, map_smul, hw]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Pi.single_eq_of_ne hij]

omit [Fintype ι] in
/-- If `M_K` is injective, `M_K w = e_j` and `a e_j ∈ range M_R`, then `a w` is integral. -/
lemma integral_of_smul_single_mem_range
    (MR : (ι → R) →ₗ[R] (ι → R)) (MK : (ι → K) →ₗ[K] (ι → K))
    (hcomp : ∀ f, MK (fun i => algebraMap R K (f i)) = fun i => algebraMap R K (MR f i))
    (hMK : Function.Injective MK)
    {j : ι} {w : ι → K} (hw : MK w = Pi.single j 1) {a : R}
    (hmem : a • (Pi.single j 1 : ι → R) ∈ LinearMap.range MR) :
    ∀ i, ∃ r, algebraMap R K r = algebraMap R K a * w i := by
  obtain ⟨y, hy⟩ := hmem
  have : (fun i => algebraMap R K (y i)) = algebraMap R K a • w := by
    apply hMK
    rw [hcomp, map_smul, hw, hy]
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij]
  exact fun i => ⟨y i, by simpa using congrFun this i⟩

/-- **Exponent criterion, abstract form.**  Let `M_R` be an endomorphism of `ι → R` and `M_K` an
injective endomorphism of `ι → K` extending it, and let `w_j` satisfy `M_K w_j = e_j` (so the
`w_j` are the columns of `M_K^{−1}`).  Then `a` kills `coker M_R` iff every `a w_j` is
integral. -/
theorem kills_coker_iff_integral' (hinj : Function.Injective (algebraMap R K))
    (MR : (ι → R) →ₗ[R] (ι → R)) (MK : (ι → K) →ₗ[K] (ι → K))
    (hcomp : ∀ f, MK (fun i => algebraMap R K (f i)) = fun i => algebraMap R K (MR f i))
    (hMK : Function.Injective MK) (w : ι → ι → K) (hw : ∀ j, MK (w j) = Pi.single j 1) (a : R) :
    (∀ x : (ι → R) ⧸ LinearMap.range MR, a • x = 0) ↔
      ∀ i j, ∃ r, algebraMap R K r = algebraMap R K a * w j i := by
  rw [kills_coker_iff_single]
  constructor
  · intro h i j
    exact integral_of_smul_single_mem_range MR MK hcomp hMK (hw j) (h j) i
  · intro h j
    exact smul_single_mem_range hinj MR MK hcomp (hw j) fun i => h i j

end core

/-! ### The matrix form -/

section matrix

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [IsDomain R] in
lemma det_map_ne_zero (M : Matrix ι ι R) (hM : M.det ≠ 0) :
    (M.map (algebraMap R K)).det ≠ 0 := by
  have : (M.map (algebraMap R K)).det = algebraMap R K M.det := by rw [RingHom.map_det]; rfl
  rw [this]
  exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hM

omit [IsDomain R] in
/-- **Exponent criterion over a domain** (more general than the file).  Let `M` be a square
matrix over a domain `R` with `det M ≠ 0` (i.e. invertible over the fraction field `K`).  Then
`a ∈ R` kills `coker M` iff `a M^{−1}` is integral. -/
theorem kills_coker_iff_integral (M : Matrix ι ι R) (hM : M.det ≠ 0) (a : R) :
    (∀ x : (ι → R) ⧸ LinearMap.range M.mulVecLin, a • x = 0) ↔
      ∀ i j, ∃ r : R, algebraMap R K r = algebraMap R K a * (M.map (algebraMap R K))⁻¹ i j := by
  set A := M.map (algebraMap R K)
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (det_map_ne_zero M hM)
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hdet
  refine kills_coker_iff_integral' (IsFractionRing.injective R K) M.mulVecLin A.mulVecLin
    (fun f => funext fun i => ?_) (Matrix.mulVec_injective_iff_isUnit.mpr hA)
    (fun j i => A⁻¹ i j) (fun j => funext fun i => ?_) a
  · simp only [Matrix.mulVecLin_apply]
    rw [RingHom.map_mulVec]
    rfl
  · simp only [Matrix.mulVecLin_apply]
    have := congrFun (congrFun (Matrix.mul_nonsing_inv A hdet) i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, eq_comm] using this

/-- `det M` kills `coker M`. -/
lemma det_smul_coker {R : Type*} [CommRing R] (M : Matrix ι ι R)
    (x : (ι → R) ⧸ LinearMap.range M.mulVecLin) : M.det • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨M.adjugate.mulVec f, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec]

/-- **(C2) The exponent criterion.**  Let `R` be a discrete valuation ring with uniformizer `p`
and `M` a square matrix over `R` that is invertible over the fraction field `K`
(`det M ≠ 0`).  Then there is `ε` such that `p^n M^{−1}` is integral exactly when `n ≥ ε`
(so `ε` is the least `n ≥ 0` with `p^n M^{−1}` integral, i.e. `−ε` is the least valuation of an
entry of `M^{−1}`; see `exponent_criterion_padic` for this reading spelled out over `ℤ_[p]`), and the exponent of `coker M` is `p^ε`:
its annihilator is the ideal `(p^ε)`. -/
theorem exponent_criterion [IsDiscreteValuationRing R] {p : R} (hp : Irreducible p)
    (M : Matrix ι ι R) (hM : M.det ≠ 0) :
    ∃ ε : ℕ, (∀ n : ℕ, (∀ i j, ∃ r : R, algebraMap R K r =
        algebraMap R K (p ^ n) * (M.map (algebraMap R K))⁻¹ i j) ↔ ε ≤ n) ∧
      Module.annihilator R ((ι → R) ⧸ LinearMap.range M.mulVecLin) = Ideal.span {p ^ ε} := by
  set X := (ι → R) ⧸ LinearMap.range M.mulVecLin
  have hne : Module.annihilator R X ≠ ⊥ := by
    intro h
    have : M.det ∈ Module.annihilator R X :=
      Module.mem_annihilator.mpr fun x => det_smul_coker M x
    rw [h, Ideal.mem_bot] at this
    exact hM this
  obtain ⟨ε, hε⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hp
  refine ⟨ε, fun n => ?_, hε⟩
  rw [← kills_coker_iff_integral M hM, ← Module.mem_annihilator, hε, Ideal.mem_span_singleton]
  exact pow_dvd_pow_iff hp.ne_zero hp.not_isUnit

end matrix

/-! ### The case `R = ℤ_[p]` -/

section padic

variable {p : ℕ} [hp : Fact p.Prime]

lemma padic_integral_iff (x : ℚ_[p]) : (∃ r : ℤ_[p], (r : ℚ_[p]) = x) ↔ 0 ≤ x.valuation := by
  rw [← Padic.norm_le_one_iff_val_nonneg]
  exact ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- `p^n x` is integral iff `x = 0` or `v_p(x) ≥ −n`. -/
lemma padic_pow_mul_integral_iff (n : ℕ) (x : ℚ_[p]) :
    (∃ r : ℤ_[p], (r : ℚ_[p]) = (p : ℚ_[p]) ^ n * x) ↔ (x ≠ 0 → -(n : ℤ) ≤ x.valuation) := by
  rw [padic_integral_iff]
  by_cases hx : x = 0
  · simp [hx]
  · have hp0 : (p : ℚ_[p]) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    rw [Padic.valuation_mul hp0 hx, Padic.valuation_pow, Padic.valuation_p]
    simp only [mul_one, ne_eq, hx, not_false_eq_true, forall_const]
    omega

/-- **(C2) over `ℤ_[p]`, with `AddMonoid.exponent`.**  For a square matrix `M` over `ℤ_[p]`
with `det M ≠ 0` (invertible over `ℚ_[p]`) and at least one row, the exponent of `coker M` is
`p^ε`, where `−ε` is the least `p`-adic valuation of an entry of `M^{−1}`: every entry of
`M^{−1}` has valuation `≥ −ε`, and some nonzero entry has valuation exactly `−ε`.
(`Padic.valuation 0 = 0`, so the zero entries do not affect the first condition.) -/
theorem exponent_criterion_padic {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℤ_[p]) (hM : M.det ≠ 0) :
    ∃ ε : ℕ, AddMonoid.exponent ((ι → ℤ_[p]) ⧸ LinearMap.range M.mulVecLin) = p ^ ε ∧
      (∀ i j, -(ε : ℤ) ≤ ((M.map (algebraMap ℤ_[p] ℚ_[p]))⁻¹ i j).valuation) ∧
      ∃ i j, (M.map (algebraMap ℤ_[p] ℚ_[p]))⁻¹ i j ≠ 0 ∧
        ((M.map (algebraMap ℤ_[p] ℚ_[p]))⁻¹ i j).valuation = -(ε : ℤ) := by
  set A := M.map (algebraMap ℤ_[p] ℚ_[p])
  obtain ⟨ε, hε, -⟩ := exponent_criterion (K := ℚ_[p]) PadicInt.irreducible_p M hM
  have hint : ∀ n : ℕ, (∀ i j, A⁻¹ i j ≠ 0 → -(n : ℤ) ≤ (A⁻¹ i j).valuation) ↔ ε ≤ n := by
    intro n
    rw [← hε n]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [map_pow, ← padic_pow_mul_integral_iff]
    rfl
  refine ⟨ε, exponent_eq_pow_of_kills_iff hp.out fun n => ?_, fun i j => ?_, ?_⟩
  · rw [← hε n]
    rw [← kills_coker_iff_integral M hM]
    refine forall_congr' fun x => ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p], Nat.cast_pow]
  · by_cases h0 : A⁻¹ i j = 0
    · rw [h0, Padic.valuation_zero]; omega
    · exact (hint ε).mpr le_rfl i j h0
  · by_contra hcon
    push_neg at hcon
    have hall : ∀ i j, A⁻¹ i j ≠ 0 → -(ε : ℤ) + 1 ≤ (A⁻¹ i j).valuation := by
      intro i j h0
      have := (hint ε).mpr le_rfl i j h0
      have := hcon i j h0
      omega
    rcases Nat.eq_zero_or_pos ε with hε0 | hεpos
    · -- all entries of `A⁻¹` are divisible by `p`, so `p` would be a unit
      subst hε0
      have hdiv : ∀ i j, ∃ r : ℤ_[p], (r : ℚ_[p]) * p = A⁻¹ i j := by
        intro i j
        by_cases h0 : A⁻¹ i j = 0
        · exact ⟨0, by simp [h0]⟩
        · have hv := hall i j h0
          have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
          obtain ⟨r, hr⟩ := (padic_integral_iff (A⁻¹ i j / (p : ℚ_[p]))).mpr (by
            rw [div_eq_mul_inv, Padic.valuation_mul h0 (inv_ne_zero hp0), Padic.valuation_inv,
              Padic.valuation_p]
            omega)
          exact ⟨r, by rw [hr]; field_simp⟩
      choose N hN using hdiv
      have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (det_map_ne_zero M hM)
      have hMN : M * ((p : ℤ_[p]) • Matrix.of N) = 1 := by
        apply Matrix.map_injective (IsFractionRing.injective ℤ_[p] ℚ_[p])
        show (M * _).map (algebraMap ℤ_[p] ℚ_[p]) = (1 : Matrix ι ι ℤ_[p]).map _
        rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        convert Matrix.mul_nonsing_inv A hdet using 2
        ext i j
        simp [← hN i j, mul_comm]
      have hu : IsUnit (p : ℤ_[p]) := by
        obtain ⟨i⟩ := ‹Nonempty ι›
        have := congrFun (congrFun hMN i) i
        rw [Matrix.mul_smul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] at this
        exact IsUnit.of_mul_eq_one _ this
      exact PadicInt.irreducible_p.not_isUnit hu
    · have := (hint (ε - 1)).mp (fun i j h0 => by have := hall i j h0; omega)
      omega

end padic

end ColouredSand.Exponent
