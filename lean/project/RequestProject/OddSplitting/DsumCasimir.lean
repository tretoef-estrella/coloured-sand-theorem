module

public import RequestProject.OddSplitting.PartH

/-!
# `CSI5_the_splitting.md`: Part T — the Casimir of a direct sum, and the congruence hypotheses

Namespace `ColouredSand.OddTwist`. Part T of the file notes that "`Ω` on a `dsum` is the `dsum`
of the two Casimirs" and that a `Dcas` on a `Lemma35.dsum` is not yet in the project; this file
proves it.

Encodings: `Lemma35.blk f g` is the blockwise map `f ⊕ g` on `ι ⊕ κ → A`
(`z ↦ Sum.elim (f (z ∘ inl)) (g (z ∘ inr))`), CSI4's `casimir`, `Dcas X c = Ω_X − c • 1`.

* `casimir_dsum`: `Ω_{M ⊕ N} = Ω_M ⊕ Ω_N` (any commutative ring).
* `Dcas_dsum`: `Dcas (M ⊕ N) c = Dcas M c ⊕ Dcas N c`.
* `Dcas_sq_dsum`: if `(Ω_M − c)² = p • R_M` and `(Ω_N − c)² = p • R_N`, then
  `(Ω_{M ⊕ N} − c)² = p • (R_M ⊕ R_N)`.
* `Dcas_sq_zero_of_casimir`: if `Ω_X = p • R` (CSI4 (C3)) then `(Ω_X − 0)² = p • (R ∘ Ω_X)`.
* `isUnit_natCast_padic`: a natural number not divisible by `p` is a unit of `ℤ_[p]`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Lemma35

section general

variable {A : Type*} [CommRing A] (M N : DPLattice A)

omit [CommRing A] in
/-- Part T (auxiliary): `blk` is additive. -/
lemma blk_add' [CommRing A] {ι ι' κ κ' : Type*} (f f' : (ι → A) →ₗ[A] (ι' → A))
    (g g' : (κ → A) →ₗ[A] (κ' → A)) : blk (f + f') (g + g') = blk f g + blk f' g' := by
  refine LinearMap.ext fun z => funext fun i => ?_
  cases i <;> rfl

/-- Part T: the Casimir of a direct sum is the direct sum of the Casimirs. -/
theorem casimir_dsum : casimir (dsum M N) = blk (casimir M) (casimir N) := by
  have hF : (dsum M N).Fd 1 = blk (M.Fd 1) (N.Fd 1) := rfl
  have hE : (dsum M N).Ed 1 = blk (M.Ed 1) (N.Ed 1) := rfl
  rw [casimir, casimir, casimir, hF, hE, H_dsum, blk_comp, ← blk_one, ← blk_add', sq, sq, sq,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp, Module.End.mul_eq_comp, blk_comp,
    ← blk_smul, ← blk_add']

/-- Part T: `Dcas (M ⊕ N) c = Dcas M c ⊕ Dcas N c`. -/
theorem Dcas_dsum (c : A) : Dcas (dsum M N) c = blk (Dcas M c) (Dcas N c) := by
  rw [Dcas, casimir_dsum]
  refine LinearMap.ext fun z => funext fun i => ?_
  cases i <;> rfl

variable {M N}

/-- Part T: the congruence hypothesis of Part H passes to direct sums. -/
theorem Dcas_sq_dsum (q c : A) (hM : ∃ R, Dcas M c ∘ₗ Dcas M c = q • R)
    (hN : ∃ R, Dcas N c ∘ₗ Dcas N c = q • R) :
    ∃ R, Dcas (dsum M N) c ∘ₗ Dcas (dsum M N) c = q • R := by
  obtain ⟨RM, hRM⟩ := hM
  obtain ⟨RN, hRN⟩ := hN
  exact ⟨blk RM RN, by rw [Dcas_dsum, blk_comp, hRM, hRN, blk_smul]⟩

/-- Part T: from `Ω_X = q • R` (CSI4 (C3)) to the congruence hypothesis of Part H with `b = 0`. -/
theorem Dcas_sq_zero_of_casimir {X : DPLattice A} (q : A) (h : ∃ R, casimir X = q • R) :
    ∃ R, Dcas X 0 ∘ₗ Dcas X 0 = q • R := by
  obtain ⟨R, hR⟩ := h
  refine ⟨R ∘ₗ casimir X, ?_⟩
  rw [Dcas, zero_smul, sub_zero, hR, LinearMap.smul_comp]

end general

/-- Part T (auxiliary): a natural number not divisible by `p` is a unit of `ℤ_[p]`. -/
theorem isUnit_natCast_padic {p : ℕ} [Fact p.Prime] {n : ℕ} (h : ¬ p ∣ n) :
    IsUnit (n : ℤ_[p]) := by
  by_contra hd
  have hm : (n : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := hd
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at hm
  exact h hm

end ColouredSand.OddTwist
