module

public import Mathlib

/-!
# `C16_the_family_group_over_Z2.md`, Parts L and U

* **Part L** (cokernels of diagonalizable matrices over any commutative ring): (L1) `L1`,
  (L2) `L2_range` and `L2`, (L3) `L3_unit` and `L3_zero`.  The reindexing of a product of cyclic
  quotients along an equivalence of index types (`piQuotReindex`) is an auxiliary result used in
  Part X.
* **Part U** (odd integers in `ℤ_[2]`): (U1) `U1`, (U2) `U2`.

Encodings: a matrix is `Matrix (Fin n) (Fin n) R`, its linear map is `Matrix.toLin' B`
(`v ↦ B *ᵥ v`), its cokernel is `(Fin n → R) ⧸ LinearMap.range (Matrix.toLin' B)`; "`det P` is a
unit" is `IsUnit P.det`; the cyclic module `R ⧸ (d)` is the quotient `R ⧸ Ideal.span {d}`;
isomorphisms are `R`-linear equivalences, stated as `Nonempty (… ≃ₗ[R] …)`.
-/

@[expose] public section

namespace FamilyGroup

open Matrix

section PartL

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **(L1)** of `C16_the_family_group_over_Z2.md` (Part L): if `P, Q` have unit determinant and
`P * B * Q = diagonal d`, then `(Fin n → R) ⧸ range (toLin' B) ≅ Π_j R ⧸ span {d j}`. -/
theorem L1 (B P Q : Matrix (Fin n) (Fin n) R) (d : Fin n → R)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (h : P * B * Q = diagonal d) :
    Nonempty (((Fin n → R) ⧸ LinearMap.range (Matrix.toLin' B)) ≃ₗ[R]
      ((j : Fin n) → R ⧸ Ideal.span {d j})) := by
  let eP : (Fin n → R) ≃ₗ[R] (Fin n → R) := LinearEquiv.ofLinear (toLin' P) (toLin' P⁻¹)
    (by rw [← toLin'_mul, mul_nonsing_inv _ hP, toLin'_one])
    (by rw [← toLin'_mul, nonsing_inv_mul _ hP, toLin'_one])
  have hQs : LinearMap.range (toLin' Q) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨toLin' Q⁻¹ v, ?_⟩
    rw [← LinearMap.comp_apply, ← toLin'_mul, mul_nonsing_inv _ hQ, toLin'_one, LinearMap.id_apply]
  have h1 : Submodule.map (eP : (Fin n → R) →ₗ[R] (Fin n → R)) (LinearMap.range (toLin' B)) =
      LinearMap.range (toLin' (diagonal d)) := by
    rw [← h, toLin'_mul, toLin'_mul, LinearMap.range_comp_of_range_eq_top _ hQs,
      LinearMap.range_comp]
    rfl
  have h2 : LinearMap.range (toLin' (diagonal d)) =
      Submodule.pi Set.univ (fun j => (Ideal.span {d j} : Submodule R R)) := by
    ext v
    simp only [LinearMap.mem_range, toLin'_apply, Submodule.mem_pi, Set.mem_univ, true_implies,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨w, rfl⟩ j
      simp [mulVec_diagonal]
    · intro hv
      choose w hw using hv
      exact ⟨w, funext fun j => by simp [mulVec_diagonal, hw j]⟩
  exact ⟨(Submodule.Quotient.equiv _ _ eP h1).trans
    ((Submodule.quotEquivOfEq _ _ h2).trans (Submodule.quotientPi _))⟩

/-- **(L2)** of `C16_the_family_group_over_Z2.md` (Part L), first half:
`range (c • toLin' B) = range (toLin' (c • B))`. -/
theorem L2_range (c : R) (B : Matrix (Fin n) (Fin n) R) :
    LinearMap.range (c • Matrix.toLin' B) = LinearMap.range (Matrix.toLin' (c • B)) := by
  rw [(Matrix.toLin' (R := R) (m := Fin n) (n := Fin n)).map_smul]

/-- **(L2)** of `C16_the_family_group_over_Z2.md` (Part L), second half: under the hypotheses of
(L1), `(Fin n → R) ⧸ range (c • toLin' B) ≅ Π_j R ⧸ span {c · d j}`. -/
theorem L2 (c : R) (B P Q : Matrix (Fin n) (Fin n) R) (d : Fin n → R)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (h : P * B * Q = diagonal d) :
    Nonempty (((Fin n → R) ⧸ LinearMap.range (c • Matrix.toLin' B)) ≃ₗ[R]
      ((j : Fin n) → R ⧸ Ideal.span {c * d j})) := by
  rw [L2_range]
  refine L1 (c • B) P Q (fun j => c * d j) hP hQ ?_
  rw [mul_smul_comm, smul_mul_assoc, h]
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [diagonal_apply_ne _ hij]

/-- **(L3)** of `C16_the_family_group_over_Z2.md` (Part L), first half: a unit drops out of a
principal ideal, `span {u · y} = span {y}`. -/
theorem L3_unit {u : R} (hu : IsUnit u) (y : R) : Ideal.span {u * y} = Ideal.span {y} :=
  Ideal.span_singleton_mul_left_unit hu y

/-- **(L3)** of `C16_the_family_group_over_Z2.md` (Part L), second half: `R ⧸ span {0} ≅ R`. -/
theorem L3_zero : Nonempty ((R ⧸ Ideal.span {(0 : R)}) ≃ₗ[R] R) :=
  ⟨Submodule.quotEquivOfEqBot _ (Ideal.span_singleton_eq_bot.2 rfl)⟩

/-- Reindexing a product of cyclic quotients along an equivalence of index types, with generators
that agree up to the ideal they span (auxiliary for Part X of
`C16_the_family_group_over_Z2.md`). -/
theorem piQuotReindex {ι ι' : Type*} (d : ι → R) (g : ι' → R) (e : ι' ≃ ι)
    (h : ∀ x, Ideal.span {d (e x)} = Ideal.span {g x}) :
    Nonempty (((i : ι) → R ⧸ Ideal.span {d i}) ≃ₗ[R] ((x : ι') → R ⧸ Ideal.span {g x})) :=
  ⟨(LinearEquiv.piCongrLeft R (fun i => R ⧸ Ideal.span {d i}) e).symm.trans
    (LinearEquiv.piCongrRight fun x => Submodule.quotEquivOfEq _ _ (h x))⟩

end PartL

section PartU

/-- **(U1)** of `C16_the_family_group_over_Z2.md` (Part U): an odd integer is a unit of `ℤ_[2]`. -/
theorem U1 {z : ℤ} (h : Odd z) : IsUnit (z : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  have hdvd := PadicInt.norm_int_lt_one_iff_dvd (p := 2) z
  have h2 : ¬ ((2 : ℕ) : ℤ) ∣ z := by
    rintro ⟨w, hw⟩; obtain ⟨v, hv⟩ := h; omega
  have hle := PadicInt.norm_le_one (z : ℤ_[2])
  by_contra hne
  exact h2 (hdvd.1 (lt_of_le_of_ne hle hne))

/-- **(U2)** of `C16_the_family_group_over_Z2.md` (Part U): if `P` has odd determinant then the
image of `P` in `ℤ_[2]` has unit determinant; and `(P * B * Q).map φ = P.map φ * B.map φ * Q.map φ`
for `φ = Int.castRingHom ℤ_[2]`. -/
theorem U2 {n : ℕ} (P B Q : Matrix (Fin n) (Fin n) ℤ) :
    (Odd P.det → IsUnit (P.map (Int.castRingHom ℤ_[2])).det) ∧
      (P * B * Q).map (Int.castRingHom ℤ_[2]) =
        P.map (Int.castRingHom ℤ_[2]) * B.map (Int.castRingHom ℤ_[2]) *
          Q.map (Int.castRingHom ℤ_[2]) := by
  refine ⟨fun h => ?_, by rw [Matrix.map_mul, Matrix.map_mul]⟩
  have := RingHom.map_det (Int.castRingHom ℤ_[2]) P
  rw [RingHom.mapMatrix_apply] at this
  rw [← this]
  exact U1 h

end PartU

end FamilyGroup
