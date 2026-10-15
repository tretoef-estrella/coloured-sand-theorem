module

public import RequestProject.Glue.Lattice

/-!
# (G4) Rescaling by a unit (CSG2, §1 (G4) and §2 "*(G4)*")

* `rescale u : V ≃ₗ[ℚ_[p]] V` is the identity on the `inl` coordinates and multiplication by
  `u⁻¹` on the `inr` coordinates.
* `G4_rescaling`: for a unit `u : ℤ_[p]ˣ` there is a `ℚ_[p]`-linear equivalence `φ : V ≃ V`
  commuting with every `F t`, `E t`, `P w`, with `φ ℓ_i = ℓ_i`, and mapping `Lx x` onto
  `Lx (u x)` (the image is `Submodule.map` of `φ` viewed as a `ℤ_[p]`-linear map).

This holds for arbitrary `λ`, `μ`, `r` (more general than the setting of the document).
-/

@[expose] public section

open Finset

namespace ColouredSand.Glue

variable {p : ℕ} [Fact p.Prime] {L M : ℕ}

variable (p L M) in
/-- The rescaling `φ`: identity on the `inl` coordinates, multiplication by `c` on the `inr`
coordinates (for a unit `c`). -/
noncomputable def scaleR (c : ℚ_[p]) : V p L M →ₗ[ℚ_[p]] V p L M where
  toFun v := fun y => match y with
    | .inl i => v (.inl i)
    | .inr j => c * v (.inr j)
  map_add' v w := by ext (i | j) <;> simp [mul_add]
  map_smul' a v := by ext (i | j) <;> simp; ring

lemma scaleR_inl (c : ℚ_[p]) (v : V p L M) (i : Fin (L + 1)) :
    scaleR p L M c v (.inl i) = v (.inl i) := rfl

lemma scaleR_inr (c : ℚ_[p]) (v : V p L M) (j : Fin (M + 1)) :
    scaleR p L M c v (.inr j) = c * v (.inr j) := rfl

lemma cL_scaleR (c : ℚ_[p]) (v : V p L M) (n : ℕ) : cL (scaleR p L M c v) n = cL v n := by
  unfold cL; split_ifs <;> rfl

lemma cR_scaleR (c : ℚ_[p]) (v : V p L M) (n : ℕ) :
    cR (scaleR p L M c v) n = c * cR v n := by
  unfold cR; split_ifs
  · rfl
  · ring

lemma scaleR_scaleR (c d : ℚ_[p]) (h : c * d = 1) (v : V p L M) :
    scaleR p L M c (scaleR p L M d v) = v := by
  ext (i | j)
  · rfl
  · rw [scaleR_inr, scaleR_inr, ← mul_assoc, h, one_mul]

lemma unit_inv_mul (u : ℤ_[p]ˣ) :
    (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
  rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]

lemma unit_mul_inv (u : ℤ_[p]ˣ) :
    ((u : ℤ_[p]) : ℚ_[p]) * (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1 := by
  rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]

variable (p L M) in
/-- `φ = rescale u`: multiplication by `u⁻¹` on the `inr` coordinates. -/
noncomputable def rescale (u : ℤ_[p]ˣ) : V p L M ≃ₗ[ℚ_[p]] V p L M :=
  LinearEquiv.ofLinear (scaleR p L M (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]))
    (scaleR p L M ((u : ℤ_[p]) : ℚ_[p]))
    (LinearMap.ext fun v => scaleR_scaleR _ _ (unit_inv_mul u) v)
    (LinearMap.ext fun v => scaleR_scaleR _ _ (unit_mul_inv u) v)

lemma rescale_apply (u : ℤ_[p]ˣ) (v : V p L M) :
    rescale p L M u v = scaleR p L M (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) v := rfl

lemma rescale_symm_apply (u : ℤ_[p]ˣ) (v : V p L M) :
    ((rescale p L M u).restrictScalars ℤ_[p]).symm v = scaleR p L M ((u : ℤ_[p]) : ℚ_[p]) v :=
  rfl

lemma norm_unit_mul (u : ℤ_[p]ˣ) (z : ℚ_[p]) : ‖((u : ℤ_[p]) : ℚ_[p]) * z‖ = ‖z‖ := by
  rw [norm_mul, show ‖((u : ℤ_[p]) : ℚ_[p])‖ = ‖(u : ℤ_[p])‖ from rfl, PadicInt.isUnit_iff.1
    u.isUnit, one_mul]

/-- **(G4) Rescaling.**  For a unit `u` of `ℤ_[p]` there is a `ℚ_[p]`-linear automorphism `φ`
of `V`, commuting with every `F t`, `E t` and `P w`, fixing every `ℓ_i`, and mapping `Lx x` onto
`Lx (u x)`. -/
theorem G4_rescaling (r : ℕ) (u : ℤ_[p]ˣ) (x : ℚ_[p]) :
    ∃ φ : V p L M ≃ₗ[ℚ_[p]] V p L M,
      (∀ t v, φ (Fop p L M t v) = Fop p L M t (φ v)) ∧
      (∀ t v, φ (Eop p L M t v) = Eop p L M t (φ v)) ∧
      (∀ (w : ℤ) v, φ (Pop p L M w v) = Pop p L M w (φ v)) ∧
      (∀ i, φ (ell p L M i) = ell p L M i) ∧
      (Lx p L M r x).map ((φ.restrictScalars ℤ_[p]).toLinearMap) =
        Lx p L M r (((u : ℤ_[p]) : ℚ_[p]) * x) := by
  refine ⟨rescale p L M u, ?_, ?_, ?_, ?_, ?_⟩
  · intro t v
    ext (i | j)
    · rw [rescale_apply, rescale_apply, scaleR_inl, Fop_inl, Fop_inl, cL_scaleR]
    · rw [rescale_apply, rescale_apply, scaleR_inr, Fop_inr, Fop_inr, cR_scaleR]
      split_ifs <;> ring
  · intro t v
    ext (i | j)
    · rw [rescale_apply, rescale_apply, scaleR_inl, Eop_inl, Eop_inl, cL_scaleR]
    · rw [rescale_apply, rescale_apply, scaleR_inr, Eop_inr, Eop_inr, cR_scaleR]
      ring
  · intro w v
    ext (i | j)
    · rw [rescale_apply, rescale_apply, scaleR_inl, Pop_apply, Pop_apply, scaleR_inl]
    · rw [rescale_apply, rescale_apply, scaleR_inr, Pop_apply, Pop_apply, scaleR_inr]
      split_ifs <;> ring
  · intro i
    ext (i' | j)
    · rw [rescale_apply, scaleR_inl]
    · rw [rescale_apply, scaleR_inr, ell_inr, mul_zero]
  · ext v
    rw [Submodule.mem_map_equiv, mem_Lx_iff, mem_Lx_iff, rescale_symm_apply]
    have key : ∀ y, ‖Phi p L M r x (scaleR p L M ((u : ℤ_[p]) : ℚ_[p]) v) y‖ =
        ‖Phi p L M r (((u : ℤ_[p]) : ℚ_[p]) * x) v y‖ := by
      intro y
      rcases y with i | j
      · rw [Phi_inl, Phi_inl, scaleR_inl, cR_scaleR]; ring_nf
      · rw [Phi_inr, Phi_inr, scaleR_inr, norm_unit_mul]
    simp only [key]

end ColouredSand.Glue
