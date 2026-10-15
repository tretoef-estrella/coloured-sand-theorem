module

public import RequestProject.TiltRules.SplitZero

/-!
# Part S of `CSG4_tensor_rules.md`: `V ⊗ Δ(l)` for the simple weights

## Encoding

* DP-lattices over `ℤ_[p]` are the cube's `DPLattice ℤ_[p]`; `delta ℤ_[p] l` is the Weyl
  lattice `Δ(l)` (basis `Fin (l + 1)`), `tensorV M` is `V ⊗ M`, `dsum M N` is `M ⊕ N`
  (`Lemma35.dsum`), and an isomorphism of DP-lattices is a term of `Doubling.Iso M N`; the
  statements assert `Nonempty (Iso _ _)`.
* `Tglue p r a` is the glued tilting lattice of `RequestProject/TiltP` (the glued lattice
  `glueDP p λ μ r x₀` with `λ = lam p r a`, `μ = mu p r a`, `x₀ = xzero p r a = p^{−ν}`).

## Contents

* **(S0)** `S0 : V ⊗ Δ(0) ≅ Δ(1)`.
* **(S1)** `S1 : V ⊗ Δ(l) ≅ Δ(l + 1) ⊕ Δ(l − 1)` for `1 ≤ l ≤ p − 2` (a restatement of
  `TiltP.G3`).
* **(S2)** `S2 : V ⊗ Δ((b + 1) p − 1) ≅ Tglue p 1 b` for `b ≤ p − 1`.

None of these needs `p ≠ 2`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltRules

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP

variable {p : ℕ} [Fact p.Prime]

/-! ### Small `p`-adic facts -/

lemma norm_natCast_unit {n : ℕ} (h : ¬ p ∣ n) : ‖(n : ℚ_[p])‖ = 1 := by
  have h1 : ‖((n : ℕ) : ℤ_[p])‖ = 1 := by
    rw [PadicInt.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd Fact.out]; exact h
  rw [PadicInt.norm_def] at h1; push_cast at h1; exact h1

lemma norm_xzero_mul_natCast (r a : ℕ) (n : ℕ) (hn : p ^ nu p r a ∣ n) :
    ‖xzero p r a * (n : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨k, rfl⟩ := hn
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [xzero, Nat.cast_mul, Nat.cast_pow, ← mul_assoc, zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]
  exact norm_natCast_le k

/-! ### (S0) -/

/-- **(S0)** (`CSG4_tensor_rules.md`, Part S, (S0)): `V ⊗ Δ(0) ≅ Δ(1)` as DP-lattices over
`ℤ_[p]`.  The isomorphism is `b_k ⊗ e_0 ↦ e_k`. -/
theorem S0 : Nonempty (Iso (tensorV (delta ℤ_[p] 0)) (delta ℤ_[p] 1)) := by
  obtain ⟨u⟩ := iso_of_untw (untwDelta p 1) (untwTensor (untwDelta p 0)) (s0E p)
    (fun t f => s0E_F t f) (fun t f => s0E_E t f) (by
      intro f
      show f ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin (1 + 1))) ↔
        slice 0 (s0E p f) ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin (0 + 1))) ∧
          slice 1 (s0E p f) ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin (0 + 1)))
      simp only [mem_range_coeL_iff, slice_apply, s0E_apply]
      constructor
      · intro h; exact ⟨fun _ => h 0, fun _ => h 1⟩
      · rintro ⟨h0, h1⟩ i
        fin_cases i
        · exact h0 0
        · exact h1 0)
  exact ⟨u.symm⟩

/-! ### (S1) -/

/-- **(S1)** (`CSG4_tensor_rules.md`, Part S, (S1)): for `1 ≤ l ≤ p − 2`,
`V ⊗ Δ(l) ≅ Δ(l + 1) ⊕ Δ(l − 1)` as DP-lattices over `ℤ_[p]` (this is `TiltP.G3`, since
`p ∤ l + 1`). -/
theorem S1 {l : ℕ} (hl1 : 1 ≤ l) (hl2 : l ≤ p - 2) :
    Nonempty (Iso (tensorV (delta ℤ_[p] l)) (dsum (delta ℤ_[p] (l + 1)) (delta ℤ_[p] (l - 1)))) :=
  G3 hl1 (fun h => by
    have hp := (Fact.out : p.Prime).two_le
    have := Nat.le_of_dvd (by omega) h
    omega)

/-! ### (S2) -/

omit [Fact p.Prime] in
lemma glueHyp_one {b : ℕ} (hp : 2 ≤ p) (hb : b ≤ p - 1) : GlueHyp p 1 b :=
  ⟨le_rfl, by omega, hb, by omega⟩

/-- **(S2)** (`CSG4_tensor_rules.md`, Part S, (S2)): for `b ≤ p − 1` and `l = (b + 1) p − 1`,
`V ⊗ Δ(l) ≅ Tglue p 1 b` as DP-lattices over `ℤ_[p]` (for `b = 0` this is `TiltP.G4`).

Proof: `iso_tensor_glueDP` gives `V ⊗ Δ(l) ≅ glueDP (l + 1) (l − 1) 1 (1/(l + 1))`, and
`1/(l + 1) = u⁻¹ p^{−ν(1, b)}` with `u = p^{−ν} (l + 1)` a unit, so the rescaling by `u`
(`glueIso_unit`, from `G4_rescaling`) finishes. -/
theorem S2 {b l : ℕ} (hb : b ≤ p - 1) (hl : l = (b + 1) * p - 1) :
    Nonempty (Iso (tensorV (delta ℤ_[p] l)) (Tglue p 1 b)) := by
  have hp := (Fact.out : p.Prime).two_le
  have hl1 : 1 ≤ l := by
    subst hl; have : 2 ≤ (b + 1) * p := le_trans hp (Nat.le_mul_of_pos_left p (by omega)); omega
  have hlam : lam p 1 b = l + 1 := by
    subst hl; unfold lam
    have : 1 ≤ (b + 1) * p := by nlinarith
    rw [Nat.sub_add_cancel this]; ring_nf; omega
  have hmu : mu p 1 b = l - 1 := by unfold mu; rw [hlam]; omega
  have hlc : (l : ℚ_[p]) + 1 = ((p * (b + 1) : ℕ) : ℚ_[p]) := by
    rw [← Nat.cast_add_one]; congr 1; subst hl
    have : 1 ≤ (b + 1) * p := by nlinarith
    rw [Nat.sub_add_cancel this, mul_comm]
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hl0 : (l : ℚ_[p]) + 1 ≠ 0 := by
    rw [hlc]; push_cast; exact mul_ne_zero hp0 (by exact_mod_cast Nat.succ_ne_zero b)
  set u : ℚ_[p] := xT p 1 b * ((l : ℚ_[p]) + 1) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, xT_of_hyp (glueHyp_one hp hb), norm_mul, norm_xzero, hlc]
    by_cases hbp : b = p - 1
    · have hν : nu p 1 b = 2 := by unfold nu; rw [if_pos ⟨by omega, hbp⟩]
      have : p * (b + 1) = p * p := by rw [hbp, Nat.sub_add_cancel (by omega)]
      rw [hν, this]; push_cast; rw [norm_mul, Padic.norm_p]
      have : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      field_simp
    · have hν : nu p 1 b = 1 := by unfold nu; rw [if_neg (by omega)]
      rw [hν]; push_cast; rw [norm_mul, Padic.norm_p]
      rw [show ((b : ℚ_[p]) + 1) = ((b + 1 : ℕ) : ℚ_[p]) by push_cast; rfl,
        norm_natCast_unit (fun h => by have := Nat.le_of_dvd (by omega) h; omega)]
      have : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      field_simp
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  have hx : u⁻¹ * xT p 1 b = 1 / ((l : ℚ_[p]) + 1) := by
    rw [hu_def, mul_inv]
    have : xT p 1 b ≠ 0 := by
      intro h; apply hu0; rw [hu_def, h, zero_mul]
    field_simp
  have h : GlueOK p (lam p 1 b) (mu p 1 b) 1 (1 / ((l : ℚ_[p]) + 1)) :=
    hx ▸ glueOK_unit (glueOK_xT 1 b) u⁻¹ (by rw [norm_inv, hu, inv_one])
  obtain ⟨i1⟩ := iso_tensor_glueDP hl1 hlam hmu _ rfl h
  obtain ⟨i2⟩ := glueIso_unit h (glueOK_xT 1 b) rfl rfl rfl u hu (by
    rw [← hx, ← mul_assoc, mul_inv_cancel₀ hu0, one_mul])
  exact ⟨i1.trans i2⟩

end ColouredSand.TiltRules
