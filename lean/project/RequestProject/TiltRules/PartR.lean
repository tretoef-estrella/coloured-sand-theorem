module

public import RequestProject.TiltRules.PartS

/-!
# Part R of `CSG4_tensor_rules.md`: `V ⊗ Tglue p r a` for `r ≤ p − 1`

## Encoding

As in `RequestProject/TiltRules/PartS.lean`: DP-lattices over `ℤ_[p]` are `DPLattice ℤ_[p]`,
`delta ℤ_[p] l = Δ(l)`, `tensorV M = V ⊗ M`, `dsum M N = M ⊕ N`, and an isomorphism of
DP-lattices is a term of `Doubling.Iso`.  `Tglue p r a` is the glued tilting lattice of
`RequestProject/TiltP`; `λ = lam p r a = p − 1 + r + p a` and `μ = mu p r a = λ − 2 r` are written
out explicitly in the statements.  The hypothesis `GlueHyp p r a` is
`1 ≤ r ≤ p ∧ a ≤ p − 1 ∧ (r = p → a = p − 1)`.

## Contents

* `lam_succ`, `mu_succ`, `lam_pred`, `mu_pred` (`lam_mu_shift`): `lam p (r ± 1) a = λ ± 1`,
  `mu p (r ± 1) a = μ ∓ 1`.
* **(R1)** `R1` (`r = 1`), **(R2)** `R2` (`2 ≤ r ≤ p − 2`), **(R3)** `R3_pos` (`r = p − 1`,
  `1 ≤ a ≤ p − 2`) and `R3_zero` (`r = p − 1`, `a = 0`), **(R4)** `R4` (`r = a = p − 1`).

## Proof

`tensor_glue_split` (resp. `tensor_glue_split0` when `μ = 0`) splits `V ⊗ Tglue p r a` into the
glued lattice of `A ⊕ D = Δ(λ + 1) ⊕ Δ(μ − 1)` (shift `r + 1`, glue `y₁ = −x₀ (r + 1)/(μ + 1)`)
and that of `B ⊕ C = Δ(λ − 1) ⊕ Δ(μ + 1)` (shift `r − 1`, glue `−x₀`) (§3, Steps 1–3).  The
valuations of §3, Step 3, then identify the pieces: a glue differing from `xzero` by a unit gives
`Tglue` (`glueIso_unit`), an integral glue gives `Δ ⊕ Δ` (`glueIso_int`), and shift `0` gives
`Δ(λ − 1) ⊕ Δ(λ − 1)` (`glueIso_shift0`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltRules

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP

variable {p : ℕ} [Fact p.Prime]

/-! ### The shifted weights -/

omit [Fact p.Prime] in
/-- `lam p (r + 1) a = λ + 1` (`CSG4_tensor_rules.md`, Part R; holds unconditionally). -/
theorem lam_succ (r a : ℕ) : lam p (r + 1) a = lam p r a + 1 := by
  unfold lam; omega

omit [Fact p.Prime] in
/-- `mu p (r + 1) a = μ − 1` (`CSG4_tensor_rules.md`, Part R; holds unconditionally, with
truncated subtraction). -/
theorem mu_succ (r a : ℕ) : mu p (r + 1) a = mu p r a - 1 := by
  unfold mu; rw [lam_succ]; omega

omit [Fact p.Prime] in
/-- `lam p (r − 1) a = λ − 1` (`CSG4_tensor_rules.md`, Part R; needs only `1 ≤ r`). -/
theorem lam_pred {r : ℕ} (a : ℕ) (hr : 1 ≤ r) : lam p (r - 1) a = lam p r a - 1 := by
  unfold lam; omega

omit [Fact p.Prime] in
/-- `mu p (r − 1) a = μ + 1` (`CSG4_tensor_rules.md`, Part R; needs only `1 ≤ r ≤ p − 1`). -/
theorem mu_pred {r : ℕ} (a : ℕ) (hr : 1 ≤ r) (hrp : r ≤ p - 1) :
    mu p (r - 1) a = mu p r a + 1 := by
  unfold mu; rw [lam_pred a hr]; unfold lam
  generalize p * a = q; omega

omit [Fact p.Prime] in
/-- **The shifted weights** (`CSG4_tensor_rules.md`, Part R): under `GlueHyp p r a` and
`r ≤ p − 1`, `lam p (r+1) a = λ + 1`, `mu p (r+1) a = μ − 1`, `lam p (r−1) a = λ − 1`,
`mu p (r−1) a = μ + 1`. -/
theorem lam_mu_shift {r a : ℕ} (h : GlueHyp p r a) (hrp : r ≤ p - 1) :
    lam p (r + 1) a = lam p r a + 1 ∧ mu p (r + 1) a = mu p r a - 1 ∧
      lam p (r - 1) a = lam p r a - 1 ∧ mu p (r - 1) a = mu p r a + 1 :=
  ⟨lam_succ r a, mu_succ r a, lam_pred a h.1, mu_pred a h.1 hrp⟩

/-! ### Numerical facts -/

omit [Fact p.Prime] in
lemma lam_add_one {r a : ℕ} (hr : 1 ≤ r) (hrp : r ≤ p - 1) : lam p r a + 1 = p * (a + 1) + r := by
  unfold lam; rw [mul_add, mul_one]; generalize p * a = q; omega

omit [Fact p.Prime] in
lemma mu_add_r {r a : ℕ} (hr : 1 ≤ r) (hrp : r ≤ p - 1) : mu p r a + r + 1 = p * (a + 1) := by
  unfold mu lam; rw [mul_add, mul_one]; generalize p * a = q; omega

omit [Fact p.Prime] in
lemma lam_eq_mu {r a : ℕ} (hrp : r ≤ p - 1) : lam p r a = mu p r a + 2 * r := by
  unfold mu lam; generalize p * a = q; omega

lemma norm_lam_add_one {r a : ℕ} (hr : 1 ≤ r) (hrp : r ≤ p - 1) :
    ‖(lam p r a : ℚ_[p]) + 1‖ = 1 := by
  rw [← Nat.cast_add_one, lam_add_one hr hrp]
  refine norm_natCast_unit fun h => ?_
  have := (Nat.dvd_add_right (dvd_mul_right p (a + 1))).1 h
  have := Nat.le_of_dvd (by omega) this
  omega

lemma norm_mu_add_one {r a : ℕ} (hr : 1 ≤ r) (hrp : r ≤ p - 1) :
    ‖(mu p r a : ℚ_[p]) + 1‖ = 1 := by
  have e : mu p r a + 1 = p * a + (p - r) := by
    have := mu_add_r (a := a) hr hrp; rw [mul_add, mul_one] at this; omega
  rw [← Nat.cast_add_one, e]
  refine norm_natCast_unit fun h => ?_
  have := (Nat.dvd_add_right (dvd_mul_right p a)).1 h
  have := Nat.le_of_dvd (by omega) this
  omega

lemma norm_natCast_add_one_unit {r : ℕ} (hrp : r + 1 ≤ p - 1) : ‖(r : ℚ_[p]) + 1‖ = 1 := by
  rw [← Nat.cast_add_one]
  refine norm_natCast_unit fun h => ?_
  have := Nat.le_of_dvd (by omega) h
  omega

omit [Fact p.Prime] in
lemma nu_eq_of_le {r r' a : ℕ} (hr : r ≤ p - 1) (hr' : r' ≤ p - 1) : nu p r' a = nu p r a := by
  unfold nu; by_cases ha : a = p - 1
  · rw [if_pos ⟨hr', ha⟩, if_pos ⟨hr, ha⟩]
  · rw [if_neg (fun h => ha h.2), if_neg (fun h => ha h.2)]

omit [Fact p.Prime] in
lemma glueHyp_of_le {r a : ℕ} (hr : 1 ≤ r) (hrp : r ≤ p - 1) (ha : a ≤ p - 1) : GlueHyp p r a :=
  ⟨hr, by omega, ha, by omega⟩

lemma xT_eq_xT {r r' a : ℕ} (hr : 1 ≤ r) (hr' : 1 ≤ r') (hrp : r ≤ p - 1) (hrp' : r' ≤ p - 1)
    (ha : a ≤ p - 1) : xT p r' a = xT p r a := by
  rw [xT_of_hyp (glueHyp_of_le hr' hrp' ha), xT_of_hyp (glueHyp_of_le hr hrp ha), xzero, xzero,
    nu_eq_of_le hrp hrp']

lemma norm_glue_cross {r a : ℕ} (hr : 1 ≤ r) (hrp : r ≤ p - 1) (ha : a ≤ p - 1) :
    ‖xT p r a * ((mu p r a : ℚ_[p]) + r + 1)‖ ≤ 1 := by
  rw [xT_of_hyp (glueHyp_of_le hr hrp ha)]
  have e : (mu p r a : ℚ_[p]) + r + 1 = ((p * (a + 1) : ℕ) : ℚ_[p]) := by
    rw [← mu_add_r (a := a) hr hrp]; push_cast; ring
  rw [e]
  refine norm_xzero_mul_natCast r a _ ?_
  unfold nu
  split_ifs with h
  · rw [h.2, Nat.sub_add_cancel (Fact.out : p.Prime).one_le, pow_two]
  · rw [pow_one]; exact dvd_mul_right p _

lemma xzero_ne_zero (r a : ℕ) : xzero p r a ≠ 0 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold xzero; exact zpow_ne_zero _ hp0

lemma ne_zero_of_norm_one {c : ℚ_[p]} (hc : ‖c‖ = 1) : c ≠ 0 := by
  intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc

/-! ### Identifying the pieces -/

/-- Stability of the glued lattice for a glue that is a unit multiple of `xT p r a`. -/
lemma glueOK_of_Tglue {r a L M r' : ℕ} {y : ℚ_[p]} (hL : lam p r a = L) (hM : mu p r a = M)
    (hr : r = r') (u : ℚ_[p]) (hu : ‖u‖ = 1) (hy : y = u * xT p r a) : GlueOK p L M r' y := by
  subst hL hM hr hy; exact glueOK_unit (glueOK_xT r a) u hu

/-- A glued lattice whose glue is a unit multiple of `xT p r a` is isomorphic to `Tglue p r a`. -/
lemma iso_Tglue_of {r a L M r' : ℕ} {y : ℚ_[p]} (h : GlueOK p L M r' y) (hL : lam p r a = L)
    (hM : mu p r a = M) (hr : r = r') (u : ℚ_[p]) (hu : ‖u‖ = 1) (hy : xT p r a = u * y) :
    Nonempty (Iso (glueDP p L M r' y h) (Tglue p r a)) :=
  glueIso_unit h (glueOK_xT r a) hL.symm hM.symm hr.symm u hu hy

/-- Shift `0`: the glued lattice is always stable. -/
theorem glueOK_shift0 (N : ℕ) (y : ℚ_[p]) : GlueOK p N N 0 y := by
  refine ⟨Or.inr (by ring), fun t v hv => ?_⟩
  rw [mem_Lx_iff] at hv
  have hv0 : Phi p N N 0 y v ∈ Lx p N N 0 0 := (mem_Lx_zero_iff 0 _).2 hv
  have hs := (glueOK_zero (p := p) (L := N) (M := N) 0).stab t _ hv0
  rw [mem_Lx_zero_iff, mem_Lx_zero_iff] at hs
  rw [mem_Lx_iff, mem_Lx_iff]
  constructor
  · rw [Fop_eq_blk, Phi_shift0_comm, ← Fop_eq_blk]; exact hs.1
  · rw [Eop_eq_blk, Phi_shift0_comm, ← Eop_eq_blk]; exact hs.2

/-- The first piece (shift `r + 1`) when `r + 1 ≤ p − 1`: it is `Tglue p (r + 1) a`. -/
lemma first_piece {r a : ℕ} (hr : 1 ≤ r) (hrp : r + 1 ≤ p - 1) (ha : a ≤ p - 1) :
    ∃ h1 : GlueOK p (lam p r a + 1) (mu p r a - 1) (r + 1)
        (-(xT p r a * ((r : ℚ_[p]) + 1) / ((mu p r a : ℚ_[p]) + 1))),
      Nonempty (Iso (glueDP p (lam p r a + 1) (mu p r a - 1) (r + 1)
        (-(xT p r a * ((r : ℚ_[p]) + 1) / ((mu p r a : ℚ_[p]) + 1))) h1) (Tglue p (r + 1) a)) := by
  have hM1 := norm_mu_add_one (a := a) hr (by omega : r ≤ p - 1)
  have hr1 := norm_natCast_add_one_unit (p := p) hrp
  have hM0 := ne_zero_of_norm_one hM1
  have hr0 := ne_zero_of_norm_one hr1
  set u : ℚ_[p] := -(((mu p r a : ℚ_[p]) + 1) / ((r : ℚ_[p]) + 1)) with hu_def
  have hu : ‖u‖ = 1 := by rw [hu_def, norm_neg, norm_div, hM1, hr1, div_one]
  have hu0 := ne_zero_of_norm_one hu
  have hxx := xT_eq_xT (a := a) hr (by omega : 1 ≤ r + 1) (by omega) hrp ha
  have hy : -(xT p r a * ((r : ℚ_[p]) + 1) / ((mu p r a : ℚ_[p]) + 1)) = u⁻¹ * xT p (r + 1) a := by
    rw [hxx, hu_def]; field_simp
  refine ⟨glueOK_of_Tglue (lam_succ r a) (mu_succ r a) rfl u⁻¹
    (by rw [norm_inv, hu, inv_one]) hy, ?_⟩
  exact iso_Tglue_of _ (lam_succ r a) (mu_succ r a) rfl u hu
    (by rw [hy, ← mul_assoc, mul_inv_cancel₀ hu0, one_mul])

/-- The second piece (shift `r − 1`) when `r ≥ 2`: it is `Tglue p (r − 1) a`. -/
lemma second_piece {r a : ℕ} (hr : 2 ≤ r) (hrp : r ≤ p - 1) (ha : a ≤ p - 1) :
    ∃ h2 : GlueOK p (lam p r a - 1) (mu p r a + 1) (r - 1) (-xT p r a),
      Nonempty (Iso (glueDP p (lam p r a - 1) (mu p r a + 1) (r - 1) (-xT p r a) h2)
        (Tglue p (r - 1) a)) := by
  have hxx := xT_eq_xT (a := a) (by omega : 1 ≤ r) (by omega : 1 ≤ r - 1) hrp (by omega) ha
  have hy : -xT p r a = (-1) * xT p (r - 1) a := by rw [hxx]; ring
  refine ⟨glueOK_of_Tglue (lam_pred a (by omega)) (mu_pred a (by omega) hrp) rfl (-1)
    (by simp) hy, ?_⟩
  exact iso_Tglue_of _ (lam_pred a (by omega)) (mu_pred a (by omega) hrp) rfl (-1) (by simp)
    (by rw [hy]; ring)

/-! ### (R2) -/

/-- **(R2)** (`CSG4_tensor_rules.md`, Part R, (R2)): for `GlueHyp p r a` and `2 ≤ r ≤ p − 2`,
`V ⊗ Tglue p r a ≅ Tglue p (r + 1) a ⊕ Tglue p (r − 1) a` as DP-lattices over `ℤ_[p]`.
(`GlueHyp p r a` is implied by `2 ≤ r ≤ p − 2` and `a ≤ p − 1`.) -/
theorem R2 {r a : ℕ} (h : GlueHyp p r a) (hr : 2 ≤ r) (hrp : r ≤ p - 2) :
    Nonempty (Iso (tensorV (Tglue p r a)) (dsum (Tglue p (r + 1) a) (Tglue p (r - 1) a))) := by
  have ha := h.2.2.1
  obtain ⟨h1, ⟨j1⟩⟩ := first_piece (r := r) (a := a) (by omega) (by omega) ha
  obtain ⟨h2, ⟨j2⟩⟩ := second_piece (a := a) hr (by omega) ha
  have hM : 1 ≤ mu p r a := by
    have := mu_add_r (a := a) (p := p) (r := r) (by omega) (by omega)
    have : p ≤ p * (a + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  obtain ⟨i⟩ := tensor_glue_split (lam_eq_mu (by omega)) (by omega) hM
    (norm_lam_add_one (by omega) (by omega)) (norm_mu_add_one (by omega) (by omega))
    (norm_glue_cross (by omega) (by omega) ha) (glueOK_xT r a) h1 h2
  exact ⟨i.symm.trans (Tensor2.dsumIso j1 j2)⟩

/-! ### (R1) -/

/-- **(R1)** (`CSG4_tensor_rules.md`, Part R, (R1)): for `p ≠ 2` and `GlueHyp p 1 a`,
`V ⊗ Tglue p 1 a ≅ Tglue p 2 a ⊕ (Δ(λ − 1) ⊕ Δ(λ − 1))` as DP-lattices over `ℤ_[p]`, with
`λ = lam p 1 a`. -/
theorem R1 (hp2 : p ≠ 2) {a : ℕ} (h : GlueHyp p 1 a) :
    Nonempty (Iso (tensorV (Tglue p 1 a)) (dsum (Tglue p 2 a)
      (dsum (delta ℤ_[p] (lam p 1 a - 1)) (delta ℤ_[p] (lam p 1 a - 1))))) := by
  have hp := (Fact.out : p.Prime).two_le
  have ha := h.2.2.1
  obtain ⟨h1, ⟨j1⟩⟩ := first_piece (a := a) le_rfl (by omega) ha
  have hLM := lam_eq_mu (p := p) (r := 1) (a := a) (by omega)
  have hM : 1 ≤ mu p 1 a := by
    have := mu_add_r (a := a) (p := p) (r := 1) le_rfl (by omega)
    have : p ≤ p * (a + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have e : lam p 1 a - 1 = mu p 1 a + 1 := by omega
  have h2 : GlueOK p (lam p 1 a - 1) (mu p 1 a + 1) (1 - 1) (-xT p 1 a) := by
    rw [e]; exact glueOK_shift0 _ _
  obtain ⟨j2⟩ := glueIso_shift0 h2 rfl e.symm
  obtain ⟨i⟩ := tensor_glue_split hLM le_rfl hM
    (norm_lam_add_one le_rfl (by omega)) (norm_mu_add_one le_rfl (by omega))
    (norm_glue_cross le_rfl (by omega) ha) (glueOK_xT 1 a) h1 h2
  exact ⟨i.symm.trans (Tensor2.dsumIso j1 j2)⟩

/-! ### (R3) -/

/-- **(R3), `a ≥ 1`** (`CSG4_tensor_rules.md`, Part R, (R3)): for `1 ≤ a ≤ p − 2`,
`V ⊗ Tglue p (p − 1) a ≅ Δ(λ + 1) ⊕ (Tglue p (p − 2) a ⊕ Δ(μ − 1))` as DP-lattices over `ℤ_[p]`,
with `λ = lam p (p − 1) a`, `μ = mu p (p − 1) a`.  (`GlueHyp p (p − 1) a` holds automatically, and
`1 ≤ a ≤ p − 2` forces `p ≥ 3`, so the hypothesis `p ≠ 2` of the file is not needed.) -/
theorem R3_pos {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ p - 2) :
    Nonempty (Iso (tensorV (Tglue p (p - 1) a)) (dsum (delta ℤ_[p] (lam p (p - 1) a + 1))
      (dsum (Tglue p (p - 2) a) (delta ℤ_[p] (mu p (p - 1) a - 1))))) := by
  have hp := (Fact.out : p.Prime).two_le
  have hp3 : 3 ≤ p := by omega
  have hrp : p - 1 ≤ p - 1 := le_rfl
  obtain ⟨h2, ⟨j2⟩⟩ := second_piece (a := a) (by omega) hrp (by omega)
  have hLM := lam_eq_mu (p := p) (r := p - 1) (a := a) hrp
  have hMr := mu_add_r (p := p) (r := p - 1) (a := a) (by omega) hrp
  have hM : 1 ≤ mu p (p - 1) a := by
    have : p * (a + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
    omega
  have hM1 := norm_mu_add_one (a := a) (by omega) hrp
  -- the first piece has an integral glue
  have hx0 : xT p (p - 1) a = (p : ℚ_[p])⁻¹ := by
    rw [xT_of_hyp (glueHyp_of_le (by omega) hrp (by omega)), xzero]
    unfold nu; rw [if_neg (by omega), Nat.cast_one, zpow_neg_one]
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hr1 : (((p - 1 : ℕ) : ℚ_[p]) + 1) = p := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel (by omega)]
  have hy1 : ‖-(xT p (p - 1) a * (((p - 1 : ℕ) : ℚ_[p]) + 1) / ((mu p (p - 1) a : ℚ_[p]) + 1))‖
      ≤ 1 := by
    rw [hx0, hr1, inv_mul_cancel₀ hp0, norm_neg, norm_div, hM1, norm_one, div_one]
  have h1 : GlueOK p (lam p (p - 1) a + 1) (mu p (p - 1) a - 1) (p - 1 + 1)
      (-(xT p (p - 1) a * (((p - 1 : ℕ) : ℚ_[p]) + 1) / ((mu p (p - 1) a : ℚ_[p]) + 1))) :=
    glueOK_int hy1 (Or.inr (by omega))
  obtain ⟨j1⟩ := glueIso_int h1 hy1 rfl rfl
  obtain ⟨i⟩ := tensor_glue_split hLM (by omega) hM
    (norm_lam_add_one (by omega) hrp) hM1
    (norm_glue_cross (by omega) hrp (by omega)) (glueOK_xT (p - 1) a) h1 h2
  have k : Iso (glueDP p (lam p (p - 1) a - 1) (mu p (p - 1) a + 1) (p - 1 - 1)
      (-xT p (p - 1) a) h2) (Tglue p (p - 2) a) := by
    rw [show p - 2 = p - 1 - 1 by omega]; exact j2
  exact ⟨((i.symm.trans (Tensor2.dsumIso j1 k)).trans (Lemma35b.dsumAssoc _ _ _)).trans
    (Tensor2.dsumIso (Lemma35b.Iso.refl _) (Lemma35b.dsumComm _ _))⟩

/-- **(R3), `a = 0`** (`CSG4_tensor_rules.md`, Part R, (R3)): for `p ≠ 2`,
`V ⊗ Tglue p (p − 1) 0 ≅ Δ(λ + 1) ⊕ Tglue p (p − 2) 0` as DP-lattices over `ℤ_[p]`, with
`λ = lam p (p − 1) 0` (here `μ = 0`). -/
theorem R3_zero (hp2 : p ≠ 2) :
    Nonempty (Iso (tensorV (Tglue p (p - 1) 0))
      (dsum (delta ℤ_[p] (lam p (p - 1) 0 + 1)) (Tglue p (p - 2) 0))) := by
  have hp := (Fact.out : p.Prime).two_le
  have hp3 : 3 ≤ p := by omega
  have hrp : p - 1 ≤ p - 1 := le_rfl
  have hmu0 : mu p (p - 1) 0 = 0 := by unfold mu lam; omega
  have hLr : lam p (p - 1) 0 = 2 * (p - 1) := by unfold lam; omega
  have h0 : GlueOK p (lam p (p - 1) 0) 0 (p - 1) (xT p (p - 1) 0) := by
    have := glueOK_xT (p := p) (p - 1) 0; rwa [hmu0] at this
  obtain ⟨c⟩ : Nonempty (Iso (Tglue p (p - 1) 0)
      (glueDP p (lam p (p - 1) 0) 0 (p - 1) (xT p (p - 1) 0) h0)) :=
    ⟨glueIso_cast (glueOK_xT (p - 1) 0) h0 rfl hmu0 rfl rfl⟩
  have hx0 : xT p (p - 1) 0 = (p : ℚ_[p])⁻¹ := by
    rw [xT_of_hyp (glueHyp_of_le (by omega) hrp (by omega)), xzero]
    unfold nu; rw [if_neg (by omega), Nat.cast_one, zpow_neg_one]
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hr1 : (((p - 1 : ℕ) : ℚ_[p]) + 1) = p := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel (by omega)]
  have hx : ‖xT p (p - 1) 0 * (((p - 1 : ℕ) : ℚ_[p]) + 1)‖ ≤ 1 := by
    rw [hx0, hr1, inv_mul_cancel₀ hp0, norm_one]
  -- the second piece
  have hxx := xT_eq_xT (p := p) (a := 0) (by omega : 1 ≤ p - 1) (by omega : 1 ≤ p - 2)
    hrp (by omega) (by omega)
  have hL2 : lam p (p - 2) 0 = lam p (p - 1) 0 - 1 := by unfold lam; omega
  have hM2 : mu p (p - 2) 0 = 1 := by unfold mu lam; omega
  have hy : -xT p (p - 1) 0 = (-1) * xT p (p - 2) 0 := by rw [hxx]; ring
  have h2 : GlueOK p (lam p (p - 1) 0 - 1) 1 (p - 1 - 1) (-xT p (p - 1) 0) :=
    glueOK_of_Tglue hL2 hM2 (by omega) (-1) (by simp) hy
  obtain ⟨j2⟩ := iso_Tglue_of h2 hL2 hM2 (by omega) (-1) (by simp) (by rw [hy]; ring)
  obtain ⟨i⟩ := tensor_glue_split0 hLr (by omega) (norm_lam_add_one (by omega) hrp) hx h0 h2
  exact ⟨((Tensor2.tensorVIso c).trans i.symm).trans
    (Tensor2.dsumIso (Lemma35b.Iso.refl _) j2)⟩

/-! ### (R4) -/

/-- **(R4)** (`CSG4_tensor_rules.md`, Part R, (R4)): for `p ≠ 2`,
`V ⊗ Tglue p (p − 1) (p − 1) ≅ Tglue p p (p − 1) ⊕ Tglue p (p − 2) (p − 1)` as DP-lattices over
`ℤ_[p]`. -/
theorem R4 (hp2 : p ≠ 2) :
    Nonempty (Iso (tensorV (Tglue p (p - 1) (p - 1)))
      (dsum (Tglue p p (p - 1)) (Tglue p (p - 2) (p - 1)))) := by
  have hp := (Fact.out : p.Prime).two_le
  have hp3 : 3 ≤ p := by omega
  have hrp : p - 1 ≤ p - 1 := le_rfl
  obtain ⟨h2, ⟨j2⟩⟩ := second_piece (a := p - 1) (by omega) hrp le_rfl
  have hLM := lam_eq_mu (p := p) (r := p - 1) (a := p - 1) hrp
  have hMr := mu_add_r (p := p) (r := p - 1) (a := p - 1) (by omega) hrp
  have hM : 1 ≤ mu p (p - 1) (p - 1) := by
    have : p * (p - 1 + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
    omega
  have hM1 := norm_mu_add_one (a := p - 1) (by omega) hrp
  have hM0 := ne_zero_of_norm_one hM1
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : xT p (p - 1) (p - 1) = ((p : ℚ_[p]) ^ 2)⁻¹ := by
    rw [xT_of_hyp (glueHyp_of_le (by omega) hrp le_rfl), xzero]
    unfold nu; rw [if_pos ⟨le_rfl, rfl⟩, zpow_neg, Nat.cast_ofNat]; norm_cast
  have hx1 : xT p p (p - 1) = (p : ℚ_[p])⁻¹ := by
    rw [xT_of_hyp ⟨by omega, le_rfl, le_rfl, fun _ => rfl⟩, xzero]
    unfold nu; rw [if_neg (by omega), Nat.cast_one, zpow_neg_one]
  have hr1 : (((p - 1 : ℕ) : ℚ_[p]) + 1) = p := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel (by omega)]
  set u : ℚ_[p] := -((mu p (p - 1) (p - 1) : ℚ_[p]) + 1) with hu_def
  have hu : ‖u‖ = 1 := by rw [hu_def, norm_neg, hM1]
  have hu0 := ne_zero_of_norm_one hu
  have hy : -(xT p (p - 1) (p - 1) * (((p - 1 : ℕ) : ℚ_[p]) + 1) /
      ((mu p (p - 1) (p - 1) : ℚ_[p]) + 1)) = u⁻¹ * xT p (p - 1 + 1) (p - 1) := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ p), hx0, hx1, hr1, hu_def]
    field_simp
  have hpp : p = p - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ p)).symm
  have hl : lam p p (p - 1) = lam p (p - 1) (p - 1) + 1 := by
    rw [← lam_succ]; congr 1
  have hm : mu p p (p - 1) = mu p (p - 1) (p - 1) - 1 := by
    rw [← mu_succ]; congr 1
  have hy' : -(xT p (p - 1) (p - 1) * (((p - 1 : ℕ) : ℚ_[p]) + 1) /
      ((mu p (p - 1) (p - 1) : ℚ_[p]) + 1)) = u⁻¹ * xT p p (p - 1) := by
    rw [hy, ← hpp]
  have h1 := glueOK_of_Tglue hl hm hpp u⁻¹ (by rw [norm_inv, hu, inv_one]) hy'
  obtain ⟨k1⟩ := iso_Tglue_of h1 hl hm hpp u hu
    (by rw [hy', ← mul_assoc, mul_inv_cancel₀ hu0, one_mul])
  obtain ⟨i⟩ := tensor_glue_split hLM (by omega) hM
    (norm_lam_add_one (by omega) hrp) hM1
    (norm_glue_cross (by omega) hrp le_rfl) (glueOK_xT (p - 1) (p - 1)) h1 h2
  have k2 : Iso (glueDP p (lam p (p - 1) (p - 1) - 1) (mu p (p - 1) (p - 1) + 1) (p - 1 - 1)
      (-xT p (p - 1) (p - 1)) h2) (Tglue p (p - 2) (p - 1)) := by
    rw [show p - 2 = p - 1 - 1 by omega]; exact j2
  exact ⟨i.symm.trans (Tensor2.dsumIso k1 k2)⟩

end ColouredSand.TiltRules
