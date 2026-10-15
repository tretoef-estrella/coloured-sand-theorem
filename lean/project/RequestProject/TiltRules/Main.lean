module

public import RequestProject.TiltRules.Slices

/-!
# The splitting `V ⊗ glueDP ≅ glueDP ⊕ glueDP` (`CSG4_tensor_rules.md`, §3, Steps 2–3, `M ≥ 1`)

Let `L = M + 2 r`, `r ≥ 1`, `M ≥ 1`, and let `x ∈ ℚ_[p]` be such that `Lx p L M r x` is stable.
Assume that `L + 1` and `M + 1` are `p`-adic units and that `x (M + r + 1)` is integral
(in the application `M + r + 1 = (a + 1) p` and `x = x₀ = p^{−ν}`, §3, Step 3).  Then
(`tensor_glue_split`)

  `glueDP (L + 1) (M − 1) (r + 1) y₁ ⊕ glueDP (L − 1) (M + 1) (r − 1) (−x) ≅ V ⊗ glueDP L M r x`

as DP-lattices over `ℤ_[p]`, with `y₁ = −x (r + 1)/(M + 1)`.  This is the splitting
`L = (L ∩ (A ⊕ D)) ⊕ (L ∩ (B ⊕ C))` of §3, Step 3: the first summand is the glued lattice of
`A ⊕ D = Δ(λ + 1) ⊕ Δ(μ − 1)` (shift `r + 1`), the second the glued lattice of
`B ⊕ C = Δ(λ − 1) ⊕ Δ(μ + 1)` (shift `r − 1`, glue `−x`).  (With the normalisation `D_j = DV j`
used here the glue of the first summand is `y₁`, which differs from the file's `x₀ κ_DA` by an
integral amount; only its valuation matters.)

## Proof

`psiW` (from `RequestProject/TiltRules/Split.lean`) intertwines the operators; by `lat_of_gen` it
remains to check that the generators `ℓ_0, s̃_0` of both summands are mapped into
`V ⊗ Lx p L M r x` (`img_*`), and that the generators `b_ε ⊗ ℓ_0`, `b_ε ⊗ s̃_0` of
`V ⊗ Lx p L M r x` are images of lattice vectors (`pre_*`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltRules

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP

variable {p : ℕ} [Fact p.Prime]

lemma mem_Lx_comb {L M r : ℕ} {x a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (j k : ℕ) :
    a • stilde p L M r x j + b • ell p L M k ∈ Lx p L M r x :=
  Submodule.add_mem _ (smul_mem_of_norm ha (stilde_mem_Lx r x j))
    (smul_mem_of_norm hb (ell_mem_Lx r x k))

lemma norm_one_div_unit {c : ℚ_[p]} (hc : ‖c‖ = 1) : ‖1 / c‖ = 1 := by
  rw [norm_div_unit hc, norm_one]

section checks

variable {L M r : ℕ} {x : ℚ_[p]}

/-! ### Images of the generators of the two summands -/

lemma img_A0 (hL : 1 ≤ L) (hM : 1 ≤ M) :
    slice 0 (psiW p L M hL hM (inlL (ell p (L + 1) (M - 1) 0))) ∈ Lx p L M r x ∧
      slice 1 (psiW p L M hL hM (inlL (ell p (L + 1) (M - 1) 0))) ∈ Lx p L M r x := by
  rw [psiW_A, slice0_AV, slice1_AV, if_neg (by omega)]
  exact ⟨ell_mem_Lx r x 0, Submodule.zero_mem _⟩

lemma img_A1 (hL : 1 ≤ L) (hM : 1 ≤ M) (hM1 : ‖(M : ℚ_[p]) + 1‖ = 1)
    (hx : ‖x * ((M : ℚ_[p]) + r + 1)‖ ≤ 1) :
    slice 0 (psiW p L M hL hM (inlL (stilde p (L + 1) (M - 1) (r + 1)
        (-(x * ((r : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1))) 0))) ∈ Lx p L M r x ∧
      slice 1 (psiW p L M hL hM (inlL (stilde p (L + 1) (M - 1) (r + 1)
        (-(x * ((r : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1))) 0))) ∈ Lx p L M r x := by
  rw [stilde_zero', map_add, map_smul, map_add, map_smul, psiW_D, psiW_A]
  simp only [map_add, map_smul, slice0_DV, slice1_DV, slice0_AV, slice1_AV,
    if_pos (show 1 ≤ r + 1 by omega), Nat.add_sub_cancel, Nat.cast_zero, zero_add, sub_zero]
  constructor
  · have e : (-(1 / ((M : ℚ_[p]) + 1))) • ess p L M 1 +
        (-(x * ((r : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1))) • ell p L M (r + 1) =
        (-(1 / ((M : ℚ_[p]) + 1))) • stilde p L M r x 1 + (0 : ℚ_[p]) • ell p L M 0 := by
      rw [stilde_one' r x hM]; module
    rw [e]
    exact mem_Lx_comb (by rw [norm_neg, norm_one_div_unit hM1]) (by simp) 1 0
  · have e : ((M : ℚ_[p]) / ((M : ℚ_[p]) + 1)) • ess p L M 0 +
        (-(x * ((r : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1))) • ell p L M r =
        ((M : ℚ_[p]) / ((M : ℚ_[p]) + 1)) • stilde p L M r x 0 +
          (-(x * ((M : ℚ_[p]) + r + 1) / ((M : ℚ_[p]) + 1))) • ell p L M r := by
      rw [stilde_zero']; module
    rw [e]
    exact mem_Lx_comb (by rw [norm_div_unit hM1]; exact norm_natCast_le M)
      (by rw [norm_neg, norm_div_unit hM1]; exact hx) 0 r

lemma img_B0v (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) :
    slice 0 (BV p L M 0) ∈ Lx p L M r x ∧ slice 1 (BV p L M 0) ∈ Lx p L M r x := by
  rw [slice0_BV, slice1_BV]
  refine ⟨smul_mem_of_norm ?_ (ell_mem_Lx r x _), smul_mem_of_norm ?_ (ell_mem_Lx r x _)⟩
  · rw [norm_neg, norm_div_unit hL1]; simp
  · rw [norm_div_unit hL1]; simpa using norm_natCast_le (p := p) L

lemma img_B0 (hL : 1 ≤ L) (hM : 1 ≤ M) (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) :
    slice 0 (psiW p L M hL hM (inrL (ell p (L - 1) (M + 1) 0))) ∈ Lx p L M r x ∧
      slice 1 (psiW p L M hL hM (inrL (ell p (L - 1) (M + 1) 0))) ∈ Lx p L M r x := by
  rw [psiW_B]; exact img_B0v hL1

lemma img_B1v (hLM : L = M + 2 * r) (hr : 1 ≤ r)
    (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) (hx : ‖x * ((M : ℚ_[p]) + r + 1)‖ ≤ 1) :
    slice 0 (CV p L M 0 + (-x) • BV p L M (r - 1)) ∈ Lx p L M r x ∧
      slice 1 (CV p L M 0 + (-x) • BV p L M (r - 1)) ∈ Lx p L M r x := by
  have hL0 : (L : ℚ_[p]) + 1 ≠ 0 := by intro h; rw [h, norm_zero] at hL1; exact zero_ne_one hL1
  have hLc : (L : ℚ_[p]) = M + 2 * r := by rw [hLM]; push_cast; ring
  have hrc : ((r - 1 : ℕ) : ℚ_[p]) = r - 1 := by rw [Nat.cast_sub hr]; simp
  have hr' : r - 1 + 1 = r := by omega
  simp only [map_add, map_smul, slice0_CV, slice1_CV, slice0_BV, slice1_BV, hr', hrc,
    if_neg (show ¬ 1 ≤ 0 by omega), zero_add]
  constructor
  · have e : ess p L M 0 + (-x) • (-(((r : ℚ_[p]) - 1 + 1) / ((L : ℚ_[p]) + 1))) • ell p L M r =
        (1 : ℚ_[p]) • stilde p L M r x 0 + (x * r / ((L : ℚ_[p]) + 1) - x) • ell p L M r := by
      rw [stilde_zero']; module
    have hs : x * r / ((L : ℚ_[p]) + 1) - x = -(x * ((M : ℚ_[p]) + r + 1) / ((L : ℚ_[p]) + 1)) := by
      field_simp; rw [hLc]; ring
    rw [e, hs]
    exact mem_Lx_comb (by simp) (by rw [norm_neg, norm_div_unit hL1]; exact hx) 0 r
  · have hs : -x * (((L : ℚ_[p]) - ((r : ℚ_[p]) - 1)) / ((L : ℚ_[p]) + 1)) =
        -(x * ((M : ℚ_[p]) + r + 1) / ((L : ℚ_[p]) + 1)) := by
      field_simp; rw [hLc]; ring
    rw [smul_smul, hs]
    exact smul_mem_of_norm (by rw [norm_neg, norm_div_unit hL1]; exact hx) (ell_mem_Lx r x _)

lemma img_B1 (hLM : L = M + 2 * r) (hr : 1 ≤ r) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) (hx : ‖x * ((M : ℚ_[p]) + r + 1)‖ ≤ 1) :
    slice 0 (psiW p L M hL hM (inrL (stilde p (L - 1) (M + 1) (r - 1) (-x) 0))) ∈ Lx p L M r x ∧
      slice 1 (psiW p L M hL hM (inrL (stilde p (L - 1) (M + 1) (r - 1) (-x) 0))) ∈
        Lx p L M r x := by
  rw [stilde_zero', map_add, map_smul, map_add, map_smul, psiW_C, psiW_B]
  exact img_B1v hLM hr hL1 hx

/-! ### The generators of `V ⊗ Lx p L M r x` are images of lattice vectors -/

lemma pre_00 (hL : 1 ≤ L) (hM : 1 ≤ M) :
    psiW p L M hL hM (Sum.elim (ell p (L + 1) (M - 1) 0) 0) = bvec 0 (ell p L M 0) := by
  rw [Sum_elim_eq, map_zero, map_add, map_zero, add_zero, psiW_A]
  unfold AV; rw [if_neg (by omega), add_zero]

lemma pre_10v (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) :
    (1 / ((L : ℚ_[p]) + 1)) • AV p L M 1 + BV p L M 0 = bvec 1 (ell p L M 0) := by
  have hL0 : (L : ℚ_[p]) + 1 ≠ 0 := by intro h; rw [h, norm_zero] at hL1; exact zero_ne_one hL1
  apply ext_slice
  · simp only [map_add, map_smul, slice0_AV, slice0_BV, slice0_bvec1, Nat.cast_zero, zero_add]
    module
  · simp only [map_add, map_smul, slice1_AV, slice1_BV, slice_bvec_self, if_pos le_rfl,
      Nat.sub_self, Nat.cast_zero, sub_zero]
    rw [← add_smul]
    conv_rhs => rw [← one_smul ℚ_[p] (ell p L M 0)]
    congr 1; field_simp; ring

lemma pre_01v (hLM : L = M + 2 * r) (hr : 1 ≤ r) (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) :
    (x * ((M : ℚ_[p]) + r + 1) / ((L : ℚ_[p]) + 1)) • AV p L M r +
      (CV p L M 0 + (-x) • BV p L M (r - 1)) = bvec 0 (stilde p L M r x 0) := by
  have hL0 : (L : ℚ_[p]) + 1 ≠ 0 := by intro h; rw [h, norm_zero] at hL1; exact zero_ne_one hL1
  have hLc : (L : ℚ_[p]) = M + 2 * r := by rw [hLM]; push_cast; ring
  have hrc : ((r - 1 : ℕ) : ℚ_[p]) = r - 1 := by rw [Nat.cast_sub hr]; simp
  have hr' : r - 1 + 1 = r := by omega
  apply ext_slice
  · simp only [map_add, map_smul, slice0_AV, slice0_CV, slice0_BV, slice_bvec_self, hr', hrc]
    rw [stilde_zero']
    have h2 : (M : ℚ_[p]) + r + 1 + ((r : ℚ_[p]) - 1 + 1) = L + 1 := by rw [hLc]; ring
    have hs : x * ((M : ℚ_[p]) + r + 1) / ((L : ℚ_[p]) + 1) +
        -x * -(((r : ℚ_[p]) - 1 + 1) / ((L : ℚ_[p]) + 1)) = x := by
      calc _ = x * (((M : ℚ_[p]) + r + 1) + ((r : ℚ_[p]) - 1 + 1)) / ((L : ℚ_[p]) + 1) := by ring
        _ = x := by rw [h2, mul_div_assoc, div_self hL0, mul_one]
    match_scalars
    · linear_combination hs
    · ring
  · simp only [map_add, map_smul, slice1_AV, slice1_CV, slice1_BV, slice1_bvec0, hrc,
      if_pos hr, if_neg (show ¬ 1 ≤ 0 by omega), zero_add]
    match_scalars
    simp only [hLc] at hL0 ⊢; field_simp; ring

lemma pre_10 (hL : 1 ≤ L) (hM : 1 ≤ M) (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) :
    psiW p L M hL hM (Sum.elim ((1 / ((L : ℚ_[p]) + 1)) • ell p (L + 1) (M - 1) 1)
      (ell p (L - 1) (M + 1) 0)) = bvec 1 (ell p L M 0) := by
  rw [Sum_elim_eq, map_smul, map_add, map_smul, psiW_A, psiW_B]
  exact pre_10v hL1

lemma pre_01 (hLM : L = M + 2 * r) (hr : 1 ≤ r) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) :
    psiW p L M hL hM (Sum.elim ((x * ((M : ℚ_[p]) + r + 1) / ((L : ℚ_[p]) + 1)) •
      ell p (L + 1) (M - 1) r) (stilde p (L - 1) (M + 1) (r - 1) (-x) 0)) =
        bvec 0 (stilde p L M r x 0) := by
  rw [← pre_01v hLM hr hL1, Sum_elim_eq, stilde_zero']
  simp only [map_add, map_smul, psiW_A, psiW_B, psiW_C]

lemma pre_11 (hL : 1 ≤ L) (hM : 1 ≤ M)
    (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) (hM1 : ‖(M : ℚ_[p]) + 1‖ = 1) :
    psiW p L M hL hM (Sum.elim (ess p (L + 1) (M - 1) 0 +
        (x * ((r : ℚ_[p]) + 1) / ((L : ℚ_[p]) + 1)) • ell p (L + 1) (M - 1) (r + 1))
      ((1 / ((M : ℚ_[p]) + 1)) • ess p (L - 1) (M + 1) 1 + x • ell p (L - 1) (M + 1) r)) =
        bvec 1 (stilde p L M r x 0) := by
  have hL0 : (L : ℚ_[p]) + 1 ≠ 0 := by intro h; rw [h, norm_zero] at hL1; exact zero_ne_one hL1
  have hM0 : (M : ℚ_[p]) + 1 ≠ 0 := by intro h; rw [h, norm_zero] at hM1; exact zero_ne_one hM1
  rw [Sum_elim_eq]
  simp only [map_add, map_smul, psiW_A, psiW_B, psiW_C, psiW_D]
  apply ext_slice
  · simp only [map_add, map_smul, slice0_AV, slice0_CV, slice0_BV, slice0_DV, slice0_bvec1,
      Nat.cast_zero, zero_add]
    module
  · simp only [map_add, map_smul, slice1_AV, slice1_CV, slice1_BV, slice1_DV, slice_bvec_self,
      if_pos (show 1 ≤ r + 1 by omega), if_pos (le_refl 1), Nat.add_sub_cancel, Nat.sub_self,
      Nat.cast_zero, sub_zero]
    rw [stilde_zero']
    match_scalars <;> field_simp
    ring

/-! ### Lattice membership of the preimages -/

lemma mem_11a (hLM : L = M + 2 * r) (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) (hM1 : ‖(M : ℚ_[p]) + 1‖ = 1)
    (hx : ‖x * ((M : ℚ_[p]) + r + 1)‖ ≤ 1) :
    ess p (L + 1) (M - 1) 0 + (x * ((r : ℚ_[p]) + 1) / ((L : ℚ_[p]) + 1)) •
      ell p (L + 1) (M - 1) (r + 1) ∈
        Lx p (L + 1) (M - 1) (r + 1) (-(x * ((r : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1))) := by
  have hL0 : (L : ℚ_[p]) + 1 ≠ 0 := by intro h; rw [h, norm_zero] at hL1; exact zero_ne_one hL1
  have hM0 : (M : ℚ_[p]) + 1 ≠ 0 := by intro h; rw [h, norm_zero] at hM1; exact zero_ne_one hM1
  have hLc : (L : ℚ_[p]) = M + 2 * r := by rw [hLM]; push_cast; ring
  have e : ess p (L + 1) (M - 1) 0 + (x * ((r : ℚ_[p]) + 1) / ((L : ℚ_[p]) + 1)) •
      ell p (L + 1) (M - 1) (r + 1) =
      (1 : ℚ_[p]) • stilde p (L + 1) (M - 1) (r + 1)
        (-(x * ((r : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1))) 0 +
      (x * ((r : ℚ_[p]) + 1) / ((L : ℚ_[p]) + 1) + x * ((r : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1)) •
        ell p (L + 1) (M - 1) (r + 1) := by
    rw [stilde_zero']; module
  have h2 : (M : ℚ_[p]) + 1 + ((L : ℚ_[p]) + 1) = 2 * ((M : ℚ_[p]) + r + 1) := by
    rw [hLc]; ring
  have hs : x * ((r : ℚ_[p]) + 1) / ((L : ℚ_[p]) + 1) + x * ((r : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1) =
      (2 * ((r : ℚ_[p]) + 1)) * (x * ((M : ℚ_[p]) + r + 1)) / (((L : ℚ_[p]) + 1) * ((M : ℚ_[p]) + 1)) := by
    rw [div_add_div _ _ hL0 hM0]
    congr 1
    linear_combination (x * ((r : ℚ_[p]) + 1)) * h2
  rw [e, hs]
  refine mem_Lx_comb (by simp) ?_ 0 (r + 1)
  rw [norm_div_unit (by rw [norm_mul, hL1, hM1, one_mul]), norm_mul]
  refine mul_le_one₀ ?_ (norm_nonneg _) hx
  rw [norm_mul]
  refine mul_le_one₀ ?_ (norm_nonneg _) ?_
  · exact_mod_cast norm_natCast_le (p := p) 2
  · exact_mod_cast norm_natCast_le (p := p) (r + 1)

lemma mem_11b (hr : 1 ≤ r) (hM1 : ‖(M : ℚ_[p]) + 1‖ = 1)
    (hx : ‖x * ((M : ℚ_[p]) + r + 1)‖ ≤ 1) :
    (1 / ((M : ℚ_[p]) + 1)) • ess p (L - 1) (M + 1) 1 + x • ell p (L - 1) (M + 1) r ∈
      Lx p (L - 1) (M + 1) (r - 1) (-x) := by
  have hM0 : (M : ℚ_[p]) + 1 ≠ 0 := by intro h; rw [h, norm_zero] at hM1; exact zero_ne_one hM1
  have hrc : ((r - 1 : ℕ) : ℚ_[p]) = r - 1 := by rw [Nat.cast_sub hr]; simp
  have hr' : r - 1 + 1 = r := by omega
  have e : (1 / ((M : ℚ_[p]) + 1)) • ess p (L - 1) (M + 1) 1 + x • ell p (L - 1) (M + 1) r =
      (1 / ((M : ℚ_[p]) + 1)) • stilde p (L - 1) (M + 1) (r - 1) (-x) 1 +
        (x * ((M : ℚ_[p]) + r + 1) / ((M : ℚ_[p]) + 1)) • ell p (L - 1) (M + 1) r := by
    rw [stilde_one' _ _ (by omega), hr', hrc]
    match_scalars
    · ring
    · field_simp; ring
  rw [e]
  exact mem_Lx_comb (norm_one_div_unit hM1).le (by rw [norm_div_unit hM1]; exact hx) 1 r

end checks

/-- **The splitting** (`CSG4_tensor_rules.md`, §3, Steps 1–3, for `μ ≥ 1`).  Let `L = M + 2 r`,
`r ≥ 1`, `M ≥ 1`, with `L + 1`, `M + 1` units of `ℤ_[p]` and `x (M + r + 1)` integral.  Then
`glueDP (L + 1) (M − 1) (r + 1) (−x (r + 1)/(M + 1)) ⊕ glueDP (L − 1) (M + 1) (r − 1) (−x)`
is isomorphic to `V ⊗ glueDP L M r x` as DP-lattices over `ℤ_[p]`. -/
theorem tensor_glue_split {L M r : ℕ} {x : ℚ_[p]} (hLM : L = M + 2 * r) (hr : 1 ≤ r)
    (hM : 1 ≤ M) (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) (hM1 : ‖(M : ℚ_[p]) + 1‖ = 1)
    (hx : ‖x * ((M : ℚ_[p]) + r + 1)‖ ≤ 1) (h : GlueOK p L M r x)
    (h1 : GlueOK p (L + 1) (M - 1) (r + 1) (-(x * ((r : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1))))
    (h2 : GlueOK p (L - 1) (M + 1) (r - 1) (-x)) :
    Nonempty (Iso (dsum (glueDP p (L + 1) (M - 1) (r + 1)
        (-(x * ((r : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1))) h1)
      (glueDP p (L - 1) (M + 1) (r - 1) (-x) h2)) (tensorV (glueDP p L M r x h))) := by
  have hL : 1 ≤ L := by omega
  set U := untwDsum (untwGlue p (L + 1) (M - 1) (r + 1)
    (-(x * ((r : ℚ_[p]) + 1) / ((M : ℚ_[p]) + 1))) h1) (untwGlue p (L - 1) (M + 1) (r - 1) (-x) h2)
  set W := untwTensor (untwGlue p L M r x h)
  refine iso_of_untw U W (psiW p L M hL hM) (fun t z => psiW_F hL hM t z)
    (fun t z => psiW_E hL hM t z) ?_
  refine lat_of_gen (psiW p L M hL hM) (fun t z => psiW_F hL hM t z) W.stabF U.stabF
    (isGen_dsum (isGen_glue (L + 1) (M - 1) (r + 1) _ (by omega))
      (isGen_glue (L - 1) (M + 1) (r - 1) (-x) (by omega)))
    (isGen_tensor (isGen_glue L M r x hLM)) ?_ ?_
  · rintro (i | i) <;> fin_cases i
    · exact img_A0 hL hM
    · exact img_A1 hL hM hM1 hx
    · exact img_B0 hL hM hL1
    · exact img_B1 hLM hr hL hM hL1 hx
  · rintro ⟨e, i⟩; fin_cases e <;> fin_cases i
    · refine ⟨Sum.elim (ell p (L + 1) (M - 1) 0) 0, ?_, ?_⟩
      · exact (mem_untwDsum _ _ _).2 ⟨ell_mem_Lx _ _ 0, Submodule.zero_mem _⟩
      · rw [pre_00 hL hM]; rfl
    · refine ⟨Sum.elim ((x * ((M : ℚ_[p]) + r + 1) / ((L : ℚ_[p]) + 1)) • ell p (L + 1) (M - 1) r)
        (stilde p (L - 1) (M + 1) (r - 1) (-x) 0), ?_, ?_⟩
      · exact (mem_untwDsum _ _ _).2
          ⟨smul_mem_of_norm (by rw [norm_div_unit hL1]; exact hx) (ell_mem_Lx _ _ _),
            stilde_mem_Lx _ _ 0⟩
      · rw [pre_01 hLM hr hL hM hL1]; rfl
    · refine ⟨Sum.elim ((1 / ((L : ℚ_[p]) + 1)) • ell p (L + 1) (M - 1) 1)
        (ell p (L - 1) (M + 1) 0), ?_, ?_⟩
      · exact (mem_untwDsum _ _ _).2
          ⟨smul_mem_of_norm (norm_one_div_unit hL1).le (ell_mem_Lx _ _ 1), ell_mem_Lx _ _ 0⟩
      · rw [pre_10 hL hM hL1]; rfl
    · refine ⟨Sum.elim (ess p (L + 1) (M - 1) 0 +
        (x * ((r : ℚ_[p]) + 1) / ((L : ℚ_[p]) + 1)) • ell p (L + 1) (M - 1) (r + 1))
        ((1 / ((M : ℚ_[p]) + 1)) • ess p (L - 1) (M + 1) 1 + x • ell p (L - 1) (M + 1) r), ?_, ?_⟩
      · exact (mem_untwDsum _ _ _).2 ⟨mem_11a hLM hL1 hM1 hx, mem_11b hr hM1 hx⟩
      · rw [pre_11 hL hM hL1 hM1]; rfl

end ColouredSand.TiltRules
