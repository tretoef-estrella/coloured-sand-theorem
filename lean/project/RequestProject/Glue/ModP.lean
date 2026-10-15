module

public import RequestProject.Glue.Stability

/-!
# (G3) Split versus non-split modulo `p` (CSG2, §1 (G3) and §2 "*(G3)*")

`p • Lx x` is the pointwise scalar multiple `(p : ℤ_[p]) • Lx x` of the submodule `Lx x`
(Mathlib's `Pointwise` action on submodules).

* `G3a_split`: if `‖x‖ < p^ν`, then for every `t` and every `j ≤ μ`,
  `E t (s̃ x j) − C(μ−j+t, t) • s̃ x (j−t) ∈ p • Lx x` (the second term only if `t ≤ j`) and
  `F t (s̃ x j) − C(j+t, t) • s̃ x (j+t) ∈ p • Lx x` (`s̃ x (j+t) = 0` if `j + t > μ`, by the
  convention of `stilde`).  (The document asks this for `t ≥ 1`; the proof works for every `t`,
  so the hypothesis `1 ≤ t` is dropped — a slightly more general statement.)
* `G3b_nonsplit`: if `‖x‖ = p^ν`, then for every `w ∈ Lx x` with `P μ w = w` and
  `w (inr 0) = 1` there is `t` with `1 ≤ t ≤ r` and `E t w ∉ p • Lx x`.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ColouredSand.Glue

open ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime] {L M : ℕ}

lemma p_pos_real : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos

lemma one_lt_p_real : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

/-- A vector of `p • Lx x` has untwisted coordinates of norm `≤ p⁻¹`. -/
lemma norm_Phi_le_of_mem_pLx (r : ℕ) (x : ℚ_[p]) {v : V p L M}
    (hv : v ∈ (p : ℤ_[p]) • Lx p L M r x) (y : Idx L M) :
    ‖Phi p L M r x v y‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
  rw [LinearMap.map_smul_of_tower, padic_smul_apply, norm_mul]
  have h1 := (mem_Lx_iff r x b).1 hb y
  have h2 : ‖((p : ℤ_[p]) : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [PadicInt.coe_natCast]; exact Padic.norm_p
  rw [h2]
  calc (p : ℝ)⁻¹ * ‖Phi p L M r x b y‖ ≤ (p : ℝ)⁻¹ * 1 := by
        gcongr
    _ = (p : ℝ)⁻¹ := mul_one _

/-- `z • ℓ_i ∈ p • Lx x` as soon as `‖z‖ ≤ p⁻¹`. -/
lemma smul_ell_mem_pLx (r : ℕ) (x z : ℚ_[p]) (hz : ‖z‖ ≤ (p : ℝ)⁻¹) (i : ℕ) :
    z • ell p L M i ∈ (p : ℤ_[p]) • Lx p L M r x := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨(z / p) • ell p L M i, smul_ell_mem r x _ ?_ i, ?_⟩
  · rw [norm_div, Padic.norm_p, div_le_one (by simpa using p_pos_real (p := p))]
    simpa using hz
  · rw [padic_smul_vec, smul_smul, PadicInt.coe_natCast, mul_div_cancel₀ _ hp0]

lemma norm_le_zpow_pred {x : ℚ_[p]} {n : ℕ} (hx : ‖x‖ < (p : ℝ) ^ n) :
    ‖x‖ ≤ (p : ℝ) ^ ((n : ℤ) - 1) := by
  by_cases h0 : x = 0
  · rw [h0, norm_zero]; exact (zpow_pos p_pos_real _).le
  rw [Padic.norm_eq_zpow_neg_valuation h0] at hx ⊢
  rw [← zpow_natCast, zpow_lt_zpow_iff_right₀ one_lt_p_real] at hx
  exact zpow_le_zpow_right₀ one_lt_p_real.le (by omega)

lemma norm_mul_le_inv_p {x : ℚ_[p]} {n : ℕ} (hx : ‖x‖ < (p : ℝ) ^ n) {k : ℤ}
    (hk : ((p : ℤ) ^ n) ∣ k) : ‖x * (k : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  rw [norm_mul]
  have hp := p_pos_real (p := p)
  calc ‖x‖ * ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ ((n : ℤ) - 1) * (p : ℝ) ^ (-(n : ℤ)) :=
        mul_le_mul (norm_le_zpow_pred hx) (norm_int_le_of_dvd hk) (norm_nonneg _) (by positivity)
    _ = (p : ℝ)⁻¹ := by
      rw [← zpow_add₀ hp.ne', show (n : ℤ) - 1 + -(n : ℤ) = -1 by ring, zpow_neg_one]

/-- **(G3)(a) Split case.**  If `‖x‖ < p^ν`, the images of the `s̃ x j` span a stable piece
modulo `p`: for every `t` (in particular every `t ≥ 1`) and every `j ≤ μ`,
`E t (s̃ x j) − C(μ−j+t, t) • s̃ x (j−t) ∈ p • Lx x` (second term only when `t ≤ j`) and
`F t (s̃ x j) − C(j+t, t) • s̃ x (j+t) ∈ p • Lx x` (`s̃ x (j+t) = 0` when `j + t > μ`). -/
theorem G3a_split {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (x : ℚ_[p]) (hx : ‖x‖ < (p : ℝ) ^ nu p r a)
    (t : ℕ) (j : ℕ) (hj : j ≤ mu p r a) :
    Eop p (lam p r a) (mu p r a) t (stilde p (lam p r a) (mu p r a) r x j) -
        (if t ≤ j then ((mu p r a - j + t).choose t : ℚ_[p]) •
          stilde p (lam p r a) (mu p r a) r x (j - t) else 0) ∈
        (p : ℤ_[p]) • Lx p (lam p r a) (mu p r a) r x ∧
      Fop p (lam p r a) (mu p r a) t (stilde p (lam p r a) (mu p r a) r x j) -
          ((j + t).choose t : ℚ_[p]) • stilde p (lam p r a) (mu p r a) r x (j + t) ∈
        (p : ℤ_[p]) • Lx p (lam p r a) (mu p r a) r x := by
  have hLM := lam_eq_mu_add (p := p) r a hrp hra
  constructor
  · rw [E_stilde r hLM x t j hj, add_sub_cancel_left]
    apply smul_ell_mem_pLx
    apply norm_mul_le_inv_p hx
    exact_mod_cast dvd_betaE hLM (p ^ nu p r a)
      (fun m hm1 hmr => pow_nu_dvd_link hr1 hrp ha hra m hm1 hmr) (t := t) hj
  · rw [F_stilde r hLM x t j hj, add_sub_cancel_left]
    apply smul_ell_mem_pLx
    apply norm_mul_le_inv_p hx
    exact_mod_cast dvd_betaF hLM (p ^ nu p r a)
      (fun s hs1 hs2 => pow_nu_dvd_tail hr1 hrp ha hra s hs1 hs2) (j := j) (t := t)

/-- A vector of weight `μ` is `w(inr 0) • s₀ + w(inl r) • ℓ_r` (`λ = μ + 2r`). -/
lemma weight_mu_vector (r : ℕ) (hLM : L = M + 2 * r) (w : V p L M)
    (hw : Pop p L M (M : ℤ) w = w) :
    w = cR w 0 • ess p L M 0 + cL w r • ell p L M r := by
  conv_lhs => rw [← hw]
  ext (i | j)
  · rw [Pop_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ess_inl, ell_inl, smul_eq_mul,
      smul_eq_mul, mul_zero, zero_add]
    simp only [wt]
    by_cases h : (i : ℕ) = r
    · rw [if_pos (by rw [h, hLM]; push_cast; ring), if_pos h, ← h, cL_fin]; ring
    · rw [if_neg (by intro h'; apply h; omega), if_neg h]; ring
  · rw [Pop_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ess_inr, ell_inr, smul_eq_mul,
      smul_eq_mul, mul_zero, add_zero]
    simp only [wt]
    by_cases h : (j : ℕ) = 0
    · rw [if_pos (by rw [h]; ring), if_pos h, cR, dif_pos (Nat.zero_le _)]
      have : j = ⟨0, Nat.succ_pos _⟩ := Fin.ext h
      rw [this]; ring
    · rw [if_neg (by intro h'; apply h; omega), if_neg h]; ring

/-- **(G3)(b) Non-split case.**  If `‖x‖ = p^ν`, there is no highest-weight lift of `s₀`
modulo `p`: every `w ∈ Lx x` of weight `μ` with `w (inr 0) = 1` has `E t w ∉ p • Lx x` for some
`1 ≤ t ≤ r`. -/
theorem G3b_nonsplit {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (x : ℚ_[p]) (hx : ‖x‖ = (p : ℝ) ^ nu p r a)
    (w : V p (lam p r a) (mu p r a)) (hwL : w ∈ Lx p (lam p r a) (mu p r a) r x)
    (hwP : Pop p (lam p r a) (mu p r a) (mu p r a : ℤ) w = w)
    (hw0 : w (.inr ⟨0, Nat.succ_pos _⟩) = 1) :
    ∃ t, 1 ≤ t ∧ t ≤ r ∧
      Eop p (lam p r a) (mu p r a) t w ∉ (p : ℤ_[p]) • Lx p (lam p r a) (mu p r a) r x := by
  have hLM := lam_eq_mu_add (p := p) r a hrp hra
  set c := cL w r with hc
  have hcR : cR w 0 = 1 := by rw [cR, dif_pos (Nat.zero_le _)]; exact hw0
  have hform := weight_mu_vector r hLM w hwP
  rw [hcR, one_smul] at hform
  -- `c − x` is integral
  have hcx : ‖c - x‖ ≤ 1 := by
    have := (mem_Lx_iff r x w).1 hwL (.inl ⟨r, by omega⟩)
    have e2 : w (.inl ⟨r, by omega⟩) = c := by rw [hc, cL, dif_pos (by omega)]
    have e3 : cR w (((⟨r, by omega⟩ : Fin (lam p r a + 1)) : ℕ) - r) = 1 := by
      rw [show ((⟨r, by omega⟩ : Fin (lam p r a + 1)) : ℕ) - r = 0 by simp]; exact hcR
    have e4 : (gl r ((⟨r, by omega⟩ : Fin (lam p r a + 1)) : ℕ) : ℚ_[p]) = 1 := by
      simp [gl]
    rw [Phi_inl, e2, e3, e4, mul_one, mul_one] at this
    exact this
  -- `‖c‖ = p^ν`
  have hnu1 : 1 ≤ nu p r a := by unfold nu; split_ifs <;> omega
  have hpnu : (1 : ℝ) < (p : ℝ) ^ nu p r a := one_lt_pow₀ one_lt_p_real (by omega)
  have hcn : ‖c‖ = (p : ℝ) ^ nu p r a := by
    have : c = x + (c - x) := by ring
    rw [this, Padic.add_eq_max_of_ne (by rw [hx]; linarith), hx]
    exact max_eq_left (by linarith)
  -- choose `t` with `v_p C(λ − r + t, t) = ν`
  obtain ⟨t, ht, hval⟩ := Finset.exists_mem_eq_inf' (s := Finset.Icc 1 r)
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hr1⟩⟩
    (fun t => padicValNat p (Nat.choose (lam p r a - r + t) t))
  rw [← (glue_exponent_N (p := p) hr1 hrp ha hra).1] at hval
  obtain ⟨ht1, htr⟩ := Finset.mem_Icc.mp ht
  refine ⟨t, ht1, htr, fun hmem => ?_⟩
  have hEw : Eop p (lam p r a) (mu p r a) t w =
      (c * ((lam p r a - r + t).choose t : ℚ_[p])) • ell p (lam p r a) (mu p r a) (r - t) := by
    rw [hform, map_add, LinearMap.map_smul, E_ess t 0 (Nat.zero_le _), if_neg (by omega),
      zero_add, E_ell t r (by omega), if_pos htr, smul_smul,
      show lam p r a - r + t = lam p r a - r + t from rfl]
  have h1 := norm_Phi_le_of_mem_pLx r x hmem (.inl ⟨r - t, by omega⟩)
  rw [hEw, LinearMap.map_smul, Phi_ell, Pi.smul_apply, ell_inl, if_pos rfl, smul_eq_mul,
    mul_one, norm_mul, hcn] at h1
  have hC : (lam p r a - r + t).choose t ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [norm_natCast_eq_pow _ hC, ← hval, ← zpow_natCast, ← zpow_add₀ p_pos_real.ne',
    add_neg_cancel, zpow_zero] at h1
  have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_p_real
  linarith

end ColouredSand.Glue
