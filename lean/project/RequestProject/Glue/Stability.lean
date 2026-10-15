module

public import RequestProject.Glue.Identities

/-!
# (G1) The stability threshold (CSG2, §1 (G1) and §2 "*(G1)*")

* `G1_stability_threshold`: for every `x : ℚ_[p]`, `Lx x` is stable iff `‖x‖ ≤ p^ν`.

Proof (§2): `P w` preserves `Lx x` because `s̃ x j` and `ℓ_{j+r}` have the same weight.
By `E_stilde` and `F_stilde`, `E t (s̃ x j)` and `F t (s̃ x j)` are, modulo `Lx x`,
`x β_E(j,t) ℓ_…` and `x β_F(j,t) ℓ_…`; `p^ν` divides every `β` (`dvd_betaE`, `dvd_betaF`
with the Kummer computations `pow_nu_dvd_link`, `pow_nu_dvd_tail`), and for `j = 0` the
coefficients `β_E(0,t) = C(λ−r+t, t)`, `1 ≤ t ≤ r`, have least valuation exactly `ν` (by (N),
`glue_exponent_N`).
-/

@[expose] public section

open Finset

namespace ColouredSand.Glue

open ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime] {L M : ℕ}

/-! ### Generic facts about `Lx` -/

lemma natCast_smul_mem {Λ : Submodule ℤ_[p] (V p L M)} (n : ℕ) {v : V p L M} (hv : v ∈ Λ) :
    ((n : ℚ_[p])) • v ∈ Λ := by
  have : ((n : ℚ_[p])) • v = (n : ℤ_[p]) • v := by rw [padic_smul_vec]; push_cast; rfl
  rw [this]; exact Λ.smul_mem _ hv

lemma intCoe_smul_mem {Λ : Submodule ℤ_[p] (V p L M)} (c : ℤ_[p]) {v : V p L M} (hv : v ∈ Λ) :
    ((c : ℚ_[p])) • v ∈ Λ := by
  rw [← padic_smul_vec]; exact Λ.smul_mem _ hv

lemma smul_ell_mem (r : ℕ) (x z : ℚ_[p]) (hz : ‖z‖ ≤ 1) (i : ℕ) :
    z • ell p L M i ∈ Lx p L M r x := by
  have := intCoe_smul_mem (Λ := Lx p L M r x) ⟨z, hz⟩ (ell_mem_Lx r x i)
  exact this

lemma norm_le_of_smul_ell_mem (r : ℕ) (x z : ℚ_[p]) (i : ℕ) (hi : i ≤ L)
    (h : z • ell p L M i ∈ Lx p L M r x) : ‖z‖ ≤ 1 := by
  rw [mem_Lx_iff] at h
  have := h (.inl ⟨i, Nat.lt_succ_of_le hi⟩)
  rwa [LinearMap.map_smul, Phi_ell, Pi.smul_apply, ell_inl, if_pos rfl, smul_eq_mul,
    mul_one] at this

/-- A `ℚ_[p]`-linear map preserves `Lx x` as soon as it maps the generators into `Lx x`. -/
lemma map_mem_Lx (r : ℕ) (x : ℚ_[p]) (T : V p L M →ₗ[ℚ_[p]] V p L M)
    (h1 : ∀ i, i ≤ L → T (ell p L M i) ∈ Lx p L M r x)
    (h2 : ∀ j, j ≤ M → T (stilde p L M r x j) ∈ Lx p L M r x) :
    ∀ v ∈ Lx p L M r x, T v ∈ Lx p L M r x := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    rcases hw with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact h1 i (Nat.le_of_lt_succ i.2)
    · exact h2 j (Nat.le_of_lt_succ j.2)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
  | smul c v _ hv => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ c hv

/-- `Lx x` is stable as soon as `x β_E` and `x β_F` are integral. -/
lemma isStable_of (r : ℕ) (hLM : L = M + 2 * r) (x : ℚ_[p])
    (hE : ∀ j t, j ≤ M → ‖x * (betaE L M r j t : ℚ_[p])‖ ≤ 1)
    (hF : ∀ j t, j ≤ M → ‖x * (betaF L M r j t : ℚ_[p])‖ ≤ 1) :
    IsStable p L M (Lx p L M r x) := by
  refine ⟨fun t _ v hv => ⟨?_, ?_⟩, fun w v hv => ?_⟩
  · refine map_mem_Lx r x _ ?_ ?_ v hv
    · intro i hi
      rw [F_ell t i hi]; exact natCast_smul_mem _ (ell_mem_Lx r x _)
    · intro j hj
      rw [F_stilde r hLM x t j hj]
      exact Submodule.add_mem _ (natCast_smul_mem _ (stilde_mem_Lx r x _))
        (smul_ell_mem r x _ (hF j t hj) _)
  · refine map_mem_Lx r x _ ?_ ?_ v hv
    · intro i hi
      rw [E_ell t i hi]
      split_ifs
      · exact natCast_smul_mem _ (ell_mem_Lx r x _)
      · exact Submodule.zero_mem _
    · intro j hj
      rw [E_stilde r hLM x t j hj]
      refine Submodule.add_mem _ ?_ (smul_ell_mem r x _ (hE j t hj) _)
      split_ifs
      · exact natCast_smul_mem _ (stilde_mem_Lx r x _)
      · exact Submodule.zero_mem _
  · refine map_mem_Lx r x _ ?_ ?_ v hv
    · intro i hi
      rw [P_ell w i hi]
      split_ifs
      · exact ell_mem_Lx r x _
      · exact Submodule.zero_mem _
    · intro j _
      rw [P_stilde r hLM x w j]
      split_ifs
      · exact stilde_mem_Lx r x _
      · exact Submodule.zero_mem _

/-! ### The numbers of §1 -/

lemma lam_eq_mu_add (r a : ℕ) (hrp : r ≤ p) (hra : r = p → a = p - 1) :
    lam p r a = mu p r a + 2 * r := by
  have := (mu_add (p := p) r a hrp hra).2
  unfold mu; omega

lemma norm_natCast_eq_pow (n : ℕ) (hn : n ≠ 0) :
    ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hn), Padic.valuation_natCast]

lemma norm_int_le_of_dvd {k : ℤ} {n : ℕ} (h : ((p : ℤ) ^ n) ∣ k) :
    ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
  (Padic.norm_int_le_pow_iff_dvd k n).2 h

lemma norm_mul_le_one_of {x : ℚ_[p]} {n : ℕ} (hx : ‖x‖ ≤ (p : ℝ) ^ n) {k : ℤ}
    (hk : ((p : ℤ) ^ n) ∣ k) : ‖x * (k : ℚ_[p])‖ ≤ 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [norm_mul]
  calc ‖x‖ * ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ n * (p : ℝ) ^ (-(n : ℤ)) :=
        mul_le_mul hx (norm_int_le_of_dvd hk) (norm_nonneg _) (by positivity)
    _ = 1 := by rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (by positivity)]

/-- `β_E(0, t) = C(λ − r + t, t)` for `1 ≤ t ≤ r ≤ λ`. -/
lemma betaE_zero {L M r t : ℕ} (hrL : r ≤ L) (ht1 : 1 ≤ t) (htr : t ≤ r) :
    betaE L M r 0 t = (((L - r + t).choose t : ℕ) : ℤ) := by
  unfold betaE
  rw [if_pos (by omega), if_neg (by omega), show L - (0 + r - t) = L - r + t by omega]
  simp

/-- **(G1) The stability threshold.**  For every `x : ℚ_[p]`, the glued lattice `Lx x` is
stable (under all `F t`, `E t`, `t ≥ 1`, and all weight projections `P w`) iff
`‖x‖ ≤ p^ν`. -/
theorem G1_stability_threshold {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (x : ℚ_[p]) :
    IsStable p (lam p r a) (mu p r a) (Lx p (lam p r a) (mu p r a) r x) ↔
      ‖x‖ ≤ (p : ℝ) ^ nu p r a := by
  have hLM := lam_eq_mu_add (p := p) r a hrp hra
  constructor
  · intro hS
    obtain ⟨t, ht, hval⟩ := Finset.exists_mem_eq_inf' (s := Finset.Icc 1 r)
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hr1⟩⟩
      (fun t => padicValNat p (Nat.choose (lam p r a - r + t) t))
    rw [← (glue_exponent_N (p := p) hr1 hrp ha hra).1] at hval
    obtain ⟨ht1, htr⟩ := Finset.mem_Icc.mp ht
    have hmem := (hS.1 t ht1 _ (stilde_mem_Lx r x 0)).2
    rw [E_stilde r hLM x t 0 (Nat.zero_le _), if_neg (by omega), zero_add,
      betaE_zero (by omega) ht1 htr] at hmem
    have h1 := norm_le_of_smul_ell_mem r x _ _ (by omega) hmem
    have hC : (lam p r a - r + t).choose t ≠ 0 := (Nat.choose_pos (by omega)).ne'
    rw [norm_mul, Int.cast_natCast, norm_natCast_eq_pow _ hC, ← hval] at h1
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-(nu p r a : ℤ)) := by positivity
    calc ‖x‖ = ‖x‖ * (p : ℝ) ^ (-(nu p r a : ℤ)) * (p : ℝ) ^ nu p r a := by
          rw [mul_assoc, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), mul_one]
      _ ≤ 1 * (p : ℝ) ^ nu p r a := by gcongr
      _ = (p : ℝ) ^ nu p r a := one_mul _
  · intro hx
    apply isStable_of r hLM x
    · intro j t hj
      apply norm_mul_le_one_of hx
      have := dvd_betaE hLM (p ^ nu p r a)
        (fun m hm1 hmr => pow_nu_dvd_link hr1 hrp ha hra m hm1 hmr) (t := t) hj
      exact_mod_cast this
    · intro j t _
      apply norm_mul_le_one_of hx
      have := dvd_betaF hLM (p ^ nu p r a)
        (fun s hs1 hs2 => pow_nu_dvd_tail hr1 hrp ha hra s hs1 hs2) (j := j) (t := t)
      exact_mod_cast this

end ColouredSand.Glue
