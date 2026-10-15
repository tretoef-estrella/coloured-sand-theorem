module

public import RequestProject.Blocks.Defs

/-!
# Positivity (P) and the glue exponent (N) (CSG1, §1)

This file corresponds to **(P) positivity** and **(N) the glue exponent** of §1 of
`CSG1_lemma_8_the_blocks.md`.  All statements are about natural numbers.

* `positivity_P`: `a + 1 ≤ A'` and `a + 1 ≤ A − α`.
* `glue_exponent_N`: `ν = min_{1 ≤ t ≤ r} v_p(C(λ − r + t, t))` (Kummer), `p^ν ∣ C(μ+r, μ)(a+1)p`,
  `C(μ+r, μ)` is prime to `p` (Lucas; here also via Kummer), and `v_p(u) = 0` if `r ≤ p − 1`,
  `v_p(u) = 1` if `r = p`.

The standing hypotheses of §1 are `1 ≤ r ≤ p`, `a ≤ p − 1` and `r = p → a = p − 1`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Blocks

variable {p : ℕ} [hp : Fact p.Prime]

lemma two_le_p : 2 ≤ p := hp.out.two_le

omit hp in
lemma ring_aux (a : ℕ) : (a + 1) * p = p * a + p := by ring

lemma lam_eq (r a : ℕ) : lam p r a + 1 = (a + 1) * p + r := by
  have := (two_le_p (p := p)); have := ring_aux (p := p) a; unfold lam; omega

lemma mu_add (r a : ℕ) (hrp : r ≤ p) (hra : r = p → a = p - 1) :
    mu p r a + r + 1 = (a + 1) * p ∧ 2 * r ≤ lam p r a := by
  have h2 := two_le_p (p := p)
  have hl := lam_eq (p := p) r a
  have : r ≤ p - 1 + p * a := by
    by_cases h : r = p
    · have ha := hra h
      have : p ≤ p * a := Nat.le_mul_of_pos_right p (by omega)
      omega
    · omega
  unfold mu
  constructor
  · unfold lam at hl ⊢; omega
  · unfold lam; omega

/-- **(P) positivity.**  `a + 1 ≤ A'` and `a + 1 ≤ A − α`.  (The standing hypothesis
`a ≤ p − 1` is not needed here.) -/
theorem positivity_P {q c k r a : ℕ} (hq : 1 ≤ padicValNat p q) (hr1 : 1 ≤ r) (hrp : r ≤ p)
    (hra : r = p → a = p - 1) :
    a + 1 ≤ blkA' p q c k r a ∧ a + 1 ≤ blkA p q c k r a - blkAlpha p q c k r a := by
  have h2 := two_le_p (p := p)
  have hv : ∀ t, 1 ≤ vt p q c k t := fun t => by unfold vt; omega
  obtain ⟨hmu, h2r⟩ := mu_add (p := p) r a hrp hra
  have hl := lam_eq (p := p) r a
  have hring := ring_aux (p := p) a
  constructor
  · have := Finset.card_nsmul_le_sum (Icc r (r + mu p r a)) (fun t => vt p q c k t) 1
      (fun t _ => hv t)
    simp only [Nat.card_Icc, smul_eq_mul, mul_one] at this
    unfold blkA'
    have hpa : a ≤ p * a := Nat.le_mul_of_pos_left a (by omega)
    have : a + 1 ≤ mu p r a + 1 := by
      by_cases h : r = p
      · have ha' := hra h
        have : 2 * a ≤ p * a := Nat.mul_le_mul_right a h2
        omega
      · omega
    omega
  · have hsplit : blkA p q c k r a = (∑ t ∈ range ((a + 1) * p), vt p q c k t) +
        blkAlpha p q c k r a := by
      unfold blkA blkAlpha
      rw [← Finset.sum_range_add_sum_Ico _ (show (a + 1) * p ≤ lam p r a + 1 by omega)]
      congr 1
    have := Finset.card_nsmul_le_sum (range ((a + 1) * p)) (fun t => vt p q c k t) 1
      (fun t _ => hv t)
    simp only [card_range, smul_eq_mul, mul_one] at this
    have : a + 1 ≤ (a + 1) * p := Nat.le_mul_of_pos_right _ (by omega)
    omega

/-! ### Kummer computations -/

lemma mod_aux (a : ℕ) : ((a + 1) * p - 1) % p = p - 1 := by
  have h2 := two_le_p (p := p)
  rw [show (a + 1) * p - 1 = a * p + (p - 1) by rw [Nat.add_mul, one_mul]; omega,
    Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]

lemma lt_sq_aux {a : ℕ} (ha : a ≤ p - 1) : (a + 1) * p - 1 < p * p := by
  have h2 := two_le_p (p := p)
  have h1 : (a + 1) * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
  have h3 : 0 < p * p := by positivity
  generalize (a + 1) * p = M at h1 ⊢
  generalize p * p = PP at h1 h3 ⊢
  omega

lemma choose_val_aux {n k : ℕ} (hk : k ≤ n) (hn : n < p * p * p) (hn0 : n ≠ 0) :
    padicValNat p (n.choose k) =
      (if p ≤ k % p + (n - k) % p then 1 else 0) +
        (if p * p ≤ k % (p * p) + (n - k) % (p * p) then 1 else 0) := by
  rw [padicValNat_choose (b := 3) hk (Nat.log_lt_of_lt_pow hn0 (by rw [pow_three]; nlinarith))]
  rw [show Finset.Ico 1 3 = {1, 2} by decide, Finset.filter_insert, Finset.filter_singleton]
  simp only [pow_one, sq]
  split_ifs <;> simp_all

/-- `v_p(C((a+1)p − 1 + t, t)) = [t < p] + [a = p − 1]` for `1 ≤ t ≤ p`, `a ≤ p − 1`. -/
lemma val_choose_link {a t : ℕ} (ha : a ≤ p - 1) (ht1 : 1 ≤ t) (htp : t ≤ p) :
    padicValNat p (Nat.choose ((a + 1) * p - 1 + t) t) =
      (if t < p then 1 else 0) + (if a = p - 1 then 1 else 0) := by
  have h2 := two_le_p (p := p)
  have hsq := lt_sq_aux (p := p) ha
  have hpp : p ≤ p * p := Nat.le_mul_of_pos_left p (by omega)
  have hppp : p * p + p < p * p * p := by nlinarith
  have hn : (a + 1) * p - 1 + t < p * p * p := by
    generalize p * p * p = PPP at hppp ⊢
    generalize (a + 1) * p = M at hsq ⊢
    generalize p * p = PP at hsq hppp ⊢
    omega
  rw [choose_val_aux (by omega) hn (by omega)]
  rw [show (a + 1) * p - 1 + t - t = (a + 1) * p - 1 by omega, mod_aux,
    Nat.mod_eq_of_lt (show t < p * p by nlinarith), Nat.mod_eq_of_lt hsq]
  congr 1
  · by_cases h : t < p
    · rw [Nat.mod_eq_of_lt h, if_pos (by omega), if_pos h]
    · rw [show t = p by omega, Nat.mod_self, if_neg (by omega), if_neg (by omega)]
  · by_cases h : a = p - 1
    · rw [if_pos h, if_pos]
      rw [h, show p - 1 + 1 = p by omega]
      generalize p * p = PP
      omega
    · rw [if_neg h, if_neg]
      have h' := Nat.mul_le_mul_right p (show a + 2 ≤ p by omega)
      have : (a + 1) * p + p ≤ p * p := by nlinarith
      have hM : 1 ≤ (a + 1) * p := by nlinarith
      generalize (a + 1) * p = M at this hM ⊢
      generalize p * p = PP at this ⊢
      omega

/-- `v_p(C(μ + r, μ)) = 0`. -/
lemma val_choose_glue {r a : ℕ} (hrp : r ≤ p) (ha : a ≤ p - 1) (hra : r = p → a = p - 1) :
    padicValNat p (Nat.choose (mu p r a + r) (mu p r a)) = 0 := by
  have h2 := two_le_p (p := p)
  obtain ⟨hmu, _⟩ := mu_add (p := p) r a hrp hra
  have hsq := lt_sq_aux (p := p) ha
  have hpp : p < p * p := by nlinarith
  have hppp : p * p + p < p * p * p := by nlinarith
  have hn : mu p r a + r = (a + 1) * p - 1 := by omega
  have hnlt : mu p r a + r < p * p * p := by
    rw [hn]
    generalize p * p * p = PPP at hppp ⊢
    generalize (a + 1) * p = M at hsq ⊢
    generalize p * p = PP at hsq hppp ⊢
    omega
  have hn0 : mu p r a + r ≠ 0 := by
    have : 2 ≤ (a + 1) * p := by nlinarith
    omega
  rw [choose_val_aux (by omega) hnlt hn0, show mu p r a + r - mu p r a = r by omega]
  have hs : mu p r a % p + r % p < p := by
    have hm := mod_aux (p := p) a
    rw [← hn, Nat.add_mod] at hm
    have h1 := Nat.mod_lt (mu p r a) (show p > 0 by omega)
    have h3 := Nat.mod_lt r (show p > 0 by omega)
    by_contra hc
    push_neg at hc
    rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)] at hm
    omega
  rw [if_neg (by omega), Nat.mod_eq_of_lt (show mu p r a < p * p by omega),
    Nat.mod_eq_of_lt (show r < p * p by omega), if_neg]
  omega

lemma val_succ_a {a : ℕ} (ha : a ≤ p - 1) :
    padicValNat p (a + 1) = if a = p - 1 then 1 else 0 := by
  have h2 := two_le_p (p := p)
  split_ifs with h
  · rw [show a + 1 = p by omega]; exact padicValNat_self
  · exact padicValNat.eq_zero_of_not_dvd (fun hd => by
      have := Nat.le_of_dvd (by omega) hd; omega)

/-- **(N) the glue exponent (Lemma 7, Kummer).**
* `ν = min_{t ∈ [1, r]} v_p(C(λ − r + t, t))`;
* `p^ν ∣ C(μ + r, μ) (a + 1) p` (so `u` is an exact quotient);
* `C(μ + r, μ)` is prime to `p`;
* `v_p(u) = 0` if `r ≤ p − 1` and `v_p(u) = 1` if `r = p`. -/
theorem glue_exponent_N {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) :
    nu p r a = (Finset.Icc 1 r).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hr1⟩⟩
        (fun t => padicValNat p (Nat.choose (lam p r a - r + t) t)) ∧
      p ^ nu p r a ∣ Nat.choose (mu p r a + r) (mu p r a) * (a + 1) * p ∧
      Nat.Coprime p (Nat.choose (mu p r a + r) (mu p r a)) ∧
      (r ≤ p - 1 → padicValNat p (uGlue p r a) = 0) ∧
      (r = p → padicValNat p (uGlue p r a) = 1) := by
  have h2 := two_le_p (p := p)
  have hl : ∀ t, lam p r a - r + t = (a + 1) * p - 1 + t := by
    intro t; have := lam_eq (p := p) r a; omega
  have hf : ∀ t ∈ Finset.Icc 1 r, padicValNat p (Nat.choose (lam p r a - r + t) t) =
      (if t < p then 1 else 0) + (if a = p - 1 then 1 else 0) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    rw [hl]; exact val_choose_link ha ht.1 (by omega)
  have hC0 : Nat.choose (mu p r a + r) (mu p r a) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hvC := val_choose_glue (p := p) hrp ha hra
  have hn0 : Nat.choose (mu p r a + r) (mu p r a) * (a + 1) * p ≠ 0 := by positivity
  have hvn : padicValNat p (Nat.choose (mu p r a + r) (mu p r a) * (a + 1) * p) =
      (if a = p - 1 then 1 else 0) + 1 := by
    rw [padicValNat.mul (by positivity) (by omega), padicValNat.mul hC0 (by omega), hvC,
      val_succ_a ha, padicValNat_self, zero_add]
  have hdvd : p ^ nu p r a ∣ Nat.choose (mu p r a + r) (mu p r a) * (a + 1) * p := by
    rw [padicValNat_dvd_iff_le hn0, hvn]
    unfold nu; split_ifs <;> omega
  refine ⟨?_, hdvd, ?_, ?_, ?_⟩
  · apply le_antisymm
    · apply Finset.le_inf'
      intro t ht
      rw [hf t ht]
      have := (Finset.mem_Icc.mp ht)
      unfold nu
      by_cases hr : r ≤ p - 1
      · rw [if_pos (by omega : t < p)]; split_ifs <;> omega
      · rw [hra (by omega)]; split_ifs <;> omega
    · refine le_trans (Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hr1, le_rfl⟩)) ?_
      rw [hf r (Finset.mem_Icc.mpr ⟨hr1, le_rfl⟩)]
      unfold nu
      by_cases hr : r ≤ p - 1
      · rw [if_pos (by omega : r < p)]; split_ifs <;> omega
      · rw [if_neg (by omega : ¬ r < p), hra (by omega)]; split_ifs <;> omega
  · rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hd
    have := (dvd_iff_padicValNat_ne_zero hC0).mp hd
    exact this hvC
  · intro hr
    unfold uGlue
    rw [padicValNat.div_pow hdvd, hvn]
    unfold nu; split_ifs <;> omega
  · intro hr
    have ha' := hra hr
    unfold uGlue
    rw [padicValNat.div_pow hdvd, hvn]
    unfold nu; split_ifs <;> omega

end ColouredSand.Blocks
