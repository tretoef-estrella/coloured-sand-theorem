module

public import RequestProject.Blocks.Numbers

/-!
# Binomial identities behind (G1) (CSG2, §2, proof of (G1))

This file contains no statement of `CSG2_lemma_7_the_glue.md` itself; it is the arithmetic used in
the proof of **(G1)** (§2, "*(G1)*").

* `choose_commutation`: the integer identity
  `C(w+t, j) C(u+w+t−j, t) = Σ_{k ≤ t, k ≤ j} C(u, k) C(w, j−k) C(u+w+t−k, t−k)`.
  It is the identity `e^{(t)} f^{(j)} = Σ_k C(h+t−j, k) f^{(j−k)} e^{(t−k)}` evaluated on a basis
  vector of a Weyl module, and is proved by two Vandermonde convolutions.
* `betaE`, `betaF`: the coefficients of §2 (the `ℓ`-component of
  `E t (s̃ j) − C(μ−j+t, t) s̃ (j−t)` and of `F t (s̃ j) − C(j+t, t) s̃ (j+t)`, divided by `x`).
* `dvd_betaE`, `dvd_betaF_of`: if `d` divides the "`j = 0`" coefficients, it divides all of them.
* `pow_nu_dvd_link`, `pow_nu_dvd_tail`: the Kummer computations giving `p^ν` as such a `d`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Glue

/-! ### The commutation identity -/

lemma vandermonde_range (m n k : ℕ) :
    (m + n).choose k = ∑ i ∈ range (k + 1), m.choose i * n.choose (k - i) := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma choose_term_aux {w t s j : ℕ} (hs : s ≤ t) (hj : j ≤ w + t) :
    (w + t).choose j * (w + t - j).choose (t - s) =
      (w + t).choose (t - s) * (s + w).choose j := by
  rw [Nat.choose_symm_of_eq_add (show w + t = (t - s) + (w + s) by omega), add_comm s w]
  by_cases hj : j ≤ w + s
  · rw [Nat.choose_mul hj,
      Nat.choose_symm_of_eq_add (show w + t - j = (t - s) + (w + s - j) by omega)]
  · push_neg at hj
    rw [Nat.choose_eq_zero_of_lt hj, Nat.choose_eq_zero_of_lt (show w + t - j < t - s by omega)]
    simp

lemma vandermonde_ind (s w j A : ℕ) (hA : s < A) :
    ∑ k ∈ range A, (if k ≤ j then s.choose k * w.choose (j - k) else 0) = (s + w).choose j := by
  rw [vandermonde_range]
  have h1 : ∑ k ∈ range A, (if k ≤ j then s.choose k * w.choose (j - k) else 0) =
      ∑ k ∈ range (A + j + 1), (if k ≤ j then s.choose k * w.choose (j - k) else 0) := by
    apply Finset.sum_subset (by intro x; simp; omega)
    intro x hx hx'
    simp at hx hx'
    rw [Nat.choose_eq_zero_of_lt (show s < x by omega)]; simp
  have h2 : ∑ k ∈ range (j + 1), s.choose k * w.choose (j - k) =
      ∑ k ∈ range (A + j + 1), (if k ≤ j then s.choose k * w.choose (j - k) else 0) := by
    apply Finset.sum_subset_zero_on_sdiff (by intro x; simp; omega)
    · intro x hx; simp at hx; simp; omega
    · intro x hx; simp at hx; simp; omega
  rw [h1, h2]

lemma choose_expand_aux (u w t k : ℕ) (hk : k ≤ t) :
    u.choose k * (u + w + t - k).choose (t - k) =
      ∑ s ∈ range (t + 1),
        if k ≤ s then u.choose s * s.choose k * (w + t).choose (t - s) else 0 := by
  by_cases hku : u < k
  · rw [Nat.choose_eq_zero_of_lt hku, zero_mul]
    symm; apply Finset.sum_eq_zero; intro s hs
    split_ifs with h
    · rw [Nat.choose_eq_zero_of_lt (show u < s by omega)]; simp
    · rfl
  push_neg at hku
  rw [show u + w + t - k = (u - k) + (w + t) by omega, vandermonde_range, Finset.mul_sum]
  rw [← Finset.sum_filter, show (range (t+1)).filter (fun s => k ≤ s) = Ico k (t + 1) by
    ext s; simp; omega, Finset.sum_Ico_eq_sum_range, show t + 1 - k = t - k + 1 by omega]
  apply Finset.sum_congr rfl
  intro m hm
  simp at hm
  rw [show t - (k + m) = t - k - m by omega]
  by_cases hkm : k + m ≤ u
  · have := Nat.choose_mul (n := u) (k := k + m) (s := k) (by omega)
    rw [show k + m - k = m by omega] at this
    rw [← mul_assoc, ← this]
  · rw [Nat.choose_eq_zero_of_lt (show u - k < m by omega),
      Nat.choose_eq_zero_of_lt (show u < k + m by omega)]
    simp

/-- The commutation identity (the coefficients of `e^{(t)} f^{(j)}` on a Weyl module). -/
theorem choose_commutation (u w t j : ℕ) :
    (w + t).choose j * (u + w + t - j).choose t =
      ∑ k ∈ range (t + 1), if k ≤ j then
        u.choose k * w.choose (j - k) * (u + w + t - k).choose (t - k) else 0 := by
  by_cases hj : w + t < j
  · rw [Nat.choose_eq_zero_of_lt hj, zero_mul]
    symm; apply Finset.sum_eq_zero; intro k hk
    simp at hk
    split_ifs
    · rw [Nat.choose_eq_zero_of_lt (show w < j - k by omega)]; simp
    · rfl
  push_neg at hj
  have hL : (w + t).choose j * (u + w + t - j).choose t =
      ∑ s ∈ range (t + 1), u.choose s * ((w + t).choose (t - s) * (s + w).choose j) := by
    rw [show u + w + t - j = u + (w + t - j) by omega, vandermonde_range u (w + t - j) t,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs; simp at hs
    rw [← choose_term_aux (by omega) hj]; ring
  have hR : (∑ k ∈ range (t + 1), if k ≤ j then
        u.choose k * w.choose (j - k) * (u + w + t - k).choose (t - k) else 0) =
      ∑ k ∈ range (t + 1), ∑ s ∈ range (t + 1),
        (if k ≤ j then w.choose (j - k) * (if k ≤ s then
          u.choose s * s.choose k * (w + t).choose (t - s) else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro k hk; simp at hk
    split_ifs with h
    · rw [mul_comm (u.choose k), mul_assoc, choose_expand_aux u w t k (by omega), Finset.mul_sum]
    · simp
  rw [hL, hR, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs; simp at hs
  rw [← vandermonde_ind s w j (t + 1) (by omega), Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hks : k ≤ s
  · split_ifs <;> ring
  · rw [Nat.choose_eq_zero_of_lt (show s < k by omega)]; split_ifs <;> simp

/-- `C(j+r, j) C(j+r+t, t) = C(j+t, t) C(j+t+r, j+t)` (both are `(j+r+t)!/(j! r! t!)`). -/
lemma choose_glue_comm (j r t : ℕ) :
    (j + r).choose j * (j + r + t).choose t = (j + t).choose t * (j + t + r).choose (j + t) := by
  have h1 : (j + r + t).choose t = (j + r + t).choose (j + r) :=
    Nat.choose_symm_of_eq_add (by ring)
  have h2 : (j + t + r).choose (j + t) = (j + r + t).choose (j + t) := by
    rw [show j + t + r = j + r + t by ring]
  have h3 : (j + t).choose t = (j + t).choose j := Nat.choose_symm_of_eq_add (by ring)
  have e1 := Nat.choose_mul (n := j + r + t) (k := j + r) (s := j) (by omega)
  have e2 := Nat.choose_mul (n := j + r + t) (k := j + t) (s := j) (by omega)
  rw [show j + r + t - j = r + t by omega, show j + r - j = r by omega] at e1
  rw [show j + r + t - j = r + t by omega, show j + t - j = t by omega] at e2
  have h4 : (r + t).choose r = (r + t).choose t := Nat.choose_symm_of_eq_add (by ring)
  rw [h1, h2, h3, mul_comm, e1, mul_comm ((j + t).choose j), e2, h4]

/-! ### The coefficients of §2 -/

/-- `β_E(j, t)`: the coefficient of `x ℓ (j + r − t)` in `E t (s̃ j) − C(μ−j+t, t) s̃ (j − t)`
(the second term only when `t ≤ j`; the first only when `t ≤ j + r`). -/
def betaE (L M r j t : ℕ) : ℤ :=
  (if t ≤ j + r then (((j + r).choose j * (L - (j + r - t)).choose t : ℕ) : ℤ) else 0) -
    (if t ≤ j then (((M - j + t).choose t * (j - t + r).choose (j - t) : ℕ) : ℤ) else 0)

/-- `β_F(j, t)`: the coefficient of `x ℓ (j + r + t)` in `F t (s̃ j) − C(j+t, t) s̃ (j + t)`. -/
def betaF (L M r j t : ℕ) : ℤ :=
  (if j + r + t ≤ L then (((j + r).choose j * (j + r + t).choose t : ℕ) : ℤ) else 0) -
    (if j + t ≤ M then (((j + t).choose t * (j + t + r).choose (j + t) : ℕ) : ℤ) else 0)

/-- If `d` divides `C(λ − r + m, m)` for `1 ≤ m ≤ r`, then `d ∣ β_E(j, t)` for all `j ≤ μ`. -/
lemma dvd_betaE {L M r : ℕ} (hLM : L = M + 2 * r) (d : ℕ)
    (hd : ∀ m, 1 ≤ m → m ≤ r → d ∣ (L - r + m).choose m) {j t : ℕ} (hj : j ≤ M) :
    (d : ℤ) ∣ betaE L M r j t := by
  unfold betaE
  by_cases ht : t ≤ j + r
  swap
  · rw [if_neg ht, if_neg (by omega)]; simp
  rw [if_pos ht]
  have key := choose_commutation (M + t - j) (j + r - t) t j
  rw [show j + r - t + t = j + r by omega,
    show M + t - j + (j + r - t) + t - j = L - (j + r - t) by omega,
    Finset.sum_range_succ] at key
  have hlast : (if t ≤ j then (M + t - j).choose t * (j + r - t).choose (j - t) *
      (M + t - j + (j + r - t) + t - t).choose (t - t) else 0) =
      (if t ≤ j then (M - j + t).choose t * (j - t + r).choose (j - t) else 0) := by
    split_ifs with h
    · rw [show M + t - j = M - j + t by omega, show j + r - t = j - t + r by omega]; simp
    · rfl
  rw [hlast] at key
  have hsum : (((j + r).choose j * (L - (j + r - t)).choose t : ℕ) : ℤ) -
      (if t ≤ j then (((M - j + t).choose t * (j - t + r).choose (j - t) : ℕ) : ℤ) else 0) =
      ((∑ k ∈ range t, if k ≤ j then (M + t - j).choose k * (j + r - t).choose (j - k) *
        (M + t - j + (j + r - t) + t - k).choose (t - k) else 0 : ℕ) : ℤ) := by
    rw [key]; push_cast; split_ifs <;> simp
  rw [hsum]
  apply Int.natCast_dvd_natCast.mpr
  apply Finset.dvd_sum
  intro k hk
  simp at hk
  split_ifs with hkj
  · by_cases hkr : k + r < t
    · rw [Nat.choose_eq_zero_of_lt (show j + r - t < j - k by omega)]; simp
    · apply Dvd.dvd.mul_left
      have := hd (t - k) (by omega) (by omega)
      rwa [show M + t - j + (j + r - t) + t - k = L - r + (t - k) by omega]
  · simp

/-- If `d` divides `C(s + r, r)` for `μ + 1 ≤ s ≤ μ + r`, then `d ∣ β_F(j, t)` for all `j ≤ μ`. -/
lemma dvd_betaF {L M r : ℕ} (hLM : L = M + 2 * r) (d : ℕ)
    (hd : ∀ s, M + 1 ≤ s → s ≤ M + r → d ∣ (s + r).choose r) {j t : ℕ} :
    (d : ℤ) ∣ betaF L M r j t := by
  unfold betaF
  have hc := choose_glue_comm j r t
  by_cases h1 : j + t ≤ M
  · rw [if_pos (by omega), if_pos h1, hc, sub_self]; exact dvd_zero _
  rw [if_neg h1]
  split_ifs with h2
  · rw [hc, sub_zero]
    apply Int.natCast_dvd_natCast.mpr
    apply Dvd.dvd.mul_left
    have := hd (j + t) (by omega) (by omega)
    rwa [Nat.choose_symm_of_eq_add (show j + t + r = r + (j + t) by ring)] at this
  · simp

/-! ### Kummer computations for `p^ν` -/

open ColouredSand.Blocks

variable {p : ℕ} [hp : Fact p.Prime]

/-- `p^ν ∣ C(λ − r + m, m)` for `1 ≤ m ≤ r` (from (N), first clause). -/
lemma pow_nu_dvd_link {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (m : ℕ) (hm1 : 1 ≤ m) (hmr : m ≤ r) :
    p ^ nu p r a ∣ (lam p r a - r + m).choose m := by
  have hN := (glue_exponent_N (p := p) hr1 hrp ha hra).1
  have hle : nu p r a ≤ padicValNat p ((lam p r a - r + m).choose m) := by
    rw [hN]
    exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hm1, hmr⟩)
  exact (pow_dvd_pow p hle).trans pow_padicValNat_dvd

/-- `p^ν ∣ C(s + r, r)` for `μ + 1 ≤ s ≤ μ + r` (Kummer: carries of `r + s` in base `p`). -/
lemma pow_nu_dvd_tail {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (s : ℕ) (hs1 : mu p r a + 1 ≤ s) (hs2 : s ≤ mu p r a + r) :
    p ^ nu p r a ∣ (s + r).choose r := by
  have h2 := two_le_p (p := p)
  obtain ⟨hmu, _⟩ := mu_add (p := p) r a hrp hra
  have hsq := lt_sq_aux (p := p) ha
  have hpp : p ≤ p * p := Nat.le_mul_of_pos_left p (by omega)
  have hppp : p * p + p < p * p * p := by nlinarith
  have hn1 : 1 ≤ (a + 1) * p := by nlinarith
  have hn : s + r < p * p * p := by
    generalize p * p * p = PPP at hppp ⊢
    generalize (a + 1) * p = N at hsq hmu hn1 ⊢
    generalize p * p = PP at hsq hppp hpp ⊢
    omega
  have hval := choose_val_aux (p := p) (n := s + r) (k := r) (by omega) hn (by omega)
  rw [show s + r - r = s by omega] at hval
  have hle : nu p r a ≤ padicValNat p ((s + r).choose r) := by
    rw [hval]
    unfold nu
    have hs_lt : s < p * p := by
      generalize (a + 1) * p = N at hsq hmu hn1 ⊢
      generalize p * p = PP at hsq hpp ⊢
      omega
    by_cases hr : r ≤ p - 1
    · -- `s = a p + (p − r + d)` with `d < r`: one carry in the units digit
      have hsmod : s % p = s - a * p := by
        have : s = (s - a * p) + a * p := by
          have : a * p + p = (a + 1) * p := by ring
          omega
        rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
        · omega
        · have : a * p + p = (a + 1) * p := by ring
          omega
      have hr' : r % p = r := Nat.mod_eq_of_lt (by omega)
      have c1 : p ≤ r % p + s % p := by
        rw [hsmod, hr']
        have : a * p + p = (a + 1) * p := by ring
        omega
      rw [if_pos c1]
      by_cases haa : a = p - 1
      · rw [if_pos ⟨hr, haa⟩]
        have hN : (a + 1) * p = p * p := by rw [haa, show p - 1 + 1 = p by omega]
        rw [if_pos]
        rw [Nat.mod_eq_of_lt (show r < p * p by omega), Nat.mod_eq_of_lt hs_lt]
        omega
      · rw [if_neg (fun h => haa h.2)]; omega
    · have hrp' : r = p := by omega
      have haa := hra hrp'
      rw [if_neg (by omega)]
      have hN : (a + 1) * p = p * p := by rw [haa, show p - 1 + 1 = p by omega]
      have c2 : p * p ≤ r % (p * p) + s % (p * p) := by
        rw [Nat.mod_eq_of_lt (show r < p * p by omega), Nat.mod_eq_of_lt hs_lt]
        omega
      rw [if_pos c2]
      omega
  exact (pow_dvd_pow p hle).trans pow_padicValNat_dvd

end ColouredSand.Glue
