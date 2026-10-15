module

public import RequestProject.OddTwist.Functor

/-!
# `CSI1_the_odd_twist.md`: Part D — the basis `x_R` and the coefficients `c_R`, `d_R`

Encodings (C18's `Δ_A(l) = delta ℤ_[p] l`, `∇_A(l) = nabla ℤ_[p] l`, basis `Fin (l + 1)`, with
C20's basis vectors `e_s = Doubling.eD l s`, `w_s = Doubling.eN l s`):

* `lam p μ = p·μ + p − 1` is `λ`.
* The basis of `Φ_p(Δ_A(μ))` (resp. `Φ_p(∇_A(μ))`) ordered by weight: for `R : Fin (λ + 1)`,
  `xD p μ R = b_{R mod p} e_{R / p}` (resp. `xN p μ R = b_{R mod p} w_{R / p}`), i.e.
  `x_R = b_j e_s` for `R = p·s + j`, `0 ≤ j ≤ p − 1` (`xD_eq`, `xN_eq`).
* `cD p R` is `c_R` (`c_0 = 1`, `c_{R+1} = c_R / (R+1)` if `R mod p ≤ p − 2`, i.e.
  `R mod p ≠ p − 1`, and `c_{R+1} = −c_R` if `R mod p = p − 1`; the division is multiplication by
  `Ring.inverse (R + 1)`, a genuine inverse as `R + 1` is prime to `p`), and `cDinv p R` is
  `c_R^{-1}` (same recursion with `R + 1` instead of `1/(R+1)`).
* `dN p μ R` is `d_R` (`d_0 = 1`, `d_{R+1} = d_R / (λ − R)` if `R mod p ≠ p − 1`,
  `d_{R+1} = −d_R` if `R mod p = p − 1`) and `dNinv p μ R` is `d_R^{-1}`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset Doubling

open scoped Nat

variable (p : ℕ) [Fact p.Prime]

/-- Part D: `λ = p·μ + p − 1`. -/
abbrev lam (μ : ℕ) : ℕ := p * μ + p - 1

lemma lam_succ (μ : ℕ) : lam p μ + 1 = p * μ + p := by have := one_le_p p; simp only [lam]; omega

lemma div_lt_of_fin (μ : ℕ) (R : Fin (lam p μ + 1)) : (R : ℕ) / p < μ + 1 := by
  have hR : (R : ℕ) < p * μ + p := lt_of_lt_of_eq R.isLt (lam_succ p μ)
  rw [Nat.div_lt_iff_lt_mul (by have := one_le_p p; omega)]
  calc (R : ℕ) < p * μ + p := hR
    _ = (μ + 1) * p := by ring

/-! ### The vectors `x_R` -/

/-- (D1) the `R`-th basis vector of `Φ_p(Δ_A(μ))`, ordered by weight: `x_R = b_{R mod p} e_{R/p}`. -/
def xD (μ : ℕ) (R : Fin (lam p μ + 1)) : Fin p × (delta ℤ_[p] μ).ι → ℤ_[p] :=
  bv p ((R : ℕ) % p) (eD μ ⟨(R : ℕ) / p, div_lt_of_fin p μ R⟩)

/-- (D2) the `R`-th basis vector of `Φ_p(∇_A(μ))`, ordered by weight: `x_R = b_{R mod p} w_{R/p}`. -/
def xN (μ : ℕ) (R : Fin (lam p μ + 1)) : Fin p × (nabla ℤ_[p] μ).ι → ℤ_[p] :=
  bv p ((R : ℕ) % p) (eN μ ⟨(R : ℕ) / p, div_lt_of_fin p μ R⟩)

lemma xD_eq (μ : ℕ) (R : Fin (lam p μ + 1)) (s : Fin (μ + 1)) (j : ℕ) (h : (R : ℕ) = p * s + j)
    (hj : j < p) : xD p μ R = bv p j (eD μ s) := by
  obtain ⟨h1, h2⟩ := div_mod_unique h hj
  rw [xD, h2]; congr 2; exact Fin.ext h1

lemma xN_eq (μ : ℕ) (R : Fin (lam p μ + 1)) (s : Fin (μ + 1)) (j : ℕ) (h : (R : ℕ) = p * s + j)
    (hj : j < p) : xN p μ R = bv p j (eN μ s) := by
  obtain ⟨h1, h2⟩ := div_mod_unique h hj
  rw [xN, h2]; congr 2; exact Fin.ext h1

/-- (D1), (D2): the index `R = p·s + j` of the basis vector `b_j e_s = x_R`. -/
def xIdx (μ : ℕ) (x : Fin p × Fin (μ + 1)) : Fin (lam p μ + 1) :=
  ⟨p * (x.2 : ℕ) + x.1, by
    have h1 := x.1.isLt; have h2 := x.2.isLt
    have : p * (x.2 : ℕ) ≤ p * μ := Nat.mul_le_mul_left _ (by omega)
    rw [lam_succ]; omega⟩

lemma xD_xIdx (μ : ℕ) (x : Fin p × Fin (μ + 1)) :
    xD p μ (xIdx p μ x) = Pi.single (x : Fin p × (delta ℤ_[p] μ).ι) 1 := by
  obtain ⟨j, s⟩ := x
  rw [single_eq_bv, xD_eq p μ _ s j rfl j.isLt]; rfl

lemma xN_xIdx (μ : ℕ) (x : Fin p × Fin (μ + 1)) :
    xN p μ (xIdx p μ x) = Pi.single (x : Fin p × (nabla ℤ_[p] μ).ι) 1 := by
  obtain ⟨j, s⟩ := x
  rw [single_eq_bv, xN_eq p μ _ s j rfl j.isLt]; rfl

lemma xIdx_div_mod (μ : ℕ) (R : Fin (lam p μ + 1)) :
    xIdx p μ (⟨(R : ℕ) % p, Nat.mod_lt _ (by have := one_le_p p; omega)⟩,
      ⟨(R : ℕ) / p, div_lt_of_fin p μ R⟩) = R :=
  Fin.ext (by simp only [xIdx]; exact Nat.div_add_mod (R : ℕ) p)

lemma xD_eq_single (μ : ℕ) (R : Fin (lam p μ + 1)) :
    xD p μ R = Pi.single ((⟨(R : ℕ) % p, Nat.mod_lt _ (by have := one_le_p p; omega)⟩,
      ⟨(R : ℕ) / p, div_lt_of_fin p μ R⟩) : Fin p × (delta ℤ_[p] μ).ι) 1 := by
  rw [xD, eD, single_eq_bv]

lemma xN_eq_single (μ : ℕ) (R : Fin (lam p μ + 1)) :
    xN p μ R = Pi.single ((⟨(R : ℕ) % p, Nat.mod_lt _ (by have := one_le_p p; omega)⟩,
      ⟨(R : ℕ) / p, div_lt_of_fin p μ R⟩) : Fin p × (nabla ℤ_[p] μ).ι) 1 := by
  rw [xN, eN, single_eq_bv]

/-! ### The weights of `x_R` -/

lemma lam_cast (μ : ℕ) : ((lam p μ : ℕ) : ℤ) = p * μ + p - 1 := by
  have := one_le_p p
  have h : lam p μ + 1 = p * μ + p := lam_succ p μ
  have : ((lam p μ : ℕ) : ℤ) + 1 = p * μ + p := by exact_mod_cast h
  linarith

lemma H_xD (μ : ℕ) (R : Fin (lam p μ + 1)) :
    Hop (twWt p (delta ℤ_[p] μ)) (xD p μ R) =
      ((((lam p μ : ℕ) : ℤ) - 2 * (R : ℕ) : ℤ) : ℤ_[p]) • xD p μ R := by
  have hR : (R : ℕ) = p * ((R : ℕ) / p) + (R : ℕ) % p := (Nat.div_add_mod _ _).symm
  rw [xD, Hop_of_inWt (inWt_tw p _ _ (wt_eD μ _))]
  congr 2
  have hZ : ((R : ℕ) : ℤ) = p * (((R : ℕ) / p : ℕ) : ℤ) + (((R : ℕ) % p : ℕ) : ℤ) := by
    exact_mod_cast hR
  rw [lam_cast]; linear_combination 2 * hZ

lemma H_xN (μ : ℕ) (R : Fin (lam p μ + 1)) :
    Hop (twWt p (nabla ℤ_[p] μ)) (xN p μ R) =
      ((((lam p μ : ℕ) : ℤ) - 2 * (R : ℕ) : ℤ) : ℤ_[p]) • xN p μ R := by
  have hR : (R : ℕ) = p * ((R : ℕ) / p) + (R : ℕ) % p := (Nat.div_add_mod _ _).symm
  rw [xN, Hop_of_inWt (inWt_tw p _ _ (wt_eN μ _))]
  congr 2
  have hZ : ((R : ℕ) : ℤ) = p * (((R : ℕ) / p : ℕ) : ℤ) + (((R : ℕ) % p : ℕ) : ℤ) := by
    exact_mod_cast hR
  rw [lam_cast]; linear_combination 2 * hZ

/-! ### Units -/

/-- If `R mod p ≠ p − 1`, then `R + 1` is prime to `p`. -/
lemma not_dvd_succ {R : ℕ} (h : R % p ≠ p - 1) : ¬ p ∣ R + 1 := by
  rintro ⟨k, hk⟩
  have hp := one_le_p p
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0; simp at hk
  · have := (div_mod_unique (p := p) (t := R) (c := k - 1) (m := p - 1)
      (by rw [Nat.mul_sub_one]; have : p ≤ p * k := Nat.le_mul_of_pos_right p h0; omega)
      (by omega)).2
    exact h this

lemma isUnit_succ {R : ℕ} (h : R % p ≠ p - 1) : IsUnit (((R + 1 : ℕ)) : ℤ_[p]) :=
  isUnit_natCast_of_not_dvd p (not_dvd_succ p h)

/-- If `R ≤ λ` and `R mod p ≠ p − 1`, then `λ − R` is prime to `p`. -/
lemma not_dvd_lam_sub {μ R : ℕ} (hR : R ≤ lam p μ) (h : R % p ≠ p - 1) : ¬ p ∣ lam p μ - R := by
  have hp := one_le_p p
  have hR' : R ≤ p * μ + p - 1 := hR
  set s := R / p
  set j := R % p
  have hRs : R = p * s + j := (Nat.div_add_mod _ _).symm
  have hj : j < p := Nat.mod_lt _ (by omega)
  have hs : s ≤ μ := by
    by_contra hs
    have : p * (μ + 1) ≤ p * s := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add_one] at this
    omega
  obtain ⟨t, ht⟩ : ∃ t, μ = s + t := ⟨μ - s, by omega⟩
  have e : lam p μ - R = p * t + (p - 1 - j) := by
    simp only [lam]; rw [ht, Nat.mul_add]; omega
  rw [Nat.dvd_iff_mod_eq_zero, (div_mod_unique e (by omega)).2]
  omega

lemma isUnit_lam_sub {μ R : ℕ} (hR : R ≤ lam p μ) (h : R % p ≠ p - 1) :
    IsUnit (((lam p μ - R : ℕ)) : ℤ_[p]) :=
  isUnit_natCast_of_not_dvd p (not_dvd_lam_sub p hR h)

/-! ### The coefficients `c_R` -/

/-- (D1) `c_R`: `c_0 = 1`, `c_{R+1} = c_R / (R+1)` if `R mod p ≠ p − 1`, `c_{R+1} = −c_R` if
`R mod p = p − 1`. -/
def cD : ℕ → ℤ_[p]
  | 0 => 1
  | R + 1 => if R % p = p - 1 then -cD R else Ring.inverse (((R + 1 : ℕ)) : ℤ_[p]) * cD R

/-- (D1) `c_R^{-1}`. -/
def cDinv : ℕ → ℤ_[p]
  | 0 => 1
  | R + 1 => if R % p = p - 1 then -cDinv R else (((R + 1 : ℕ)) : ℤ_[p]) * cDinv R

lemma cD_zero : cD p 0 = 1 := rfl

lemma cD_succ_wrap {R : ℕ} (h : R % p = p - 1) : cD p (R + 1) = -cD p R := by
  rw [cD, if_pos h]

lemma cD_succ {R : ℕ} (h : R % p ≠ p - 1) :
    cD p (R + 1) = Ring.inverse (((R + 1 : ℕ)) : ℤ_[p]) * cD p R := by
  rw [cD, if_neg h]

/-- (D1) `c_{R+1} = c_R / (R+1)` for `R mod p ≤ p − 2`, in the form `(R+1) · c_{R+1} = c_R`. -/
lemma succ_mul_cD_succ {R : ℕ} (h : R % p ≠ p - 1) :
    (((R + 1 : ℕ)) : ℤ_[p]) * cD p (R + 1) = cD p R := by
  rw [cD_succ p h, ← mul_assoc, Ring.mul_inverse_cancel _ (isUnit_succ p h), one_mul]

lemma cDinv_mul_cD (R : ℕ) : cDinv p R * cD p R = 1 := by
  induction R with
  | zero => simp [cDinv, cD]
  | succ R ih =>
    by_cases h : R % p = p - 1
    · rw [cDinv, cD, if_pos h, if_pos h, neg_mul_neg, ih]
    · rw [cDinv, cD, if_neg h, if_neg h]
      calc (((R + 1 : ℕ)) : ℤ_[p]) * cDinv p R * (Ring.inverse (((R + 1 : ℕ)) : ℤ_[p]) * cD p R)
          = ((((R + 1 : ℕ)) : ℤ_[p]) * Ring.inverse (((R + 1 : ℕ)) : ℤ_[p])) *
              (cDinv p R * cD p R) := by ring
        _ = 1 := by rw [Ring.mul_inverse_cancel _ (isUnit_succ p h), ih, one_mul]

/-- (D1) every `c_R` is a unit of `ℤ_[p]`. -/
lemma isUnit_cD (R : ℕ) : IsUnit (cD p R) :=
  isUnit_iff_exists_inv.mpr ⟨cDinv p R, by rw [mul_comm]; exact cDinv_mul_cD p R⟩

/-! ### The coefficients `d_R` -/

/-- (D2) `d_R`: `d_0 = 1`, `d_{R+1} = d_R / (λ − R)` if `R mod p ≠ p − 1`, `d_{R+1} = −d_R` if
`R mod p = p − 1` (`λ = p·μ + p − 1`). -/
def dN (μ : ℕ) : ℕ → ℤ_[p]
  | 0 => 1
  | R + 1 => if R % p = p - 1 then -dN μ R
      else Ring.inverse (((lam p μ - R : ℕ)) : ℤ_[p]) * dN μ R

/-- (D2) `d_R^{-1}`. -/
def dNinv (μ : ℕ) : ℕ → ℤ_[p]
  | 0 => 1
  | R + 1 => if R % p = p - 1 then -dNinv μ R else (((lam p μ - R : ℕ)) : ℤ_[p]) * dNinv μ R

lemma dN_zero (μ : ℕ) : dN p μ 0 = 1 := rfl

lemma dN_succ_wrap (μ : ℕ) {R : ℕ} (h : R % p = p - 1) : dN p μ (R + 1) = -dN p μ R := by
  rw [dN, if_pos h]

lemma dN_succ (μ : ℕ) {R : ℕ} (h : R % p ≠ p - 1) :
    dN p μ (R + 1) = Ring.inverse (((lam p μ - R : ℕ)) : ℤ_[p]) * dN p μ R := by
  rw [dN, if_neg h]

/-- (D2) `d_{R+1} = d_R / (λ − R)` for `R mod p ≤ p − 2` (and `R ≤ λ`), in the form
`(λ − R) · d_{R+1} = d_R`. -/
lemma lam_sub_mul_dN_succ (μ : ℕ) {R : ℕ} (hR : R ≤ lam p μ) (h : R % p ≠ p - 1) :
    (((lam p μ - R : ℕ)) : ℤ_[p]) * dN p μ (R + 1) = dN p μ R := by
  rw [dN_succ p μ h, ← mul_assoc, Ring.mul_inverse_cancel _ (isUnit_lam_sub p hR h), one_mul]

lemma dNinv_mul_dN (μ : ℕ) (R : ℕ) (hR : R ≤ lam p μ) : dNinv p μ R * dN p μ R = 1 := by
  induction R with
  | zero => simp [dNinv, dN]
  | succ R ih =>
    have ih := ih (by omega)
    by_cases h : R % p = p - 1
    · rw [dNinv, dN, if_pos h, if_pos h, neg_mul_neg, ih]
    · rw [dNinv, dN, if_neg h, if_neg h]
      calc (((lam p μ - R : ℕ)) : ℤ_[p]) * dNinv p μ R *
            (Ring.inverse (((lam p μ - R : ℕ)) : ℤ_[p]) * dN p μ R)
          = ((((lam p μ - R : ℕ)) : ℤ_[p]) * Ring.inverse (((lam p μ - R : ℕ)) : ℤ_[p])) *
              (dNinv p μ R * dN p μ R) := by ring
        _ = 1 := by rw [Ring.mul_inverse_cancel _ (isUnit_lam_sub p (by omega) h), ih, one_mul]

/-- (D2) every `d_R` (`R ≤ λ`) is a unit of `ℤ_[p]`. -/
lemma isUnit_dN (μ : ℕ) (R : ℕ) (hR : R ≤ lam p μ) : IsUnit (dN p μ R) :=
  isUnit_iff_exists_inv.mpr ⟨dNinv p μ R, by rw [mul_comm]; exact dNinv_mul_dN p μ R hR⟩

end ColouredSand.OddTwist
