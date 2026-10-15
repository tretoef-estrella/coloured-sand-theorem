module

public import RequestProject.OddSES.PartP1

/-!
# `CSI4_the_short_exact_sequences.md`: Part P, (P2)–(P3) — the formulas of (I1) with `r = p`

We use CSI3's map `iota L` (Part I, (I1)) for `L : PsiData p N t` with `t + 1 = p`
(i.e. `r = p`, `r − 1 = t = p − 1`): `iota L (A_j n) = F^j α(n)`, `iota L (C_j n) = F^j γ(n)`,
with CSI3's `alphaL p N t`, `gammaL p N t w`. CSI3 proved the intertwining for `t + 2 ≤ p`;
here we prove it for `t + 1 = p`, with the operators `psiF p N p`, `psiE p N p` of
Definition 1.3 for `r = p` (which are those of `Φ_p(V ⊗ N)` by (P1)):

* `iota_F_p`: `ι ∘ psiF p N p = Z.Fd 1 ∘ ι` (the wrap `F^p α(n) = −p α(Fn) + p γ(n)`);
* `iota_E_p`: `ι ∘ psiE p N p = Z.Ed 1 ∘ ι` (on `A_0 n`, `C_0 n` by computation, then by (D1) for
  `r = p`, `psi_D1_p`);
* `iota_H_p`: `ι` is weight-preserving and commutes with `H`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

lemma cast_t_eq {t : ℕ} (ht : t + 1 = p) : (t : ℤ_[p]) = p - 1 := by
  have : ((t + 1 : ℕ) : ℤ_[p]) = p := by rw [ht]
  push_cast at this; linear_combination this

section wrap

variable {t : ℕ} (L : PsiData p N t) (ht : t + 1 = p)
include ht

/-- (P3) `F^p γ(n) = −p·γ(Fn)` in `V ⊗ Ψ_{p−1}(N)` (`r = p`). -/
lemma Zs_Fpow_p_gamma_p (w : ℤ) (n : N.ι → ℤ_[p]) :
    (ZF L ^ p) (gammaL p N t w n) = (-(p : ℤ_[p])) • gammaL p N t (w - 2) (N.Fd 1 n) := by
  have hp := two_le_p' (p := p)
  simp only [gammaL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  rw [Zs_Fpow_tv0, Zs_Fpow_tv1, Zs_Fpow_tv1,
    psiF_pow_cV_wrap t (j := 1) (k := p) (t := 1) (by omega) (by omega) (by omega),
    psiF_pow_cV_wrap t (j := 1) (k := p - 1) (t := 0) (by omega) (by omega) (by omega),
    psiF_pow_aV_wrap t (j := t) (k := p) (t := t) (by omega) (by omega) (by omega),
    psiF_pow_cV_wrap t (j := p - t) (k := t) (t := 0) (by omega) (by omega) (by omega),
    psiF_pow_cV_wrap t (j := 0) (k := p) (t := 0) (by omega) (by omega) (by omega)]
  simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg, smul_sub]
  push_cast
  module

/-- (P3) `F^p α(n) = −p·α(Fn) + p·γ(n)` in `V ⊗ Ψ_{p−1}(N)`, for `n` of weight `w` (`r = p`). -/
lemma Zs_Fpow_p_alpha_p {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    (ZF L ^ p) (alphaL p N t n) = (-(p : ℤ_[p])) • alphaL p N t (N.Fd 1 n) +
      (p : ℤ_[p]) • gammaL p N t w n := by
  have hp := two_le_p' (p := p)
  have h0 : p - (t + 1) = 0 := by omega
  have hpt : p - t = 1 := by omega
  have hct := cast_t_eq ht
  simp only [alphaL, gammaL, h0, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  rw [Zs_Fpow_tv0, Zs_Fpow_tv1,
    psiF_pow_aV_wrap t (j := 0) (k := p) (t := 0) (by omega) (by omega) (by omega),
    psiF_pow_aV t (j := 0) (k := p - 1) (by omega),
    psiF_pow_cV_wrap t (j := 0) (k := p) (t := 0) (by omega) (by omega) (by omega), lie_N hn,
    hpt, pow_zero, Module.End.one_apply, zero_add, show p - 1 = t by omega]
  simp only [map_add, map_sub, map_smul, smul_add, smul_sub, smul_neg, hct]
  module

end wrap

/-! ### (P3) `ι` and `F` -/

section intertwine

variable {t : ℕ} (L : PsiData p N t) (ht : t + 1 = p)
include ht

/-- (P3) `ι ∘ psiF p N p = Z.Fd 1 ∘ ι` (`r = p`, `t = p − 1`). -/
theorem iota_F_p : iota L ∘ₗ psiF p N p = ZF L ∘ₗ iota L := by
  have hp := two_le_p' (p := p)
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · have hn := inWt_single (A := ℤ_[p]) N.wt i
    simp only [LinearMap.comp_apply]
    by_cases hl : j + 1 < p
    · rw [psiF_A_lt p hl, iota_aV L hl, iota_aV L hj, pow_succ', Module.End.mul_apply]
    · obtain rfl : j = p - 1 := by omega
      rw [psiF_A_last, map_add, map_smul, map_smul, Nat.sub_self, iota_aV L (by omega),
        iota_cV L (by omega) hn, iota_aV L hj, ← Module.End.mul_apply, ← pow_succ',
        show p - 1 + 1 = p by omega, Zs_Fpow_p_alpha_p L ht hn]
      simp only [pow_zero, Module.End.one_apply]
  · have hn := inWt_single (A := ℤ_[p]) N.wt i
    simp only [LinearMap.comp_apply]
    by_cases hl : j + 1 < p
    · rw [psiF_C_lt p hl, iota_cV L hl hn, iota_cV L hj hn, pow_succ', Module.End.mul_apply]
    · obtain rfl : j = p - 1 := by omega
      rw [psiF_C_last, map_smul, iota_cV L (by omega) (inWt_F hn), iota_cV L hj hn,
        ← Module.End.mul_apply, ← pow_succ', show p - 1 + 1 = p by omega,
        Zs_Fpow_p_gamma_p L ht, pow_zero, Module.End.one_apply]

end intertwine

/-! ### (P3) weights -/

section weights

variable {t : ℕ} (L : PsiData p N t) (ht : t + 1 = p)
include ht

lemma inWt_alpha_p {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    InWt (Zs L).wt (p * w + p - 1 + p) (alphaL p N t n) := by
  simp only [alphaL, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
  refine inWt_sub' (Doubling.inWt_congr ?_ (inWt_tv L.lat 0 (inWt_aV t 0 hn)))
    (Doubling.inWt_smul _ (Doubling.inWt_congr ?_ (inWt_tv L.lat 1
      (inWt_cV t (p - (t + 1)) (inWt_E hn)))))
  · have : (t : ℤ) = p - 1 := by omega
    simp [this]; ring
  · have : (t : ℤ) = p - 1 := by omega
    rw [show p - (t + 1) = 0 by omega]
    simp [this]; ring

lemma inWt_gamma_p {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    InWt (Zs L).wt (p * w + p - 1 - p) (gammaL p N t w n) :=
  Doubling.inWt_congr (by push_cast [← ht]; ring) (inWt_gamma L hn)

/-- (P3) `ι` is weight-preserving for the weights `psiWt p N p` of Definition 1.3 with `r = p`. -/
lemma iota_single_inWt_p (x : Bool × Fin p × N.ι) :
    InWt (Zs L).wt (psiWt p N p x) (iota L (Pi.single x 1)) := by
  obtain ⟨b, ⟨j, hj⟩, i⟩ := x
  have hn := inWt_single (A := ℤ_[p]) N.wt i
  cases b
  · rw [single_false, iota_aV L hj]
    exact Doubling.inWt_congr (by simp [psiWt]) (inWt_ZFpow L j (inWt_alpha_p L ht hn))
  · rw [single_true, iota_cV L hj hn]
    exact Doubling.inWt_congr (by simp [psiWt]; ring) (inWt_ZFpow L j (inWt_gamma_p L ht hn))

lemma iota_wtPres_p (x : Bool × Fin p × N.ι) (z : Fin 2 × (Bool × Fin p × N.ι))
    (h : psiWt p N p x ≠ (Zs L).wt z) : iota L (Pi.single x 1) z = 0 :=
  iota_single_inWt_p L ht x z (Ne.symm h)

/-- (P3) `ι ∘ H = H ∘ ι` (`r = p`). -/
lemma iota_H_p : iota L ∘ₗ Hop (psiWt p N p) = H (Zs L) ∘ₗ iota L :=
  comm_Hop_of_wtPres (iota L) (iota_wtPres_p L ht)

end weights

/-! ### (P3) `ι` and `E` -/

section E

variable {t : ℕ} (L : PsiData p N t) (ht : t + 1 = p)
include ht

/-- (P3) `ι(E A_0 n) = E ι(A_0 n)` (`r = p`), for `n` of weight `w`. -/
lemma iota_E_A0_p {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    iota L (psiE p N p (aV p 0 n)) = ZE L (iota L (aV p 0 n)) := by
  have hp := two_le_p' (p := p)
  have hm := inWt_E hn
  have hct := cast_t_eq ht
  have h0 : p - (t + 1) = 0 := by omega
  have hc1 : ((p - 1 : ℕ) : ℤ_[p]) = p - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [psiE_A_zero p hn, sub_self, zero_mul, zero_smul, add_zero, map_smul,
    iota_aV L (by omega), iota_aV L (by omega), pow_zero, Module.End.one_apply]
  simp only [alphaL, h0, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    map_sub, map_smul]
  rw [Zs_E_tv0, Zs_E_tv1, Zs_Fpow_tv0, Zs_Fpow_tv1,
    psiF_pow_aV t (j := 0) (k := p - 1) (by omega),
    psiF_pow_aV t (j := 0) (k := p - 1 - 1) (by omega),
    psiF_pow_cV t (j := 0) (k := p - 1) (by omega),
    psiE_A_zero t hn, psiE_C_zero t hm, show p - 1 - t = 0 by omega,
    show t - 1 = p - 1 - 1 by omega]
  simp only [map_add, map_sub, map_smul, smul_add, smul_sub, hc1, hct, zero_add]
  module

/-- (P3) `ι(E C_0 n) = E ι(C_0 n)` (`r = p`), for `n` of weight `w`. -/
lemma iota_E_C0_p {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    iota L (psiE p N p (cV p 0 n)) = ZE L (iota L (cV p 0 n)) := by
  have hp := two_le_p' (p := p)
  have hm := inWt_E hn
  have hct := cast_t_eq ht
  have h0 : p - (t + 1) = 0 := by omega
  have hc1 : ((p - 1 : ℕ) : ℤ_[p]) = p - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [psiE_C_zero p hn, map_sub, map_smul, map_smul, iota_aV L (by omega),
    iota_cV L (by omega) hm, iota_cV L (by omega) hn, pow_zero, Module.End.one_apply]
  simp only [alphaL, gammaL, h0, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  simp only [Zs_E_tv0, Zs_E_tv1, Zs_Fpow_tv0, Zs_Fpow_tv1]
  rw [psiF_pow_aV t (j := 0) (k := p - 1) (by omega),
    psiF_pow_aV t (j := 0) (k := p - 1 - 1) (by omega),
    psiF_pow_cV t (j := 0) (k := p - 1) (by omega),
    psiF_pow_cV_wrap t (j := 1) (k := p - 1) (t := 0) (by omega) (by omega) (by omega),
    psiF_pow_cV t (j := 1) (k := p - 1 - 1) (by omega),
    psiF_pow_aV_wrap t (j := t) (k := p - 1) (t := t - 1) (by omega) (by omega) (by omega),
    psiF_pow_cV t (j := p - t) (k := t - 1) (by omega),
    psiE_C_low t (j := 1) le_rfl (by omega) (by omega) hn,
    psiE_A_low t (j := t) (by omega) le_rfl (by omega) hn, psiE_C_zero t hn,
    show p - t + (t - 1) = p - 1 by omega, show 1 + (p - 1 - 1) = p - 1 by omega,
    show 1 + t - 1 = t by omega, show p + t - 1 - t = p - 1 by omega,
    show t - 1 = p - 1 - 1 by omega, show t = p - 1 by omega]
  simp only [map_add, map_smul, map_sub, smul_add, smul_sub, hc1, zero_add]
  push_cast [hc1, hct]
  module

/-- (P3) If `ι E y = E ι y`, then `ι E F y = E ι F y` (`r = p`; from (D1) for `r = p`). -/
lemma iota_E_step_p {y : Bool × Fin p × N.ι → ℤ_[p]}
    (hy : iota L (psiE p N p y) = ZE L (iota L y)) :
    iota L (psiE p N p (psiF p N p y)) = ZE L (iota L (psiF p N p y)) := by
  rw [psi_D1_p y, map_add,
    ← LinearMap.comp_apply (iota L) (psiF p N p), iota_F_p L ht, LinearMap.comp_apply,
    hy, show iota L (Hop (psiWt p N p) y) = H (Zs L) (iota L y) from
      LinearMap.congr_fun (iota_H_p L ht) y,
    show iota L (psiF p N p y) = ZF L (iota L y) from
      LinearMap.congr_fun (iota_F_p L ht) y]
  exact (Doubling.dp_lie (Zs L) (iota L y)).symm

lemma iota_E_pow_p {y : Bool × Fin p × N.ι → ℤ_[p]}
    (hy : iota L (psiE p N p y) = ZE L (iota L y)) (k : ℕ) :
    iota L (psiE p N p ((psiF p N p ^ k) y)) = ZE L (iota L ((psiF p N p ^ k) y)) := by
  induction k with
  | zero => exact hy
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact iota_E_step_p L ht ih

/-- (P3) `ι ∘ psiE p N p = Z.Ed 1 ∘ ι` (`r = p`). -/
theorem iota_E_p : iota L ∘ₗ psiE p N p = ZE L ∘ₗ iota L := by
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · have h := iota_E_pow_p L ht (iota_E_A0_p L ht (inWt_single (A := ℤ_[p]) N.wt i)) j
    rwa [psiF_pow_aV p (by omega), zero_add] at h
  · have h := iota_E_pow_p L ht (iota_E_C0_p L ht (inWt_single (A := ℤ_[p]) N.wt i)) j
    rwa [psiF_pow_cV p (by omega), zero_add] at h

end E

end ColouredSand.OddTwist
