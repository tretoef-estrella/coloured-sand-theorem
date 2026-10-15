module

public import RequestProject.OddSplit.Iota

/-!
# `CSI3_the_split.md`: Part I — (I2) `ι ∘ psiE = Z.Ed 1 ∘ ι`

Proved directly: on the generators `A_0 n`, `C_0 n` by computation in `V ⊗ M`
(`iota_E_A0`, `iota_E_C0`), and then on `A_j n = F^j A_0 n`, `C_j n = F^j C_0 n` from the
`F`-intertwining, the `sl_2` relation (D1) on `Ψ_r(N)` and `[E, F] = H` on `V ⊗ M`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

lemma smul_tv1_pow_pred_cV1 (s : ℕ) {k : ℕ} (hk : k < p) (m : N.ι → ℤ_[p]) :
    (k : ℤ_[p]) • tv 1 ((psiF p N s ^ (k - 1)) (cV p 1 m)) = (k : ℤ_[p]) • tv 1 (cV p k m) := by
  rcases k with _ | k
  · simp
  · rw [Nat.add_sub_cancel, psiF_pow_cV s (by omega), add_comm]

section E

variable {s : ℕ} (L : PsiData p N s) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p)
include hs1 hsp

/-- (I2) `ι(E A_0 n) = E ι(A_0 n)` for `n` of weight `w`. -/
lemma iota_E_A0 {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    iota L (psiE p N (s + 1) (aV p 0 n)) = ZE L (iota L (aV p 0 n)) := by
  have hp := two_le_p' (p := p)
  have hm := inWt_E hn
  have hc1 : ((p - 1 : ℕ) : ℤ_[p]) = p - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hc2 : ((p - (s + 1) : ℕ) : ℤ_[p]) = p - (s + 1) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hc3 : ((p - 1 - (s + 1) : ℕ) : ℤ_[p]) = p - 1 - (s + 1) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hc4 : ((p - (s + 2) : ℕ) : ℤ_[p]) = p - (s + 2) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [psiE_A_zero (s + 1) hn, map_add, map_smul, map_smul, iota_aV L (by omega),
    iota_cV L (by omega) hm, iota_aV L (by omega), pow_zero, Module.End.one_apply]
  simp only [alphaL, gammaL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  rw [Zs_E_tv0, Zs_E_tv1, Zs_Fpow_tv0, Zs_Fpow_tv1, Zs_Fpow_tv1, Zs_Fpow_tv1,
    psiF_pow_aV s (j := 0) (k := p - 1) (by omega),
    psiF_pow_aV s (j := 0) (k := p - 1 - 1) (by omega),
    psiF_pow_cV_wrap s (j := p - (s + 1)) (k := p - 1) (t := p - (s + 2)) (by omega) (by omega)
      (by omega),
    psiF_pow_aV s (j := s) (k := p - 1 - (s + 1)) (by omega),
    psiF_pow_cV s (j := 0) (k := p - 1 - (s + 1)) (by omega),
    psiE_A_zero s hn, psiE_C_low s (j := p - (s + 1)) (by omega) (by omega) (by omega) hm]
  rw [Zs_Fpow_tv0, psiF_pow_cV s (j := 1) (k := p - 1 - (s + 1)) (by omega),
    smul_tv1_pow_pred_cV1 s (by omega),
    show 1 + (p - 1 - (s + 1)) = p - (s + 1) by omega,
    show s + (p - 1 - (s + 1)) = p - 1 - 1 by omega,
    show 0 + (p - 1 - (s + 1)) = p - (s + 2) by omega,
    show p - 1 - (s + 1) = p - (s + 2) by omega,
    show p - (s + 1) - 1 = p - (s + 2) by omega,
    show p - (s + 1) + s - 1 = p - 1 - 1 by omega,
    show p - 1 - s = p - (s + 1) by omega]
  simp only [map_add, map_smul, smul_add, smul_sub, zero_add]
  push_cast [hc1, hc2, hc3, hc4]
  module


/-- (I2) `ι(E C_0 n) = E ι(C_0 n)` for `n` of weight `w`. -/
lemma iota_E_C0 {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    iota L (psiE p N (s + 1) (cV p 0 n)) = ZE L (iota L (cV p 0 n)) := by
  have hp := two_le_p' (p := p)
  have hm := inWt_E hn
  have hc1 : ((p - 1 : ℕ) : ℤ_[p]) = p - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [psiE_C_zero (s + 1) hn, map_sub, map_smul, map_smul, Nat.add_sub_cancel,
    iota_aV L (by omega), iota_cV L (by omega) hm, iota_cV L (by omega) hn, pow_zero,
    Module.End.one_apply]
  simp only [alphaL, gammaL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  rw [Zs_E_tv0, Zs_E_tv1, Zs_E_tv1, Zs_Fpow_tv0, Zs_Fpow_tv1, Zs_Fpow_tv0, Zs_Fpow_tv1,
    Zs_Fpow_tv1,
    psiF_pow_aV s (j := 0) (k := s) (by omega),
    psiF_pow_aV s (j := 0) (k := s - 1) (by omega),
    psiF_pow_cV s (j := p - (s + 1)) (k := s) (by omega),
    psiF_pow_cV_wrap s (j := 1) (k := p - 1) (t := 0) (by omega) (by omega) (by omega),
    psiF_pow_cV s (j := 1) (k := p - 1 - 1) (by omega),
    psiF_pow_aV_wrap s (j := s) (k := p - 1) (t := s - 1) (by omega) (by omega) (by omega),
    psiF_pow_cV s (j := p - s) (k := s - 1) (by omega),
    psiF_pow_cV s (j := 0) (k := p - 1) (by omega),
    psiE_C_low s (j := 1) le_rfl (by omega) (by omega) hn,
    psiE_A_low s (j := s) hs1 le_rfl (by omega) hn, psiE_C_zero s hn,
    show p - (s + 1) + s = p - 1 by omega, show 1 + (p - 1 - 1) = p - 1 by omega,
    show p - s + (s - 1) = p - 1 by omega, show 1 + s - 1 = s by omega,
    show p + s - 1 - s = p - 1 by omega, Nat.sub_self]
  simp only [map_add, map_smul, map_sub, smul_add, smul_sub, zero_add]
  push_cast [hc1]
  module


/-- (I2) If `ι E y = E ι y`, then `ι E F y = E ι F y` (from (D1) on `Ψ_r(N)`, `ι F = F ι`,
`ι H = H ι` and `[E, F] = H` on `V ⊗ M`). -/
lemma iota_E_step {y : Bool × Fin p × N.ι → ℤ_[p]}
    (hy : iota L (psiE p N (s + 1) y) = ZE L (iota L y)) :
    iota L (psiE p N (s + 1) (psiF p N (s + 1) y)) = ZE L (iota L (psiF p N (s + 1) y)) := by
  rw [D1_apply (s + 1) (by omega) (by omega) y, map_add,
    ← LinearMap.comp_apply (iota L) (psiF p N (s + 1)), iota_F L hs1 hsp, LinearMap.comp_apply,
    hy, show iota L (Hop (psiWt p N (s + 1)) y) = H (Zs L) (iota L y) from
      LinearMap.congr_fun (iota_H L hs1 hsp) y,
    show iota L (psiF p N (s + 1) y) = ZF L (iota L y) from
      LinearMap.congr_fun (iota_F L hs1 hsp) y]
  exact (Doubling.dp_lie (Zs L) (iota L y)).symm

lemma iota_E_pow {y : Bool × Fin p × N.ι → ℤ_[p]}
    (hy : iota L (psiE p N (s + 1) y) = ZE L (iota L y)) (k : ℕ) :
    iota L (psiE p N (s + 1) ((psiF p N (s + 1) ^ k) y)) =
      ZE L (iota L ((psiF p N (s + 1) ^ k) y)) := by
  induction k with
  | zero => exact hy
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact iota_E_step L hs1 hsp ih

/-- (I2) `ι ∘ psiE p r N = Z.Ed 1 ∘ ι` (`r = s + 1`). -/
theorem iota_E : iota L ∘ₗ psiE p N (s + 1) = ZE L ∘ₗ iota L := by
  refine ext_aV_cV p (fun j i hj => ?_) (fun j i hj => ?_)
  · have h := iota_E_pow L hs1 hsp (iota_E_A0 L hs1 hsp (inWt_single (A := ℤ_[p]) N.wt i)) j
    rwa [psiF_pow_aV (s + 1) (by omega), zero_add] at h
  · have h := iota_E_pow L hs1 hsp (iota_E_C0 L hs1 hsp (inWt_single (A := ℤ_[p]) N.wt i)) j
    rwa [psiF_pow_cV (s + 1) (by omega), zero_add] at h

end E

end ColouredSand.OddTwist
