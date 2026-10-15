module

public import RequestProject.OddTwist.Ops

/-!
# `CSI1_the_odd_twist.md`: Part A (A1) and Part B

`twist p N : DPLattice ℤ_[p]` is `Φ_p(N)`: basis `Fin p × N.ι`, weights `twWt p N`, divided powers
`twFd p N`, `twEd p N` given by the closed formulas of the Setting. A vector `n` "of weight `w`"
of `N` is encoded by C18's `InWt N.wt w n` (all coordinates outside the weight `w` vanish). The
proof follows the sketch of the file: (W), (P0) by inspection, the recursions
`F^{(1)} F^{(r)} = (r+1) F^{(r+1)}`, `E^{(1)} E^{(r)} = (r+1) E^{(r+1)}` and `[E, F] = H` on basis
vectors, and C20's `isDP_of_rec`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset Polynomial

open scoped Nat

variable (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p])

lemma div_le_of_lt {r c : ℕ} (h : r < p * c + p) : r / p ≤ c := by
  have hp := one_le_p p
  have : r / p < c + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    calc r < p * c + p := h
      _ = (c + 1) * p := by ring
  omega

/-! ### The recursions of the divided powers on `Φ_p(N)` -/

/-- (B2, proof) `F^{(1)} F^{(r)} = (r+1) F^{(r+1)}` on `Φ_p(N)`. -/
theorem tw_rec_F (r : ℕ) (x : Fin p × N.ι → ℤ_[p]) :
    twFd p N 1 (twFd p N r x) = ((r : ℤ_[p]) + 1) • twFd p N (r + 1) x := by
  have hp := one_le_p p
  have key : twFd p N 1 ∘ₗ twFd p N r = ((r : ℤ_[p]) + 1) • twFd p N (r + 1) := by
    refine ext_single fun x => ?_
    obtain ⟨j, i⟩ := x
    rw [LinearMap.comp_apply, LinearMap.smul_apply, single_eq_bv]
    have hj := j.isLt
    set c := ((j : ℕ) + r) / p
    set m := ((j : ℕ) + r) % p
    have hdm : (j : ℕ) + r = p * c + m := (Nat.div_add_mod _ _).symm
    have hm : m < p := Nat.mod_lt _ (by omega)
    have hc : r / p ≤ c := div_le_of_lt p (by omega)
    rw [twFd_bv p N r hj, twFdL_eq p N hdm hm, twFd_bv p N (r + 1) hj]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
    by_cases hm1 : m + 1 < p
    · rw [F1_lt p N hm1, twFdL_eq p N (c := c) (m := m + 1) (by omega) hm1]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_smul]
      congr 1
      have h := qc_succ p (div_le_of_lt p (r := r + 1) (c := c) (by omega))
      linear_combination (-1 : ℤ_[p]) ^ c * h
    · have hm' : m = p - 1 := by omega
      rw [hm', F1_last, Doubling.dp_rec_F,
        twFdL_eq p N (c := c + 1) (m := 0) (by rw [Nat.mul_add_one]; omega) (by omega)]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul]
      congr 1
      have h := qc_succ_succ p hc
      rw [pow_succ]
      linear_combination (-(-1 : ℤ_[p]) ^ c) * h
  exact LinearMap.congr_fun key x

/-- (B2, proof) `E^{(1)} E^{(r)} = (r+1) E^{(r+1)}` on `Φ_p(N)`. -/
theorem tw_rec_E (r : ℕ) (x : Fin p × N.ι → ℤ_[p]) :
    twEd p N 1 (twEd p N r x) = ((r : ℤ_[p]) + 1) • twEd p N (r + 1) x := by
  have hp := one_le_p p
  have key : twEd p N 1 ∘ₗ twEd p N r = ((r : ℤ_[p]) + 1) • twEd p N (r + 1) := by
    refine ext_single fun x => ?_
    obtain ⟨j, i⟩ := x
    rw [LinearMap.comp_apply, LinearMap.smul_apply, single_eq_bv]
    have hj := j.isLt
    have hδ := inWt_single (A := ℤ_[p]) N.wt i
    set w := N.wt i
    set t := r + p - 1 - (j : ℕ)
    set c := t / p
    set q := t % p
    have ht : t = p * c + q := (Nat.div_add_mod _ _).symm
    have hq : q < p := Nat.mod_lt _ (by omega)
    have h : r + (p - 1 - q) = (j : ℕ) + p * c := by omega
    have hm : p - 1 - q < p := by omega
    set m := p - 1 - q
    rw [twEd_bv p N r hj hδ, twEdL_eq p N w h hm hj, twEd_bv p N (r + 1) hj hδ]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
    have hz := inWt_PP p N w (Sset p j r) hδ
    have hy := N.isDP.inWt_Ed c hz
    by_cases hm1 : 1 ≤ m
    · obtain ⟨hS, hnot⟩ := Sset_succ_pos p h hm1 hm
      rw [E1_pos p N hm1 hm hy, twEdL_eq p N w (c := c) (m := m - 1) (by omega) (by omega) hj, hS]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply]
      rw [PP_insert p N w hnot, aeval_pFactor, FE_Ed p N c hz,
        qc_succ p (div_le_of_lt p (r := r + 1) (c := c) (by omega))]
      simp only [map_add, map_sub, map_smul, smul_smul]
      push_cast
      module
    · have hm0 : m = 0 := by omega
      have h0 : r = (j : ℕ) + p * c := by omega
      rw [hm0, E1_zero, Doubling.dp_rec_E,
        twEdL_eq p N w (c := c + 1) (m := p - 1) (by rw [Nat.mul_add_one]; omega) (by omega) hj,
        Sset_succ_zero p h0]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul]
      congr 1
      have h := qc_succ_succ p (div_le_of_lt p (r := r) (c := c) (by omega))
      rw [pow_succ]
      linear_combination (-(-1 : ℤ_[p]) ^ c) * h
  exact LinearMap.congr_fun key x

/-! ### `[E, F] = H` -/

/-- (A1, proof) The Lie relation `[E, F] = H` on `Φ_p(N)`. -/
theorem tw_lie (x : Fin p × N.ι → ℤ_[p]) :
    twEd p N 1 (twFd p N 1 x) = twFd p N 1 (twEd p N 1 x) + Hop (twWt p N) x := by
  have hp := two_le_p p
  have key : twEd p N 1 ∘ₗ twFd p N 1 = twFd p N 1 ∘ₗ twEd p N 1 + Hop (twWt p N) := by
    refine ext_single fun x => ?_
    obtain ⟨j, i⟩ := x
    simp only [LinearMap.comp_apply, LinearMap.add_apply]
    rw [single_eq_bv]
    have hj := j.isLt
    have hδ := inWt_single (A := ℤ_[p]) N.wt i
    rw [Doubling.Hop_of_inWt (inWt_tw p N j hδ)]
    by_cases hj1 : (j : ℕ) + 1 < p
    · rw [F1_lt p N hj1, E1_pos p N (by omega) hj1 hδ, show (j : ℕ) + 1 - 1 = j by omega]
      rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
      · rw [h0, E1_zero, map_smul, F1_last]
        simp only [map_add, map_smul, smul_smul]
        push_cast
        module
      · rw [E1_pos p N h0 hj hδ, F1_lt p N (show (j : ℕ) - 1 + 1 < p by omega),
          show (j : ℕ) - 1 + 1 = j by omega]
        simp only [map_add, map_smul]
        push_cast
        module
    · have hjp : (j : ℕ) = p - 1 := by omega
      have hc : (((p - 1 : ℕ)) : ℤ) = (p : ℤ) - 1 := by omega
      rw [hjp, F1_last, map_smul, E1_zero, smul_smul, Doubling.dp_lie,
        E1_pos p N (by omega) (by omega) hδ, F1_lt p N (show p - 1 - 1 + 1 < p by omega),
        show p - 1 - 1 + 1 = p - 1 by omega]
      dsimp only [H]
      rw [Doubling.Hop_of_inWt hδ]
      simp only [map_add, map_smul, hc]
      push_cast
      module
  exact LinearMap.congr_fun key x

/-! ### (W) and (P0) on `Φ_p(N)` -/

lemma tw_W_F (x : Fin p × N.ι) (r : ℕ) (y : Fin p × N.ι)
    (hy : twWt p N y ≠ twWt p N x - 2 * r) : twFd p N r (Pi.single x 1) y = 0 := by
  obtain ⟨j, i⟩ := x
  have hp := one_le_p p
  have hδ := inWt_single (A := ℤ_[p]) N.wt i
  have key : InWt (twWt p N) (twWt p N (j, i) - 2 * r) (twFd p N r (Pi.single (j, i) 1)) := by
    rw [single_eq_bv, twFd_bv p N r j.isLt]
    set c := ((j : ℕ) + r) / p
    set m := ((j : ℕ) + r) % p
    have hdm : (j : ℕ) + r = p * c + m := (Nat.div_add_mod _ _).symm
    have hm : m < p := Nat.mod_lt _ (by omega)
    have hZ : ((j : ℕ) : ℤ) + r = p * c + m := by exact_mod_cast hdm
    rw [twFdL_eq p N hdm hm]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply]
    exact Doubling.inWt_smul _ (Doubling.inWt_congr (by simp only [twWt]; linear_combination 2 * hZ)
      (inWt_tw p N m (N.isDP.inWt_Fd c hδ)))
  exact key y hy

lemma tw_W_E (x : Fin p × N.ι) (r : ℕ) (y : Fin p × N.ι)
    (hy : twWt p N y ≠ twWt p N x + 2 * r) : twEd p N r (Pi.single x 1) y = 0 := by
  obtain ⟨j, i⟩ := x
  have hp := one_le_p p
  have hj := j.isLt
  have hδ := inWt_single (A := ℤ_[p]) N.wt i
  have key : InWt (twWt p N) (twWt p N (j, i) + 2 * r) (twEd p N r (Pi.single (j, i) 1)) := by
    rw [single_eq_bv, twEd_bv p N r hj hδ]
    set t := r + p - 1 - (j : ℕ)
    set c := t / p
    set q := t % p
    have ht : t = p * c + q := (Nat.div_add_mod _ _).symm
    have hq : q < p := Nat.mod_lt _ (by omega)
    have h : r + (p - 1 - q) = (j : ℕ) + p * c := by omega
    have hm : p - 1 - q < p := by omega
    have hZ : (r : ℤ) + ((p - 1 - q : ℕ) : ℤ) = ((j : ℕ) : ℤ) + p * c := by exact_mod_cast h
    rw [twEdL_eq p N _ h hm hj]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply]
    exact Doubling.inWt_smul _ (Doubling.inWt_congr
      (by simp only [twWt]; linear_combination (-2) * hZ)
      (inWt_tw p N _ (N.isDP.inWt_Ed c (inWt_PP p N _ _ hδ))))
  exact key y hy

lemma tw_P0_F : twFd p N 0 = 1 := by
  refine ext_single fun x => ?_
  obtain ⟨j, i⟩ := x
  rw [single_eq_bv, twFd_bv p N 0 j.isLt, twFdL_eq p N (c := 0) (m := j) (by ring) j.isLt]
  simp [qc_zero_zero, N.isDP.P0_F]

lemma tw_P0_E : twEd p N 0 = 1 := by
  refine ext_single fun x => ?_
  obtain ⟨j, i⟩ := x
  have hδ := inWt_single (A := ℤ_[p]) N.wt i
  rw [single_eq_bv, twEd_bv p N 0 j.isLt hδ,
    twEdL_eq p N _ (c := 0) (m := j) (by ring) j.isLt j.isLt, Sset_zero, PP_empty]
  simp [qc_zero_zero, N.isDP.P0_E]

/-! ### `Φ_p(N)` -/

lemma tw_recData : Doubling.RecData (twWt p N) (twFd p N) (twEd p N) :=
  ⟨tw_W_F p N, tw_W_E p N, tw_P0_F p N, tw_P0_E p N, tw_rec_F p N, tw_rec_E p N, tw_lie p N⟩

/-- (A1) `Φ_p(N)` as a DP-lattice over `ℤ_[p]`: basis `Fin p × N.ι`, weights
`wt(j, i) = p·w_i + p − 1 − 2j`, and `F^{(r)}`, `E^{(r)}` given by the closed formulas of the
Setting. -/
def twist (N : DPLattice ℤ_[p]) : DPLattice ℤ_[p] where
  ι := Fin p × N.ι
  wt := twWt p N
  Fd := twFd p N
  Ed := twEd p N
  isDP := Doubling.isDP_of_rec (tw_recData p N)

/-- (A1) The data of `Φ_p(N)` (weights `twWt p N`, closed formulas `twFd p N`, `twEd p N`)
satisfy `IsDP`: (W) for `F` and `E`, (P0), (P1) for `F` and `E`, and (K). -/
theorem A1 : IsDP (twWt p N) (twFd p N) (twEd p N) := Doubling.isDP_of_rec (tw_recData p N)

/-- (A1) `twist p N` is the DP-lattice `Φ_p(N)` with the data of the Setting. -/
theorem twist_data : (twist p N).ι = (Fin p × N.ι) ∧ (twist p N).wt = twWt p N ∧
    (twist p N).Fd = twFd p N ∧ (twist p N).Ed = twEd p N := ⟨rfl, rfl, rfl, rfl⟩

/-- (B1) The single operators of `Φ_p(N)`, for every vector `n` of `N` (and, where the formula
involves the weight, for every `n` of weight `w`):
`F(b_j n) = b_{j+1} n` for `j ≤ p − 2`; `F(b_{p−1} n) = −p · b_0 (F n)`;
`E(b_j n) = b_{j−1}(g_j n)` with `g_j = p²·X + j(p·w + p − j)` for `1 ≤ j ≤ p − 1`;
`E(b_0 n) = −p · b_{p−1}(E n)`; `H(b_j n) = (p·w + p − 1 − 2j) · b_j n`. -/
theorem B1 :
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]), j + 1 < p → (twist p N).Fd 1 (bv p j n) = bv p (j + 1) n) ∧
    (∀ n : N.ι → ℤ_[p], (twist p N).Fd 1 (bv p (p - 1) n) = (-(p : ℤ_[p])) • bv p 0 (N.Fd 1 n)) ∧
    (∀ (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]), 1 ≤ j → j < p → InWt N.wt w n →
      (twist p N).Ed 1 (bv p j n) = bv p (j - 1)
        ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) + (((j : ℤ) * (p * w + p - j) : ℤ) : ℤ_[p]) • n)) ∧
    (∀ n : N.ι → ℤ_[p], (twist p N).Ed 1 (bv p 0 n) = (-(p : ℤ_[p])) • bv p (p - 1) (N.Ed 1 n)) ∧
    (∀ (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]), InWt N.wt w n →
      H (twist p N) (bv p j n) = ((p * w + p - 1 - 2 * j : ℤ) : ℤ_[p]) • bv p j n) :=
  ⟨fun _ n hj => F1_lt p N hj n, F1_last p N, fun _ _ _ h1 hj hn => E1_pos p N h1 hj hn,
    E1_zero p N, fun j _ _ hn => Doubling.Hop_of_inWt (inWt_tw p N j hn)⟩

/-- (B2) On `Φ_p(N)`, `r! • F^{(r)} = (F^{(1)})^r` and `r! • E^{(r)} = (E^{(1)})^r` for every
`r`. -/
theorem B2 (r : ℕ) :
    ((r ! : ℕ) : ℤ_[p]) • (twist p N).Fd r = (twist p N).Fd 1 ^ r ∧
    ((r ! : ℕ) : ℤ_[p]) • (twist p N).Ed r = (twist p N).Ed 1 ^ r :=
  ⟨Doubling.factorial_smul_of_rec _ (tw_P0_F p N) (tw_rec_F p N) r,
    Doubling.factorial_smul_of_rec _ (tw_P0_E p N) (tw_rec_E p N) r⟩

/-- (B3) The formula of (b) for every vector `n` of `N` (and every slot `j ≤ p − 1`):
`F^{(r)}(b_j n) = (−1)^c · q(c, r) · b_{j+r−pc} F^{(c)} n` with `c = (j + r)/p`.
In addition (more than the file asks), the closed `E`-formula holds for every vector `n` of
weight `w`: `E^{(r)}(b_j n) = (−1)^c · q(c, r) · b_{j−r+pc} E^{(c)} P_{j,r}(n)` with
`c = (r + p − 1 − j)/p` and `P_{j,r}` built with `w`. -/
theorem B3 (r j : ℕ) (hj : j < p) :
    (∀ n : N.ι → ℤ_[p], (twist p N).Fd r (bv p j n) =
      ((-1 : ℤ_[p]) ^ ((j + r) / p) * qc p ((j + r) / p) r) •
        bv p (j + r - p * ((j + r) / p)) (N.Fd ((j + r) / p) n)) ∧
    (∀ (w : ℤ) (n : N.ι → ℤ_[p]), InWt N.wt w n → (twist p N).Ed r (bv p j n) =
      ((-1 : ℤ_[p]) ^ ((r + p - 1 - j) / p) * qc p ((r + p - 1 - j) / p) r) •
        bv p (j + p * ((r + p - 1 - j) / p) - r)
          (N.Ed ((r + p - 1 - j) / p) (PP p N w (Sset p j r) n))) := by
  refine ⟨fun n => ?_, fun w n hn => ?_⟩
  · show twFd p N r (bv p j n) = _
    rw [twFd_bv p N r hj, twFdL, ← Nat.mod_eq_sub_mul_div]; rfl
  · show twEd p N r (bv p j n) = _
    rw [twEd_bv p N r hj hn, twEdL]; rfl

end ColouredSand.OddTwist
