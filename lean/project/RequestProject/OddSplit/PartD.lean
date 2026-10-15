module

public import RequestProject.OddSplit.Ops

/-!
# `CSI3_the_split.md`: Part D — (D1) the `sl_2` relation and (D2) the weights

`psiE ∘ psiF − psiF ∘ psiE = H` (`D1`), checked case by case on `A_j n` and `C_j n` from the
formulas of Definition 1.3, `[E, F] = H` on `N` and the weight rules of `N`; and `psiF` lowers,
`psiE` raises the weights `psiWt` by `2` (`D2`). Throughout `1 ≤ r ≤ p − 1`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

/-- `E F n = F E n + w n` on `N`, for `n` of weight `w`. -/
lemma lie_N {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    N.Ed 1 (N.Fd 1 n) = N.Fd 1 (N.Ed 1 n) + (w : ℤ_[p]) • n := by
  rw [Doubling.dp_lie, Doubling.Hop_of_inWt hn]

lemma inWt_F {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) : InWt N.wt (w - 2) (N.Fd 1 n) := by
  have := N.isDP.inWt_Fd 1 hn; simpa using this

lemma inWt_E {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) : InWt N.wt (w + 2) (N.Ed 1 n) := by
  have := N.isDP.inWt_Ed 1 hn; simpa using this

lemma inWt_FE {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    InWt N.wt w (N.Fd 1 (N.Ed 1 n)) := by
  have := inWt_F (inWt_E hn); simpa using this

/-! ### (D1) on `A_j n` -/

section D1

variable (r : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p - 1)
include hr1 hrp

lemma D1_A_zero {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (aV p 0 n)) - psiF p N r (psiE p N r (aV p 0 n)) =
      Hop (psiWt p N r) (aV p 0 n) := by
  have hp := two_le_p' (p := p)
  rw [psiF_A_lt r (by omega), psiE_A_low r (j := 0 + 1) (by omega) (by omega) (by omega) hn,
    psiE_A_zero r hn, H_aV r 0 hn]
  simp only [map_add, map_sub, map_smul, map_neg]
  simp only [psiF_A_last, psiF_C_lt (N := N) r (j := p - 1 - r) (by omega),
    show p + (0 + 1) - 1 - r = p - r by omega, show p - 1 - r + 1 = p - r by omega]
  try simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg]
  push_cast
  module


lemma D1_A_mid {j : ℕ} (h1 : 1 ≤ j) (h2 : j + 1 ≤ r) {w : ℤ} {n : N.ι → ℤ_[p]}
    (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (aV p j n)) - psiF p N r (psiE p N r (aV p j n)) =
      Hop (psiWt p N r) (aV p j n) := by
  have hp := two_le_p' (p := p)
  rw [psiF_A_lt r (by omega), psiE_A_low r (j := j + 1) (by omega) (by omega) (by omega) hn,
    psiE_A_low r h1 (by omega) (by omega) hn, H_aV r j hn]
  simp only [map_add, map_sub, map_smul, map_neg]
  simp only [psiF_A_lt (N := N) r (j := j - 1) (by omega), psiF_C_lt (N := N) r (j := p + j - 1 - r) (by omega),
    show p + (j + 1) - 1 - r = p + j - 1 - r + 1 by omega, show j - 1 + 1 = j by omega,
    Nat.add_sub_cancel]
  try simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg]
  push_cast
  module

lemma D1_A_r {j : ℕ} (h1 : 1 ≤ j) (h2 : j = r) (h3 : j + 1 < p) {w : ℤ} {n : N.ι → ℤ_[p]}
    (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (aV p j n)) - psiF p N r (psiE p N r (aV p j n)) =
      Hop (psiWt p N r) (aV p j n) := by
  have hp := two_le_p' (p := p)
  rw [psiF_A_lt r h3, psiE_A_high r (j := j + 1) (by omega) (by omega) hn,
    psiE_A_low r h1 (by omega) (by omega) hn, H_aV r j hn]
  simp only [map_add, map_sub, map_smul, map_neg]
  simp only [psiF_A_lt (N := N) r (j := j - 1) (by omega), show p + j - 1 - r = p - 1 by omega, psiF_C_last,
    show j - 1 + 1 = j by omega, Nat.add_sub_cancel, show j - r = 0 by omega]
  try simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg]
  push_cast
  module

lemma D1_A_high {j : ℕ} (h1 : r + 1 ≤ j) (h3 : j + 1 < p) {w : ℤ} {n : N.ι → ℤ_[p]}
    (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (aV p j n)) - psiF p N r (psiE p N r (aV p j n)) =
      Hop (psiWt p N r) (aV p j n) := by
  rw [psiF_A_lt r h3, psiE_A_high r (j := j + 1) (by omega) (by omega) hn,
    psiE_A_high r h1 (by omega) hn, H_aV r j hn]
  simp only [map_add, map_sub, map_smul, map_neg]
  simp only [psiF_A_lt (N := N) r (j := j - 1) (by omega), psiF_C_lt (N := N) r (j := j - 1 - r) (by omega),
    show j - 1 + 1 = j by omega, Nat.add_sub_cancel, show j - 1 - r + 1 = j - r by omega]
  try simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg]
  push_cast
  module

lemma D1_A_last {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (aV p (p - 1) n)) - psiF p N r (psiE p N r (aV p (p - 1) n)) =
      Hop (psiWt p N r) (aV p (p - 1) n) := by
  have hp := two_le_p' (p := p)
  have hp1 : ((p - 1 : ℕ) : ℤ_[p]) = p - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hpr : ((p - r : ℕ) : ℤ_[p]) = p - r := by rw [Nat.cast_sub (by omega)]
  rw [psiF_A_last, H_aV r (p - 1) hn]
  simp only [map_add, map_sub, map_smul, map_neg]
  rw [psiE_A_zero r (inWt_F hn), psiE_C_low r (j := p - r) (by omega) le_rfl (by omega) hn,
    lie_N hn, show p - r - 1 = p - 1 - r by omega, show p - r + r - 1 = p - 1 by omega]
  rcases Nat.lt_or_ge r (p - 1) with hlt | hge
  · rw [psiE_A_high r (j := p - 1) (by omega) (by omega) hn]
    simp only [map_add, map_sub, map_smul, map_neg]
    simp only [psiF_A_lt (N := N) r (j := p - 1 - 1) (by omega), psiF_C_lt (N := N) r (j := p - 1 - 1 - r) (by omega),
      show p - 1 - 1 + 1 = p - 1 by omega, show p - 1 - 1 - r + 1 = p - 1 - r by omega]
    simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg, hp1, hpr]
    push_cast [hp1, hpr]
    module
  · have hr : r = p - 1 := by omega
    rw [psiE_A_low r (j := p - 1) (by omega) (by omega) (by omega) hn]
    simp only [map_add, map_sub, map_smul, map_neg]
    simp only [psiF_A_lt (N := N) r (j := p - 1 - 1) (by omega), show p + (p - 1) - 1 - r = p - 1 by omega,
      psiF_C_last, show p - 1 - 1 + 1 = p - 1 by omega, show p - 1 - r = 0 by omega]
    have hrc : (r : ℤ_[p]) = p - 1 := by rw [hr, hp1]
    simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg, hp1, hpr]
    push_cast [hp1, hpr, hrc]
    module

/-! ### (D1) on `C_j n` -/

lemma D1_C_zero {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (cV p 0 n)) - psiF p N r (psiE p N r (cV p 0 n)) =
      Hop (psiWt p N r) (cV p 0 n) := by
  have hp := two_le_p' (p := p)
  rw [psiF_C_lt r (by omega), psiE_C_low r (j := 0 + 1) (by omega) (by omega) (by omega) hn,
    psiE_C_zero r hn, H_cV r 0 hn]
  simp only [map_add, map_sub, map_smul, map_neg]
  simp only [psiF_A_lt (N := N) r (j := r - 1) (by omega), psiF_C_last,
    show 0 + 1 + r - 1 = r - 1 + 1 by omega]
  try simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg]
  push_cast
  module

lemma D1_C_mid {j : ℕ} (h1 : 1 ≤ j) (h2 : j + 1 ≤ p - r) {w : ℤ} {n : N.ι → ℤ_[p]}
    (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (cV p j n)) - psiF p N r (psiE p N r (cV p j n)) =
      Hop (psiWt p N r) (cV p j n) := by
  rw [psiF_C_lt r (by omega), psiE_C_low r (j := j + 1) (by omega) h2 (by omega) hn,
    psiE_C_low r h1 (by omega) (by omega) hn, H_cV r j hn]
  simp only [map_add, map_sub, map_smul, map_neg]
  simp only [psiF_C_lt (N := N) r (j := j - 1) (by omega), psiF_A_lt (N := N) r (j := j + r - 1) (by omega),
    show j - 1 + 1 = j by omega, Nat.add_sub_cancel, show j + 1 + r - 1 = j + r - 1 + 1 by omega]
  try simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg]
  push_cast
  module

lemma D1_C_pr {j : ℕ} (h1 : 1 ≤ j) (h2 : j = p - r) (h3 : j + 1 < p) {w : ℤ}
    {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (cV p j n)) - psiF p N r (psiE p N r (cV p j n)) =
      Hop (psiWt p N r) (cV p j n) := by
  rw [psiF_C_lt r h3, psiE_C_high r (j := j + 1) (by omega) h3 hn,
    psiE_C_low r h1 (by omega) (by omega) hn, H_cV r j hn]
  simp only [map_add, map_sub, map_smul, map_neg]
  simp only [psiF_C_lt (N := N) r (j := j - 1) (by omega), show j + r - 1 = p - 1 by omega, psiF_A_last,
    show j - 1 + 1 = j by omega, Nat.add_sub_cancel, show j + 1 + r - 1 - p = 0 by omega,
    show p - r = j by omega]
  try simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg]
  push_cast
  module

lemma D1_C_high {j : ℕ} (h1 : p - r + 1 ≤ j) (h3 : j + 1 < p) {w : ℤ} {n : N.ι → ℤ_[p]}
    (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (cV p j n)) - psiF p N r (psiE p N r (cV p j n)) =
      Hop (psiWt p N r) (cV p j n) := by
  rw [psiF_C_lt r h3, psiE_C_high r (j := j + 1) (by omega) h3 hn,
    psiE_C_high r h1 (by omega) hn, H_cV r j hn]
  simp only [map_add, map_sub, map_smul, map_neg]
  simp only [psiF_C_lt (N := N) r (j := j - 1) (by omega), psiF_A_lt (N := N) r (j := j + r - 1 - p) (by omega),
    show j - 1 + 1 = j by omega, Nat.add_sub_cancel,
    show j + 1 + r - 1 - p = j + r - 1 - p + 1 by omega]
  try simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg]
  push_cast
  module

lemma D1_C_last {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (cV p (p - 1) n)) - psiF p N r (psiE p N r (cV p (p - 1) n)) =
      Hop (psiWt p N r) (cV p (p - 1) n) := by
  have hp := two_le_p' (p := p)
  have hp1 : ((p - 1 : ℕ) : ℤ_[p]) = p - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [psiF_C_last, H_cV r (p - 1) hn]
  simp only [map_add, map_sub, map_smul, map_neg]
  rw [psiE_C_zero r (inWt_F hn), lie_N hn]
  rcases Nat.lt_or_ge 1 r with hlt | hge
  · rw [psiE_C_high r (j := p - 1) (by omega) (by omega) hn]
    simp only [map_add, map_sub, map_smul, map_neg]
    simp only [psiF_C_lt (N := N) r (j := p - 1 - 1) (by omega), psiF_A_lt (N := N) r (j := p - 1 + r - 1 - p) (by omega),
      show p - 1 - 1 + 1 = p - 1 by omega, show p - 1 + r - 1 - p + 1 = r - 1 by omega]
    simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg]
    push_cast [hp1]
    module
  · have hr : r = 1 := by omega
    subst hr
    rw [psiE_C_low 1 (j := p - 1) (by omega) le_rfl (by omega) hn]
    simp only [map_add, map_sub, map_smul, map_neg]
    simp only [psiF_C_lt (N := N) 1 (j := p - 1 - 1) (by omega), show p - 1 + 1 - 1 = p - 1 by omega,
      psiF_A_last, show p - 1 - 1 + 1 = p - 1 by omega]
    simp only [map_add, map_sub, map_smul, map_neg, smul_add, smul_neg, Nat.sub_self]
    push_cast [hp1]
    module

/-- (D1) on the vectors `A_j n`, `0 ≤ j ≤ p − 1`, `n` of weight `w`. -/
lemma D1_A {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (aV p j n)) - psiF p N r (psiE p N r (aV p j n)) =
      Hop (psiWt p N r) (aV p j n) := by
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; exact D1_A_zero r hr1 hrp hn
  by_cases hl : j + 1 < p
  · rcases Nat.lt_or_ge j r with h | h
    · exact D1_A_mid r hr1 hrp hpos (by omega) hn
    · rcases Nat.lt_or_ge r j with h' | h'
      · exact D1_A_high r hr1 hrp (by omega) hl hn
      · exact D1_A_r r hr1 hrp hpos (by omega) hl hn
  · obtain rfl : j = p - 1 := by omega
    exact D1_A_last r hr1 hrp hn

/-- (D1) on the vectors `C_j n`, `0 ≤ j ≤ p − 1`, `n` of weight `w`. -/
lemma D1_C {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    psiE p N r (psiF p N r (cV p j n)) - psiF p N r (psiE p N r (cV p j n)) =
      Hop (psiWt p N r) (cV p j n) := by
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; exact D1_C_zero r hr1 hrp hn
  by_cases hl : j + 1 < p
  · rcases Nat.lt_or_ge j (p - r) with h | h
    · exact D1_C_mid r hr1 hrp hpos (by omega) hn
    · rcases Nat.lt_or_ge (p - r) j with h' | h'
      · exact D1_C_high r hr1 hrp (by omega) hl hn
      · exact D1_C_pr r hr1 hrp hpos (by omega) hl hn
  · obtain rfl : j = p - 1 := by omega
    exact D1_C_last r hr1 hrp hn

end D1

variable (p N) in
/-- (D1) **The `sl_2` relation.** For `1 ≤ r ≤ p − 1`, `psiE ∘ psiF − psiF ∘ psiE = H` on
`Bool × Fin p × N.ι → ℤ_[p]`, where `H` is the weight operator of the weights `psiWt` of
Part D. -/
theorem psi_D1 (r : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p - 1) :
    psiE p N r ∘ₗ psiF p N r - psiF p N r ∘ₗ psiE p N r = Hop (psiWt p N r) :=
  ext_aV_cV p (fun j i hj => by
      simpa using D1_A r hr1 hrp hj (inWt_single N.wt i))
    (fun j i hj => by simpa using D1_C r hr1 hrp hj (inWt_single N.wt i))

/-- (D1) in the form `E F x = F E x + H x`. -/
lemma D1_apply (r : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p - 1) (x : Bool × Fin p × N.ι → ℤ_[p]) :
    psiE p N r (psiF p N r x) = psiF p N r (psiE p N r x) + Hop (psiWt p N r) x := by
  have := LinearMap.congr_fun (psi_D1 p N r hr1 hrp) x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply] at this
  rw [← this]; abel


/-! ### (D2) weights -/

section D2

lemma inWt_sub' {ι : Type*} {wt : ι → ℤ} {μ : ℤ} {x y : ι → ℤ_[p]} (hx : InWt wt μ x)
    (hy : InWt wt μ y) : InWt wt μ (x - y) := fun j hj => by simp [hx j hj, hy j hj]

lemma inWt_aVz (r k : ℕ) {kz μ ν : ℤ} (hk : (k : ℤ) = kz) (h : ν = p * μ + p - 1 + r - 2 * kz)
    {n : N.ι → ℤ_[p]} (hn : InWt N.wt μ n) : InWt (psiWt p N r) ν (aV p k n) :=
  Doubling.inWt_congr (by rw [h, ← hk]) (inWt_aV r k hn)

lemma inWt_cVz (r k : ℕ) {kz μ ν : ℤ} (hk : (k : ℤ) = kz) (h : ν = p * μ + p - 1 - r - 2 * kz)
    {n : N.ι → ℤ_[p]} (hn : InWt N.wt μ n) : InWt (psiWt p N r) ν (cV p k n) :=
  Doubling.inWt_congr (by rw [h, ← hk]) (inWt_cV r k hn)

lemma inWt_g {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) (c : ℤ_[p]) :
    InWt N.wt w ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) + c • n) :=
  Doubling.inWt_add (Doubling.inWt_smul _ (inWt_FE hn)) (Doubling.inWt_smul _ hn)

variable (r : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p - 1)
include hr1 hrp

lemma psiF_single_inWt (x : Bool × Fin p × N.ι) :
    InWt (psiWt p N r) (psiWt p N r x - 2) (psiF p N r (Pi.single x 1)) := by
  have hp := two_le_p' (p := p)
  obtain ⟨b, ⟨j, hj⟩, i⟩ := x
  have hn := inWt_single (A := ℤ_[p]) N.wt i
  cases b
  · rw [single_false]
    simp only [psiWt, Bool.false_eq_true, if_false]
    by_cases hl : j + 1 < p
    · rw [psiF_A_lt r hl]
      exact inWt_aVz r (j + 1) (kz := j + 1) (by push_cast; ring) (by ring) hn
    · obtain rfl : j = p - 1 := by omega
      rw [psiF_A_last]
      refine Doubling.inWt_add (Doubling.inWt_smul _ (inWt_aVz r 0 (kz := 0) (by simp) ?_
        (inWt_F hn))) (Doubling.inWt_smul _ (inWt_cVz r (p - r) (kz := p - r) (by omega) ?_ hn))
      · push_cast [Nat.cast_sub (show 1 ≤ p by omega)]; ring
      · push_cast [Nat.cast_sub (show 1 ≤ p by omega)]; ring
  · rw [single_true]
    simp only [psiWt, if_true]
    by_cases hl : j + 1 < p
    · rw [psiF_C_lt r hl]
      exact inWt_cVz r (j + 1) (kz := j + 1) (by push_cast; ring) (by ring) hn
    · obtain rfl : j = p - 1 := by omega
      rw [psiF_C_last]
      refine Doubling.inWt_smul _ (inWt_cVz r 0 (kz := 0) (by simp) ?_ (inWt_F hn))
      push_cast [Nat.cast_sub (show 1 ≤ p by omega)]; ring

lemma psiE_single_inWt (x : Bool × Fin p × N.ι) :
    InWt (psiWt p N r) (psiWt p N r x + 2) (psiE p N r (Pi.single x 1)) := by
  have hp := two_le_p' (p := p)
  obtain ⟨b, ⟨j, hj⟩, i⟩ := x
  have hn := inWt_single (A := ℤ_[p]) N.wt i
  cases b
  · rw [single_false]
    simp only [psiWt, Bool.false_eq_true, if_false]
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      rw [psiE_A_zero r hn]
      refine Doubling.inWt_add (Doubling.inWt_smul _ (inWt_aVz r (p - 1) (kz := p - 1)
        (by omega) ?_ (inWt_E hn))) (Doubling.inWt_smul _ (inWt_cVz r (p - 1 - r)
        (kz := p - 1 - r) (by omega) ?_ (inWt_E hn))) <;> ring
    · by_cases hjr : j ≤ r
      · rw [psiE_A_low r hpos hjr hj hn]
        refine inWt_sub' (inWt_aVz r (j - 1) (kz := j - 1) (by omega) ?_ (inWt_g hn _))
          (Doubling.inWt_smul _ (inWt_cVz r (p + j - 1 - r) (kz := p + j - 1 - r) (by omega) ?_
          (inWt_E hn))) <;> ring
      · rw [psiE_A_high r (by omega) hj hn]
        refine Doubling.inWt_add (inWt_aVz r (j - 1) (kz := j - 1) (by omega) ?_ (inWt_g hn _))
          (Doubling.inWt_smul _ (inWt_cVz r (j - 1 - r) (kz := j - 1 - r) (by omega) ?_
          (inWt_FE hn))) <;> ring
  · rw [single_true]
    simp only [psiWt, if_true]
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      rw [psiE_C_zero r hn]
      refine inWt_sub' (Doubling.inWt_smul _ (inWt_aVz r (r - 1) (kz := r - 1) (by omega) ?_ hn))
        (Doubling.inWt_smul _ (inWt_cVz r (p - 1) (kz := p - 1) (by omega) ?_ (inWt_E hn))) <;>
        push_cast <;> ring
    · by_cases hjr : j ≤ p - r
      · rw [psiE_C_low r hpos hjr hj hn]
        refine Doubling.inWt_add (inWt_cVz r (j - 1) (kz := j - 1) (by omega) ?_ (inWt_g hn _))
          (Doubling.inWt_smul _ (inWt_aVz r (j + r - 1) (kz := j + r - 1) (by omega) ?_ hn)) <;>
          ring
      · rw [psiE_C_high r (by omega) hj hn]
        refine inWt_sub' (inWt_cVz r (j - 1) (kz := j - 1) (by omega) ?_ (inWt_g hn _))
          (Doubling.inWt_smul _ (inWt_aVz r (j + r - 1 - p) (kz := j + r - 1 - p) (by omega) ?_
          (inWt_F hn))) <;> ring

end D2

variable (p N) in
/-- (D2) For `1 ≤ r ≤ p − 1`, `psiF` lowers and `psiE` raises the weights `psiWt` of Part D by
`2`: on basis vectors (the form of the axiom (W) of C18), and on every vector of weight `μ`. -/
theorem psi_D2 (r : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p - 1) :
    (∀ x y, psiWt p N r y ≠ psiWt p N r x - 2 → psiF p N r (Pi.single x 1) y = 0) ∧
    (∀ x y, psiWt p N r y ≠ psiWt p N r x + 2 → psiE p N r (Pi.single x 1) y = 0) ∧
    (∀ (μ : ℤ) (v : Bool × Fin p × N.ι → ℤ_[p]), InWt (psiWt p N r) μ v →
      InWt (psiWt p N r) (μ - 2) (psiF p N r v)) ∧
    (∀ (μ : ℤ) (v : Bool × Fin p × N.ι → ℤ_[p]), InWt (psiWt p N r) μ v →
      InWt (psiWt p N r) (μ + 2) (psiE p N r v)) := by
  refine ⟨fun x y h => psiF_single_inWt r hr1 hrp x y h,
    fun x y h => psiE_single_inWt r hr1 hrp x y h, fun μ v hv => ?_, fun μ v hv => ?_⟩
  · have := inWt_of_basis (psiF p N r) (-2)
      (fun x y h => psiF_single_inWt r hr1 hrp x y (by omega)) hv
    simpa [sub_eq_add_neg] using this
  · exact inWt_of_basis (psiE p N r) 2 (fun x y h => psiE_single_inWt r hr1 hrp x y h) hv

end ColouredSand.OddTwist
