module

public import Mathlib

/-!
# `CSI6_the_dance_lattices.md`, the combinatorial side: the rule `VdotL` (R1), the lists
`LL p m` (R3), and the rank `rankL` with its digit formula (L2)

Namespace `ColouredSand.OddTwist`. Nothing here needs `p` prime; the hypotheses are only
`2 ≤ p` or `3 ≤ p` where used.

Encodings:
* The paper's `λ` is written `l`; `d₀ = (l + 1) % p` and `b = (l + 1) / p − 1` (natural numbers;
  for `l ≥ p − 1` one has `l + 1 = d₀ + p (b + 1)`, see `succ_eq_d0_b`).
* A formal sum `Σ c_μ [μ]` of weights is a `List ℕ` with `c_μ` copies of `μ` (its order is
  irrelevant; lists are compared up to `List.Perm`); the multiplicity of `μ` is `List.count μ`.
* **(R1)** `VdotL p l : List ℕ` is defined by well-founded recursion on `l`, by the chain of
  cases of the file: `l = 0`; `l + 1 < p` (i.e. `1 ≤ l ≤ p − 2`); then, for `l ≥ p − 1`:
  `d₀ = 0`; `d₀ = 1`; `d₀ ≤ p − 2`; and otherwise (`d₀ = p − 1`)
  `(l − 1) :: (VdotL p b).map (fun b' => p b' + p − 1)`. The cases are the theorems
  `VdotL_zero`, `VdotL_small`, `VdotL_d0_zero`, `VdotL_d0_one`, `VdotL_d0_mid`, `VdotL_d0_top`.
* **(R3)** `LL p 0 = [0]`, `LL p (m + 1) = (LL p m).flatMap (VdotL p)`, and
  `nL p l m = (LL p m).count l` is the multiplicity `n_λ(m)`.
* **(L2)** `rankL p l` is the recursive form of the rank: `l + 1` if `l + 1 < p`, `p · rankL p b`
  if `d₀ = 0`, `2p · rankL p b` otherwise. The digit formula `rankL_digits` uses Mathlib's
  base-`p` expansion `Nat.digits p (l + 1)` (least significant digit first): `d_t` is
  `(Nat.digits p (l + 1)).getD t 0`, `k = (Nat.digits p (l + 1)).length − 1` (so `d_k ≠ 0` is the
  leading digit) and `I = {t < k : d_t ≠ 0}` is `(Finset.range k).filter (fun t => d_t ≠ 0)`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

/-! ### (R1) the rule -/

/-- **(R1)** (Part R of `CSI6_the_dance_lattices.md`) the tensor rule `V ⊗ L(λ)` as a list of
weights: `[1]` for `λ = 0`; `[λ + 1, λ − 1]` for `1 ≤ λ ≤ p − 2`; and for `λ ≥ p − 1`, with
`d₀ = (λ + 1) % p`, `b = (λ + 1)/p − 1`: `[λ + 1]` if `d₀ = 0`, `[λ + 1, λ − 1, λ − 1]` if
`d₀ = 1`, `[λ + 1, λ − 1]` if `2 ≤ d₀ ≤ p − 2`, and
`(λ − 1) :: (VdotL p b).map (fun b' => p b' + p − 1)` if `d₀ = p − 1`. -/
def VdotL (p : ℕ) (l : ℕ) : List ℕ :=
  if _h0 : l = 0 then [1]
  else if _h1 : l + 1 < p then [l + 1, l - 1]
  else if h2 : (l + 1) % p = 0 then [l + 1]
  else if (l + 1) % p = 1 then [l + 1, l - 1, l - 1]
  else if (l + 1) % p ≤ p - 2 then [l + 1, l - 1]
  else (l - 1) :: (VdotL p ((l + 1) / p - 1)).map (fun b' => p * b' + p - 1)
termination_by l
decreasing_by
  rcases Nat.lt_or_ge p 2 with h | hp
  · interval_cases p
    · simp; omega
    · exact absurd (Nat.mod_one _) h2
  · have : (l + 1) / p ≤ (l + 1) / 2 := Nat.div_le_div_left hp (by norm_num)
    omega

/-- **(R1)** `λ = 0`: `VdotL p 0 = [1]`. -/
theorem VdotL_zero (p : ℕ) : VdotL p 0 = [1] := by
  rw [VdotL]; simp

/-- **(R1)** `1 ≤ λ ≤ p − 2`: `VdotL p λ = [λ + 1, λ − 1]`. -/
theorem VdotL_small {p l : ℕ} (hl1 : 1 ≤ l) (hl : l ≤ p - 2) : VdotL p l = [l + 1, l - 1] := by
  rw [VdotL, dif_neg (by omega), dif_pos (by omega)]

/-- **(R1)** `λ ≥ p − 1`, `d₀ = 0`: `VdotL p λ = [λ + 1]` (`p ≥ 2`). -/
theorem VdotL_d0_zero {p l : ℕ} (hp : 2 ≤ p) (hl : p - 1 ≤ l) (hd : (l + 1) % p = 0) :
    VdotL p l = [l + 1] := by
  rw [VdotL, dif_neg (by omega), dif_neg (by omega), dif_pos hd]

/-- **(R1)** `λ ≥ p − 1`, `d₀ = 1`: `VdotL p λ = [λ + 1, λ − 1, λ − 1]` (`p ≥ 2`). -/
theorem VdotL_d0_one {p l : ℕ} (hp : 2 ≤ p) (hl : p - 1 ≤ l) (hd : (l + 1) % p = 1) :
    VdotL p l = [l + 1, l - 1, l - 1] := by
  have : l + 1 ≠ p := fun h => by rw [h, Nat.mod_self] at hd; omega
  rw [VdotL, dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), if_pos hd]

/-- **(R1)** `λ ≥ p − 1`, `2 ≤ d₀ ≤ p − 2`: `VdotL p λ = [λ + 1, λ − 1]`. -/
theorem VdotL_d0_mid {p l : ℕ} (hl : p - 1 ≤ l) (hd1 : 2 ≤ (l + 1) % p)
    (hd : (l + 1) % p ≤ p - 2) : VdotL p l = [l + 1, l - 1] := by
  have hp : 2 ≤ p := by
    rcases p with _ | _ | p
    · simp at hd
    · simp at hd1; omega
    · omega
  have : l + 1 ≠ p := fun h => by rw [h, Nat.mod_self] at hd1; omega
  rw [VdotL, dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), if_neg (by omega),
    if_pos hd]

/-- **(R1)** `λ ≥ p − 1`, `d₀ = p − 1`:
`VdotL p λ = (λ − 1) :: (VdotL p b).map (fun b' => p b' + p − 1)` with `b = (λ + 1)/p − 1`
(`p ≥ 3`). -/
theorem VdotL_d0_top {p l : ℕ} (hp : 3 ≤ p) (hl : p - 1 ≤ l) (hd : (l + 1) % p = p - 1) :
    VdotL p l = (l - 1) :: (VdotL p ((l + 1) / p - 1)).map (fun b' => p * b' + p - 1) := by
  have : l + 1 ≠ p := fun h => by rw [h, Nat.mod_self] at hd; omega
  rw [VdotL, dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- (L1)/(R1), arithmetic: for `p ≥ 1` and `λ ≥ p − 1`,
`λ + 1 = d₀ + p (b + 1)` with `d₀ = (λ + 1) % p`, `b = (λ + 1)/p − 1`. -/
theorem succ_eq_d0_b {p l : ℕ} (hp : 1 ≤ p) (hl : p - 1 ≤ l) :
    l + 1 = (l + 1) % p + p * ((l + 1) / p - 1 + 1) := by
  have h1 : 1 ≤ (l + 1) / p := (Nat.one_le_div_iff (by omega)).mpr (by omega)
  rw [Nat.sub_add_cancel h1]
  exact (Nat.mod_add_div _ _).symm

/-- (L1)/(R1), arithmetic: `b = (λ + 1)/p − 1 < λ` for `p ≥ 2` and `λ ≥ 1`. -/
theorem b_lt {p l : ℕ} (hp : 2 ≤ p) (hl : 1 ≤ l) : (l + 1) / p - 1 < l := by
  have : (l + 1) / p ≤ (l + 1) / 2 := Nat.div_le_div_left hp (by norm_num)
  omega

/-! ### (R3) the lists `LL p m` -/

/-- **(R3)** (Part R of `CSI6_the_dance_lattices.md`) the weights of `V^{⊗m}`:
`LL p 0 = [0]`, `LL p (m + 1) = (LL p m).flatMap (VdotL p)`. -/
def LL (p : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | m + 1 => (LL p m).flatMap (VdotL p)

/-- **(R3)** `LL p 0 = [0]`. -/
theorem LL_zero (p : ℕ) : LL p 0 = [0] := rfl

/-- **(R3)** `LL p (m + 1) = (LL p m).flatMap (VdotL p)`. -/
theorem LL_succ (p m : ℕ) : LL p (m + 1) = (LL p m).flatMap (VdotL p) := rfl

/-- **(R3)** the multiplicity `n_λ(m) := (LL p m).count λ`. -/
def nL (p l m : ℕ) : ℕ := (LL p m).count l

/-- (R3), auxiliary: every weight of `VdotL p λ` is `≤ λ + 1` (for `p ≥ 2`). -/
theorem le_of_mem_VdotL {p : ℕ} (hp : 2 ≤ p) (l : ℕ) : ∀ μ ∈ VdotL p l, μ ≤ l + 1 := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  intro μ hμ
  by_cases h0 : l = 0
  · subst h0; rw [VdotL_zero] at hμ; simp at hμ; omega
  by_cases h1 : l + 1 < p
  · rw [VdotL_small (by omega) (by omega)] at hμ; simp at hμ; omega
  have hl' : p - 1 ≤ l := by omega
  have hk := succ_eq_d0_b (by omega : 1 ≤ p) hl'
  have hdp : (l + 1) % p < p := Nat.mod_lt _ (by omega)
  by_cases hd0 : (l + 1) % p = 0
  · rw [VdotL_d0_zero hp hl' hd0] at hμ; simp at hμ; omega
  by_cases hd1 : (l + 1) % p = 1
  · rw [VdotL_d0_one hp hl' hd1] at hμ; simp at hμ; omega
  by_cases hdm : (l + 1) % p ≤ p - 2
  · rw [VdotL_d0_mid hl' (by omega) hdm] at hμ; simp at hμ; omega
  rw [VdotL_d0_top (by omega) hl' (by omega)] at hμ
  simp only [List.mem_cons, List.mem_map] at hμ
  rcases hμ with rfl | ⟨a, ha, rfl⟩
  · omega
  · have := ih _ (b_lt hp (by omega)) a ha
    have : p * a ≤ p * ((l + 1) / p - 1 + 1) := Nat.mul_le_mul_left _ this
    omega

/-- (R3), auxiliary: every weight of `LL p m` is `≤ m` (for `p ≥ 2`). -/
theorem le_of_mem_LL {p : ℕ} (hp : 2 ≤ p) (m : ℕ) : ∀ l ∈ LL p m, l ≤ m := by
  induction m with
  | zero => intro l hl; simp [LL_zero] at hl; omega
  | succ m ih =>
    intro l hl
    rw [LL_succ, List.mem_flatMap] at hl
    obtain ⟨a, ha, hla⟩ := hl
    have := ih a ha
    have := le_of_mem_VdotL hp a l hla
    omega

/-! ### (L2) the rank -/

/-- **(L2)** (Part L of `CSI6_the_dance_lattices.md`) the recursive form of the rank of
`L(λ)`: `λ + 1` if `λ + 1 < p`; otherwise, with `d₀ = (λ + 1) % p`, `b = (λ + 1)/p − 1`:
`p · rankL p b` if `d₀ = 0` and `2p · rankL p b` if `d₀ ≠ 0`. (For `p ≤ 1` the value is the
irrelevant `λ + 1`.) -/
def rankL (p : ℕ) (l : ℕ) : ℕ :=
  if _h : l + 1 < p ∨ p < 2 then l + 1
  else if (l + 1) % p = 0 then p * rankL p ((l + 1) / p - 1)
  else 2 * p * rankL p ((l + 1) / p - 1)
termination_by l
decreasing_by
  all_goals
    have : (l + 1) / p ≤ (l + 1) / 2 := Nat.div_le_div_left (by omega) (by norm_num)
    omega

theorem rankL_lt {p l : ℕ} (h : l + 1 < p) : rankL p l = l + 1 := by
  rw [rankL, dif_pos (Or.inl h)]

theorem rankL_d0_zero {p l : ℕ} (hp : 2 ≤ p) (h : ¬ l + 1 < p) (hd : (l + 1) % p = 0) :
    rankL p l = p * rankL p ((l + 1) / p - 1) := by
  rw [rankL, dif_neg (by omega), if_pos hd]

theorem rankL_d0_pos {p l : ℕ} (hp : 2 ≤ p) (h : ¬ l + 1 < p) (hd : (l + 1) % p ≠ 0) :
    rankL p l = 2 * p * rankL p ((l + 1) / p - 1) := by
  rw [rankL, dif_neg (by omega), if_neg hd]

/-- (L2), auxiliary: the computational form of the digit formula: with
`k = log_p (λ + 1)` and `d_t = (λ + 1)/p^t % p`, `rankL p λ = d_k · p^k · 2^{|I|}`. -/
theorem rankL_digits_aux {p : ℕ} (hp : 2 ≤ p) (l : ℕ) :
    rankL p l = (l + 1) / p ^ Nat.log p (l + 1) % p * p ^ Nat.log p (l + 1) *
      2 ^ ((Finset.range (Nat.log p (l + 1))).filter (fun t => (l + 1) / p ^ t % p ≠ 0)).card := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    by_cases h : l + 1 < p
    · rw [rankL_lt h, Nat.log_of_lt h]
      simp [Nat.mod_eq_of_lt h]
    · have hm1 : 1 ≤ (l + 1) / p := (Nat.one_le_div_iff (by omega)).mpr (by omega)
      have hb : (l + 1) / p - 1 + 1 = (l + 1) / p := by omega
      have hlt : (l + 1) / p - 1 < l := b_lt hp (by omega)
      have IH := ih _ hlt
      rw [hb] at IH
      have hrk : rankL p l = (if (l + 1) % p = 0 then p else 2 * p) * rankL p ((l + 1) / p - 1) := by
        by_cases hd : (l + 1) % p = 0
        · rw [if_pos hd, rankL_d0_zero hp h hd]
        · rw [if_neg hd, rankL_d0_pos hp h hd]
      rw [hrk, IH]
      generalize hn : l + 1 = n at *
      generalize hm : n / p = m at *
      have hlog : Nat.log p n = Nat.log p m + 1 := by
        rw [← hm]; exact Nat.log_of_one_lt_of_le (by omega) (by omega)
      have hdig : ∀ t, n / p ^ (t + 1) % p = m / p ^ t % p := fun t => by
        rw [← hm, Nat.div_div_eq_div_mul, pow_succ, mul_comm]
      have hcard : ((Finset.range (Nat.log p n)).filter (fun t => n / p ^ t % p ≠ 0)).card =
          ((Finset.range (Nat.log p m)).filter (fun t => m / p ^ t % p ≠ 0)).card +
            (if n % p ≠ 0 then 1 else 0) := by
        rw [Finset.card_filter, Finset.card_filter, hlog, Finset.sum_range_succ']
        simp only [hdig, pow_zero, Nat.div_one]
      rw [hcard, hlog, hdig]
      by_cases hd : n % p = 0
      · rw [if_pos hd, if_neg (by simpa using hd)]
        ring
      · rw [if_neg hd, if_pos hd]
        ring

/-- **(L2)** (Part L of `CSI6_the_dance_lattices.md`) the digit formula for `rankL`: write
`λ + 1 = Σ_{t ≤ k} d_t p^t` in base `p` (Mathlib's `Nat.digits p (λ + 1)`, least significant
digit first, `d_k ≠ 0`), and `I = {t < k : d_t ≠ 0}`; then `rankL p λ = d_k · p^k · 2^{|I|}`. -/
theorem rankL_digits {p : ℕ} (hp : 2 ≤ p) (l : ℕ) :
    let ds := Nat.digits p (l + 1)
    let k := ds.length - 1
    rankL p l = ds.getD k 0 * p ^ k *
      2 ^ ((Finset.range k).filter (fun t => ds.getD t 0 ≠ 0)).card := by
  intro ds k
  have hk : k = Nat.log p (l + 1) := by
    simp only [k, ds, Nat.digits_len p (l + 1) (by omega) (by omega), Nat.add_sub_cancel]
  have hd : ∀ t, ds.getD t 0 = (l + 1) / p ^ t % p := fun t => Nat.getD_digits _ _ hp
  simp only [hd, hk]
  exact rankL_digits_aux hp l

/-- (L2), the leading digit `d_k` is nonzero. -/
theorem leading_digit_ne_zero (p l : ℕ) :
    (Nat.digits p (l + 1)).getD ((Nat.digits p (l + 1)).length - 1) 0 ≠ 0 := by
  have hne : Nat.digits p (l + 1) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  rw [List.getD_eq_getElem _ _ (by
    have := List.length_pos_of_ne_nil hne; omega)]
  have := Nat.getLast_digit_ne_zero p (m := l + 1) (by omega)
  rwa [List.getLast_eq_getElem] at this

end ColouredSand.OddTwist
