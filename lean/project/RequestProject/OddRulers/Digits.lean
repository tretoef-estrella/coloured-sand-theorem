module

public import RequestProject.Rulers.All
public import RequestProject.OddWindows.All
public import RequestProject.OddDeficit.All

/-!
# `CSI13_the_odd_cost_form.md` — *Setting* (base-`p` digit sums and carries) and **Part L**

Namespace `ColouredSand.OddTwist`.  This is the `p`-odd analogue of the binary part of C3
(`RequestProject/Rulers/Basic.lean`, `Bits.lean`).

## Encodings

* `sP p x` is `s_p(x)`, the digit sum of `x` in base `p`: `(Nat.digits p x).sum`.
* `kappaP p a b : ℤ` is `κ_p(a, b) := (s_p(a) + s_p(b) − s_p(a + b))/(p − 1)`, the difference
  being taken in `ℤ` and the division being `Int` division.  The division is exact
  (`kappaP_mul`), and `kappaP p a b = v_p (C(a+b, a))` (Kummer, `kappaP_eq_padicValNat_choose`).
* The digits are an abstract digit function `dg : ℕ → ℕ` (`d_t = dg t`) together with a set
  `I : Finset ℕ`; the setting `I = {t < k : d_t ≠ 0}`, `d_t < p` is used only through the
  hypotheses `hI : ∀ t ∈ I, t < k` and `hd : ∀ t ∈ I, 0 < dg t ∧ dg t < p` (which it implies).
  The top digit `d_k` is a separate natural number `dk`, and `K = d_k p^k` is `dk * p ^ k`.
* `o_E := Σ_{t ∈ E} d_t p^t` is CSI12's `oW p dg E : ℕ`.
* `min E` for `E ≠ ∅` is `E.min' h`; where a convention for `E = ∅` is convenient we use C3's
  `Rulers.minOr k E` (`min ∅ := k`).
* Sums `Σ_{d=x}^{y−1}` are sums over `Finset.Ico x y`; valuations `v_p(n)` are
  `padicValNat p n`.  Identities involving the divisions by `p − 1` of the file are stated in `ℚ`
  (with the rational division), or in `ℤ` multiplied out by `p − 1`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset

/-- `s_p(x)`, the digit sum of `x` in base `p` (*Setting* of `CSI13_the_odd_cost_form.md`). -/
def sP (p x : ℕ) : ℕ := (Nat.digits p x).sum

/-- `κ_p(a, b) := (s_p(a) + s_p(b) − s_p(a + b))/(p − 1)`, the number of carries of `a + b` in
base `p` (*Setting* of `CSI13_the_odd_cost_form.md`).  The difference is taken in `ℤ` and the
division is integer division; it is exact (`kappaP_mul`). -/
def kappaP (p a b : ℕ) : ℤ := (((sP p a : ℤ) + sP p b) - sP p (a + b)) / ((p : ℤ) - 1)

/-! ### Digit sums -/

section digits

variable {p : ℕ}

@[simp] lemma sP_zero (p : ℕ) : sP p 0 = 0 := by simp [sP]

lemma sP_add_mul (hp : 2 ≤ p) {c : ℕ} (d : ℕ) (hc : c < p) : sP p (c + p * d) = c + sP p d := by
  by_cases h : c = 0 ∧ d = 0
  · obtain ⟨rfl, rfl⟩ := h; simp
  · unfold sP
    rw [Nat.digits_add p (by omega) c d hc (by tauto), List.sum_cons]

lemma sP_lt (hp : 2 ≤ p) {c : ℕ} (hc : c < p) : sP p c = c := by
  simpa using sP_add_mul hp 0 hc

lemma sP_add_pow_mul (hp : 2 ≤ p) (j : ℕ) :
    ∀ x y : ℕ, x < p ^ j → sP p (x + p ^ j * y) = sP p x + sP p y := by
  induction j with
  | zero => intro x y hx; simp at hx; subst hx; simp
  | succ j ih =>
    intro x y hx
    have hp0 : 0 < p := by omega
    have e1 : x + p ^ (j + 1) * y = x % p + p * (x / p + p ^ j * y) := by
      rw [pow_succ]; have := Nat.mod_add_div x p; nlinarith
    have e2 : x = x % p + p * (x / p) := (Nat.mod_add_div x p).symm
    have hlt : x / p < p ^ j := by
      rw [pow_succ] at hx; exact Nat.div_lt_of_lt_mul (by linarith)
    rw [e1, sP_add_mul hp _ (Nat.mod_lt _ hp0), ih _ _ hlt]
    conv_rhs => rw [e2, sP_add_mul hp _ (Nat.mod_lt _ hp0)]
    ring

/-- The digit sum of `p^j · y` is that of `y`. -/
lemma sP_pow_mul (hp : 2 ≤ p) (j y : ℕ) : sP p (p ^ j * y) = sP p y := by
  simpa using sP_add_pow_mul hp j 0 y (by positivity)

lemma filter_not_lt_eq (E : Finset ℕ) (n : ℕ) (hE : ∀ t ∈ E, t < n + 1) :
    E.filter (fun t => ¬ t < n) = if n ∈ E then {n} else ∅ := by
  ext t
  simp only [mem_filter]
  split_ifs with h
  · simp only [mem_singleton]
    constructor
    · rintro ⟨ht, h'⟩; have := hE t ht; omega
    · rintro rfl; exact ⟨h, by omega⟩
  · simp only [notMem_empty, iff_false, not_and, not_lt]
    intro ht h'; have := hE t ht
    exact h (by rwa [show t = n by omega] at ht)

lemma oW_split (p : ℕ) (dg : ℕ → ℕ) (n : ℕ) (E : Finset ℕ) (hE : ∀ t ∈ E, t < n + 1) :
    oW p dg E = oW p dg (E.filter (· < n)) + p ^ n * (if n ∈ E then dg n else 0) := by
  unfold oW
  rw [← sum_filter_add_sum_filter_not E (· < n)]
  congr 1
  rw [filter_not_lt_eq E n hE]; split_ifs <;> simp [mul_comm]

/-- `o_E < p^n` and `s_p(o_E) = Σ_{t ∈ E} d_t`, when all digits are `< p` and `E ⊆ [0, n)`. -/
lemma oW_lt_and_sP (hp : 2 ≤ p) (dg : ℕ → ℕ) (n : ℕ) :
    ∀ E : Finset ℕ, (∀ t ∈ E, t < n) → (∀ t ∈ E, dg t < p) →
      oW p dg E < p ^ n ∧ sP p (oW p dg E) = ∑ t ∈ E, dg t := by
  induction n with
  | zero =>
    intro E hE _
    have : E = ∅ := eq_empty_of_forall_notMem (fun t ht => by have := hE t ht; omega)
    subst this; simp [oW]
  | succ n ih =>
    intro E hE hd
    obtain ⟨h1, h2⟩ := ih (E.filter (· < n)) (fun t ht => (mem_filter.1 ht).2)
      (fun t ht => hd t (mem_filter.1 ht).1)
    have hc : (if n ∈ E then dg n else 0) < p := by
      split_ifs with h
      · exact hd n h
      · omega
    have hc' : (if n ∈ E then dg n else 0) ≤ p - 1 := by omega
    rw [oW_split p dg n E hE]
    refine ⟨?_, ?_⟩
    · have : p ^ n * (if n ∈ E then dg n else 0) ≤ p ^ n * (p - 1) :=
        Nat.mul_le_mul_left _ hc'
      have e : p ^ n * (p - 1) + p ^ n = p ^ (n + 1) := by
        rw [pow_succ]; obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        simp; ring
      omega
    · rw [sP_add_pow_mul hp n _ _ h1, h2, sP_lt hp hc,
        ← sum_filter_add_sum_filter_not E (· < n)]
      congr 1
      rw [filter_not_lt_eq E n hE]; split_ifs <;> simp

/-- The digits of `o_E` are the `d_t`, `t ∈ E`: `s_p(o_E) = Σ_{t ∈ E} d_t`. -/
lemma sP_oW (hp : 2 ≤ p) (dg : ℕ → ℕ) (E : Finset ℕ) (hd : ∀ t ∈ E, dg t < p) :
    sP p (oW p dg E) = ∑ t ∈ E, dg t :=
  (oW_lt_and_sP hp dg (E.sup id + 1) E
    (fun _ ht => Nat.lt_succ_of_le (le_sup (f := id) ht)) hd).2

lemma oW_lt_pow (hp : 2 ≤ p) (dg : ℕ → ℕ) {n : ℕ} (E : Finset ℕ) (hE : ∀ t ∈ E, t < n)
    (hd : ∀ t ∈ E, dg t < p) : oW p dg E < p ^ n :=
  (oW_lt_and_sP hp dg n E hE hd).1

lemma oW_sdiff (p : ℕ) (dg : ℕ → ℕ) {a b : Finset ℕ} (h : b ⊆ a) :
    oW p dg (a \ b) + oW p dg b = oW p dg a := by
  simp only [oW]; exact sum_sdiff h

/-- `Σ_{t < m} (p − 1) p^t + 1 = p^m`. -/
lemma oW_const_range (hp : 1 ≤ p) (m : ℕ) : oW p (fun _ => p - 1) (range m) + 1 = p ^ m := by
  induction m with
  | zero => simp [oW]
  | succ m ih =>
    rw [oW, sum_range_succ, ← oW, pow_succ]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ih ⊢
    nlinarith

/-- `s_p(p^m − 1) = m (p − 1)`. -/
lemma sP_pow_sub_one (hp : 2 ≤ p) (m : ℕ) : sP p (p ^ m - 1) = m * (p - 1) := by
  have := oW_const_range (p := p) (by omega) m
  rw [show p ^ m - 1 = oW p (fun _ => p - 1) (range m) by omega,
    sP_oW hp _ _ (fun _ _ => by omega)]
  simp

/-- `(p^t − 1)/(p − 1) = Σ_{j < t} p^j` (natural division), so `(p − 1)·N_t = p^t − 1`. -/
lemma geomN_mul (hp : 2 ≤ p) (t : ℕ) :
    ((p : ℤ) - 1) * (((p ^ t - 1) / (p - 1) : ℕ) : ℤ) = (p : ℤ) ^ t - 1 := by
  have h1 := oW_const_range (p := p) (by omega) t
  have h2 : oW p (fun _ => p - 1) (range t) = (p - 1) * ∑ j ∈ range t, p ^ j := by
    simp [oW, mul_sum]
  have hdiv : (p ^ t - 1) / (p - 1) = ∑ j ∈ range t, p ^ j := by
    rw [show p ^ t - 1 = (p - 1) * ∑ j ∈ range t, p ^ j by omega]
    exact Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv]
  have : (((p ^ t : ℕ)) : ℤ) = ((p - 1) * ∑ j ∈ range t, p ^ j : ℕ) + 1 := by
    rw [← h2]; exact_mod_cast h1.symm
  push_cast [show 1 ≤ p by omega] at this ⊢
  linarith

end digits

/-! ### Kummer and Legendre -/

section padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- Legendre's formula, multiplied out: `(p − 1) v_p(n!) = n − s_p(n)` in `ℤ`. -/
lemma legendre_mul (n : ℕ) :
    ((p : ℤ) - 1) * (padicValNat p n.factorial : ℤ) = n - sP p n := by
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  have hle : sP p n ≤ n := Nat.digit_sum_le p n
  have h1 : 1 ≤ p := hp.out.one_lt.le
  unfold sP at hle ⊢
  generalize padicValNat p n.factorial = v at h ⊢
  generalize (p.digits n).sum = s at h hle ⊢
  have : (((p - 1) * v : ℕ) : ℤ) = ((n - s : ℕ) : ℤ) := by
    rw [h]
  push_cast [hle, h1] at this
  linarith

/-- `s_p(a) + s_p(b) − s_p(a + b) = (p − 1) v_p C(a+b, a)` (Kummer, from Legendre). -/
lemma kappaP_mul_aux (a b : ℕ) :
    (((sP p a : ℤ) + sP p b) - sP p (a + b)) =
      ((p : ℤ) - 1) * (padicValNat p ((a + b).choose a) : ℤ) := by
  have hc := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rw [Nat.add_sub_cancel_left] at hc
  have hv : padicValNat p ((a + b).factorial) =
      padicValNat p ((a + b).choose a) + padicValNat p a.factorial +
        padicValNat p b.factorial := by
    rw [← hc, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos (Nat.le_add_right a b)).ne'
      (by positivity)) (by positivity),
      padicValNat.mul (Nat.choose_pos (Nat.le_add_right a b)).ne' (by positivity)]
  have e1 := legendre_mul (p := p) (a + b)
  have e2 := legendre_mul (p := p) a
  have e3 := legendre_mul (p := p) b
  have hv' : (padicValNat p ((a + b).factorial) : ℤ) =
      padicValNat p ((a + b).choose a) + padicValNat p a.factorial +
        padicValNat p b.factorial := by exact_mod_cast hv
  rw [hv'] at e1
  simp only [Nat.cast_add] at e1
  linear_combination -e1 + e2 + e3

/-- **Kummer** (*Setting* of `CSI13_the_odd_cost_form.md`): `κ_p(a, b) = v_p C(a+b, a)`. -/
theorem kappaP_eq_padicValNat_choose (a b : ℕ) :
    kappaP p a b = padicValNat p ((a + b).choose a) := by
  unfold kappaP
  rw [kappaP_mul_aux]
  have : ((p : ℤ) - 1) ≠ 0 := by have := hp.out.two_le; omega
  exact Int.mul_ediv_cancel_left _ this

/-- The division defining `κ_p` is exact: `(p − 1) κ_p(a, b) = s_p(a) + s_p(b) − s_p(a + b)`. -/
lemma kappaP_mul (a b : ℕ) :
    ((p : ℤ) - 1) * kappaP p a b = ((sP p a : ℤ) + sP p b) - sP p (a + b) := by
  rw [kappaP_eq_padicValNat_choose, kappaP_mul_aux]

lemma kappaP_nonneg (a b : ℕ) : 0 ≤ kappaP p a b := by
  rw [kappaP_eq_padicValNat_choose]; positivity

/-- The basic step: `(p − 1) v_p(n + 1) = 1 + s_p(n) − s_p(n + 1)`. -/
lemma padicValNat_succ_mul (n : ℕ) :
    ((p : ℤ) - 1) * (padicValNat p (n + 1) : ℤ) = 1 + sP p n - sP p (n + 1) := by
  have e1 := legendre_mul (p := p) (n + 1)
  have e2 := legendre_mul (p := p) n
  rw [Nat.factorial_succ, padicValNat.mul (by omega) (by positivity)] at e1
  simp only [Nat.cast_add, Nat.cast_one] at e1
  linear_combination e1 - e2

/-- Legendre sums, multiplied out: `(p − 1) Σ_{d=x}^{y−1} v_p(μ + 1 + d)
= (y − x) − s_p(μ + y) + s_p(μ + x)`. -/
lemma legendre_sum_mul (μ x y : ℕ) (hxy : x ≤ y) :
    ((p : ℤ) - 1) * ∑ d ∈ Ico x y, (padicValNat p (μ + 1 + d) : ℤ) =
      ((y : ℤ) - x) - sP p (μ + y) + sP p (μ + x) := by
  induction y, hxy using Nat.le_induction with
  | base => simp
  | succ y hxy ih =>
    rw [sum_Ico_succ_top hxy, mul_add, ih, show μ + 1 + y = μ + y + 1 by ring,
      padicValNat_succ_mul, show μ + (y + 1) = μ + y + 1 by ring]
    push_cast; ring

/-- Legendre sums, `μ = −1` form, multiplied out: for `1 ≤ x ≤ y`,
`(p − 1) Σ_{d=x}^{y−1} v_p(d) = (y − x) − s_p(y − 1) + s_p(x − 1)`. -/
lemma legendre_sum_neg_mul (x y : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    ((p : ℤ) - 1) * ∑ d ∈ Ico x y, (padicValNat p d : ℤ) =
      ((y : ℤ) - x) - sP p (y - 1) + sP p (x - 1) := by
  induction y, hxy using Nat.le_induction with
  | base => simp
  | succ y hxy ih =>
    rw [sum_Ico_succ_top hxy, mul_add, ih, show y + 1 - 1 = (y - 1) + 1 by omega,
      show y = (y - 1) + 1 by omega, padicValNat_succ_mul]
    push_cast; ring

/-- **(L1) Legendre, base `p`** (*Part L* of `CSI13_the_odd_cost_form.md`), first statement:
`v_p(n!) = (n − s_p(n))/(p − 1)`. -/
theorem L1_legendre (n : ℕ) :
    (padicValNat p n.factorial : ℚ) = ((n : ℚ) - sP p n) / ((p : ℚ) - 1) := by
  have h := legendre_mul (p := p) n
  have hp1 : ((p : ℚ) - 1) ≠ 0 := by
    have := hp.out.two_le
    have : (2 : ℚ) ≤ p := by exact_mod_cast this
    linarith
  rw [eq_div_iff hp1]
  have := congrArg (Int.cast : ℤ → ℚ) h
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one] at this
  linarith

/-- **(L1) Legendre, base `p`** (*Part L* of `CSI13_the_odd_cost_form.md`), the sums: for `μ ≥ 0`
and `x ≤ y`, `Σ_{d=x}^{y−1} v_p(μ + 1 + d) = [(y − x) − s_p(μ + y) + s_p(μ + x)]/(p − 1)`. -/
theorem L1_sum (μ x y : ℕ) (hxy : x ≤ y) :
    ∑ d ∈ Ico x y, (padicValNat p (μ + 1 + d) : ℚ) =
      (((y : ℚ) - x) - sP p (μ + y) + sP p (μ + x)) / ((p : ℚ) - 1) := by
  have h := legendre_sum_mul (p := p) μ x y hxy
  have hp1 : ((p : ℚ) - 1) ≠ 0 := by
    have := hp.out.two_le
    have : (2 : ℚ) ≤ p := by exact_mod_cast this
    linarith
  rw [eq_div_iff hp1]
  have := congrArg (Int.cast : ℤ → ℚ) h
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one, Int.cast_sum,
    Int.cast_add] at this
  linarith

/-- **(L1) Legendre, base `p`** (*Part L* of `CSI13_the_odd_cost_form.md`), the `μ = −1` form:
for `1 ≤ x ≤ y`, `Σ_{d=x}^{y−1} v_p(d) = [(y − x) − s_p(y − 1) + s_p(x − 1)]/(p − 1)`. -/
theorem L1_sum_neg (x y : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    ∑ d ∈ Ico x y, (padicValNat p d : ℚ) =
      (((y : ℚ) - x) - sP p (y - 1) + sP p (x - 1)) / ((p : ℚ) - 1) := by
  have h := legendre_sum_neg_mul (p := p) x y hx hxy
  have hp1 : ((p : ℚ) - 1) ≠ 0 := by
    have := hp.out.two_le
    have : (2 : ℚ) ≤ p := by exact_mod_cast this
    linarith
  rw [eq_div_iff hp1]
  have := congrArg (Int.cast : ℤ → ℚ) h
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one, Int.cast_sum,
    Int.cast_add] at this
  linarith

/-- **(L2)** (*Part L* of `CSI13_the_odd_cost_form.md`): if every digit `d_t`, `t ∈ E`, is `< p`,
then `s_p(x + o_E) = s_p(x) + Σ_{t ∈ E} d_t − (p − 1) κ_p(x, o_E)`. -/
theorem L2 (dg : ℕ → ℕ) (E : Finset ℕ) (hd : ∀ t ∈ E, dg t < p) (x : ℕ) :
    (sP p (x + oW p dg E) : ℤ) =
      sP p x + ∑ t ∈ E, (dg t : ℤ) - ((p : ℤ) - 1) * kappaP p x (oW p dg E) := by
  rw [kappaP_mul, sP_oW hp.out.two_le dg E hd]
  push_cast; ring

end padic

end ColouredSand.OddTwist
