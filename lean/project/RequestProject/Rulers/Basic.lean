module

public import Mathlib

/-!
# Binary digits, carries and the Legendre sums (`C3_rulers_gold_clocks.md`, *Setting* and
*Lemma (Legendre sums)*)

Encodings (namespace `Rulers`):

* `s2 x` (the file's `s_2(x)`, the number of ones in the binary expansion of `x`) is
  `(Nat.digits 2 x).count 1`.
* `v2 x` (the file's `v_2(x)`) is `padicValNat 2 x`.
* `kappa a b` (the file's `κ(a, b) := s_2(a) + s_2(b) − s_2(a + b)`) is this difference, taken in
  `ℤ`.
* `phi x` (the file's `φ(x) := x + v_2(x)`) is `x + v2 x`, taken in `ℤ`.
* `oE E` (the file's `o_E := Σ_{t∈E} 2^t`) is `∑ t ∈ E, 2 ^ t` for a `Finset ℕ` `E`.

Sums `Σ_{d=x}^{y−1}` are sums over `Finset.Ico x y`.
-/

@[expose] public section

namespace Rulers

open Finset

/-- `s_2(x)`, the number of ones in the binary expansion of `x` (*Setting* of
`C3_rulers_gold_clocks.md`). -/
def s2 (x : ℕ) : ℕ := (Nat.digits 2 x).count 1

/-- `v_2(x)`, the 2-adic valuation of `x` (*Setting* of `C3_rulers_gold_clocks.md`). -/
def v2 (x : ℕ) : ℕ := padicValNat 2 x

/-- `κ(a, b) := s_2(a) + s_2(b) − s_2(a + b)`, the number of carries in `a + b`
(*Setting* of `C3_rulers_gold_clocks.md`); the difference is taken in `ℤ`. -/
def kappa (a b : ℕ) : ℤ := s2 a + s2 b - s2 (a + b)

/-- `φ(x) := x + v_2(x)` (*Setting* of `C3_rulers_gold_clocks.md`), as an integer. -/
def phi (x : ℕ) : ℤ := x + v2 x

/-- `o_E := Σ_{t∈E} 2^t` (*A family*, `C3_rulers_gold_clocks.md`). -/
def oE (E : Finset ℕ) : ℕ := ∑ t ∈ E, 2 ^ t

@[simp] lemma s2_zero : s2 0 = 0 := by simp [s2]

/-- The binary recursion for `s2`. -/
lemma s2_bit (c d : ℕ) (hc : c < 2) : s2 (c + 2 * d) = c + s2 d := by
  rcases Nat.eq_zero_or_pos (c + 2 * d) with h | h
  · have hc0 : c = 0 := by omega
    have hd0 : d = 0 := by omega
    subst hc0 hd0; simp
  · unfold s2
    rw [Nat.digits_def' (by norm_num) h]
    have h1 : (c + 2 * d) % 2 = c := by omega
    have h2 : (c + 2 * d) / 2 = d := by omega
    rw [h1, h2, List.count_cons]
    interval_cases c <;> simp [Nat.add_comm]

lemma s2_one : s2 1 = 1 := by simpa using s2_bit 1 0 (by norm_num)

lemma s2_add_two_pow_mul (j : ℕ) : ∀ a b : ℕ, a < 2 ^ j → s2 (a + 2 ^ j * b) = s2 a + s2 b := by
  induction j with
  | zero => intro a b ha; simp at ha; subst ha; simp
  | succ j ih =>
    intro a b ha
    have e1 : a + 2 ^ (j + 1) * b = a % 2 + 2 * (a / 2 + 2 ^ j * b) := by
      rw [pow_succ]; have := Nat.mod_add_div a 2; nlinarith
    have e2 : a = a % 2 + 2 * (a / 2) := (Nat.mod_add_div a 2).symm
    have hlt : a / 2 < 2 ^ j := by rw [pow_succ] at ha; omega
    rw [e1, s2_bit _ _ (Nat.mod_lt _ (by norm_num)), ih _ _ hlt]
    conv_rhs => rw [e2, s2_bit _ _ (Nat.mod_lt _ (by norm_num))]
    ring

lemma s2_two_pow (j : ℕ) : s2 (2 ^ j) = 1 := by
  simpa [s2_one] using s2_add_two_pow_mul j 0 1 (by positivity)

lemma oE_lt (S : Finset ℕ) (n : ℕ) (h : ∀ t ∈ S, t < n) : oE S < 2 ^ n :=
  Nat.geomSum_lt (le_refl 2) h

lemma oE_empty : oE ∅ = 0 := by simp [oE]

/-- The digits of `o_E` are the elements of `E`: `s_2(o_E) = |E|`. -/
lemma s2_oE (S : Finset ℕ) : s2 (oE S) = S.card := by
  induction S using Finset.induction_on_max with
  | h0 => simp [oE]
  | step a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    rw [oE, sum_insert ha, card_insert_of_notMem ha, add_comm, ← oE,
      show 2 ^ a = 2 ^ a * 1 by ring, s2_add_two_pow_mul a _ _ (oE_lt s a hlt), ih, s2_one]

lemma oE_union {A B : Finset ℕ} (h : Disjoint A B) : oE (A ∪ B) = oE A + oE B := by
  simp [oE, sum_union h]

lemma oE_sdiff {a b : Finset ℕ} (h : b ⊆ a) : oE (a \ b) + oE b = oE a := by
  simp only [oE]; exact sum_sdiff h

lemma oE_range (n : ℕ) : oE (range n) + 1 = 2 ^ n := by
  induction n with
  | zero => simp [oE]
  | succ n ih => rw [oE, sum_range_succ, ← oE, pow_succ]; omega

/-- The basic step `s_2(n+1) = s_2(n) + 1 − v_2(n+1)` (Legendre's formula in difference form). -/
lemma s2_succ (n : ℕ) : (s2 (n + 1) : ℤ) = s2 n + 1 - v2 (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hv : v2 (2 * m + 1) = 0 := by
        unfold v2; apply padicValNat.eq_zero_of_not_dvd; omega
      have e1 : s2 (2 * m + 1) = 1 + s2 m := by
        rw [show 2 * m + 1 = 1 + 2 * m by ring, s2_bit 1 m (by norm_num)]
      have e0 : s2 (2 * m) = s2 m := by
        rw [show 2 * m = 0 + 2 * m by ring, s2_bit 0 m (by norm_num)]; simp
      rw [e1, e0, hv]
      push_cast; ring
    · have hv : v2 (2 * m + 1 + 1) = 1 + v2 (m + 1) := by
        unfold v2; rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring,
          padicValNat.mul (by norm_num) (by omega)]; simp
      have ihm := ih m (by omega)
      have e2 : s2 (2 * m + 1 + 1) = s2 (m + 1) := by
        rw [show 2 * m + 1 + 1 = 0 + 2 * (m + 1) by ring, s2_bit 0 _ (by norm_num)]; simp
      have e1 : s2 (2 * m + 1) = 1 + s2 m := by
        rw [show 2 * m + 1 = 1 + 2 * m by ring, s2_bit 1 m (by norm_num)]
      rw [e2, e1, hv]
      push_cast; linarith

/-- **Lemma (Legendre sums)**, first sum, of `C3_rulers_gold_clocks.md`: for `μ ≥ 0` and
`x ≤ y`, `Σ_{d=x}^{y−1} v_2(μ + 1 + d) = (y − x) − s_2(μ + y) + s_2(μ + x)`. -/
theorem legendre_sum_shift (μ x y : ℕ) (hxy : x ≤ y) :
    (∑ d ∈ Ico x y, (v2 (μ + 1 + d) : ℤ)) = ((y : ℤ) - x) - s2 (μ + y) + s2 (μ + x) := by
  induction y, hxy using Nat.le_induction with
  | base => simp
  | succ y hxy ih =>
    rw [sum_Ico_succ_top hxy, ih, show μ + (y + 1) = μ + y + 1 by ring, s2_succ,
      show μ + 1 + y = μ + y + 1 by ring]
    push_cast; ring

/-- **Lemma (Legendre sums)**, second sum, of `C3_rulers_gold_clocks.md`: for `1 ≤ x ≤ y`,
`Σ_{d=x}^{y−1} v_2(d) = (y − x) − s_2(y − 1) + s_2(x − 1)`. -/
theorem legendre_sum (x y : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    (∑ d ∈ Ico x y, (v2 d : ℤ)) = ((y : ℤ) - x) - s2 (y - 1) + s2 (x - 1) := by
  induction y, hxy using Nat.le_induction with
  | base => simp
  | succ y hxy ih =>
    rw [sum_Ico_succ_top hxy, ih, show y + 1 - 1 = (y - 1) + 1 by omega, s2_succ,
      show y - 1 + 1 = y by omega]
    push_cast; ring

end Rulers
