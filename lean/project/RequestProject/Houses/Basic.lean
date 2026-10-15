module

public import RequestProject.Rulers.Family
public import RequestProject.GoldenMatching.Complement

/-!
# Houses: the data of `C6_houses_windows_penalties.md` (*Setting*, *Part B* data)

Encodings (namespace `Houses`).  A **house** `H = (I, k, ℓ, α)` is not bundled: every definition
below takes the components explicitly, in the order of the file, `I : Finset ℕ`, `k : ℕ`,
`ℓ : ℕ`, `α : ℤ` (only the arguments that are actually used).  The house conditions
`I ⊆ {0, …, k − 1}` and `0 ≤ ℓ < 2^k` are hypotheses of the theorems, written
`hI : ∀ t ∈ I, t < k` and `hℓ : ℓ < 2 ^ k`; each theorem only carries the ones its proof uses
(this is noted in its docstring).  `K = 2^k` is written `2 ^ k`.

From piece C3 we reuse `Rulers.oE` (`o_E`), `Rulers.kappa` (`κ`), `Rulers.next`, `Rulers.h`
(`h_t`), `Rulers.gamma` (`γ`), `Rulers.ruler` (`R_μ`) and `Rulers.v2` (`v_2`); from C4 we reuse
`GoldenMatching.cHat`.

* `bit u x` is `bit_u(x) := ⌊x / 2^u⌋ mod 2`.
* `r u x` is `r_u(x) := v_2(⌊x / 2^u⌋ + 1)`; it is used both as `r_k(μ)` (Part A) and as
  `r_u(ℓ)` (Part B).
* `RH I k ℓ α E` is the base ruler `R_H(E)`, defined as `Rulers.ruler k I α ℓ E`.
* `JH k ℓ E` is the carry-out indicator `J_H(E) := [ℓ + o_E ≥ 2^k]` (a natural number `0`/`1`;
  it only depends on `k`, `ℓ` and `E`).
* `xH I k ℓ α D` is the base clock `x_H(D) := R_H(D) − R_H(I ∖ D)`.
* `cHatH I k ℓ α a b` is the base cost `ĉ_H(a, b) := R_H(a) − R_H(b) + γ(a ∖ b)`, with
  `γ = Rulers.gamma k I`.
* Window data of `t` (Part B): `typ ℓ t` is the type `T_t := bit_t(ℓ)`; `kap I k ℓ t` is `κ_t`;
  `sat I k ℓ t` is `sat_t`; `tau I k ℓ α t` is `τ_t` (an integer).
* `cin ℓ u E` is the carry into bit `u` of `ℓ + o_E`:
  `c_u(E) := [(ℓ mod 2^u) + (o_E mod 2^u) ≥ 2^u]`.
* `car I k ℓ t E` is `car_t(E) := #{u ∈ [t, next(t)) : c_{u+1}(E) = 1}`, the cardinality of a
  filter of `Finset.Ico t (next k I t)`.
* `d1 I k ℓ α c D₀` is `d_1(D₀)` of (C6).

Indicators `[P]` are written `if P then 1 else 0`.
-/

@[expose] public section

namespace Houses

open Finset Rulers

/-- `bit_u(x) := ⌊x / 2^u⌋ mod 2` (*Setting* of `C6_houses_windows_penalties.md`). -/
def bit (u x : ℕ) : ℕ := x / 2 ^ u % 2

/-- `r_u(x) := v_2(⌊x / 2^u⌋ + 1)`, the number of consecutive ones of `x` starting at bit `u`
(*Setting* (`r_k(μ)`) and *Part B* (`r_u(ℓ)`) of `C6_houses_windows_penalties.md`). -/
def r (u x : ℕ) : ℕ := v2 (x / 2 ^ u + 1)

/-- **Base ruler** `R_H(E) := Σ_{t∈E} (h_t − α 2^t) − κ(ℓ, o_E)`, i.e. `Rulers.ruler k I α ℓ E`
(*Setting* of `C6_houses_windows_penalties.md`). -/
def RH (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (E : Finset ℕ) : ℤ := ruler k I α ℓ E

/-- **Carry-out set** `J_H(E) := 1` if `ℓ + o_E ≥ 2^k`, else `0`
(*Setting* of `C6_houses_windows_penalties.md`). -/
def JH (k ℓ : ℕ) (E : Finset ℕ) : ℕ := if 2 ^ k ≤ ℓ + oE E then 1 else 0

/-- **Base clocks** `x_H(D) := R_H(D) − R_H(I ∖ D)`
(*Setting* of `C6_houses_windows_penalties.md`). -/
def xH (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (D : Finset ℕ) : ℤ := RH I k ℓ α D - RH I k ℓ α (I \ D)

/-- **Base costs** `ĉ_H(a, b) := R_H(a) − R_H(b) + γ(a ∖ b)`
(*Setting* of `C6_houses_windows_penalties.md`). -/
def cHatH (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (a b : Finset ℕ) : ℤ :=
  RH I k ℓ α a - RH I k ℓ α b + gamma k I (a \ b)

/-- The **type** `T_t := bit_t(ℓ)` of the window of `t` (*Part B* of
`C6_houses_windows_penalties.md`). -/
def typ (ℓ t : ℕ) : ℕ := bit t ℓ

/-- `κ_t := min(r_t(ℓ), h_t)` if `T_t = 1`, and `κ_t := 1 + min(r_{t+1}(ℓ), h_t − 1)` if `T_t = 0`
(*Part B* of `C6_houses_windows_penalties.md`). -/
def kap (I : Finset ℕ) (k ℓ t : ℕ) : ℕ :=
  if typ ℓ t = 1 then min (r t ℓ) (h k I t) else 1 + min (r (t + 1) ℓ) (h k I t - 1)

/-- `sat_t := 1` if `κ_t = h_t`, else `0` (*Part B* of `C6_houses_windows_penalties.md`). -/
def sat (I : Finset ℕ) (k ℓ t : ℕ) : ℕ := if kap I k ℓ t = h k I t then 1 else 0

/-- `τ_t := h_t − α 2^t − [T_t = 1] κ_t`, an integer (*Part B* of
`C6_houses_windows_penalties.md`). -/
def tau (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (t : ℕ) : ℤ :=
  (h k I t : ℤ) - α * 2 ^ t - (if typ ℓ t = 1 then (kap I k ℓ t : ℤ) else 0)

/-- The **carry into bit `u`** of `ℓ + o_E`: `c_u(E) := 1` if
`(ℓ mod 2^u) + (o_E mod 2^u) ≥ 2^u`, else `0` (*Part B* of `C6_houses_windows_penalties.md`). -/
def cin (ℓ u : ℕ) (E : Finset ℕ) : ℕ := if 2 ^ u ≤ ℓ % 2 ^ u + oE E % 2 ^ u then 1 else 0

/-- The **carries made by `W_t`**: `car_t(E) := #{u ∈ [t, next(t)) : c_{u+1}(E) = 1}`
(*Part B* of `C6_houses_windows_penalties.md`). -/
def car (I : Finset ℕ) (k ℓ t : ℕ) (E : Finset ℕ) : ℕ :=
  ((Ico t (next k I t)).filter (fun u => cin ℓ (u + 1) E = 1)).card

/-- `d_1(D₀) := −τ − [T = 1] κ J_{H'}(D₀) + [T = 0] κ J_{H'}(I' ∖ D₀)` of (C6), where
`τ, T, κ` are the data of the window of `c` in `H = (I, k, ℓ, α)` and `H' = (I ∖ {c}, c, ℓ mod 2^c, α)`
(*Part C* of `C6_houses_windows_penalties.md`). -/
def d1 (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c : ℕ) (D₀ : Finset ℕ) : ℤ :=
  -tau I k ℓ α c - (if typ ℓ c = 1 then (kap I k ℓ c : ℤ) else 0) * JH c (ℓ % 2 ^ c) D₀
    + (if typ ℓ c = 0 then (kap I k ℓ c : ℤ) else 0) * JH c (ℓ % 2 ^ c) (I.erase c \ D₀)

/-! ### Arithmetic of carries -/

/-- Division of a carry condition by `P = 2^u`. -/
lemma carry_aux {P M X Y : ℕ} (hX : X < 2 * P) :
    P * M ≤ X + P * Y ↔ M ≤ (if P ≤ X then 1 else 0) + Y := by
  split_ifs with h
  · constructor
    · intro hle; by_contra hc; push_neg at hc
      have : P * (2 + Y) ≤ P * M := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    · intro hle
      have : P * M ≤ P * (1 + Y) := Nat.mul_le_mul_left _ hle
      nlinarith
  · push_neg at h
    constructor
    · intro hle; by_contra hc; push_neg at hc
      have : P * (Y + 1) ≤ P * M := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    · intro hle
      have : P * M ≤ P * (0 + Y) := Nat.mul_le_mul_left _ hle
      nlinarith

lemma dvd_succ_iff_mod (q j : ℕ) : 2 ^ j ∣ q + 1 ↔ 2 ^ j ≤ q % 2 ^ j + 1 := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hlt : q % 2 ^ j < 2 ^ j := Nat.mod_lt _ hpos
  have hq : q + 1 = 2 ^ j * (q / 2 ^ j) + (q % 2 ^ j + 1) := by
    have := Nat.div_add_mod q (2 ^ j); omega
  rw [hq, Nat.dvd_add_right (dvd_mul_right _ _)]
  constructor
  · intro hd; exact Nat.le_of_dvd (by omega) hd
  · intro hle; rw [show q % 2 ^ j + 1 = 2 ^ j by omega]

lemma le_v2_iff (q j : ℕ) : j ≤ v2 (q + 1) ↔ 2 ^ j ≤ q % 2 ^ j + 1 := by
  rw [← dvd_succ_iff_mod, v2, padicValNat_dvd_iff_le (by omega)]

lemma v2_succ_of_even {q : ℕ} (hq : q % 2 = 0) : v2 (q + 1) = 0 := by
  unfold v2; apply padicValNat.eq_zero_of_not_dvd; omega

lemma v2_succ_of_odd {q : ℕ} (hq : q % 2 = 1) : v2 (q + 1) = 1 + v2 (q / 2 + 1) := by
  unfold v2
  rw [show q + 1 = 2 * (q / 2 + 1) by omega, padicValNat.mul (by norm_num) (by omega)]
  simp

lemma v2_succ_le {q n : ℕ} (hq : q < 2 ^ n) : v2 (q + 1) ≤ n := by
  by_contra hc
  push_neg at hc
  have hd : 2 ^ (n + 1) ∣ q + 1 := by
    rw [v2] at hc; exact (padicValNat_dvd_iff_le (by omega)).2 hc
  have := Nat.le_of_dvd (by omega) hd
  rw [pow_succ] at this
  omega

/-- The carry condition when two units come in. -/
lemma two_le_iff (q j : ℕ) (hj : 1 ≤ j) : 2 ^ j ≤ 2 + q % 2 ^ j ↔ j ≤ 1 + v2 (q / 2 + 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hm : q % 2 ^ (i + 1) = q % 2 + 2 * (q / 2 % 2 ^ i) := by
    rw [pow_succ', Nat.mod_mul]
  have h2 := le_v2_iff (q / 2) i
  have hq2 : q % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [hm, pow_succ']
  omega

/-- `s_2(n) + Σ_{u<M} ⌊n / 2^{u+1}⌋ = n` for `n < 2^M`. -/
lemma s2_add_sum_div : ∀ (M n : ℕ), n < 2 ^ M → s2 n + ∑ u ∈ range M, n / 2 ^ (u + 1) = n := by
  intro M
  induction M with
  | zero => intro n hn; simp at hn; subst hn; simp
  | succ M ih =>
    intro n hn
    have hn2 : n / 2 < 2 ^ M := by rw [pow_succ] at hn; omega
    have ih' := ih (n / 2) hn2
    have hs : s2 n = n % 2 + s2 (n / 2) := by
      conv_lhs => rw [← Nat.mod_add_div n 2]
      exact s2_bit _ _ (Nat.mod_lt _ (by norm_num))
    have hsum : ∑ u ∈ range (M + 1), n / 2 ^ (u + 1) =
        (∑ u ∈ range M, n / 2 / 2 ^ (u + 1)) + n / 2 := by
      rw [sum_range_succ']
      congr 1
      · apply sum_congr rfl; intro u _
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
    rw [hsum, hs]
    omega

/-- `κ(a, b)` is the number of carries: `κ(a, b) = Σ_{u<M} c_{u+1}` whenever `a + b < 2^M`. -/
lemma kappa_eq_sum (a b M : ℕ) (hM : a + b < 2 ^ M) :
    kappa a b = ∑ u ∈ range M,
      ((if 2 ^ (u + 1) ≤ a % 2 ^ (u + 1) + b % 2 ^ (u + 1) then 1 else 0 : ℕ) : ℤ) := by
  have ha := s2_add_sum_div M a (by omega)
  have hb := s2_add_sum_div M b (by omega)
  have hab := s2_add_sum_div M (a + b) hM
  have hsplit : ∑ u ∈ range M, (a + b) / 2 ^ (u + 1) = ∑ u ∈ range M, a / 2 ^ (u + 1)
      + ∑ u ∈ range M, b / 2 ^ (u + 1)
      + ∑ u ∈ range M, (if 2 ^ (u + 1) ≤ a % 2 ^ (u + 1) + b % 2 ^ (u + 1) then 1 else 0) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro u _
    exact Nat.add_div (Nat.two_pow_pos _)
  rw [← Nat.cast_sum, kappa]
  omega

/-- The low/high split of `κ(ℓ, x)` at bit `c`, for `x < 2^c` (the heart of **Lemma A**). -/
lemma kappa_split (c ℓ x : ℕ) (hx : x < 2 ^ c) :
    kappa ℓ x = kappa (ℓ % 2 ^ c) x +
      (v2 (ℓ / 2 ^ c + 1) : ℤ) * ((if 2 ^ c ≤ ℓ % 2 ^ c + x then 1 else 0 : ℕ) : ℤ) := by
  have hℓ : ℓ = ℓ % 2 ^ c + 2 ^ c * (ℓ / 2 ^ c) := (Nat.mod_add_div _ _).symm
  have ha : ℓ % 2 ^ c < 2 ^ c := Nat.mod_lt _ (Nat.two_pow_pos c)
  set a := ℓ % 2 ^ c
  set q := ℓ / 2 ^ c
  have e1 : s2 (a + 2 ^ c * q) = s2 a + s2 q := s2_add_two_pow_mul c a q ha
  rw [← hℓ] at e1
  have hsucc := s2_succ q
  unfold kappa
  split_ifs with hJ
  · have e2 : s2 ((a + x - 2 ^ c) + 2 ^ c * (q + 1)) = s2 (a + x - 2 ^ c) + s2 (q + 1) :=
      s2_add_two_pow_mul c _ _ (by omega)
    have e3 : s2 ((a + x - 2 ^ c) + 2 ^ c * 1) = s2 (a + x - 2 ^ c) + s2 1 :=
      s2_add_two_pow_mul c _ _ (by omega)
    rw [show a + x - 2 ^ c + 2 ^ c * (q + 1) = ℓ + x by rw [mul_add]; omega] at e2
    rw [show a + x - 2 ^ c + 2 ^ c * 1 = a + x by omega, s2_one] at e3
    rw [e2, e3, e1]
    push_cast; linarith
  · have e2 : s2 ((a + x) + 2 ^ c * q) = s2 (a + x) + s2 q :=
      s2_add_two_pow_mul c _ _ (by omega)
    rw [show a + x + 2 ^ c * q = ℓ + x by omega] at e2
    rw [e2, e1]
    push_cast; ring

/-- The split of `κ(ℓ, x + 2^c)` at bit `c`, for `x < 2^c` (used for (C2)). -/
lemma kappa_split_top (c ℓ x : ℕ) (hx : x < 2 ^ c) :
    kappa ℓ (x + 2 ^ c) = kappa (ℓ % 2 ^ c) x +
      (if 2 ^ c ≤ ℓ % 2 ^ c + x then 1 + (v2 (ℓ / 2 ^ c / 2 + 1) : ℤ)
        else (v2 (ℓ / 2 ^ c + 1) : ℤ)) := by
  have hℓ : ℓ = ℓ % 2 ^ c + 2 ^ c * (ℓ / 2 ^ c) := (Nat.mod_add_div _ _).symm
  have ha : ℓ % 2 ^ c < 2 ^ c := Nat.mod_lt _ (Nat.two_pow_pos c)
  set a := ℓ % 2 ^ c
  set q := ℓ / 2 ^ c
  have e1 : s2 (a + 2 ^ c * q) = s2 a + s2 q := s2_add_two_pow_mul c a q ha
  rw [← hℓ] at e1
  have ex : s2 (x + 2 ^ c * 1) = s2 x + s2 1 := s2_add_two_pow_mul c _ _ hx
  rw [mul_one, s2_one] at ex
  unfold kappa
  split_ifs with hJ
  · have e2 : s2 ((a + x - 2 ^ c) + 2 ^ c * (q + 2)) = s2 (a + x - 2 ^ c) + s2 (q + 2) :=
      s2_add_two_pow_mul c _ _ (by omega)
    have e3 : s2 ((a + x - 2 ^ c) + 2 ^ c * 1) = s2 (a + x - 2 ^ c) + s2 1 :=
      s2_add_two_pow_mul c _ _ (by omega)
    rw [show a + x - 2 ^ c + 2 ^ c * (q + 2) = ℓ + (x + 2 ^ c) by rw [mul_add]; omega] at e2
    rw [show a + x - 2 ^ c + 2 ^ c * 1 = a + x by omega, s2_one] at e3
    have hq : s2 q = q % 2 + s2 (q / 2) := by
      conv_lhs => rw [← Nat.mod_add_div q 2]
      exact s2_bit _ _ (Nat.mod_lt _ (by norm_num))
    have hq2 : s2 (q + 2) = q % 2 + s2 (q / 2 + 1) := by
      rw [show q + 2 = q % 2 + 2 * (q / 2 + 1) by omega]
      exact s2_bit _ _ (Nat.mod_lt _ (by norm_num))
    have hsucc := s2_succ (q / 2)
    rw [e2, e3, e1, ex, hq2, hq]
    push_cast; linarith
  · have e2 : s2 ((a + x) + 2 ^ c * (q + 1)) = s2 (a + x) + s2 (q + 1) :=
      s2_add_two_pow_mul c _ _ (by omega)
    rw [show a + x + 2 ^ c * (q + 1) = ℓ + (x + 2 ^ c) by rw [mul_add]; omega] at e2
    have hsucc := s2_succ q
    rw [e2, e1, ex]
    push_cast; linarith

/-- `o_E mod 2^u = o_{E ∩ [0, u)}`. -/
lemma oE_mod (E : Finset ℕ) (u : ℕ) : oE E % 2 ^ u = oE (E.filter (· < u)) := by
  have hsplit : oE E = oE (E.filter (· < u)) + oE (E.filter (fun t => ¬ t < u)) := by
    simp only [oE]; rw [sum_filter_add_sum_filter_not]
  have hdvd : 2 ^ u ∣ oE (E.filter (fun t => ¬ t < u)) := by
    apply dvd_sum; intro t ht
    exact pow_dvd_pow 2 (by simp at ht; omega)
  have hlt : oE (E.filter (· < u)) < 2 ^ u := oE_lt _ _ (fun t ht => (mem_filter.1 ht).2)
  obtain ⟨m, hm⟩ := hdvd
  rw [hsplit, hm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end Houses
