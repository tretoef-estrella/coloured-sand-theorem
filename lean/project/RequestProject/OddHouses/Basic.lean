module

public import RequestProject.OddRulers.All
public import RequestProject.Houses.All

/-!
# `CSI15_houses_at_p.md` — *Setting* and *Part B* data: houses at a prime `p`

Namespace `ColouredSand.OddTwist`.  This is the base-`p` analogue of C6
(`RequestProject/Houses/Basic.lean`).

## Encodings

* The prime is `p : ℕ` with `[Fact p.Prime]` (the file's `p ≥ 3` is never needed: everything is
  proved for every prime `p`, including `p = 2`).
* A **house** `H = (I, k, ℓ, e, d)` is not bundled: every definition takes its components
  explicitly, `I : Finset ℕ`, `k : ℕ`, `ℓ : ℕ`, `e : ℤ` and the digit function `dg : ℕ → ℕ`
  (`d_t = dg t`).  The house conditions are hypotheses of the theorems:
  `hI : ∀ t ∈ I, t < k` (`I ⊆ {0, …, k − 1}`), `hℓ : ℓ < p ^ k` (`0 ≤ ℓ < p^k`) and
  `hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1`.  Each theorem carries only those it uses.
* Reused, not redefined: C3's `Rulers.next`, `Rulers.h` (`h_t`), `Rulers.gamma` (`γ`, cast to `ℤ`);
  CSI12's `oW p dg E` (`o_E = Σ_{t∈E} d_t p^t`); CSI13's `sP` (`s_p`), `kappaP` (`κ_p`) and
  `rulerP` (the ruler `R_μ` with `e : ℕ`).
* `digP p u x := ⌊x / p^u⌋ mod p` is digit `u` of `x` in base `p`.
* `rP p u x` is `r_u(x)`, the number of consecutive base-`p` digits of `x` equal to `p − 1`
  starting at digit `u`.  It is defined as `v_p(⌊x / p^u⌋ + 1)` (`padicValNat`), and
  `rP_spec` proves that it is exactly that count:
  `j ≤ rP p u x ↔ ∀ i < j, digP p (u + i) x = p − 1`.
* `RHP p k I dg ℓ e E` is the base ruler `R_H(E) := Σ_{t∈E}(h_t − e d_t p^t) − κ_p(ℓ, o_E)` with
  `e : ℤ`; for an arbitrary natural number in place of `ℓ` it is the ruler `R_μ`
  (`RHP_eq_rulerP`: it equals CSI13's `rulerP` when `e` is a natural number).
* `JHP p k dg ℓ E` is the carry-out indicator `J_H(E) := [ℓ + o_E ≥ p^k]` (a natural number
  `0`/`1`).
* `xHP` is the clock `x_H(D) := R_H(D) − R_H(I ∖ D)`; `cHatHP` the cost
  `ĉ_H(a, b) := R_H(a) − R_H(b) + γ(a ∖ b)` with `γ = Rulers.gamma k I`.
* `cinP p dg ℓ u E` is the carry into digit `u`:
  `c_u(E) := [(ℓ mod p^u) + (o_E mod p^u) ≥ p^u]`.
* `carP p k I dg ℓ t E` is `car_t(E) := #{u ∈ [t, next(t)) : c_{u+1}(E) = 1}`, the cardinality
  of a filter of `Finset.Ico t (Rulers.next k I t)`.
* Window data of `t` (Part B): `thetaP p ℓ t` is `θ_t := p − ℓ_t` (`ℓ_t = digP p t ℓ`);
  `kapP p k I ℓ t` is `κ_t := 1 + min(r_{t+1}(ℓ), h_t − 1)`; `satP` is `sat_t := [κ_t = h_t]`;
  the four types are the constructors of `WinTypeP` (`OR`, `DIG`, `AND`, `NEV`) and `typP p dg ℓ t`
  is the type of `t`; `tauP p k I dg ℓ e t` is `τ_t := h_t − e d_t p^t − [type ∈ {OR, DIG}] κ_t`.
* `firesP p dg ℓ t E` is the firing condition of (B2) (a `Prop`, by cases on the type).
* `d1P p k I dg ℓ e c D₀` is `d_1(D₀)` of (C6).

Indicators `[P]` are written `if P then 1 else 0`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset

/-- Digit `u` of `x` in base `p`: `⌊x / p^u⌋ mod p` (*Setting* of `CSI15_houses_at_p.md`). -/
def digP (p u x : ℕ) : ℕ := x / p ^ u % p

/-- `r_u(x)`, the number of consecutive base-`p` digits of `x` equal to `p − 1` starting at digit
`u` (*Setting* of `CSI15_houses_at_p.md`), defined as `v_p(⌊x / p^u⌋ + 1)`; `rP_spec` shows that
it is this count. -/
def rP (p u x : ℕ) : ℕ := padicValNat p (x / p ^ u + 1)

/-- **Base ruler** `R_H(E) := Σ_{t∈E}(h_t − e·d_t·p^t) − κ_p(ℓ, o_E)` with `e ∈ ℤ`
(*Setting* of `CSI15_houses_at_p.md`).  With any `μ` in place of `ℓ` this is `R_μ`. -/
def RHP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (E : Finset ℕ) : ℤ :=
  ∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t) - kappaP p ℓ (oW p dg E)

/-- **Carry-out set** `J_H(E) := [ℓ + o_E ≥ p^k]` (*Setting* of `CSI15_houses_at_p.md`). -/
def JHP (p k : ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (E : Finset ℕ) : ℕ :=
  if p ^ k ≤ ℓ + oW p dg E then 1 else 0

/-- **Clocks** `x_H(D) := R_H(D) − R_H(I ∖ D)` (*Setting* of `CSI15_houses_at_p.md`). -/
def xHP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (D : Finset ℕ) : ℤ :=
  RHP p k I dg ℓ e D - RHP p k I dg ℓ e (I \ D)

/-- **Costs** `ĉ_H(a, b) := R_H(a) − R_H(b) + γ(a ∖ b)` (*Setting* of `CSI15_houses_at_p.md`). -/
def cHatHP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (a b : Finset ℕ) : ℤ :=
  RHP p k I dg ℓ e a - RHP p k I dg ℓ e b + Rulers.gamma k I (a \ b)

/-- The **carry into digit `u`**: `c_u(E) := [(ℓ mod p^u) + (o_E mod p^u) ≥ p^u]`
(*Setting* of `CSI15_houses_at_p.md`). -/
def cinP (p : ℕ) (dg : ℕ → ℕ) (ℓ u : ℕ) (E : Finset ℕ) : ℕ :=
  if p ^ u ≤ ℓ % p ^ u + oW p dg E % p ^ u then 1 else 0

/-- The carries made by the window `W_t = [t, next(t))`:
`car_t(E) := #{u ∈ [t, next(t)) : c_{u+1}(E) = 1}` (*Setting* of `CSI15_houses_at_p.md`). -/
def carP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ t : ℕ) (E : Finset ℕ) : ℕ :=
  ((Ico t (Rulers.next k I t)).filter (fun u => cinP p dg ℓ (u + 1) E = 1)).card

/-- `θ_t := p − ℓ_t`, `ℓ_t` the digit `t` of `ℓ` (*Part B* of `CSI15_houses_at_p.md`). -/
def thetaP (p ℓ t : ℕ) : ℕ := p - digP p t ℓ

/-- `κ_t := 1 + min(r_{t+1}(ℓ), h_t − 1)` (*Part B* of `CSI15_houses_at_p.md`). -/
def kapP (p k : ℕ) (I : Finset ℕ) (ℓ t : ℕ) : ℕ := 1 + min (rP p (t + 1) ℓ) (Rulers.h k I t - 1)

/-- `sat_t := [κ_t = h_t]` (*Part B* of `CSI15_houses_at_p.md`). -/
def satP (p k : ℕ) (I : Finset ℕ) (ℓ t : ℕ) : ℕ := if kapP p k I ℓ t = Rulers.h k I t then 1 else 0

/-- The four window types of *Part B* of `CSI15_houses_at_p.md`. -/
inductive WinTypeP
  | OR
  | DIG
  | AND
  | NEV
  deriving DecidableEq

/-- The **type** of `t` (*Part B* of `CSI15_houses_at_p.md`): OR if `θ_t = 1`, DIG if
`2 ≤ θ_t ≤ d_t`, AND if `θ_t = d_t + 1`, NEV if `θ_t ≥ d_t + 2` (since `θ_t ≥ 1`,
`thetaP_pos`, the chain of tests below is exactly this case split). -/
def typP (p : ℕ) (dg : ℕ → ℕ) (ℓ t : ℕ) : WinTypeP :=
  if thetaP p ℓ t = 1 then .OR
  else if thetaP p ℓ t ≤ dg t then .DIG
  else if thetaP p ℓ t = dg t + 1 then .AND
  else .NEV

/-- `τ_t := h_t − e d_t p^t − [type t ∈ {OR, DIG}]·κ_t` (*Part B* of `CSI15_houses_at_p.md`). -/
def tauP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (t : ℕ) : ℤ :=
  (Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t -
    (if typP p dg ℓ t = .OR ∨ typP p dg ℓ t = .DIG then (kapP p k I ℓ t : ℤ) else 0)

/-- The window of `t` **fires** for `E` (*Part B* (B2) of `CSI15_houses_at_p.md`), with
`δ = [t ∈ E]`: OR: `δ = 1 ∨ c_t(E) = 1`; DIG: `δ = 1`; AND: `δ = 1 ∧ c_t(E) = 1`; NEV: never. -/
def firesP (p : ℕ) (dg : ℕ → ℕ) (ℓ t : ℕ) (E : Finset ℕ) : Prop :=
  match typP p dg ℓ t with
  | .OR => t ∈ E ∨ cinP p dg ℓ t E = 1
  | .DIG => t ∈ E
  | .AND => t ∈ E ∧ cinP p dg ℓ t E = 1
  | .NEV => False

/-- `d_1(D₀) := −τ − OR·κ·J_{H'}(D₀) + AND·κ·J_{H'}(I' ∖ D₀)` of (C6), where `τ, κ` and the type
are the data of `t = c` in `H = (I, k, ℓ, e, d)` and `H' = (I ∖ {c}, c, ℓ mod p^c, e, d)`
(*Part C* of `CSI15_houses_at_p.md`). -/
def d1P (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (c : ℕ) (D₀ : Finset ℕ) : ℤ :=
  -tauP p k I dg ℓ e c
    - (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) * JHP p c dg (ℓ % p ^ c) D₀
    + (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) *
        JHP p c dg (ℓ % p ^ c) (I.erase c \ D₀)

/-- The base ruler with `e` a natural number is CSI13's ruler `rulerP` (*Setting* of
`CSI15_houses_at_p.md`: `R_H` is the CSI13 ruler with `μ = ℓ`). -/
theorem RHP_eq_rulerP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ e : ℕ) (E : Finset ℕ) :
    RHP p k I dg ℓ (e : ℤ) E = rulerP p e k I dg ℓ E := rfl

/-- `r_{t+1}(ℓ) = v_p(⌊⌊ℓ/p^t⌋/p⌋ + 1)`. -/
lemma rP_succ (p t ℓ : ℕ) : rP p (t + 1) ℓ = padicValNat p (ℓ / p ^ t / p + 1) := by
  unfold rP; rw [Nat.div_div_eq_div_mul, ← pow_succ]

/-! ### Arithmetic in base `p` -/

section arith

variable {p : ℕ} [hp : Fact p.Prime]

lemma oddHou_two_le_p : 2 ≤ p := hp.out.two_le

lemma thetaP_pos (ℓ t : ℕ) : 1 ≤ thetaP p ℓ t := by
  have := Nat.mod_lt (ℓ / p ^ t) hp.out.pos
  unfold thetaP digP; omega

/-- `j ≤ v_p(q + 1) ↔ p^j ≤ q mod p^j + 1`. -/
lemma le_vP_iff (q j : ℕ) : j ≤ padicValNat p (q + 1) ↔ p ^ j ≤ q % p ^ j + 1 := by
  rw [← padicValNat_dvd_iff_le (by omega)]
  have hpos : 0 < p ^ j := pow_pos hp.out.pos j
  have hlt : q % p ^ j < p ^ j := Nat.mod_lt _ hpos
  have hq : q + 1 = p ^ j * (q / p ^ j) + (q % p ^ j + 1) := by
    have := Nat.div_add_mod q (p ^ j); omega
  rw [hq, Nat.dvd_add_right (dvd_mul_right _ _)]
  constructor
  · intro hd; exact Nat.le_of_dvd (Nat.succ_pos _) hd
  · intro hle; rw [show q % p ^ j + 1 = p ^ j by omega]

lemma vP_succ_le {q n : ℕ} (hq : q < p ^ n) : padicValNat p (q + 1) ≤ n := by
  by_contra hc
  push_neg at hc
  have hd : p ^ (n + 1) ∣ q + 1 := (padicValNat_dvd_iff_le (by omega)).2 hc
  have := Nat.le_of_dvd (by omega) hd
  rw [pow_succ] at this
  have := oddHou_two_le_p (p := p)
  nlinarith

lemma vP_succ_of_ne {q : ℕ} (hq : q % p ≠ p - 1) : padicValNat p (q + 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  have h2 := oddHou_two_le_p (p := p)
  have := Nat.mod_lt q hp.out.pos
  intro hd
  have h0 : (q + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hd
  have hd' := Nat.mod_add_div q p
  have hd'' := Nat.mod_add_div (q + 1) p
  rw [h0] at hd''
  -- q + 1 = p * m, q = r + p * s with r < p - 1
  have : q % p + 1 < p := by omega
  have e1 : (q + 1) % p = q % p + 1 := by
    rw [show q + 1 = (q % p + 1) + p * (q / p) by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt this]
  omega

lemma vP_succ_of_eq {q : ℕ} (hq : q % p = p - 1) :
    padicValNat p (q + 1) = 1 + padicValNat p (q / p + 1) := by
  have h2 := oddHou_two_le_p (p := p)
  have e : q + 1 = p * (q / p + 1) := by
    have := Nat.mod_add_div q p; rw [Nat.mul_add, Nat.mul_one]; omega
  rw [e, padicValNat.mul hp.out.ne_zero (Nat.succ_ne_zero _), padicValNat_self]

/-- `r_u(x)` is the number of consecutive base-`p` digits of `x` equal to `p − 1` starting at
digit `u` (*Setting* of `CSI15_houses_at_p.md`). -/
theorem rP_spec (u x j : ℕ) : j ≤ rP p u x ↔ ∀ i < j, digP p (u + i) x = p - 1 := by
  have h2 := oddHou_two_le_p (p := p)
  unfold rP digP
  suffices H : ∀ q : ℕ, (j ≤ padicValNat p (q + 1) ↔ ∀ i < j, q / p ^ i % p = p - 1) by
    rw [H]
    refine forall_congr' fun i => imp_congr_right fun _ => ?_
    rw [Nat.div_div_eq_div_mul, ← pow_add]
  induction j with
  | zero => intro q; simp
  | succ j ih =>
    intro q
    by_cases hq : q % p = p - 1
    · rw [vP_succ_of_eq hq, show j + 1 = 1 + j by ring, Nat.add_le_add_iff_left, ih (q / p)]
      constructor
      · intro H i hi
        rcases i with _ | i
        · simpa using hq
        · have := H i (by omega)
          rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at this
      · intro H i hi
        have := H (i + 1) (by omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul] at this
    · rw [vP_succ_of_ne hq]
      constructor
      · intro H; omega
      · intro H; exact absurd (by simpa using H 0 (by omega)) hq

/-- `n − s_p(n) = (p − 1) Σ_{u<M} ⌊n / p^{u+1}⌋` for `n < p^M`. -/
lemma sP_add_sum_div : ∀ (M n : ℕ), n < p ^ M →
    (sP p n : ℤ) + ((p : ℤ) - 1) * ∑ u ∈ range M, ((n / p ^ (u + 1) : ℕ) : ℤ) = n := by
  have h2 := oddHou_two_le_p (p := p)
  intro M
  induction M with
  | zero => intro n hn; simp at hn; subst hn; simp
  | succ M ih =>
    intro n hn
    have hn2 : n / p < p ^ M := by
      rw [pow_succ] at hn; exact Nat.div_lt_of_lt_mul (by linarith)
    have ih' := ih (n / p) hn2
    have hs : sP p n = n % p + sP p (n / p) := by
      conv_lhs => rw [← Nat.mod_add_div n p]
      exact sP_add_mul h2 _ (Nat.mod_lt _ (by omega))
    have hsum : ∑ u ∈ range (M + 1), ((n / p ^ (u + 1) : ℕ) : ℤ) =
        (∑ u ∈ range M, ((n / p / p ^ (u + 1) : ℕ) : ℤ)) + ((n / p : ℕ) : ℤ) := by
      rw [sum_range_succ']
      congr 1
      · apply sum_congr rfl; intro u _
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      · simp
    rw [hsum, hs]
    have hd := Nat.mod_add_div n p
    have hd' : ((n % p : ℕ) : ℤ) + (p : ℤ) * ((n / p : ℕ) : ℤ) = n := by exact_mod_cast hd
    rw [Nat.cast_add]
    linear_combination ih' + hd'

/-- `κ_p(a, b)` is the number of carries: `κ_p(a, b) = Σ_{u<M} c_{u+1}` whenever `a + b < p^M`. -/
lemma kappaP_eq_sum (a b M : ℕ) (hM : a + b < p ^ M) :
    kappaP p a b = ∑ u ∈ range M,
      ((if p ^ (u + 1) ≤ a % p ^ (u + 1) + b % p ^ (u + 1) then 1 else 0 : ℕ) : ℤ) := by
  have h2 := oddHou_two_le_p (p := p)
  have hp1 : ((p : ℤ) - 1) ≠ 0 := by omega
  apply mul_left_cancel₀ hp1
  rw [kappaP_mul]
  have ha := sP_add_sum_div (p := p) M a (by omega)
  have hb := sP_add_sum_div (p := p) M b (by omega)
  have hab := sP_add_sum_div (p := p) M (a + b) hM
  have hsplit : ∑ u ∈ range M, (((a + b) / p ^ (u + 1) : ℕ) : ℤ) =
      ∑ u ∈ range M, ((a / p ^ (u + 1) : ℕ) : ℤ) + ∑ u ∈ range M, ((b / p ^ (u + 1) : ℕ) : ℤ)
      + ∑ u ∈ range M, ((if p ^ (u + 1) ≤ a % p ^ (u + 1) + b % p ^ (u + 1) then 1 else 0 : ℕ)
          : ℤ) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro u _
    rw [Nat.add_div (pow_pos (by omega) _), Nat.cast_add, Nat.cast_add]
  rw [hsplit, Nat.cast_add] at hab
  linear_combination ha + hb - hab

/-- The carries made by a small addend `n ≤ p` on `q`:
`s_p(q) + n − s_p(q + n) = (p − 1)·[p ≤ q mod p + n]·(1 + v_p(⌊q/p⌋ + 1))`. -/
lemma sP_small_add (q n : ℕ) (hn : n ≤ p) :
    (sP p q : ℤ) + n - sP p (q + n) =
      ((p : ℤ) - 1) * (if p ≤ q % p + n then 1 + (padicValNat p (q / p + 1) : ℤ) else 0) := by
  have h2 := oddHou_two_le_p (p := p)
  have hlt := Nat.mod_lt q (show 0 < p by omega)
  have hs : sP p q = q % p + sP p (q / p) := by
    conv_lhs => rw [← Nat.mod_add_div q p]
    exact sP_add_mul h2 _ hlt
  have hd := Nat.mod_add_div q p
  split_ifs with h
  · have e : q + n = (q % p + n - p) + p * (q / p + 1) := by rw [mul_add]; omega
    rw [e, sP_add_mul h2 _ (by omega), hs]
    have hv := padicValNat_succ_mul (p := p) (q / p)
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega : p ≤ q % p + n), Nat.cast_add]
    linear_combination -hv
  · have e : q + n = (q % p + n) + p * (q / p) := by omega
    rw [e, sP_add_mul h2 _ (by omega), hs]
    simp only [Nat.cast_add]; ring

/-- `[p ≤ q mod p + J]·(1 + v_p(⌊q/p⌋ + 1)) = J·v_p(q + 1)` for `J ≤ 1`. -/
lemma small_one (q J : ℕ) (hJ : J ≤ 1) :
    (if p ≤ q % p + J then 1 + (padicValNat p (q / p + 1) : ℤ) else 0) =
      (J : ℤ) * padicValNat p (q + 1) := by
  have hlt := Nat.mod_lt q hp.out.pos
  rcases (show J = 0 ∨ J = 1 by omega) with rfl | rfl
  · rw [if_neg (by omega)]; simp
  · by_cases hq : q % p = p - 1
    · rw [if_pos (by omega), vP_succ_of_eq hq]; push_cast; ring
    · rw [if_neg (by omega), vP_succ_of_ne hq]; simp

/-- **The split of `κ_p` at digit `c`**: for `x < p^c` and `y < p`, with `a = ℓ mod p^c`,
`q = ⌊ℓ / p^c⌋` and `J = [a + x ≥ p^c]`,
`κ_p(ℓ, x + p^c y) = κ_p(a, x) + [p ≤ q mod p + y + J]·(1 + v_p(⌊q/p⌋ + 1))`. -/
lemma kappaP_split_top (c ℓ x y : ℕ) (hx : x < p ^ c) (hy : y < p) :
    kappaP p ℓ (x + p ^ c * y) = kappaP p (ℓ % p ^ c) x +
      (if p ≤ ℓ / p ^ c % p + (y + (if p ^ c ≤ ℓ % p ^ c + x then 1 else 0))
        then 1 + (padicValNat p (ℓ / p ^ c / p + 1) : ℤ) else 0) := by
  have h2 := oddHou_two_le_p (p := p)
  have hp1 : ((p : ℤ) - 1) ≠ 0 := by omega
  have hpc : 0 < p ^ c := pow_pos (by omega) c
  apply mul_left_cancel₀ hp1
  have ha : ℓ % p ^ c < p ^ c := Nat.mod_lt _ hpc
  have hℓ := Nat.mod_add_div ℓ (p ^ c)
  set a := ℓ % p ^ c
  set q := ℓ / p ^ c
  set J : ℕ := if p ^ c ≤ a + x then 1 else 0 with hJdef
  have hJ1 : J ≤ 1 := by rw [hJdef]; split_ifs <;> omega
  obtain ⟨r, hr, hrJ⟩ : ∃ r, r < p ^ c ∧ a + x = r + p ^ c * J := by
    rw [hJdef]; split_ifs with h
    · exact ⟨a + x - p ^ c, by omega, by omega⟩
    · exact ⟨a + x, by omega, by omega⟩
  have e1 : sP p ℓ = sP p a + sP p q := by
    rw [← sP_add_pow_mul h2 c a q ha, hℓ]
  have ex : sP p (x + p ^ c * y) = sP p x + y := by
    rw [sP_add_pow_mul h2 c x y hx, sP_lt h2 hy]
  have eax : sP p (a + x) = sP p r + J := by
    rw [hrJ, sP_add_pow_mul h2 c r J hr, sP_lt h2 (show J < p by omega)]
  have esum : sP p (ℓ + (x + p ^ c * y)) = sP p r + sP p (q + (y + J)) := by
    rw [← sP_add_pow_mul h2 c r _ hr]
    congr 1
    rw [mul_add, mul_add]; nth_rewrite 1 [← hℓ]; linarith
  have hsmall := sP_small_add (p := p) q (y + J) (by omega)
  rw [mul_add, kappaP_mul, kappaP_mul, ← hsmall, e1, ex, esum, eax]
  push_cast; ring

/-- The split of `κ_p` at digit `c` without top digit:
`κ_p(ℓ, x) = κ_p(ℓ mod p^c, x) + v_p(⌊ℓ/p^c⌋ + 1)·[ℓ mod p^c + x ≥ p^c]` for `x < p^c`. -/
lemma kappaP_split (c ℓ x : ℕ) (hx : x < p ^ c) :
    kappaP p ℓ x = kappaP p (ℓ % p ^ c) x +
      (padicValNat p (ℓ / p ^ c + 1) : ℤ) *
        ((if p ^ c ≤ ℓ % p ^ c + x then 1 else 0 : ℕ) : ℤ) := by
  have h := kappaP_split_top (p := p) c ℓ x 0 hx hp.out.pos
  simp only [mul_zero, add_zero, zero_add] at h
  rw [h, small_one _ _ (by split_ifs <;> omega)]
  ring

/-- `o_E mod p^u = o_{E ∩ [0, u)}` when the digits on `E` are `< p`. -/
lemma oW_mod (dg : ℕ → ℕ) (E : Finset ℕ) (hd : ∀ t ∈ E, dg t < p) (u : ℕ) :
    oW p dg E % p ^ u = oW p dg (E.filter (· < u)) := by
  have h2 := oddHou_two_le_p (p := p)
  have hsplit : oW p dg E = oW p dg (E.filter (· < u)) + oW p dg (E.filter (fun t => ¬ t < u)) := by
    simp only [oW]; rw [sum_filter_add_sum_filter_not]
  have hdvd : p ^ u ∣ oW p dg (E.filter (fun t => ¬ t < u)) := by
    apply dvd_sum; intro t ht
    exact Dvd.dvd.mul_left (pow_dvd_pow p (by simp at ht; omega)) _
  have hlt : oW p dg (E.filter (· < u)) < p ^ u :=
    oW_lt_pow h2 dg _ (fun t ht => (mem_filter.1 ht).2) (fun t ht => hd t (mem_filter.1 ht).1)
  obtain ⟨m, hm⟩ := hdvd
  rw [hsplit, hm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The carry condition at the top: for `q < p^h`, `1 ≤ h` and `n ≤ p`,
`p^h ≤ q + n ↔ p ≤ q mod p + n ∧ ⌊q/p⌋ + 1 = p^{h−1}`. -/
lemma top_carry_out {q h n : ℕ} (hq : q < p ^ h) (hh : 1 ≤ h) (hn : n ≤ p) :
    p ^ h ≤ q + n ↔ p ≤ q % p + n ∧ q / p + 1 = p ^ (h - 1) := by
  have h2 := oddHou_two_le_p (p := p)
  have hlt := Nat.mod_lt q (show 0 < p by omega)
  have hph : p ^ h = p * p ^ (h - 1) := by rw [← pow_succ']; congr 1; omega
  have hs : q / p < p ^ (h - 1) := by
    rw [hph] at hq; exact Nat.div_lt_of_lt_mul hq
  have key := Houses.carry_aux (P := p) (M := p ^ (h - 1)) (X := q % p + n) (Y := q / p)
    (by omega)
  have hd := Nat.mod_add_div q p
  rw [show q + n = q % p + n + p * (q / p) by omega, hph, key]
  split_ifs <;> constructor <;> intro hh' <;> omega

end arith

end ColouredSand.OddTwist
