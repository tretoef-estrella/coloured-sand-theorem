module

public import RequestProject.OddHouses.LemmaA

/-!
# `CSI15_houses_at_p.md` — **Part C**: the top digit (Lemma 7.7_p)

Namespace `ColouredSand.OddTwist`; encodings as in `RequestProject/OddHouses/Basic.lean`.
The hypothesis «`I ≠ ∅`, `c := max I`» is written `hne : I.Nonempty` and `hc : c = I.max' hne`;
`I' := I ∖ {c}` is `I.erase c`; the house `H' = (I', c, ℓ mod p^c, e, d)` has
`R_{H'} = RHP p c (I.erase c) dg (ℓ % p ^ c) e`, `J_{H'} = JHP p c dg (ℓ % p ^ c)`,
`x_{H'} = xHP p c (I.erase c) dg (ℓ % p ^ c) e` and `γ' = Rulers.gamma c (I.erase c)`.  The data
`κ, sat, τ` and the type of `t = c` in `H` are `kapP p k I ℓ c`, `satP p k I ℓ c`,
`tauP p k I dg ℓ e c` and `typP p dg ℓ c`; the indicators `OR, DIG, AND` are
`if typP p dg ℓ c = .OR then 1 else 0` etc.  The length of the window of `c` is `h = k − c`
(C6's `Houses.h_max`).  `D₀ ⊆ I'` is `D₀ ⊆ I.erase c`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset

variable {p : ℕ} [hp : Fact p.Prime] {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ}

section Setup

omit hp in
lemma typP_OR_iff (t : ℕ) : typP p dg ℓ t = .OR ↔ thetaP p ℓ t = 1 := by
  unfold typP; split_ifs <;> simp_all

/-- The type of `t` is OR iff digit `t` of `ℓ` is `p − 1`. -/
lemma typP_OR_iff_digit (t : ℕ) : typP p dg ℓ t = .OR ↔ ℓ / p ^ t % p = p - 1 := by
  have hlt : ℓ / p ^ t % p < p := Nat.mod_lt _ hp.out.pos
  rw [typP_OR_iff]; unfold thetaP digP; omega

/-- A carry leaves digit `t` when `d_t` and `J ≤ 1` units come in iff the type of `t` is OR or
DIG, or it is AND and `J = 1`. -/
lemma fire_iff_typ {t J : ℕ} (hdt : 1 ≤ dg t ∧ dg t ≤ p - 1) (hJ : J ≤ 1) :
    p ≤ ℓ / p ^ t % p + (dg t + J) ↔
      (typP p dg ℓ t = .OR ∨ typP p dg ℓ t = .DIG) ∨ (typP p dg ℓ t = .AND ∧ J = 1) := by
  have hlt : ℓ / p ^ t % p < p := Nat.mod_lt _ hp.out.pos
  unfold typP thetaP digP
  split_ifs <;> simp <;> omega

lemma oW_lt_erase (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {c : ℕ} (hcmax : ∀ t ∈ I, t ≤ c)
    {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) : oW p dg D₀ < p ^ c := by
  apply oW_lt_pow oddHou_two_le_p
  · intro t ht
    have := mem_erase.1 (hD ht)
    exact lt_of_le_of_ne (hcmax t this.2) this.1
  · intro t ht
    have := hd t (mem_erase.1 (hD ht)).2; have := oddHou_two_le_p (p := p); omega

lemma q_lt_top {c : ℕ} (hℓ : ℓ < p ^ k) (hck : c < k) : ℓ / p ^ c < p ^ (k - c) := by
  rw [Nat.div_lt_iff_lt_mul (pow_pos hp.out.pos c), ← pow_add, Nat.sub_add_cancel hck.le]
  exact hℓ

lemma q_div_lt_top {c : ℕ} (hℓ : ℓ < p ^ k) (hck : c < k) :
    ℓ / p ^ c / p < p ^ (k - c - 1) := by
  have := q_lt_top (p := p) hℓ hck
  rw [show k - c = (k - c - 1) + 1 by omega, pow_succ] at this
  exact Nat.div_lt_of_lt_mul (by linarith)

/-- `κ_c = 1 + v_p(⌊q/p⌋ + 1)` with `q = ⌊ℓ / p^c⌋`. -/
lemma kapP_max (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < p ^ k) {c : ℕ} (hc : c ∈ I)
    (hcmax : ∀ t ∈ I, t ≤ c) :
    kapP p k I ℓ c = 1 + padicValNat p (ℓ / p ^ c / p + 1) := by
  have hck := hI c hc
  have hw := vP_succ_le (q_div_lt_top (p := p) hℓ hck)
  unfold kapP
  rw [rP_succ, Houses.h_max hI hc hcmax]
  omega

/-- `OR·κ_c = v_p(q + 1)` with `q = ⌊ℓ / p^c⌋`. -/
lemma typ_kapP_max (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < p ^ k) {c : ℕ} (hc : c ∈ I)
    (hcmax : ∀ t ∈ I, t ≤ c) :
    (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) =
      (padicValNat p (ℓ / p ^ c + 1) : ℤ) := by
  rw [kapP_max hI hℓ hc hcmax]
  by_cases hq : ℓ / p ^ c % p = p - 1
  · rw [if_pos ((typP_OR_iff_digit c).2 hq), vP_succ_of_eq hq]
  · rw [if_neg (fun h => hq ((typP_OR_iff_digit c).1 h)), vP_succ_of_ne hq]; simp

/-- `sat_c = 1` iff `⌊q/p⌋ + 1 = p^{h−1}` (`h = k − c`). -/
lemma satP_max (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < p ^ k) {c : ℕ} (hc : c ∈ I)
    (hcmax : ∀ t ∈ I, t ≤ c) :
    satP p k I ℓ c = if ℓ / p ^ c / p + 1 = p ^ (k - c - 1) then 1 else 0 := by
  have hck := hI c hc
  have hlt := q_div_lt_top (p := p) hℓ hck
  have hw := vP_succ_le hlt
  have hiff := le_vP_iff (p := p) (ℓ / p ^ c / p) (k - c - 1)
  rw [Nat.mod_eq_of_lt hlt] at hiff
  unfold satP
  rw [kapP_max hI hℓ hc hcmax, Houses.h_max hI hc hcmax]
  by_cases h1 : 1 + padicValNat p (ℓ / p ^ c / p + 1) = k - c
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]

/-- The carry out of `H` in terms of the carry out of `H'`, for an addend `o_{D₀} + y p^c`. -/
lemma JHP_top (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) {c : ℕ} (hcmax : ∀ t ∈ I, t ≤ c)
    (hck : c < k) {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) (y : ℕ) :
    p ^ k ≤ ℓ + (oW p dg D₀ + p ^ c * y) ↔
      p ^ (k - c) ≤ ℓ / p ^ c + (y + JHP p c dg (ℓ % p ^ c) D₀) := by
  have hx := oW_lt_erase hd hcmax hD
  have ha := Nat.mod_lt ℓ (pow_pos hp.out.pos c)
  have key := Houses.carry_aux (P := p ^ c) (M := p ^ (k - c)) (X := ℓ % p ^ c + oW p dg D₀)
    (Y := ℓ / p ^ c + y) (by omega)
  have hℓ := Nat.mod_add_div ℓ (p ^ c)
  rw [← pow_add, Nat.add_sub_cancel' hck.le] at key
  have hsum : ℓ + (oW p dg D₀ + p ^ c * y) =
      ℓ % p ^ c + oW p dg D₀ + p ^ c * (ℓ / p ^ c + y) := by
    rw [mul_add]; nth_rewrite 1 [← hℓ]; ring
  rw [hsum, key, JHP]
  constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

omit hp in
lemma oW_insert_max {c : ℕ} {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    oW p dg (D₀ ∪ {c}) = oW p dg D₀ + p ^ c * dg c := by
  have hcD : c ∉ D₀ := fun h => by simpa using hD h
  unfold oW
  rw [sum_union (disjoint_singleton_right.2 hcD), sum_singleton, mul_comm]

omit hp in
lemma sum_h_erase' (hI : ∀ t ∈ I, t < k) {c : ℕ} (hc : c ∈ I) (hcmax : ∀ t ∈ I, t ≤ c) (e : ℤ)
    {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    ∑ t ∈ D₀, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t) =
      ∑ t ∈ D₀, ((Rulers.h c (I.erase c) t : ℤ) - e * dg t * (p : ℤ) ^ t) :=
  sum_congr rfl (fun t ht => by rw [Houses.h_erase hI hc hcmax (hD ht)])

omit hp in
lemma JHP_le_one (c ℓ' : ℕ) (D : Finset ℕ) : JHP p c dg ℓ' D ≤ 1 := by
  unfold JHP; split_ifs <;> omega

end Setup

variable {c : ℕ}

/-- **(C1)** of `CSI15_houses_at_p.md` (Part C, Lemma 7.7_p): with `c = max I` and `D₀ ⊆ I'`,
`R_H(D₀) = R_{H'}(D₀) − OR·κ·J_{H'}(D₀)`. -/
theorem houseP_C1 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) (e : ℤ) (hne : I.Nonempty) (hc : c = I.max' hne) {D₀ : Finset ℕ}
    (hD : D₀ ⊆ I.erase c) :
    RHP p k I dg ℓ e D₀ = RHP p c (I.erase c) dg (ℓ % p ^ c) e D₀
      - (if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0) *
          JHP p c dg (ℓ % p ^ c) D₀ := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ le_max' I t ht
  have hx := oW_lt_erase hd hcmax hD
  unfold RHP
  rw [kappaP_split c ℓ _ hx, sum_h_erase' hI hcI hcmax e hD, typ_kapP_max hI hℓ hcI hcmax, JHP]
  ring

/-- **(C2)** of `CSI15_houses_at_p.md` (Part C, Lemma 7.7_p): with `c = max I` and `D₀ ⊆ I'`,
`R_H(D₀ ∪ {c}) = τ + R_{H'}(D₀) − AND·κ·J_{H'}(D₀)`. -/
theorem houseP_C2 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) (e : ℤ) (hne : I.Nonempty) (hc : c = I.max' hne) {D₀ : Finset ℕ}
    (hD : D₀ ⊆ I.erase c) :
    RHP p k I dg ℓ e (D₀ ∪ {c}) = tauP p k I dg ℓ e c + RHP p c (I.erase c) dg (ℓ % p ^ c) e D₀
      - (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) *
          JHP p c dg (ℓ % p ^ c) D₀ := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ le_max' I t ht
  have hx := oW_lt_erase hd hcmax hD
  have hcD : c ∉ D₀ := fun h => by simpa using hD h
  have hdc := hd c hcI
  have hdcp : dg c < p := by have := oddHou_two_le_p (p := p); omega
  have hfire := fire_iff_typ (p := p) (ℓ := ℓ) (t := c) hdc (JHP_le_one (p := p) (dg := dg) c (ℓ % p ^ c) D₀)
  have hkap := kapP_max hI hℓ hcI hcmax
  unfold RHP tauP
  rw [sum_union (disjoint_singleton_right.2 hcD), sum_singleton, oW_insert_max hD,
    kappaP_split_top c ℓ _ _ hx hdcp, sum_h_erase' hI hcI hcmax e hD]
  change _ = _ + (_ - kappaP p (ℓ % p ^ c) (oW p dg D₀)) - _ * ((JHP p c dg (ℓ % p ^ c) D₀ : ℕ) : ℤ)
  unfold JHP at hfire ⊢
  rw [hkap]
  have hJ1 : (if p ^ c ≤ ℓ % p ^ c + oW p dg D₀ then 1 else 0) ≤ 1 := by split_ifs <;> omega
  generalize (if p ^ c ≤ ℓ % p ^ c + oW p dg D₀ then 1 else 0) = J at hfire hJ1 ⊢
  simp only [hfire]
  generalize padicValNat p (ℓ / p ^ c / p + 1) = v
  cases typP p dg ℓ c <;>
    rcases (show J = 0 ∨ J = 1 by omega) with rfl | rfl <;> simp <;> ring

/-- **(C3)** of `CSI15_houses_at_p.md` (Part C, Lemma 7.7_p): with `c = max I` and `D₀ ⊆ I'`,
`J_H(D₀) = OR·sat·J_{H'}(D₀)`. -/
theorem houseP_C3 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) (hne : I.Nonempty) (hc : c = I.max' hne) {D₀ : Finset ℕ}
    (hD : D₀ ⊆ I.erase c) :
    JHP p k dg ℓ D₀ =
      (if typP p dg ℓ c = .OR then 1 else 0) * satP p k I ℓ c * JHP p c dg (ℓ % p ^ c) D₀ := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ le_max' I t ht
  have hck := hI c hcI
  have key := JHP_top (ℓ := ℓ) hd hcmax hck hD 0
  simp only [mul_zero, add_zero, zero_add] at key
  have hq := q_lt_top (p := p) hℓ hck
  have hJ := JHP_le_one (p := p) (dg := dg) c (ℓ % p ^ c) D₀
  have htop := top_carry_out (p := p) hq (by omega : 1 ≤ k - c) (by have := oddHou_two_le_p (p := p); omega : JHP p c dg (ℓ % p ^ c) D₀ ≤ p)
  have hOR := typP_OR_iff_digit (p := p) (dg := dg) (ℓ := ℓ) c
  have hlt : ℓ / p ^ c % p < p := Nat.mod_lt _ hp.out.pos
  rw [satP_max hI hℓ hcI hcmax]
  conv_lhs => unfold JHP
  simp only [key, htop]
  generalize JHP p c dg (ℓ % p ^ c) D₀ = J at hJ ⊢
  by_cases hT : typP p dg ℓ c = .OR
  · have := hOR.1 hT
    rw [if_pos hT]
    rcases (show J = 0 ∨ J = 1 by omega) with rfl | rfl <;> split_ifs <;> omega
  · have : ℓ / p ^ c % p ≠ p - 1 := fun h => hT (hOR.2 h)
    rw [if_neg hT, if_neg (by omega)]
    simp

/-- **(C4)** of `CSI15_houses_at_p.md` (Part C, Lemma 7.7_p): with `c = max I` and `D₀ ⊆ I'`,
`J_H(D₀ ∪ {c}) = sat·([OR ∨ DIG] + AND·J_{H'}(D₀))`. -/
theorem houseP_C4 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) (hne : I.Nonempty) (hc : c = I.max' hne) {D₀ : Finset ℕ}
    (hD : D₀ ⊆ I.erase c) :
    JHP p k dg ℓ (D₀ ∪ {c}) = satP p k I ℓ c *
      ((if typP p dg ℓ c = .OR ∨ typP p dg ℓ c = .DIG then 1 else 0) +
        (if typP p dg ℓ c = .AND then 1 else 0) * JHP p c dg (ℓ % p ^ c) D₀) := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ le_max' I t ht
  have hck := hI c hcI
  have hdc := hd c hcI
  have key := JHP_top (ℓ := ℓ) hd hcmax hck hD (dg c)
  have hq := q_lt_top (p := p) hℓ hck
  have hJ := JHP_le_one (p := p) (dg := dg) c (ℓ % p ^ c) D₀
  have htop := top_carry_out (p := p) hq (by omega : 1 ≤ k - c)
    (by have := oddHou_two_le_p (p := p); omega : dg c + JHP p c dg (ℓ % p ^ c) D₀ ≤ p)
  have hfire := fire_iff_typ (p := p) (ℓ := ℓ) (t := c) hdc hJ
  rw [satP_max hI hℓ hcI hcmax]
  conv_lhs => unfold JHP
  rw [oW_insert_max hD]
  simp only [key, htop, hfire]
  generalize JHP p c dg (ℓ % p ^ c) D₀ = J at hJ ⊢
  by_cases hS : ℓ / p ^ c / p + 1 = p ^ (k - c - 1) <;>
    cases typP p dg ℓ c <;> rcases (show J = 0 ∨ J = 1 by omega) with rfl | rfl <;> simp [hS]

/-- **(C5)**, first half, of `CSI15_houses_at_p.md` (Part C, Lemma 7.7_p): with `c = max I`, for
`∅ ≠ Δ ⊆ I` with `c ∉ Δ`, `γ(Δ) = γ'(Δ) + h` where `h = k − c` and `γ' = Rulers.gamma c I'`.
(This only concerns C3's `γ`; it is C6's `Houses.lemma_C5_not_mem`.) -/
theorem houseP_C5_not_mem (hI : ∀ t ∈ I, t < k) (hne : I.Nonempty) (hc : c = I.max' hne)
    {Δ : Finset ℕ} (hΔ : Δ ⊆ I) (hcΔ : c ∉ Δ) (hΔne : Δ ≠ ∅) :
    Rulers.gamma k I Δ = Rulers.gamma c (I.erase c) Δ + (k - c) :=
  Houses.lemma_C5_not_mem hI hne hc hΔ hcΔ hΔne

/-- **(C5)**, second half, of `CSI15_houses_at_p.md` (Part C, Lemma 7.7_p): with `c = max I`, for
`Δ₀ ⊆ I'`, `γ(Δ₀ ∪ {c}) = γ'(Δ₀)`.  (This only concerns C3's `γ`; it is C6's
`Houses.lemma_C5_mem`.) -/
theorem houseP_C5_mem (hI : ∀ t ∈ I, t < k) (hne : I.Nonempty) (hc : c = I.max' hne)
    {Δ₀ : Finset ℕ} (hΔ : Δ₀ ⊆ I.erase c) :
    Rulers.gamma k I (Δ₀ ∪ {c}) = Rulers.gamma c (I.erase c) Δ₀ :=
  Houses.lemma_C5_mem hI hne hc hΔ

/-- **(C6)** of `CSI15_houses_at_p.md` (Part C, Lemma 7.7_p): with `c = max I` and `D₀ ⊆ I'`,
`x_H(D₀) = x_{H'}(D₀) + d_1(D₀)`, where
`d_1(D₀) = −τ − OR·κ·J_{H'}(D₀) + AND·κ·J_{H'}(I' ∖ D₀)` (the definition `d1P`). -/
theorem houseP_C6 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) (e : ℤ) (hne : I.Nonempty) (hc : c = I.max' hne) {D₀ : Finset ℕ}
    (hD : D₀ ⊆ I.erase c) :
    xHP p k I dg ℓ e D₀ = xHP p c (I.erase c) dg (ℓ % p ^ c) e D₀ + d1P p k I dg ℓ e c D₀ := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  unfold xHP d1P
  rw [Houses.sdiff_max_eq hcI hD, houseP_C1 hI hd hℓ e hne hc hD,
    houseP_C2 hI hd hℓ e hne hc (sdiff_subset (s := I.erase c) (t := D₀))]
  ring

/-- **(C7)** of `CSI15_houses_at_p.md` (Part C, Lemma 7.7_p): with `c = max I` and `D₀ ⊆ I'`,
`x_H(D₀ ∪ {c}) = −(x_{H'}(I' ∖ D₀) + d_1(I' ∖ D₀))`. -/
theorem houseP_C7 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) (e : ℤ) (hne : I.Nonempty) (hc : c = I.max' hne) {D₀ : Finset ℕ}
    (hD : D₀ ⊆ I.erase c) :
    xHP p k I dg ℓ e (D₀ ∪ {c}) =
      -(xHP p c (I.erase c) dg (ℓ % p ^ c) e (I.erase c \ D₀) +
        d1P p k I dg ℓ e c (I.erase c \ D₀)) := by
  have hcI : c ∈ I := hc ▸ max'_mem I hne
  have hsub : D₀ ∪ {c} ⊆ I := union_subset (hD.trans (erase_subset c I)) (by simp [hcI])
  have hcompl : I \ (D₀ ∪ {c}) = I.erase c \ D₀ := by
    ext u; simp only [mem_sdiff, mem_union, mem_singleton, mem_erase]; tauto
  have hA0 := houseP_A0_antisymm (p := p) (k := k) (dg := dg) ℓ e hsub
  rw [hcompl] at hA0
  rw [← houseP_C6 hI hd hℓ e hne hc (sdiff_subset (s := I.erase c) (t := D₀)), hA0]
  ring

end ColouredSand.OddTwist
