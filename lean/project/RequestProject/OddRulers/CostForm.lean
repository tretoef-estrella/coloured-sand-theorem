module

public import RequestProject.OddRulers.Carries

/-!
# `CSI13_the_odd_cost_form.md` — the rulers and **(P1) the identity** of **Part P**

Namespace `ColouredSand.OddTwist`; encodings as in `Digits.lean` and `Carries.lean`.

* `rulerP p e k I dg μ E` is `R_μ(E) := Σ_{t ∈ E}(h_t − e d_t p^t) − κ_p(μ, o_E)` (in `ℤ`), with
  C3's gaps `h_t = Rulers.h k I t`.
* `rulerSharpP p e k I dg E` is `R^♯(E) := Σ_{t ∈ E}(h_t − e d_t p^t) − (k − min E)` for `E ≠ ∅`,
  and `R^♯(∅) := 0`.
* `(p^t − 1)/(p − 1)` is the natural number division `(p ^ t - 1) / (p - 1)` (exact,
  `geomN_mul`), `K = d_k p^k` is `dk * p ^ k`, and `m = i − 1` is the natural number `i - 1`
  (for `i ≥ 1`).  The sum `Σ_{d=o_a}^{o_b+K−1}` is the sum over `Finset.Ico (o_a) (o_b + K)`.
* The deficit is C3's `Rulers.delta k` and the gold is C3's `Rulers.gamma k I`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset

/-- **The rulers** (*Setting* of `CSI13_the_odd_cost_form.md`):
`R_μ(E) := Σ_{t ∈ E}(h_t − e d_t p^t) − κ_p(μ, o_E)`. -/
def rulerP (p e k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (μ : ℕ) (E : Finset ℕ) : ℤ :=
  ∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t) - kappaP p μ (oW p dg E)

/-- **The rulers** (*Setting* of `CSI13_the_odd_cost_form.md`):
`R^♯(E) := Σ_{t ∈ E}(h_t − e d_t p^t) − (k − min E)`, with `R^♯(∅) := 0`. -/
def rulerSharpP (p e k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (E : Finset ℕ) : ℤ :=
  if E = ∅ then 0 else
    ∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t) - ((k : ℤ) - Rulers.minOr k E)

lemma sum_h_sub_oW (p e k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (E : Finset ℕ) :
    ∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t) =
      ∑ t ∈ E, (Rulers.h k I t : ℤ) - e * (oW p dg E : ℤ) := by
  simp only [oW, sum_sub_distrib]; push_cast; rw [mul_sum]; congr 1
  exact sum_congr rfl (fun _ _ => by ring)

/-- With the convention `min ∅ := k`, the formula of `R^♯` also holds for `E = ∅`. -/
lemma rulerSharpP_eq (p e k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (E : Finset ℕ) :
    rulerSharpP p e k I dg E =
      ∑ t ∈ E, (Rulers.h k I t : ℤ) - e * (oW p dg E : ℤ) - ((k : ℤ) - Rulers.minOr k E) := by
  rw [rulerSharpP, sum_h_sub_oW]
  split_ifs with h
  · subst h; simp [oW, Rulers.minOr_empty]
  · rfl

lemma oW_cast (p : ℕ) (dg : ℕ → ℕ) (E : Finset ℕ) :
    (oW p dg E : ℤ) = ∑ t ∈ E, (dg t : ℤ) * (p : ℤ) ^ t := by
  simp [oW]

/-- `(p − 1) Σ_{t ∈ E} d_t (p^t − 1)/(p − 1) = o_E − Σ_{t ∈ E} d_t`. -/
lemma sum_geomN_mul {p : ℕ} (hp : 2 ≤ p) (dg : ℕ → ℕ) (E : Finset ℕ) :
    ((p : ℤ) - 1) * ∑ t ∈ E, (dg t : ℤ) * (((p ^ t - 1) / (p - 1) : ℕ) : ℤ) =
      (oW p dg E : ℤ) - ∑ t ∈ E, (dg t : ℤ) := by
  rw [oW_cast, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl (fun t _ => ?_)
  have := geomN_mul hp t
  linear_combination (dg t : ℤ) * this

variable {p : ℕ} [hp : Fact p.Prime]

/-- **(P1) The identity** (*Part P* of `CSI13_the_odd_cost_form.md`), case `i ≥ 1`: for
`b ⊆ a ⊆ I`, `Δ = a ∖ b`, `i ≥ 1` and `m = i − 1`,
`−d_k(p^k − 1)/(p − 1) + Σ_{t ∈ Δ}(1 + d_t(p^t − 1)/(p − 1)) + δ(Δ) + e(K − o_Δ)
  + Σ_{d=o_a}^{o_b+K−1} v_p(i + d) = eK + κ_p(m, K) + R_m(a) − R_{m+K}(b) + γ(Δ)`.

More general than the file: `e` is any natural number (the file has `e ≥ 1`), `p` is any prime
(oddness is not used), and `I` is any set with `I ⊆ [0, k)` whose digits are in `[1, p − 1]`. -/
theorem oddRul_P1 {k : ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) {dg : ℕ → ℕ}
    (hd : ∀ t ∈ I, 0 < dg t ∧ dg t < p) {dk : ℕ} (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1)
    {a b : Finset ℕ} (hba : b ⊆ a) (ha : a ⊆ I) (e i : ℕ) (hi : 1 ≤ i) :
    -(dk : ℤ) * (((p ^ k - 1) / (p - 1) : ℕ) : ℤ) +
        ∑ t ∈ a \ b, (1 + (dg t : ℤ) * (((p ^ t - 1) / (p - 1) : ℕ) : ℤ)) +
        Rulers.delta k (a \ b) + e * (((dk * p ^ k : ℕ) : ℤ) - oW p dg (a \ b)) +
        ∑ d ∈ Ico (oW p dg a) (oW p dg b + dk * p ^ k), (padicValNat p (i + d) : ℤ) =
      e * ((dk * p ^ k : ℕ) : ℤ) + kappaP p (i - 1) (dk * p ^ k) + rulerP p e k I dg (i - 1) a -
        rulerP p e k I dg (i - 1 + dk * p ^ k) b + Rulers.gamma k I (a \ b) := by
  have h2 := hp.out.two_le
  have hp1 : ((p : ℤ) - 1) ≠ 0 := by omega
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set K := dk * p ^ k with hK
  have hdA : ∀ t ∈ a, dg t < p := fun t ht => (hd t (ha ht)).2
  have hdB : ∀ t ∈ b, dg t < p := fun t ht => hdA t (hba ht)
  have hΔ : a \ b ⊆ I := fun t ht => ha (mem_sdiff.1 ht).1
  have hs := oW_sdiff p dg hba
  have hlt := oW_lt_pow h2 dg (a \ b) (fun t ht => hI t (hΔ ht)) (fun t ht => (hd t (hΔ ht)).2)
  have hpk : p ^ k ≤ K := by rw [hK]; exact Nat.le_mul_of_pos_left _ hdk1
  have hle : oW p dg a ≤ oW p dg b + K := by omega
  -- the facts
  have hV := legendre_sum_mul (p := p) m (oW p dg a) (oW p dg b + K) hle
  have hκ1 := kappaP_mul (p := p) m K
  have hκ2 := kappaP_mul (p := p) m (oW p dg a)
  have hκ3 := kappaP_mul (p := p) (m + K) (oW p dg b)
  have hsK : sP p K = dk := L3_sP_K k dk hdk
  rw [hsK] at hκ1
  rw [sP_oW h2 dg a hdA, Nat.cast_sum] at hκ2
  rw [sP_oW h2 dg b hdB, Nat.cast_sum, show m + K + oW p dg b = m + (oW p dg b + K) by ring] at hκ3
  have hNk := geomN_mul h2 k
  have hA := sum_geomN_mul h2 dg (a \ b)
  have hL4 := L4 hI hba ha
  have hsum : ∑ t ∈ a \ b, (dg t : ℤ) + ∑ t ∈ b, (dg t : ℤ) = ∑ t ∈ a, (dg t : ℤ) :=
    sum_sdiff hba
  have ho : (oW p dg (a \ b) : ℤ) + oW p dg b = oW p dg a := by exact_mod_cast hs
  have hKc : (K : ℤ) = dk * (p : ℤ) ^ k := by rw [hK]; push_cast; ring
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
  simp only [rulerP, sum_h_sub_oW]
  simp only [Nat.cast_add] at hV
  apply mul_left_cancel₀ hp1
  linear_combination (-(dk : ℤ)) * hNk + hA + ((p : ℤ) - 1) * hL4 + hV - hκ1 + hκ2 - hκ3 -
    ((p : ℤ) - 1) * e * ho - hsum + ho + hKc

/-- **(P1) The identity** (*Part P* of `CSI13_the_odd_cost_form.md`), case `i = 0`: for
`b ⊆ a ⊆ I` with `a ≠ ∅` and `Δ = a ∖ b` (here `v_p(i + d) = v_p(d)` with `d ≥ o_a ≥ 1`),
`−d_k(p^k − 1)/(p − 1) + Σ_{t ∈ Δ}(1 + d_t(p^t − 1)/(p − 1)) + δ(Δ) + e(K − o_Δ)
  + Σ_{d=o_a}^{o_b+K−1} v_p(d) = eK + R^♯(a) − R^♯(b) + γ(Δ)`.

More general than the file: `e` is any natural number, `p` is any prime, and `I` is any set with
`I ⊆ [0, k)` whose digits are in `[1, p − 1]`. -/
theorem P1_zero {k : ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) {dg : ℕ → ℕ}
    (hd : ∀ t ∈ I, 0 < dg t ∧ dg t < p) {dk : ℕ} (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1)
    {a b : Finset ℕ} (hba : b ⊆ a) (ha : a ⊆ I) (hne : a.Nonempty) (e : ℕ) :
    -(dk : ℤ) * (((p ^ k - 1) / (p - 1) : ℕ) : ℤ) +
        ∑ t ∈ a \ b, (1 + (dg t : ℤ) * (((p ^ t - 1) / (p - 1) : ℕ) : ℤ)) +
        Rulers.delta k (a \ b) + e * (((dk * p ^ k : ℕ) : ℤ) - oW p dg (a \ b)) +
        ∑ d ∈ Ico (oW p dg a) (oW p dg b + dk * p ^ k), (padicValNat p d : ℤ) =
      e * ((dk * p ^ k : ℕ) : ℤ) + rulerSharpP p e k I dg a - rulerSharpP p e k I dg b +
        Rulers.gamma k I (a \ b) := by
  have h2 := hp.out.two_le
  have hp1 : ((p : ℤ) - 1) ≠ 0 := by omega
  set K := dk * p ^ k with hK
  have hdA : ∀ t ∈ a, 0 < dg t ∧ dg t < p := fun t ht => hd t (ha ht)
  have hdB : ∀ t ∈ b, 0 < dg t ∧ dg t < p := fun t ht => hdA t (hba ht)
  have hΔ : a \ b ⊆ I := fun t ht => ha (mem_sdiff.1 ht).1
  have hs := oW_sdiff p dg hba
  have hlt := oW_lt_pow h2 dg (a \ b) (fun t ht => hI t (hΔ ht)) (fun t ht => (hd t (hΔ ht)).2)
  have hpk : p ^ k ≤ K := by rw [hK]; exact Nat.le_mul_of_pos_left _ hdk1
  have hle : oW p dg a ≤ oW p dg b + K := by omega
  have h1 : 1 ≤ oW p dg a := one_le_oW (p := p) hne (fun t ht => (hdA t ht).1) (by omega)
  -- the facts
  have hV := legendre_sum_neg_mul (p := p) (oW p dg a) (oW p dg b + K) h1 hle
  have hpk1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
  rw [show oW p dg b + K - 1 = K - 1 + oW p dg b by omega] at hV
  have ha1 := sP_oW_sub_one h2 hne hdA
  have hb1 := sP_K_sub_one_add h2 hdk1 (by omega) (fun t ht => hI t (ha (hba ht))) hdB
  rw [← hK] at hb1
  have ha1' : ((sP p (oW p dg a - 1) : ℕ) : ℤ) + 1 =
      ∑ t ∈ a, (dg t : ℤ) + ((p : ℤ) - 1) * a.min' hne := by
    have := congrArg (fun z : ℕ => (z : ℤ)) ha1
    push_cast [show 1 ≤ p by omega] at this
    linarith
  have hb1' : ((sP p (K - 1 + oW p dg b) : ℕ) : ℤ) + 1 =
      dk + ∑ t ∈ b, (dg t : ℤ) + ((p : ℤ) - 1) * Rulers.minOr k b := by
    have := congrArg (fun z : ℕ => (z : ℤ)) hb1
    push_cast [show 1 ≤ p by omega] at this
    linarith
  have hmin : Rulers.minOr k a = a.min' hne := by rw [Rulers.minOr, dif_pos hne]
  have hNk := geomN_mul h2 k
  have hA := sum_geomN_mul h2 dg (a \ b)
  have hL4 := L4 hI hba ha
  have hsum : ∑ t ∈ a \ b, (dg t : ℤ) + ∑ t ∈ b, (dg t : ℤ) = ∑ t ∈ a, (dg t : ℤ) :=
    sum_sdiff hba
  have ho : (oW p dg (a \ b) : ℤ) + oW p dg b = oW p dg a := by exact_mod_cast hs
  have hKc : (K : ℤ) = dk * (p : ℤ) ^ k := by rw [hK]; push_cast; ring
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, rulerSharpP_eq, rulerSharpP_eq, hmin]
  simp only [Nat.cast_add] at hV
  apply mul_left_cancel₀ hp1
  linear_combination (-(dk : ℤ)) * hNk + hA + ((p : ℤ) - 1) * hL4 + hV + ha1' - hb1' -
    ((p : ℤ) - 1) * e * ho - hsum + ho + hKc

end ColouredSand.OddTwist
