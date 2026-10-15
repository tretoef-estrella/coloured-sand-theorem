module

public import RequestProject.OddRulers.CostForm
public import RequestProject.OddWindows.All
public import RequestProject.OddDeficit.All

/-!
# `CSI13_the_odd_cost_form.md` — **(P2) the valuations of `Mp`** (*Part P*)

Namespace `ColouredSand.OddTwist`.  Here `p` is an odd prime (`[Fact p.Prime]`, `Odd p`), and the
data are CSI10's: the digits of `λ + 1` (`d_t = digitL p λ t`, `k = kTop p λ`,
`I = Iset p λ`, `d_k = digitL p λ k`), the matrix `Mp p λ i e` over `ℤ_[p]` indexed by
`slots p λ i e`, and CSI12's labels `labL p λ i e k : slots → Finset ℕ` (the subset `a ⊆ I` of a
slot; by CSI12's `slots_as_subsets` this is a bijection onto the subsets of `I`).  For slots `x`
(row) and `y` (column) with labels `a` and `b`, the entry `Mp_{ab}` is `Mp p λ i e x y`.

* `v_p(Mp_{ab})` is `PadicInt.valuation (Mp p λ i e x y) : ℕ`, cast to `ℤ`; the statements also
  assert `Mp_{ab} ≠ 0` (the valuation of `0` is `0` by convention, so the non-vanishing is part of
  the claim).
* `K = d_k p^k` is `digitL p λ k * p ^ k`, `m = i − 1` is `i - 1`.
* The rulers are `rulerP p e k I dg μ` (`R_μ`) and `rulerSharpP p e k I dg` (`R^♯`), the gold is
  C3's `Rulers.gamma k I`.

The proof follows the file: CSI12's (W2) `W2_Mp` writes the entry as
`[(c^{(k)})^{⋆ d_k}](a ∖ b) · ∏_{d=o_a}^{o_b+K−1} π_0(d)`, CSI12's (C1) `C1_lambda` together with
the rescaling `starPow_scale` and CSI11's (D1) `D1_lambda` give the valuation of the first factor,
and (P1) turns the sum of the valuations into the cost form.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Finset

lemma padicValRat_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ j ∈ s, f j ≠ 0) :
    ∏ j ∈ s, f j ≠ 0 ∧ padicValRat p (∏ j ∈ s, f j) = ∑ j ∈ s, padicValRat p (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => hf i (mem_insert_of_mem hi))
    have h0 := hf j (mem_insert_self j s)
    rw [prod_insert hj, sum_insert hj]
    exact ⟨mul_ne_zero h0 h1, by rw [padicValRat.mul h0 h1, h2]⟩

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
lemma Iset_lt {l t : ℕ} (ht : t ∈ Iset p l) : t < kTop p l := by
  simp only [Iset, mem_filter, mem_range] at ht; exact ht.1

lemma Iset_digit {l t : ℕ} (ht : t ∈ Iset p l) : 0 < digitL p l t ∧ digitL p l t < p :=
  ⟨Nat.pos_of_ne_zero ((mem_Iset_iff p l t (Iset_lt p ht)).1 ht), digitL_lt hp.out l t⟩

lemma digitL_top_bounds (l : ℕ) : 1 ≤ digitL p l (kTop p l) ∧ digitL p l (kTop p l) ≤ p - 1 :=
  ⟨Nat.one_le_iff_ne_zero.2 (digitL_top_ne_zero' p l),
    by have := digitL_lt hp.out l (kTop p l); omega⟩

/-- The deficit law of CSI11 in the form `v_p = δ(Δ)` (C3's `Rulers.delta`), including
`Δ = ∅`. -/
lemma D1_delta_lambda (hodd : Odd p) (l : ℕ) {Δ : Finset ℕ} (hΔ : Δ ⊆ Iset p l) :
    starPow (aP p (dsL p l) (kTop p l)) (digitL p l (kTop p l)) Δ ≠ 0 ∧
      (padicValInt p (starPow (aP p (dsL p l) (kTop p l)) (digitL p l (kTop p l)) Δ) : ℤ) =
        Rulers.delta (kTop p l) Δ := by
  obtain ⟨h0, h1⟩ := D1_lambda hp.out hodd l
  by_cases he : Δ = ∅
  · subst he; rw [h0]; simp [Rulers.delta]
  · have hne : Δ.Nonempty := nonempty_iff_ne_empty.2 he
    obtain ⟨hz, hv⟩ := h1 Δ hne hΔ
    refine ⟨hz, ?_⟩
    rw [hv, Rulers.delta, if_neg he, Rulers.minOr, dif_pos hne]
    have hsub : Δ ⊆ Ico (Δ.min' hne) (kTop p l) := by
      intro t ht
      exact mem_Ico.2 ⟨min'_le _ _ ht, Iset_lt p (hΔ ht)⟩
    have hc := card_le_card hsub
    rw [Nat.card_Ico] at hc
    have := Iset_lt p (hΔ (min'_mem Δ hne))
    omega

/-- The valuation of `[(c^{(k)})^{⋆ d_k}](Δ)` for `Δ ⊆ I`:
`−d_k (p^k − 1)/(p − 1) + Σ_{t ∈ Δ}(1 + d_t (p^t − 1)/(p − 1)) + δ(Δ)` (and it is non-zero). -/
lemma val_starPow_cW (hodd : Odd p) (l : ℕ) {Δ : Finset ℕ} (hΔ : Δ ⊆ Iset p l) :
    starPow (cW p (Iset p l) (digitL p l) (kTop p l)) (digitL p l (kTop p l)) Δ ≠ 0 ∧
      padicValRat p
          (starPow (cW p (Iset p l) (digitL p l) (kTop p l)) (digitL p l (kTop p l)) Δ) =
        -(digitL p l (kTop p l) : ℤ) * (((p ^ kTop p l - 1) / (p - 1) : ℕ) : ℤ) +
          ∑ t ∈ Δ, (1 + (digitL p l t : ℤ) * (((p ^ t - 1) / (p - 1) : ℕ) : ℤ)) +
          Rulers.delta (kTop p l) Δ := by
  have h2 := hp.out.two_le
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set k := kTop p l
  set dk := digitL p l k
  set N := (p ^ k - 1) / (p - 1)
  set y : ℕ → ℚ := fun t => -(bW p (digitL p l) t) *
    (-(p : ℚ)) ^ (1 + digitL p l t * ((p ^ t - 1) / (p - 1))) with hy
  have hc : cW p (Iset p l) (digitL p l) k =
      fun Γ => (-1 / (p : ℚ)) ^ N * (aP p (dsL p l) k Γ : ℚ) * ∏ t ∈ Γ, y t :=
    funext (C1_lambda hp.out l k)
  rw [hc, starPow_scale, ← cast_starPow_int]
  obtain ⟨hz, hzv⟩ := D1_delta_lambda p hodd l hΔ
  set z := starPow (aP p (dsL p l) k) dk Δ
  have hlam0 : (-1 / (p : ℚ)) ≠ 0 := by simp [hp0]
  have hlam : padicValRat p (-1 / (p : ℚ)) = -1 := by
    rw [neg_div, padicValRat.neg, one_div, padicValRat.inv, padicValRat.self hp.out.one_lt]
  have hb0 : ∀ t, bW p (digitL p l) t ≠ 0 := fun t => by simp [bW]
  have hbv : ∀ t, padicValRat p (bW p (digitL p l) t) = 0 := fun t => by
    rw [bW, padicValRat.pow (by norm_num), padicValRat.neg, padicValRat.one, mul_zero]
  have hy0 : ∀ t ∈ Δ, y t ≠ 0 := fun t _ => by
    simp only [hy]; exact mul_ne_zero (neg_ne_zero.2 (hb0 t)) (pow_ne_zero _ (by simp [hp0]))
  have hyv : ∀ t ∈ Δ, padicValRat p (y t) =
      1 + (digitL p l t : ℤ) * (((p ^ t - 1) / (p - 1) : ℕ) : ℤ) := fun t _ => by
    simp only [hy]
    rw [padicValRat.mul (neg_ne_zero.2 (hb0 t)) (pow_ne_zero _ (by simp [hp0])),
      padicValRat.neg, hbv, padicValRat.pow (by simp [hp0]), padicValRat.neg,
      padicValRat.self hp.out.one_lt]
    push_cast; ring
  obtain ⟨hP0, hPv⟩ := padicValRat_prod (p := p) Δ y hy0
  have hz0 : (z : ℚ) ≠ 0 := by exact_mod_cast hz
  have hl0 : ((-1 / (p : ℚ)) ^ N) ^ dk ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hlam0)
  refine ⟨mul_ne_zero (mul_ne_zero hl0 hz0) hP0, ?_⟩
  rw [padicValRat.mul (mul_ne_zero hl0 hz0) hP0, padicValRat.mul hl0 hz0,
    padicValRat.pow (pow_ne_zero _ hlam0), padicValRat.pow hlam0, hlam, padicValRat.of_int, hzv,
    hPv, sum_congr rfl hyv]
  ring

/-- The valuation of the product of the window: for `b ⊆ a ⊆ I` and `i + d ≠ 0` on the window,
`∏_{d=o_a}^{o_b+K−1} π_0(d) ≠ 0` with valuation `e(K − o_{a∖b}) + Σ_{d=o_a}^{o_b+K−1} v_p(i + d)`. -/
lemma val_window (l e i : ℕ) {a b : Finset ℕ} (hba : b ⊆ a) (ha : a ⊆ Iset p l)
    (hpos : ∀ d ∈ Ico (oW p (digitL p l) a)
      (oW p (digitL p l) b + digitL p l (kTop p l) * p ^ kTop p l), i + d ≠ 0) :
    ∏ d ∈ Icc (oW p (digitL p l) a)
        (oW p (digitL p l) b + digitL p l (kTop p l) * p ^ kTop p l - 1), piW p e i d ≠ 0 ∧
      padicValRat p (∏ d ∈ Icc (oW p (digitL p l) a)
        (oW p (digitL p l) b + digitL p l (kTop p l) * p ^ kTop p l - 1), piW p e i d) =
        e * (((digitL p l (kTop p l) * p ^ kTop p l : ℕ) : ℤ) - oW p (digitL p l) (a \ b)) +
          ∑ d ∈ Ico (oW p (digitL p l) a)
            (oW p (digitL p l) b + digitL p l (kTop p l) * p ^ kTop p l),
            (padicValNat p (i + d) : ℤ) := by
  have h2 := hp.out.two_le
  obtain ⟨hdk1, _⟩ := digitL_top_bounds p l
  set dg := digitL p l
  set k := kTop p l
  set K := dg k * p ^ k with hK
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hpkK : p ^ k ≤ K := Nat.le_mul_of_pos_left _ hdk1
  have hΔ : a \ b ⊆ Iset p l := fun t ht => ha (mem_sdiff.1 ht).1
  have hlt := oW_lt_pow (n := k) h2 dg (a \ b) (fun t ht => Iset_lt p (hΔ ht))
    (fun t ht => (Iset_digit p (hΔ ht)).2)
  have hs := oW_sdiff p dg hba
  have hle : oW p dg a ≤ oW p dg b + K := by omega
  have hIcc : Icc (oW p dg a) (oW p dg b + K - 1) = Ico (oW p dg a) (oW p dg b + K) := by
    ext d; simp only [mem_Icc, mem_Ico]; omega
  rw [hIcc]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpi : ∀ d ∈ Ico (oW p dg a) (oW p dg b + K), piW p e i d = (p : ℚ) ^ e * ((i + d : ℕ) : ℚ) :=
    fun d _ => by simp [piW]
  have hpi0 : ∀ d ∈ Ico (oW p dg a) (oW p dg b + K), piW p e i d ≠ 0 := fun d hd => by
    rw [hpi d hd]; exact mul_ne_zero (pow_ne_zero _ hp0) (by exact_mod_cast hpos d hd)
  have hpiv : ∀ d ∈ Ico (oW p dg a) (oW p dg b + K),
      padicValRat p (piW p e i d) = (e : ℤ) + (padicValNat p (i + d) : ℤ) := fun d hd => by
    rw [hpi d hd, padicValRat.mul (pow_ne_zero _ hp0) (by exact_mod_cast hpos d hd),
      padicValRat.pow hp0, padicValRat.self hp.out.one_lt, padicValRat.of_nat]
    ring
  obtain ⟨h0, hv⟩ := padicValRat_prod (p := p) _ _ hpi0
  refine ⟨h0, ?_⟩
  rw [hv, sum_congr rfl hpiv, sum_add_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul]
  push_cast [hle]
  have : ((oW p dg (a \ b) : ℕ) : ℤ) + oW p dg b = oW p dg a := by exact_mod_cast hs
  linear_combination (e : ℤ) * this

/-- The entry `Mp_{ab}` for `b ⊆ a`, as a rational number (CSI12's (W2)), is non-zero with
valuation the left-hand side of (P1), provided `i + d ≠ 0` on the window. -/
lemma val_entry (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (x y : slots p l i e)
    (hba : labL p l i e (kTop p l) y ⊆ labL p l i e (kTop p l) x)
    (hpos : ∀ d ∈ Ico (oW p (digitL p l) (labL p l i e (kTop p l) x))
      (oW p (digitL p l) (labL p l i e (kTop p l) y) + digitL p l (kTop p l) * p ^ kTop p l),
        i + d ≠ 0) :
    Mp p l i e x y ≠ 0 ∧
      ((Mp p l i e x y).valuation : ℤ) =
        -(digitL p l (kTop p l) : ℤ) * (((p ^ kTop p l - 1) / (p - 1) : ℕ) : ℤ) +
          ∑ t ∈ labL p l i e (kTop p l) x \ labL p l i e (kTop p l) y,
            (1 + (digitL p l t : ℤ) * (((p ^ t - 1) / (p - 1) : ℕ) : ℤ)) +
          Rulers.delta (kTop p l) (labL p l i e (kTop p l) x \ labL p l i e (kTop p l) y) +
          e * (((digitL p l (kTop p l) * p ^ kTop p l : ℕ) : ℤ) -
            oW p (digitL p l) (labL p l i e (kTop p l) x \ labL p l i e (kTop p l) y)) +
          ∑ d ∈ Ico (oW p (digitL p l) (labL p l i e (kTop p l) x))
            (oW p (digitL p l) (labL p l i e (kTop p l) y) +
              digitL p l (kTop p l) * p ^ kTop p l), (padicValNat p (i + d) : ℤ) := by
  have hW := W2_Mp p l i e he x y
  rw [if_pos hba] at hW
  set a := labL p l i e (kTop p l) x
  set b := labL p l i e (kTop p l) y
  have ha : a ⊆ Iset p l := by
    have := (slots_as_subsets p l i e (kTop p l) le_rfl).sub x
    intro t ht; exact (mem_filter.1 (this ht)).1
  have hΔ : a \ b ⊆ Iset p l := fun t ht => ha (mem_sdiff.1 ht).1
  obtain ⟨hs0, hsv⟩ := val_starPow_cW p hodd l hΔ
  obtain ⟨hw0, hwv⟩ := val_window p l e i hba ha hpos
  set q := starPow (cW p (Iset p l) (digitL p l) (kTop p l)) (digitL p l (kTop p l)) (a \ b) *
    ∏ d ∈ Icc (oW p (digitL p l) a)
      (oW p (digitL p l) b + digitL p l (kTop p l) * p ^ kTop p l - 1), piW p e i d with hq
  have hq0 : q ≠ 0 := mul_ne_zero hs0 hw0
  have hM0 : Mp p l i e x y ≠ 0 := by
    intro h
    rw [h] at hW
    have : ((q : ℚ) : ℚ_[p]) = 0 := by rw [← hW]; simp
    exact hq0 (by exact_mod_cast this)
  refine ⟨hM0, ?_⟩
  have hv : ((Mp p l i e x y).valuation : ℤ) = padicValRat p q := by
    rw [← PadicInt.valuation_coe, hW, Padic.valuation_ratCast]
  rw [hv, hq, padicValRat.mul hs0 hw0, hsv, hwv]
  ring

/-- **(P2) Support** (*Part P* of `CSI13_the_odd_cost_form.md`): `Mp_{ab} = 0` unless `b ⊆ a`
(for every `i`). -/
theorem P2_support (l i e : ℕ) (he : 1 ≤ e) (x y : slots p l i e)
    (hba : ¬ labL p l i e (kTop p l) y ⊆ labL p l i e (kTop p l) x) :
    Mp p l i e x y = 0 := by
  have hW := W2_Mp p l i e he x y
  rw [if_neg hba] at hW
  exact PadicInt.coe_eq_zero.1 (by rw [hW]; simp)

/-- **(P2) The valuations of `Mp`**, case `i ≥ 1` (*Part P* of `CSI13_the_odd_cost_form.md`):
for slots with labels `b ⊆ a`, `Mp_{ab} ≠ 0` and
`v_p(Mp_{ab}) = eK + κ_p(m, K) + R_m(a) − R_{m+K}(b) + γ(a ∖ b)`, with `m = i − 1`,
`K = d_k p^k`.  (With `P2_support`, `Mp_{ab} = 0` when `b ⊄ a`.) -/
theorem P2_pos (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) (x y : slots p l i e)
    (hba : labL p l i e (kTop p l) y ⊆ labL p l i e (kTop p l) x) :
    Mp p l i e x y ≠ 0 ∧
      ((Mp p l i e x y).valuation : ℤ) =
        e * ((digitL p l (kTop p l) * p ^ kTop p l : ℕ) : ℤ) +
          kappaP p (i - 1) (digitL p l (kTop p l) * p ^ kTop p l) +
          rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1) (labL p l i e (kTop p l) x) -
          rulerP p e (kTop p l) (Iset p l) (digitL p l)
            (i - 1 + digitL p l (kTop p l) * p ^ kTop p l) (labL p l i e (kTop p l) y) +
          Rulers.gamma (kTop p l) (Iset p l)
            (labL p l i e (kTop p l) x \ labL p l i e (kTop p l) y) := by
  obtain ⟨h0, hv⟩ := val_entry p hodd l i e he x y hba (fun d _ => by omega)
  refine ⟨h0, ?_⟩
  have ha : labL p l i e (kTop p l) x ⊆ Iset p l := by
    have := (slots_as_subsets p l i e (kTop p l) le_rfl).sub x
    intro t ht; exact (mem_filter.1 (this ht)).1
  obtain ⟨hdk1, hdk⟩ := digitL_top_bounds p l
  rw [hv]
  exact oddRul_P1 (fun t ht => Iset_lt p ht) (fun t ht => Iset_digit p ht) hdk1 hdk hba ha e i hi

/-- **(P2) The zero row**, case `i = 0` (*Part P* of `CSI13_the_odd_cost_form.md`): the row of
the slot with label `∅` is zero. -/
theorem P2_zero_row (l e : ℕ) (he : 1 ≤ e) (x y : slots p l 0 e)
    (hx : labL p l 0 e (kTop p l) x = ∅) : Mp p l 0 e x y = 0 := by
  by_cases hba : labL p l 0 e (kTop p l) y ⊆ labL p l 0 e (kTop p l) x
  · have hW := W2_Mp p l 0 e he x y
    rw [if_pos hba] at hW
    have hK1 : 1 ≤ digitL p l (kTop p l) * p ^ kTop p l :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (digitL_top_ne_zero' p l)
        (pow_ne_zero _ hp.out.ne_zero))
    have hmem : 0 ∈ Icc (oW p (digitL p l) (labL p l 0 e (kTop p l) x))
        (oW p (digitL p l) (labL p l 0 e (kTop p l) y) +
          digitL p l (kTop p l) * p ^ kTop p l - 1) := by
      rw [hx]; simp [oW]
    rw [prod_eq_zero hmem (by simp [piW]), mul_zero] at hW
    exact PadicInt.coe_eq_zero.1 (by rw [hW]; simp)
  · exact P2_support p l 0 e he x y hba

/-- **(P2) The valuations of `Mp`**, case `i = 0` (*Part P* of `CSI13_the_odd_cost_form.md`): for
slots with labels `b ⊆ a` and `a ≠ ∅`, `Mp_{ab} ≠ 0` and
`v_p(Mp_{ab}) = eK + R^♯(a) − R^♯(b) + γ(a ∖ b)`, with `K = d_k p^k`.  (With `P2_support` and
`P2_zero_row`, the other entries vanish.) -/
theorem P2_zero (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (x y : slots p l 0 e)
    (hx : labL p l 0 e (kTop p l) x ≠ ∅)
    (hba : labL p l 0 e (kTop p l) y ⊆ labL p l 0 e (kTop p l) x) :
    Mp p l 0 e x y ≠ 0 ∧
      ((Mp p l 0 e x y).valuation : ℤ) =
        e * ((digitL p l (kTop p l) * p ^ kTop p l : ℕ) : ℤ) +
          rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (labL p l 0 e (kTop p l) x) -
          rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (labL p l 0 e (kTop p l) y) +
          Rulers.gamma (kTop p l) (Iset p l)
            (labL p l 0 e (kTop p l) x \ labL p l 0 e (kTop p l) y) := by
  have ha : labL p l 0 e (kTop p l) x ⊆ Iset p l := by
    have := (slots_as_subsets p l 0 e (kTop p l) le_rfl).sub x
    intro t ht; exact (mem_filter.1 (this ht)).1
  have hne : (labL p l 0 e (kTop p l) x).Nonempty := nonempty_iff_ne_empty.2 hx
  have h1 : 1 ≤ oW p (digitL p l) (labL p l 0 e (kTop p l) x) :=
    one_le_oW (p := p) hne (fun t ht => (Iset_digit p (ha ht)).1) hp.out.one_lt.le
  obtain ⟨h0, hv⟩ := val_entry p hodd l 0 e he x y hba (fun d hd => by
    have := (mem_Ico.1 hd).1; omega)
  refine ⟨h0, ?_⟩
  obtain ⟨hdk1, hdk⟩ := digitL_top_bounds p l
  rw [hv]
  simp only [zero_add]
  exact P1_zero (fun t ht => Iset_lt p ht) (fun t ht => Iset_digit p ht) hdk1 hdk hba ha hne e

end ColouredSand.OddTwist
