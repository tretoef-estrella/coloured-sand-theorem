module

public import RequestProject.OddCellFloor.Basic

/-!
# Part A of `CSI17_integrality_and_cell_floor_at_p.md`: Lemma 7.9_p (integrality)

Namespace `ColouredSand.OddTwist`; encodings as in `RequestProject/OddCellFloor/Basic.lean`.
The proofs are those of C9 (`RequestProject/CellFloor/Integrality.lean`) with the base-`p`
statements of CSI16 (Theorem F0_p (W3), Theorem F1_p (Cut), `JHseqP_mono`, `oddF_J0`) in place of
the binary ones; C9's general facts `CellFloor.ifit_eq_of_fit_eq_int`, `CellFloor.fit_one` are
reused.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset AntitonicFit TheoremF

variable {p : ℕ} [hp : Fact p.Prime] {dg : ℕ → ℕ}

/-- Statement (I1) of Lemma 7.9_p (`CSI17_integrality_and_cell_floor_at_p.md`, Part A) for one
house, as used in the induction on `|I|`. -/
def oddCellI1Prop (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) : Prop :=
  ∀ q < 2 ^ #I, fit (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) q = (yhatP p k I dg ℓ e q : ℝ)

/-- (I1) by induction on `|I|` (proof of Lemma 7.9_p (I1), `CSI17_integrality_and_cell_floor_at_p.md`
Part A): base `I = ∅` (`N = 1`), step by (W3) of Theorem F0_p (CSI16) and the induction
hypothesis for `H' = (I ∖ {c}, c, ℓ mod p^c, e, d)`. -/
lemma oddCell_I1_all : ∀ (n : ℕ) (I : Finset ℕ) (k ℓ : ℕ) (e : ℤ), #I = n → (∀ t ∈ I, t < k) →
    (∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) → ℓ < p ^ k → 1 ≤ e → oddCellI1Prop p k I dg ℓ e := by
  intro n
  induction n with
  | zero =>
    intro I k ℓ e hn _ _ _ _
    have hfit : ∀ j < 2 ^ #I,
        fit (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) j = (xHseqP p k I dg ℓ e j : ℝ) := by
      intro j hj
      rw [hn, pow_zero] at hj ⊢
      obtain rfl : j = 0 := by omega
      exact CellFloor.fit_one _
    intro q hq
    rw [yhatP, CellFloor.ifit_eq_of_fit_eq_int hfit q hq, hfit q hq]
  | succ n ih =>
    intro I k ℓ e hn hI hd hℓ he
    have hne : I.Nonempty := card_pos.1 (by omega)
    set c := I.max' hne with hc
    have hcI : c ∈ I := I.max'_mem hne
    have hI' : ∀ t ∈ I.erase c, t < c := fun t ht =>
      lt_of_le_of_ne (I.le_max' t (mem_of_mem_erase ht)) (ne_of_mem_erase ht)
    have hcard : #(I.erase c) = n := by rw [card_erase_of_mem hcI]; omega
    have ih' := ih (I.erase c) c (ℓ % p ^ c) e hcard hI' (hd_erase hd c)
      (Nat.mod_lt _ (pow_pos hp.out.pos c)) he
    have hW3 := oddF_W3 hI hd hℓ he hne hc
    have hN := card_erase_max hne hc
    intro q hq
    rw [hW3.1 q hq, yhatP, hW3.2 q hq]
    simp only [concat, mirror, Pi.add_apply]
    split_ifs with hqM
    · rw [ih' q hqM]
      simp [toR, yhatP]
    · rw [ih' _ (by omega)]
      simp [toR, yhatP]

/-- **Lemma 7.9_p (I1)** of `CSI17_integrality_and_cell_floor_at_p.md` (Part A): for every
base-`p` house `H` and every `q < N`, `fit_N(x_H)(q) = ŷ_H(q)` (as reals) — so the real fit is
integral — and `ŷ_H` is non-increasing on `[0, N)`. -/
theorem oddCell_lemma_7_9_I1 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    (∀ q < 2 ^ #I, fit (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) q = (yhatP p k I dg ℓ e q : ℝ)) ∧
      SmithBounds.NonIncrOn (2 ^ #I) (yhatP p k I dg ℓ e) := by
  have h := oddCell_I1_all _ I k ℓ e rfl hI hd hℓ he
  refine ⟨h, fun j hj => ?_⟩
  have := fit_nonIncr (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) j hj
  rw [h j (by omega), h (j + 1) hj] at this
  exact_mod_cast this

/-- The shift `δ(q) := −P_r J_H(q) + P_c J_H(N − 1 − q)` of the proof of Lemma 7.9_p (I2)
(`CSI17_integrality_and_cell_floor_at_p.md`, Part A). -/
def oddCellShift (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (Pr Pc : ℕ) : ℕ → ℤ := fun q =>
  -((Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ)) + (Pc : ℤ) * (JHseqP p k I dg ℓ (2 ^ #I - 1 - q) : ℤ)

omit hp in
/-- The cell clocks are `x_H + δ` (proof of Lemma 7.9_p (I2)). -/
lemma oddCellClock_eq (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (Pr Pc : ℕ) :
    oddCellClock p k I dg ℓ e Pr Pc = xHseqP p k I dg ℓ e + oddCellShift p k I dg ℓ Pr Pc := by
  funext q; simp only [oddCellClock, oddCellShift, Pi.add_apply]; ring

/-- `δ` is non-increasing on `[0, N)` (`J_H` is non-decreasing, CSI16); proof of Lemma 7.9_p (I2). -/
lemma oddCellShift_nonIncr {I : Finset ℕ} {k ℓ : ℕ} (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (Pr Pc : ℕ) : NonIncr (2 ^ #I) (toR (oddCellShift p k I dg ℓ Pr Pc)) := by
  intro j hj
  show ((oddCellShift p k I dg ℓ Pr Pc (j + 1) : ℤ) : ℝ) ≤ (oddCellShift p k I dg ℓ Pr Pc j : ℝ)
  have h2p := oddHou_two_le_p (p := p)
  have h1 : (JHseqP p k I dg ℓ j : ℤ) ≤ JHseqP p k I dg ℓ (j + 1) := by
    exact_mod_cast JHseqP_mono h2p hd (by omega) hj
  have h2 : (JHseqP p k I dg ℓ (2 ^ #I - 1 - (j + 1)) : ℤ) ≤ JHseqP p k I dg ℓ (2 ^ #I - 1 - j) := by
    exact_mod_cast JHseqP_mono h2p hd (by omega) (by omega)
  have h3 := mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ Pr by positivity)
  have h4 := mul_le_mul_of_nonneg_left h2 (show (0 : ℤ) ≤ Pc by positivity)
  have : oddCellShift p k I dg ℓ Pr Pc (j + 1) ≤ oddCellShift p k I dg ℓ Pr Pc j := by
    simp only [oddCellShift]; linarith
  exact_mod_cast this

/-- If `J_H` jumps between `b − 1` and `b`, then `b` is the first position with `J_H(b) = 1`
(proof of Lemma 7.9_p (I2)). -/
lemma oddCell_J_jump {I : Finset ℕ} {k ℓ b : ℕ} (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hb0 : 0 < b) (hbN : b < 2 ^ #I)
    (hne : JHseqP p k I dg ℓ (b - 1) ≠ JHseqP p k I dg ℓ b) :
    JHseqP p k I dg ℓ b = 1 ∧ ∀ q < b, JHseqP p k I dg ℓ q = 0 := by
  have h2p := oddHou_two_le_p (p := p)
  have h1 := JHseqP_mono (k := k) (ℓ := ℓ) h2p hd (show b - 1 ≤ b by omega) hbN
  have h2 := JHseqP_le_one p k I dg ℓ b
  refine ⟨by omega, fun q hq => ?_⟩
  have := JHseqP_mono (k := k) (ℓ := ℓ) h2p hd (show q ≤ b - 1 by omega) (by omega)
  omega

/-- Every position where `δ` changes is a strict cut of `x_H` (Theorem F1_p (Cut), CSI16); proof
of Lemma 7.9_p (I2). -/
lemma oddCellShift_change_strictCut {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (Pr Pc : ℕ) :
    ∀ b, 0 < b → b < 2 ^ #I →
      oddCellShift p k I dg ℓ Pr Pc (b - 1) ≠ oddCellShift p k I dg ℓ Pr Pc b →
      IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) b := by
  intro b hb0 hbN hne
  have hcut := oddF_F1_Cut hI hd hℓ he
  by_cases hA : JHseqP p k I dg ℓ (b - 1) = JHseqP p k I dg ℓ b
  · have hB : JHseqP p k I dg ℓ (2 ^ #I - 1 - b) ≠ JHseqP p k I dg ℓ (2 ^ #I - b) := by
      intro hB
      apply hne
      simp only [oddCellShift]
      rw [hA, show 2 ^ #I - 1 - (b - 1) = 2 ^ #I - b by omega, ← hB]
    have hB' : JHseqP p k I dg ℓ (2 ^ #I - b - 1) ≠ JHseqP p k I dg ℓ (2 ^ #I - b) := by
      rwa [show 2 ^ #I - b - 1 = 2 ^ #I - 1 - b by omega]
    obtain ⟨h1, h2⟩ := oddCell_J_jump hd (by omega) (by omega) hB'
    have := (hcut (2 ^ #I - b) (by omega) h1 h2).2
    rwa [show 2 ^ #I - (2 ^ #I - b) = b by omega] at this
  · obtain ⟨h1, h2⟩ := oddCell_J_jump hd hb0 hbN hA
    exact (hcut b hbN h1 h2).1

/-- **Lemma 7.9_p (I2)** of `CSI17_integrality_and_cell_floor_at_p.md` (Part A): for every base-`p`
house `H` and all `P_r, P_c ∈ ℕ` (no relation between them assumed), with `z` the cell clocks: for
every `q < N`, `ifit_N(z)(q) = ŷ_H(q) − P_r J_H(q) + P_c J_H(N − 1 − q)` and
`fit_N(z)(q) = ifit_N(z)(q)` (as reals); and `ifit_N(z)` is non-increasing on `[0, N)`. -/
theorem oddCell_lemma_7_9_I2 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (Pr Pc : ℕ) :
    (∀ q < 2 ^ #I, ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) q =
      yhatP p k I dg ℓ e q - (Pr : ℤ) * (JHseqP p k I dg ℓ q : ℤ) +
        (Pc : ℤ) * (JHseqP p k I dg ℓ (2 ^ #I - 1 - q) : ℤ)) ∧
    (∀ q < 2 ^ #I, fit (2 ^ #I) (toR (oddCellClock p k I dg ℓ e Pr Pc)) q =
      (ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc) q : ℝ)) ∧
    SmithBounds.NonIncrOn (2 ^ #I) (ifit (2 ^ #I) (oddCellClock p k I dg ℓ e Pr Pc)) := by
  have hz := oddCellClock_eq p k I dg ℓ e Pr Pc
  have hδn := oddCellShift_nonIncr (k := k) (ℓ := ℓ) hd Pr Pc
  have hch := oddCellShift_change_strictCut hI hd hℓ he Pr Pc
  have hI1 := (oddCell_lemma_7_9_I1 hI hd hℓ he).1
  set N := 2 ^ #I with hN
  set x := xHseqP p k I dg ℓ e
  set δ := oddCellShift p k I dg ℓ Pr Pc with hδ
  have hifit : ∀ q < N, ifit N (oddCellClock p k I dg ℓ e Pr Pc) q = yhatP p k I dg ℓ e q + δ q := by
    intro q hq
    rw [hz, (lemma_7_2_b3_b2 hδn hch).2.2 q hq]
    rfl
  set B := (range N).filter (fun b => 0 < b ∧ δ (b - 1) ≠ δ b) with hB
  have hBcut : ∀ b ∈ B, IsCut N (toR x) b := by
    intro b hb
    simp only [hB, mem_filter, mem_range] at hb
    exact (hch b hb.2.1 hb.1 hb.2.2).1
  have hδc : ∀ j, j + 1 < N → j + 1 ∉ B → toR δ (j + 1) = toR δ j := by
    intro j hj hjB
    by_contra hne
    apply hjB
    simp only [hB, mem_filter, mem_range, Nat.add_sub_cancel]
    refine ⟨hj, by omega, fun h => hne ?_⟩
    simp [toR, h]
  have hfit := (lemma_7_2_b1 hBcut hδn hδc).1
  have hfitz : ∀ q < N, fit N (toR (oddCellClock p k I dg ℓ e Pr Pc)) q =
      (ifit N (oddCellClock p k I dg ℓ e Pr Pc) q : ℝ) := by
    intro q hq
    rw [hifit q hq, hz, toR_add, hfit q hq, hI1 q hq]
    simp [toR]
  refine ⟨fun q hq => ?_, hfitz, fun j hj => ?_⟩
  · rw [hifit q hq]; simp only [hδ, oddCellShift]; ring
  · have := fit_nonIncr N (toR (oddCellClock p k I dg ℓ e Pr Pc)) j hj
    rw [hfitz j (by omega), hfitz (j + 1) hj] at this
    exact_mod_cast this

omit hp in
/-- `⌊(p^k − 1)/p^t⌋ mod p = p − 1` for `t < k`: every digit of `p^k − 1` below `k` is `p − 1`
(proof of Lemma 7.9_p (I3)). -/
lemma oddCell_digit_pow_sub_one (h1 : 1 ≤ p) {k t : ℕ} (htk : t < k) :
    (p ^ k - 1) / p ^ t % p = p - 1 := by
  have hpt : 0 < p ^ t := pow_pos (by omega) t
  have hm : 0 < p ^ (k - t - 1) := pow_pos (by omega) _
  have hk : p ^ k = p ^ (k - t - 1) * p * p ^ t := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have hpm : 1 ≤ p ^ (k - t - 1) * p := Nat.mul_pos hm (by omega)
  have hdiv : (p ^ k - 1) / p ^ t = p ^ (k - t - 1) * p - 1 := by
    rw [hk]
    have : p ^ (k - t - 1) * p * p ^ t - 1 = (p ^ t - 1) + (p ^ (k - t - 1) * p - 1) * p ^ t := by
      have h3 : 1 ≤ p ^ (k - t - 1) * p * p ^ t := Nat.mul_pos hpm hpt
      zify [h3, hpm, hpt]; ring
    rw [this, Nat.add_mul_div_right _ _ hpt, Nat.div_eq_of_lt (by omega), zero_add]
  rw [hdiv]
  have : p ^ (k - t - 1) * p - 1 = (p - 1) + (p ^ (k - t - 1) - 1) * p := by
    zify [hpm, hm, h1]; ring
  rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-- `o_D ≥ 1` for a non-empty `D ⊆ I` (digits `≥ 1`); proof of Lemma 7.9_p (I3). -/
lemma oddCell_oW_pos {I D : Finset ℕ} (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hD : D ⊆ I)
    (hne : D.Nonempty) : 1 ≤ oW p dg D := by
  obtain ⟨t, ht⟩ := hne
  have h1 : 1 ≤ dg t * p ^ t := Nat.mul_pos (hd t (hD ht)).1 (pow_pos hp.out.pos t)
  exact h1.trans (single_le_sum (f := fun t => dg t * p ^ t) (fun _ _ => Nat.zero_le _) ht)

/-- **Lemma 7.9_p (I3)** of `CSI17_integrality_and_cell_floor_at_p.md` (Part A): for a base-`p`
house with `ℓ = p^k − 1` and `I ≠ ∅`:
* every `t ∈ I` has type OR, i.e. `θ_t = 1`;
* `J_H(q) = [q ≠ 0]` for `q < N`;
* `x_H` has a strict cut at `1`;
* `x^♯(j) := x_H(j + 1)` (length `N − 1`) has `fit_{N−1}(x^♯)(j) = fit_N(x_H)(j + 1)` and
  `ifit_{N−1}(x^♯)(j) = ŷ_H(j + 1)` for `j < N − 1`, and these are integers
  (`fit_{N−1}(x^♯)(j) = ŷ_H(j + 1)` as reals).
(The house condition `ℓ < p^k` follows from `ℓ = p^k − 1`.) -/
theorem oddCell_lemma_7_9_I3 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ' : ℓ = p ^ k - 1) (he : 1 ≤ e)
    (hne : I.Nonempty) :
    (∀ t ∈ I, typP p dg ℓ t = .OR ∧ thetaP p ℓ t = 1) ∧
    (∀ q < 2 ^ #I, JHseqP p k I dg ℓ q = if q ≠ 0 then 1 else 0) ∧
    IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) 1 ∧
    (∀ j < 2 ^ #I - 1, fit (2 ^ #I - 1) (toR (oddCellXSharp p k I dg ℓ e)) j =
      fit (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) (j + 1)) ∧
    (∀ j < 2 ^ #I - 1, ifit (2 ^ #I - 1) (oddCellXSharp p k I dg ℓ e) j =
      yhatP p k I dg ℓ e (j + 1)) ∧
    (∀ j < 2 ^ #I - 1, fit (2 ^ #I - 1) (toR (oddCellXSharp p k I dg ℓ e)) j =
      (yhatP p k I dg ℓ e (j + 1) : ℝ)) := by
  have hk : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.out.pos
  have hℓ : ℓ < p ^ k := by omega
  have h1N : 1 < 2 ^ #I := Nat.one_lt_two_pow (card_pos.2 hne).ne'
  have htyp : ∀ t ∈ I, typP p dg ℓ t = .OR ∧ thetaP p ℓ t = 1 := by
    intro t ht
    have h : typP p dg ℓ t = .OR := by
      rw [typP_OR_iff_digit, hℓ']
      exact oddCell_digit_pow_sub_one hp.out.one_lt.le (hI t ht)
    exact ⟨h, (typP_OR_iff t).1 h⟩
  have hJ : ∀ q < 2 ^ #I, JHseqP p k I dg ℓ q = if q ≠ 0 then 1 else 0 := by
    intro q hq
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rw [oddF_J0 I hℓ]; simp
    · have hDne : (dancer I q).Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro h
        have := CellFloor.dancer_inj hq (by omega : 0 < 2 ^ #I) (h.trans (dancer_zero (I := I)).symm)
        omega
      have := oddCell_oW_pos hd (lemma_0a I q) hDne
      simp only [JHseqP, JHP]
      rw [if_pos (by omega), if_pos (by omega)]
  have hcut : IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) 1 :=
    (oddF_F1_Cut hI hd hℓ he 1 h1N (by rw [hJ 1 h1N]; simp)
      (fun q hq => by rw [hJ q (by omega)]; simp; omega)).1
  have hres : ∀ j < 2 ^ #I - 1, fit (2 ^ #I - 1) (toR (oddCellXSharp p k I dg ℓ e)) j =
      fit (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) (j + 1) := by
    intro j hj
    rw [hcut.1.2.2 (j + 1) (by omega)]
    simp only [concat, if_neg (show ¬ j + 1 < 1 by omega), Nat.add_sub_cancel]
    rw [fit_congr (x' := shift 1 (toR (xHseqP p k I dg ℓ e)))
      fun i _ => by simp [toR, oddCellXSharp, shift, add_comm]]
  have hI1 := (oddCell_lemma_7_9_I1 hI hd hℓ he).1
  have hint : ∀ j < 2 ^ #I - 1, fit (2 ^ #I - 1) (toR (oddCellXSharp p k I dg ℓ e)) j =
      (yhatP p k I dg ℓ e (j + 1) : ℝ) := fun j hj => by
    rw [hres j hj, hI1 (j + 1) (by omega)]
  exact ⟨htyp, hJ, hcut, hres,
    CellFloor.ifit_eq_of_fit_eq_int (y := fun j => yhatP p k I dg ℓ e (j + 1)) hint, hint⟩

end ColouredSand.OddTwist
