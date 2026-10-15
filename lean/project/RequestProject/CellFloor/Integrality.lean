module

public import RequestProject.CellFloor.Basic

/-!
# Part A of `C9_integrality_and_cell_floor.md`: Lemma 7.9 (integrality)

Encodings as in `RequestProject/CellFloor/Basic.lean`.
-/

@[expose] public section

namespace CellFloor

open Finset AntitonicFit TheoremF Potential

/-- Statement (I1) of Lemma 7.9 (`C9_integrality_and_cell_floor.md`) for one house, as used in
the induction on `|I|`. -/
def I1Prop (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) : Prop :=
  ∀ p < 2 ^ #I, fit (2 ^ #I) (toR (xHseq I k ℓ α)) p = (yhat I k ℓ α p : ℝ)

/-- (I1) by induction on `|I|` (proof of Lemma 7.9 (I1), `C9_integrality_and_cell_floor.md`):
base `I = ∅` (`N = 1`), step by (W3) of Theorem F0 (C7) and the induction hypothesis for `H'`. -/
lemma I1_all : ∀ (n : ℕ) (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ), #I = n → (∀ t ∈ I, t < k) →
    ℓ < 2 ^ k → 1 ≤ α → I1Prop I k ℓ α := by
  intro n
  induction n with
  | zero =>
    intro I k ℓ α hn _ _ _
    have hfit : ∀ j < 2 ^ #I, fit (2 ^ #I) (toR (xHseq I k ℓ α)) j = (xHseq I k ℓ α j : ℝ) := by
      intro j hj
      rw [hn, pow_zero] at hj ⊢
      obtain rfl : j = 0 := by omega
      exact fit_one _
    intro p hp
    rw [yhat, ifit_eq_of_fit_eq_int hfit p hp, hfit p hp]
  | succ n ih =>
    intro I k ℓ α hn hI hℓ hα
    have hne : I.Nonempty := card_pos.1 (by omega)
    set c := I.max' hne with hc
    have hcI : c ∈ I := I.max'_mem hne
    have hI' : ∀ t ∈ I.erase c, t < c := fun t ht =>
      lt_of_le_of_ne (I.le_max' t (mem_of_mem_erase ht)) (ne_of_mem_erase ht)
    have hcard : #(I.erase c) = n := by rw [card_erase_of_mem hcI]; omega
    have ih' := ih (I.erase c) c (ℓ % 2 ^ c) α hcard hI' (Nat.mod_lt _ (by positivity)) hα
    have hW3 := theorem_F0_W3 hI hℓ hα hne hc
    have hN := card_erase_max hne hc
    intro p hp
    rw [hW3.1 p hp, yhat, hW3.2 p hp]
    simp only [concat, mirror, Pi.add_apply]
    split_ifs with hpM
    · rw [ih' p hpM]
      simp [toR, yhat]
    · rw [ih' _ (by omega)]
      simp [toR, yhat]

/-- **Lemma 7.9 (I1)** of `C9_integrality_and_cell_floor.md`: for every house `H` and every
`p < N`, `fit_N(x_H)(p) = ŷ_H(p)` (as reals) — in particular the real fit of `x_H` takes integer
values — and `ŷ_H` is non-increasing on `[0, N)`. -/
theorem lemma_7_9_I1 {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k)
    (hα : 1 ≤ α) :
    (∀ p < 2 ^ #I, fit (2 ^ #I) (toR (xHseq I k ℓ α)) p = (yhat I k ℓ α p : ℝ)) ∧
      SmithBounds.NonIncrOn (2 ^ #I) (yhat I k ℓ α) := by
  have h := I1_all _ I k ℓ α rfl hI hℓ hα
  refine ⟨h, fun j hj => ?_⟩
  have := fit_nonIncr (2 ^ #I) (toR (xHseq I k ℓ α)) j hj
  rw [h j (by omega), h (j + 1) hj] at this
  exact_mod_cast this

/-- The shift `δ(p) := −P_r J_H(p) + P_c J_H(N − 1 − p)` of the proof of Lemma 7.9 (I2)
(`C9_integrality_and_cell_floor.md`). -/
def cellShift (I : Finset ℕ) (k ℓ : ℕ) (Pr Pc : ℕ) : ℕ → ℤ := fun p =>
  -((Pr : ℤ) * (JHseq I k ℓ p : ℤ)) + (Pc : ℤ) * (JHseq I k ℓ (2 ^ #I - 1 - p) : ℤ)

/-- The cell clocks are `x_H + δ` (proof of Lemma 7.9 (I2), `C9_integrality_and_cell_floor.md`). -/
lemma cellClock_eq (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (Pr Pc : ℕ) :
    cellClock I k ℓ α Pr Pc = xHseq I k ℓ α + cellShift I k ℓ Pr Pc := by
  funext p; simp only [cellClock, cellShift, Pi.add_apply]; ring

/-- `δ` is non-increasing on `[0, N)` (`J_H` is non-decreasing); proof of Lemma 7.9 (I2),
`C9_integrality_and_cell_floor.md`. -/
lemma cellShift_nonIncr (I : Finset ℕ) (k ℓ : ℕ) (Pr Pc : ℕ) :
    NonIncr (2 ^ #I) (toR (cellShift I k ℓ Pr Pc)) := by
  intro j hj
  show ((cellShift I k ℓ Pr Pc (j + 1) : ℤ) : ℝ) ≤ (cellShift I k ℓ Pr Pc j : ℝ)
  have h1 : (JHseq I k ℓ j : ℤ) ≤ JHseq I k ℓ (j + 1) := by exact_mod_cast JHseq_mono (by omega) hj
  have h2 : (JHseq I k ℓ (2 ^ #I - 1 - (j + 1)) : ℤ) ≤ JHseq I k ℓ (2 ^ #I - 1 - j) := by
    exact_mod_cast JHseq_mono (by omega) (by omega)
  have h3 := mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ Pr by positivity)
  have h4 := mul_le_mul_of_nonneg_left h2 (show (0 : ℤ) ≤ Pc by positivity)
  have : cellShift I k ℓ Pr Pc (j + 1) ≤ cellShift I k ℓ Pr Pc j := by
    simp only [cellShift]; linarith
  exact_mod_cast this

/-- If `J_H` jumps between `b − 1` and `b`, then `b` is the first position with `J_H(b) = 1`
(proof of Lemma 7.9 (I2), `C9_integrality_and_cell_floor.md`). -/
lemma J_jump {I : Finset ℕ} {k ℓ b : ℕ} (hb0 : 0 < b) (hbN : b < 2 ^ #I)
    (hne : JHseq I k ℓ (b - 1) ≠ JHseq I k ℓ b) :
    JHseq I k ℓ b = 1 ∧ ∀ p < b, JHseq I k ℓ p = 0 := by
  have h1 := JHseq_mono (I := I) (k := k) (ℓ := ℓ) (show b - 1 ≤ b by omega) hbN
  have h2 := JHseq_le_one I k ℓ b
  refine ⟨by omega, fun p hp => ?_⟩
  have := JHseq_mono (I := I) (k := k) (ℓ := ℓ) (show p ≤ b - 1 by omega) (by omega)
  omega

/-- Every position where `δ` changes is a strict cut of `x_H` (Theorem F1 (Cut) of C7); proof of
Lemma 7.9 (I2), `C9_integrality_and_cell_floor.md`. -/
lemma cellShift_change_strictCut {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k)
    (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (Pr Pc : ℕ) :
    ∀ b, 0 < b → b < 2 ^ #I → cellShift I k ℓ Pr Pc (b - 1) ≠ cellShift I k ℓ Pr Pc b →
      IsStrictCut (2 ^ #I) (toR (xHseq I k ℓ α)) b := by
  intro b hb0 hbN hne
  have hcut := theorem_F1_Cut hI hℓ hα
  by_cases hA : JHseq I k ℓ (b - 1) = JHseq I k ℓ b
  · have hB : JHseq I k ℓ (2 ^ #I - 1 - b) ≠ JHseq I k ℓ (2 ^ #I - b) := by
      intro hB
      apply hne
      simp only [cellShift]
      rw [hA, show 2 ^ #I - 1 - (b - 1) = 2 ^ #I - b by omega, ← hB]
    have hB' : JHseq I k ℓ (2 ^ #I - b - 1) ≠ JHseq I k ℓ (2 ^ #I - b) := by
      rwa [show 2 ^ #I - b - 1 = 2 ^ #I - 1 - b by omega]
    obtain ⟨h1, h2⟩ := J_jump (by omega) (by omega) hB'
    have := (hcut (2 ^ #I - b) (by omega) h1 h2).2
    rwa [show 2 ^ #I - (2 ^ #I - b) = b by omega] at this
  · obtain ⟨h1, h2⟩ := J_jump hb0 hbN hA
    exact (hcut b hbN h1 h2).1

/-- **Lemma 7.9 (I2)** of `C9_integrality_and_cell_floor.md`: for every house `H` and all
`P_r, P_c ∈ ℕ`, with `z` the cell clocks: for every `p < N`,
`ifit_N(z)(p) = ŷ_H(p) − P_r J_H(p) + P_c J_H(N − 1 − p)` and `fit_N(z)(p) = ifit_N(z)(p)` (as
reals); and `ifit_N(z)` is non-increasing on `[0, N)`. -/
theorem lemma_7_9_I2 {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k)
    (hα : 1 ≤ α) (Pr Pc : ℕ) :
    (∀ p < 2 ^ #I, ifit (2 ^ #I) (cellClock I k ℓ α Pr Pc) p =
      yhat I k ℓ α p - (Pr : ℤ) * (JHseq I k ℓ p : ℤ) +
        (Pc : ℤ) * (JHseq I k ℓ (2 ^ #I - 1 - p) : ℤ)) ∧
    (∀ p < 2 ^ #I, fit (2 ^ #I) (toR (cellClock I k ℓ α Pr Pc)) p =
      (ifit (2 ^ #I) (cellClock I k ℓ α Pr Pc) p : ℝ)) ∧
    SmithBounds.NonIncrOn (2 ^ #I) (ifit (2 ^ #I) (cellClock I k ℓ α Pr Pc)) := by
  have hz : cellClock I k ℓ α Pr Pc = xHseq I k ℓ α + cellShift I k ℓ Pr Pc :=
    cellClock_eq I k ℓ α Pr Pc
  have hδn := cellShift_nonIncr I k ℓ Pr Pc
  have hch := cellShift_change_strictCut hI hℓ hα Pr Pc
  have hI1 := (lemma_7_9_I1 hI hℓ hα).1
  set N := 2 ^ #I with hN
  set x := xHseq I k ℓ α
  set δ := cellShift I k ℓ Pr Pc with hδ
  -- integer fit, by Lemma 7.2 (b3) ⟹ (b2)
  have hifit : ∀ p < N, ifit N (cellClock I k ℓ α Pr Pc) p = yhat I k ℓ α p + δ p := by
    intro p hp
    rw [hz, (lemma_7_2_b3_b2 hδn hch).2.2 p hp]
    rfl
  -- real fit, by Lemma 7.2 (b1)
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
  have hfitz : ∀ p < N, fit N (toR (cellClock I k ℓ α Pr Pc)) p =
      (ifit N (cellClock I k ℓ α Pr Pc) p : ℝ) := by
    intro p hp
    rw [hifit p hp, hz, toR_add, hfit p hp, hI1 p hp]
    simp [toR]
  refine ⟨fun p hp => ?_, hfitz, fun j hj => ?_⟩
  · rw [hifit p hp]; simp only [hδ, cellShift]; ring
  · have := fit_nonIncr N (toR (cellClock I k ℓ α Pr Pc)) j hj
    rw [hfitz j (by omega), hfitz (j + 1) hj] at this
    exact_mod_cast this

/-- **Lemma 7.9 (I3)** of `C9_integrality_and_cell_floor.md`: for a house with `ℓ = 2^k − 1` and
`I ≠ ∅`: `J_H(p) = [p ≠ 0]` for `p < N`; `x_H` has a strict cut at `1`; and `x^♯(j) := x_H(j + 1)`
(length `N − 1`) has `fit_{N−1}(x^♯)(j) = fit_N(x_H)(j + 1)` and
`ifit_{N−1}(x^♯)(j) = ŷ_H(j + 1)` for `j < N − 1`, and these are integers
(`fit_{N−1}(x^♯)(j) = ŷ_H(j + 1)` as reals).  (The house condition `ℓ < 2^k` follows from
`ℓ = 2^k − 1`.) -/
theorem lemma_7_9_I3 {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k)
    (hℓ' : ℓ = 2 ^ k - 1) (hα : 1 ≤ α) (hne : I.Nonempty) :
    (∀ p < 2 ^ #I, JHseq I k ℓ p = if p ≠ 0 then 1 else 0) ∧
    IsStrictCut (2 ^ #I) (toR (xHseq I k ℓ α)) 1 ∧
    (∀ j < 2 ^ #I - 1,
      fit (2 ^ #I - 1) (toR (xSharp I k ℓ α)) j = fit (2 ^ #I) (toR (xHseq I k ℓ α)) (j + 1)) ∧
    (∀ j < 2 ^ #I - 1, ifit (2 ^ #I - 1) (xSharp I k ℓ α) j = yhat I k ℓ α (j + 1)) ∧
    (∀ j < 2 ^ #I - 1, fit (2 ^ #I - 1) (toR (xSharp I k ℓ α)) j = (yhat I k ℓ α (j + 1) : ℝ)) := by
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hℓ : ℓ < 2 ^ k := by omega
  have h1N : 1 < 2 ^ #I := Nat.one_lt_two_pow (card_pos.2 hne).ne'
  have hJ : ∀ p < 2 ^ #I, JHseq I k ℓ p = if p ≠ 0 then 1 else 0 := by
    intro p hp
    simp only [JHseq, Houses.JH]
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · simp [dancer_zero, Rulers.oE_empty]; omega
    · have := lemma_0b hp0 hp (I := I)
      rw [dancer_zero, Rulers.oE_empty] at this
      rw [if_pos (by omega), if_pos (by omega)]
  have hcut : IsStrictCut (2 ^ #I) (toR (xHseq I k ℓ α)) 1 :=
    (theorem_F1_Cut hI hℓ hα 1 h1N (by rw [hJ 1 h1N]; simp)
      (fun p hp => by rw [hJ p (by omega)]; simp; omega)).1
  have hres : ∀ j < 2 ^ #I - 1,
      fit (2 ^ #I - 1) (toR (xSharp I k ℓ α)) j = fit (2 ^ #I) (toR (xHseq I k ℓ α)) (j + 1) := by
    intro j hj
    rw [hcut.1.2.2 (j + 1) (by omega)]
    simp only [concat, if_neg (show ¬ j + 1 < 1 by omega), Nat.add_sub_cancel]
    rw [fit_congr (x' := shift 1 (toR (xHseq I k ℓ α)))
      fun i _ => by simp [toR, xSharp, shift, add_comm]]
  have hI1 := (lemma_7_9_I1 hI hℓ hα).1
  have hint : ∀ j < 2 ^ #I - 1,
      fit (2 ^ #I - 1) (toR (xSharp I k ℓ α)) j = (yhat I k ℓ α (j + 1) : ℝ) := fun j hj => by
    rw [hres j hj, hI1 (j + 1) (by omega)]
  exact ⟨hJ, hcut, hres, ifit_eq_of_fit_eq_int (y := fun j => yhat I k ℓ α (j + 1)) hint, hint⟩

end CellFloor
