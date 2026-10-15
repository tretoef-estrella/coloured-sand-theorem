module

public import RequestProject.TheoremF.Sequences

/-!
# The walk (Theorem F0) of `C7_theorem_F_walk_and_cut.md`, given (Cut) for `H'`

This file proves (W0)–(W3) of **Theorem F0** for a house `H` with `I ≠ ∅`, under the hypothesis
that (Cut) of Theorem F1 holds for the smaller house `H' = (I', c, ℓ mod 2^c, α)`
(`CutProp`).  The unconditional Theorem F0 is in `RequestProject/TheoremF/TheoremF.lean`, where
(Cut) for `H'` is supplied by the induction on `|I|`.  Encodings as in
`RequestProject/TheoremF/Sequences.lean`.
-/

@[expose] public section

namespace TheoremF

open Finset Rulers AntitonicFit

/-- The statement **(Cut)** of Theorem F1 (`C7_theorem_F_walk_and_cut.md`) for the house
`(I, k, ℓ, α)`: if `b < N` is the first position with `J_H(b) = 1`, then `x_H` has a strict cut
at `b` and at `N − b`. -/
def CutProp (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) : Prop :=
  ∀ b < 2 ^ #I, JHseq I k ℓ b = 1 → (∀ p < b, JHseq I k ℓ p = 0) →
    IsStrictCut (2 ^ #I) (toR (xHseq I k ℓ α)) b ∧
      IsStrictCut (2 ^ #I) (toR (xHseq I k ℓ α)) (2 ^ #I - b)

variable {I : Finset ℕ} {k ℓ : ℕ}

/-- **(W0)** of Theorem F0, `C7_theorem_F_walk_and_cut.md`: for `p < M`,
`x_H(p) = x'(p) + d(p)`.  (Uses `I ⊆ {0,…,k−1}` and `ℓ < 2^k`, not `α ≥ 1`.) -/
theorem theorem_F0_W0 (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (α : ℤ) (hne : I.Nonempty)
    {c : ℕ} (hc : c = I.max' hne) :
    ∀ p < 2 ^ #(I.erase c),
      xHseq I k ℓ α p = xHseq (I.erase c) c (ℓ % 2 ^ c) α p + dWalk I k ℓ α c p := by
  intro p hp
  simp only [xHseq, dWalk]
  rw [(lemma_0e hne hc hp).1]
  exact Houses.lemma_C6 hI hℓ α hne hc (lemma_0a _ p)

/-- **(W1)** of Theorem F0, `C7_theorem_F_walk_and_cut.md`, first claim: `d` is non-increasing
on `[0, M)`.  (More general than the file: holds for every `I`, `k`, `ℓ`, `α`, `c`.) -/
theorem theorem_F0_W1_antitone (α : ℤ) (c : ℕ) :
    ∀ p, p + 1 < 2 ^ #(I.erase c) → dWalk I k ℓ α c (p + 1) ≤ dWalk I k ℓ α c p := by
  intro p hp
  set M := 2 ^ #(I.erase c) with hM
  rw [dWalk_eq α c hp, dWalk_eq α c (by omega)]
  have h1 := JHseq_mono (I := I.erase c) (k := c) (ℓ := ℓ % 2 ^ c) (Nat.le_succ p) hp
  have h2 := JHseq_mono (I := I.erase c) (k := c) (ℓ := ℓ % 2 ^ c)
    (show M - 1 - (p + 1) ≤ M - 1 - p by omega) (by omega)
  have hA : (0 : ℤ) ≤ if Houses.typ ℓ c = 1 then (Houses.kap I k ℓ c : ℤ) else 0 := by
    split_ifs <;> simp
  have hB : (0 : ℤ) ≤ if Houses.typ ℓ c = 0 then (Houses.kap I k ℓ c : ℤ) else 0 := by
    split_ifs <;> simp
  have h1' : (JHseq (I.erase c) c (ℓ % 2 ^ c) p : ℤ) ≤ JHseq (I.erase c) c (ℓ % 2 ^ c) (p + 1) := by
    exact_mod_cast h1
  have h2' : (JHseq (I.erase c) c (ℓ % 2 ^ c) (M - 1 - (p + 1)) : ℤ) ≤
      JHseq (I.erase c) c (ℓ % 2 ^ c) (M - 1 - p) := by exact_mod_cast h2
  nlinarith [mul_le_mul_of_nonneg_left h1' hA, mul_le_mul_of_nonneg_left h2' hB]

/-- **(W1)** of Theorem F0, `C7_theorem_F_walk_and_cut.md`, second claim: if `0 < p < M` and
`d(p − 1) ≠ d(p)`, then `J'` is not identically zero on `[0, M)` and `p = b'` or `p = M − b'`,
where `b'` is the first position with `J'(b') = 1`.  (Here «`J' ≢ 0`, with first one at `b'`» is
the existence of `b' < M` with `J'(b') = 1` and `J'(q) = 0` for `q < b'`.  More general than the
file: holds for every `I`, `k`, `ℓ`, `α`, `c`.) -/
theorem theorem_F0_W1_change (α : ℤ) (c : ℕ) :
    ∀ p, 0 < p → p < 2 ^ #(I.erase c) → dWalk I k ℓ α c (p - 1) ≠ dWalk I k ℓ α c p →
      ∃ b' < 2 ^ #(I.erase c), JHseq (I.erase c) c (ℓ % 2 ^ c) b' = 1 ∧
        (∀ q < b', JHseq (I.erase c) c (ℓ % 2 ^ c) q = 0) ∧
        (p = b' ∨ p = 2 ^ #(I.erase c) - b') := by
  intro p hp0 hp hne
  rw [dWalk_eq α c hp, dWalk_eq α c (by omega)] at hne
  set M := 2 ^ #(I.erase c) with hM
  set J := JHseq (I.erase c) c (ℓ % 2 ^ c) with hJ
  have hmono : ∀ {a b}, a ≤ b → b < M → J a ≤ J b := fun hab hb => JHseq_mono hab hb
  have hle : ∀ a, J a ≤ 1 := fun a => JHseq_le_one _ _ _ a
  have hor : J (p - 1) ≠ J p ∨ J (M - 1 - (p - 1)) ≠ J (M - 1 - p) := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [hcon.1, hcon.2]
  rcases hor with h | h
  · have ha := hmono (show p - 1 ≤ p by omega) hp
    have h0 : J (p - 1) = 0 := by have := hle p; omega
    refine ⟨p, hp, by have := hle p; omega, fun q hq => ?_, Or.inl rfl⟩
    have := hmono (show q ≤ p - 1 by omega) (by omega); omega
  · have ha := hmono (show M - 1 - p ≤ M - 1 - (p - 1) by omega) (by omega)
    have h0 : J (M - 1 - p) = 0 := by have := hle (M - 1 - (p - 1)); omega
    refine ⟨M - p, by omega, ?_, fun q hq => ?_, Or.inr (by omega)⟩
    · have := hle (M - 1 - (p - 1)); rw [show M - 1 - (p - 1) = M - p by omega] at this h; omega
    · have := hmono (show q ≤ M - 1 - p by omega) (by omega); omega

/-- (W1) of Theorem F0, `C7_theorem_F_walk_and_cut.md`, in the real form used by C1. -/
lemma dWalk_nonIncr (α : ℤ) (c : ℕ) : NonIncr (2 ^ #(I.erase c)) (toR (dWalk I k ℓ α c)) := by
  intro p hp
  simp only [toR]
  exact_mod_cast theorem_F0_W1_antitone (I := I) (k := k) (ℓ := ℓ) α c p hp

/-- Step 1 of the proof of Theorem F0 (`C7_theorem_F_walk_and_cut.md`): the changes of `d` are
strict cuts of `x'`, given (Cut) for `H'`. -/
lemma dWalk_change_strictCut (α : ℤ) (c : ℕ) (hcut : CutProp (I.erase c) c (ℓ % 2 ^ c) α) :
    ∀ b, 0 < b → b < 2 ^ #(I.erase c) → dWalk I k ℓ α c (b - 1) ≠ dWalk I k ℓ α c b →
      IsStrictCut (2 ^ #(I.erase c)) (toR (xHseq (I.erase c) c (ℓ % 2 ^ c) α)) b := by
  intro b hb0 hb hne
  obtain ⟨b', hb', hJ1, hJ0, hor⟩ := theorem_F0_W1_change α c b hb0 hb hne
  have := hcut b' hb' hJ1 hJ0
  rcases hor with rfl | rfl
  · exact this.1
  · exact this.2

/-- **(W2)** of Theorem F0, `C7_theorem_F_walk_and_cut.md`, given (Cut) for `H'`:
for `p < M`, `fit_M(x' + d)(p) = fit_M(x')(p) + d(p)` and `ifit_M(x' + d)(p) = ifit_M(x')(p) + d(p)`.
-/
theorem walk_W2_of_cut (α : ℤ) (c : ℕ) (hcut : CutProp (I.erase c) c (ℓ % 2 ^ c) α) :
    (∀ p < 2 ^ #(I.erase c),
      fit (2 ^ #(I.erase c)) (toR (xHseq (I.erase c) c (ℓ % 2 ^ c) α + dWalk I k ℓ α c)) p =
        fit (2 ^ #(I.erase c)) (toR (xHseq (I.erase c) c (ℓ % 2 ^ c) α)) p +
          dWalk I k ℓ α c p) ∧
    (∀ p < 2 ^ #(I.erase c),
      ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α + dWalk I k ℓ α c) p =
        ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α) p + dWalk I k ℓ α c p) := by
  set M := 2 ^ #(I.erase c) with hM
  set x' := xHseq (I.erase c) c (ℓ % 2 ^ c) α with hx'
  set d := dWalk I k ℓ α c with hd
  have hcuts := dWalk_change_strictCut (k := k) α c hcut
  refine ⟨fun p hp => ?_, (lemma_7_2_b3_b2 (dWalk_nonIncr α c) hcuts).2.2⟩
  have hb1 := lemma_7_2_b1 (N := M) (x := toR x')
    (B := (range M).filter (fun b => 0 < b ∧ d (b - 1) ≠ d b))
    (fun b hb => by
      simp only [mem_filter, mem_range] at hb
      exact (hcuts b hb.2.1 hb.1 hb.2.2).1)
    (δ := toR d) (dWalk_nonIncr α c)
    (fun j hj hjB => by
      simp only [mem_filter, mem_range, not_and, not_not] at hjB
      have := hjB hj (by omega)
      simp only [toR, Nat.add_sub_cancel] at this ⊢
      rw [this])
  rw [toR_add]
  exact hb1.1 p hp

/-- **(W3)** of Theorem F0, `C7_theorem_F_walk_and_cut.md`, given (Cut) for `H'`: with
`Z_1 = fit_M(x') + d` and `X_1 = ifit_M(x') + d`, for `p < N`,
`fit_N(x_H)(p) = concat_M(max(Z_1, 0), min(mirror_M(Z_1), 0))(p)` and
`ŷ_H(p) = concat_M(max(X_1, 0), min(mirror_M(X_1), 0))(p)`. -/
theorem walk_W3_of_cut (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (α : ℤ) (hne : I.Nonempty)
    {c : ℕ} (hc : c = I.max' hne) (hcut : CutProp (I.erase c) c (ℓ % 2 ^ c) α) :
    (∀ p < 2 ^ #I, fit (2 ^ #I) (toR (xHseq I k ℓ α)) p =
      concat (2 ^ #(I.erase c))
        (fun i => max ((fit (2 ^ #(I.erase c)) (toR (xHseq (I.erase c) c (ℓ % 2 ^ c) α)) +
          toR (dWalk I k ℓ α c)) i) 0)
        (fun i => min (mirror (2 ^ #(I.erase c))
          (fit (2 ^ #(I.erase c)) (toR (xHseq (I.erase c) c (ℓ % 2 ^ c) α)) +
            toR (dWalk I k ℓ α c)) i) 0) p) ∧
    (∀ p < 2 ^ #I, ifit (2 ^ #I) (xHseq I k ℓ α) p =
      concat (2 ^ #(I.erase c))
        (fun i => max ((ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α) +
          dWalk I k ℓ α c) i) 0)
        (fun i => min (mirror (2 ^ #(I.erase c))
          (ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α) +
            dWalk I k ℓ α c) i) 0) p) := by
  have hN := card_erase_max hne hc
  have hW0 := theorem_F0_W0 hI hℓ α hne hc
  have hW2 := walk_W2_of_cut (k := k) α c hcut
  set M := 2 ^ #(I.erase c) with hM
  set x' := xHseq (I.erase c) c (ℓ % 2 ^ c) α with hx'
  set d := dWalk I k ℓ α c with hd
  set x := xHseq I k ℓ α with hx
  have hanti : IsAntisymm (2 * M) x := hN ▸ lemma_0f_antisymm I k ℓ α
  rw [hN]
  constructor
  · intro p hp
    rw [lemma_7_3_fit (toR_antisymm hanti) p hp]
    have hf : fit M (toR x) = fit M (toR (x' + d)) :=
      fit_congr fun j hj => by simp [toR, hW0 j hj]
    rw [hf]
    simp only [concat, mirror, Pi.add_apply]
    split_ifs with h
    · rw [hW2.1 p h]; rfl
    · rw [hW2.1 _ (by omega)]; rfl
  · intro p hp
    rw [lemma_7_3_ifit hanti p hp]
    have hf : ifit M x = ifit M (x' + d) :=
      ifit_congr fun j hj => by simp [hW0 j hj]
    rw [hf]
    simp only [concat, mirror, Pi.add_apply]
    split_ifs with h
    · rw [hW2.2 p h]
    · rw [hW2.2 _ (by omega)]

end TheoremF
