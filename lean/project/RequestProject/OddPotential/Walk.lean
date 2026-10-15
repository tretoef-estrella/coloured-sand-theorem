module

public import RequestProject.OddPotential.Sequences

/-!
# `CSI16_theorem_F_at_p.md` — *Part F0*: the walk (W0)–(W3), given (Cut) for `H'`

Base-`p` analogue of `RequestProject/TheoremF/Walk.lean` (C7).  This file proves (W0)–(W3) of
**Theorem F0_p** for a house `H` with `I ≠ ∅`, under the hypothesis that (Cut) of Theorem F1_p
holds for the smaller house `H' = (I', c, ℓ mod p^c, e, d)` (`CutPropP`).  The unconditional
Theorem F0_p is in `RequestProject/OddPotential/TheoremF1.lean`.  Encodings as in
`RequestProject/OddPotential/Sequences.lean`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset AntitonicFit TheoremF

/-- The statement **(Cut)** of Theorem F1_p (`CSI16_theorem_F_at_p.md`, Part F1) for the house
`(I, k, ℓ, e, dg)`: if `b < N` is the first position with `J_H(b) = 1`, then `x_H` has a strict cut
at `b` and at `N − b`. -/
def CutPropP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) : Prop :=
  ∀ b < 2 ^ #I, JHseqP p k I dg ℓ b = 1 → (∀ q < b, JHseqP p k I dg ℓ q = 0) →
    IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) b ∧
      IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) (2 ^ #I - b)

variable {p : ℕ} {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ}

section prime

variable [hp : Fact p.Prime]

/-- **(W0)** of Theorem F0_p (`CSI16_theorem_F_at_p.md`, Part F0): for `q < M`,
`x_H(q) = x'(q) + d_1(q)`.  (Does not use `e ≥ 1`.) -/
theorem oddF_W0 (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k)
    (e : ℤ) (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) :
    ∀ q < 2 ^ #(I.erase c),
      xHseqP p k I dg ℓ e q = xHseqP p c (I.erase c) dg (ℓ % p ^ c) e q + dWalkP p k I dg ℓ e c q := by
  intro q hq
  simp only [xHseqP, dWalkP]
  rw [(lemma_0e hne hc hq).1]
  exact houseP_C6 hI hd hℓ e hne hc (lemma_0a _ q)

/-- **(W1)** of Theorem F0_p (`CSI16_theorem_F_at_p.md`, Part F0), first claim: `d_1` is
non-increasing on `[0, M)`.  (Only the digit condition is used.) -/
theorem oddF_W1_antitone (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (e : ℤ) (c : ℕ) :
    ∀ q, q + 1 < 2 ^ #(I.erase c) → dWalkP p k I dg ℓ e c (q + 1) ≤ dWalkP p k I dg ℓ e c q := by
  intro q hq
  set M := 2 ^ #(I.erase c) with hM
  have h2p := oddHou_two_le_p (p := p)
  have hd' := hd_erase hd c
  rw [dWalkP_eq e c hq, dWalkP_eq e c (by omega)]
  have h1 := JHseqP_mono (k := c) (ℓ := ℓ % p ^ c) h2p hd' (Nat.le_succ q) hq
  have h2 := JHseqP_mono (k := c) (ℓ := ℓ % p ^ c) h2p hd'
    (show M - 1 - (q + 1) ≤ M - 1 - q by omega) (by omega)
  have hA : (0 : ℤ) ≤ if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0 := by
    split_ifs <;> simp
  have hB : (0 : ℤ) ≤ if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0 := by
    split_ifs <;> simp
  have h1' : (JHseqP p c (I.erase c) dg (ℓ % p ^ c) q : ℤ) ≤
      JHseqP p c (I.erase c) dg (ℓ % p ^ c) (q + 1) := by exact_mod_cast h1
  have h2' : (JHseqP p c (I.erase c) dg (ℓ % p ^ c) (M - 1 - (q + 1)) : ℤ) ≤
      JHseqP p c (I.erase c) dg (ℓ % p ^ c) (M - 1 - q) := by exact_mod_cast h2
  nlinarith [mul_le_mul_of_nonneg_left h1' hA, mul_le_mul_of_nonneg_left h2' hB]

/-- **(W1)** of Theorem F0_p (`CSI16_theorem_F_at_p.md`, Part F0), second claim: if `0 < q < M`
and `d_1(q − 1) ≠ d_1(q)`, then `J' ≢ 0` on `[0, M)` and `q = b'` or `q = M − b'`, where `b'` is
the first position with `J'(b') = 1` (encoded as in C7's `theorem_F0_W1_change`). -/
theorem oddF_W1_change (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (e : ℤ) (c : ℕ) :
    ∀ q, 0 < q → q < 2 ^ #(I.erase c) → dWalkP p k I dg ℓ e c (q - 1) ≠ dWalkP p k I dg ℓ e c q →
      ∃ b' < 2 ^ #(I.erase c), JHseqP p c (I.erase c) dg (ℓ % p ^ c) b' = 1 ∧
        (∀ q' < b', JHseqP p c (I.erase c) dg (ℓ % p ^ c) q' = 0) ∧
        (q = b' ∨ q = 2 ^ #(I.erase c) - b') := by
  intro q hq0 hq hne
  rw [dWalkP_eq e c hq, dWalkP_eq e c (by omega)] at hne
  set M := 2 ^ #(I.erase c) with hM
  set J := JHseqP p c (I.erase c) dg (ℓ % p ^ c) with hJ
  have hmono : ∀ {a b}, a ≤ b → b < M → J a ≤ J b := fun hab hb =>
    JHseqP_mono oddHou_two_le_p (hd_erase hd c) hab hb
  have hle : ∀ a, J a ≤ 1 := fun a => JHseqP_le_one _ _ _ _ _ a
  have hor : J (q - 1) ≠ J q ∨ J (M - 1 - (q - 1)) ≠ J (M - 1 - q) := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [hcon.1, hcon.2]
  rcases hor with h | h
  · have ha := hmono (show q - 1 ≤ q by omega) hq
    have h0 : J (q - 1) = 0 := by have := hle q; omega
    refine ⟨q, hq, by have := hle q; omega, fun q' hq' => ?_, Or.inl rfl⟩
    have := hmono (show q' ≤ q - 1 by omega) (by omega); omega
  · have ha := hmono (show M - 1 - q ≤ M - 1 - (q - 1) by omega) (by omega)
    have h0 : J (M - 1 - q) = 0 := by have := hle (M - 1 - (q - 1)); omega
    refine ⟨M - q, by omega, ?_, fun q' hq' => ?_, Or.inr (by omega)⟩
    · have := hle (M - 1 - (q - 1)); rw [show M - 1 - (q - 1) = M - q by omega] at this h; omega
    · have := hmono (show q' ≤ M - 1 - q by omega) (by omega); omega

/-- (W1) in the real form used by C1. -/
lemma dWalkP_nonIncr (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (e : ℤ) (c : ℕ) :
    NonIncr (2 ^ #(I.erase c)) (toR (dWalkP p k I dg ℓ e c)) := by
  intro q hq
  simp only [toR]
  exact_mod_cast oddF_W1_antitone (k := k) (ℓ := ℓ) hd e c q hq

/-- Step 1 of the proof of Theorem F0_p: the changes of `d_1` are strict cuts of `x'`, given (Cut)
for `H'`. -/
lemma dWalkP_change_strictCut (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (e : ℤ) (c : ℕ)
    (hcut : CutPropP p c (I.erase c) dg (ℓ % p ^ c) e) :
    ∀ b, 0 < b → b < 2 ^ #(I.erase c) → dWalkP p k I dg ℓ e c (b - 1) ≠ dWalkP p k I dg ℓ e c b →
      IsStrictCut (2 ^ #(I.erase c)) (toR (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e)) b := by
  intro b hb0 hb hne
  obtain ⟨b', hb', hJ1, hJ0, hor⟩ := oddF_W1_change hd e c b hb0 hb hne
  have := hcut b' hb' hJ1 hJ0
  rcases hor with rfl | rfl
  · exact this.1
  · exact this.2

/-- **(W2)** of Theorem F0_p (`CSI16_theorem_F_at_p.md`, Part F0), given (Cut) for `H'`: for
`q < M`, `fit_M(x' + d_1)(q) = fit_M(x')(q) + d_1(q)` and
`ifit_M(x' + d_1)(q) = ifit_M(x')(q) + d_1(q)`. -/
theorem oddF_W2_of_cut (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (e : ℤ) (c : ℕ)
    (hcut : CutPropP p c (I.erase c) dg (ℓ % p ^ c) e) :
    (∀ q < 2 ^ #(I.erase c),
      fit (2 ^ #(I.erase c))
          (toR (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e + dWalkP p k I dg ℓ e c)) q =
        fit (2 ^ #(I.erase c)) (toR (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e)) q +
          dWalkP p k I dg ℓ e c q) ∧
    (∀ q < 2 ^ #(I.erase c),
      ifit (2 ^ #(I.erase c)) (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e + dWalkP p k I dg ℓ e c) q =
        ifit (2 ^ #(I.erase c)) (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e) q +
          dWalkP p k I dg ℓ e c q) := by
  set M := 2 ^ #(I.erase c) with hM
  set x' := xHseqP p c (I.erase c) dg (ℓ % p ^ c) e with hx'
  set d := dWalkP p k I dg ℓ e c with hd_def
  have hcuts := dWalkP_change_strictCut (k := k) hd e c hcut
  refine ⟨fun q hq => ?_, (lemma_7_2_b3_b2 (dWalkP_nonIncr hd e c) hcuts).2.2⟩
  have hb1 := lemma_7_2_b1 (N := M) (x := toR x')
    (B := (range M).filter (fun b => 0 < b ∧ d (b - 1) ≠ d b))
    (fun b hb => by
      simp only [mem_filter, mem_range] at hb
      exact (hcuts b hb.2.1 hb.1 hb.2.2).1)
    (δ := toR d) (dWalkP_nonIncr hd e c)
    (fun j hj hjB => by
      simp only [mem_filter, mem_range, not_and, not_not] at hjB
      have := hjB hj (by omega)
      simp only [toR, Nat.add_sub_cancel] at this ⊢
      rw [this])
  rw [toR_add]
  exact hb1.1 q hq

/-- **(W3)** of Theorem F0_p (`CSI16_theorem_F_at_p.md`, Part F0), given (Cut) for `H'`: with
`Z_1 = fit_M(x') + d_1` and `X_1 = ifit_M(x') + d_1`, for `q < N`,
`fit_N(x_H)(q) = concat_M(max(Z_1, 0), min(mirror_M(Z_1), 0))(q)` and
`ŷ_H(q) = concat_M(max(X_1, 0), min(mirror_M(X_1), 0))(q)`. -/
theorem oddF_W3_of_cut (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) (e : ℤ) (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne)
    (hcut : CutPropP p c (I.erase c) dg (ℓ % p ^ c) e) :
    (∀ q < 2 ^ #I, fit (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) q =
      concat (2 ^ #(I.erase c))
        (fun i => max ((fit (2 ^ #(I.erase c)) (toR (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e)) +
          toR (dWalkP p k I dg ℓ e c)) i) 0)
        (fun i => min (mirror (2 ^ #(I.erase c))
          (fit (2 ^ #(I.erase c)) (toR (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e)) +
            toR (dWalkP p k I dg ℓ e c)) i) 0) q) ∧
    (∀ q < 2 ^ #I, ifit (2 ^ #I) (xHseqP p k I dg ℓ e) q =
      concat (2 ^ #(I.erase c))
        (fun i => max ((ifit (2 ^ #(I.erase c)) (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e) +
          dWalkP p k I dg ℓ e c) i) 0)
        (fun i => min (mirror (2 ^ #(I.erase c))
          (ifit (2 ^ #(I.erase c)) (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e) +
            dWalkP p k I dg ℓ e c) i) 0) q) := by
  have hN := card_erase_max hne hc
  have hW0 := oddF_W0 hI hd hℓ e hne hc
  have hW2 := oddF_W2_of_cut (k := k) hd e c hcut
  set M := 2 ^ #(I.erase c) with hM
  set x' := xHseqP p c (I.erase c) dg (ℓ % p ^ c) e with hx'
  set d := dWalkP p k I dg ℓ e c with hd_def
  set x := xHseqP p k I dg ℓ e with hx
  have hanti : IsAntisymm (2 * M) x := hN ▸ oddF_xH_antisymm p k I dg ℓ e
  rw [hN]
  constructor
  · intro q hq
    rw [lemma_7_3_fit (toR_antisymm hanti) q hq]
    have hf : fit M (toR x) = fit M (toR (x' + d)) :=
      fit_congr fun j hj => by simp [toR, hW0 j hj]
    rw [hf]
    simp only [concat, mirror, Pi.add_apply]
    split_ifs with h
    · rw [hW2.1 q h]; rfl
    · rw [hW2.1 _ (by omega)]; rfl
  · intro q hq
    rw [lemma_7_3_ifit hanti q hq]
    have hf : ifit M x = ifit M (x' + d) :=
      ifit_congr fun j hj => by simp [hW0 j hj]
    rw [hf]
    simp only [concat, mirror, Pi.add_apply]
    split_ifs with h
    · rw [hW2.2 q h]
    · rw [hW2.2 _ (by omega)]

end prime

end ColouredSand.OddTwist
