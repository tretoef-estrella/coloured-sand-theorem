module

public import RequestProject.OddTheoremI.Basic
public import RequestProject.OddDance.Lattice

/-!
# `CSI10_theorem_Dp_and_theorem_I.md`, Setting — the digits of `λ + 1` along the recursion of `danceL`

Namespace `ColouredSand.OddTwist`. For `p ≥ 2` and `λ ≥ p − 1` (written `¬ λ + 1 < p`, as in CSI6),
with `d₀ = (λ + 1) % p` and `b = (λ + 1)/p − 1` (so that `b + 1 = (λ + 1)/p`), the digits of `b + 1`
are the digits of `λ + 1` shifted by one: `digitL_step_zero`, `digitL_step_succ`, `kTop_step`,
`Iset_card_step`. For `λ + 1 < p`: `kTop_small`, `digitL_small`, `Iset_card_small`. The rank of
`danceL p λ` in these terms is `card_danceL_kTop` (from CSI6's `card_danceL_digits`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

variable {p : ℕ}

lemma digits_small {l : ℕ} (h : l + 1 < p) : Nat.digits p (l + 1) = [l + 1] :=
  Nat.digits_of_lt p (l + 1) (by omega) h

lemma kTop_small {l : ℕ} (h : l + 1 < p) : kTop p l = 0 := by
  simp [kTop, digits_small h]

lemma digitL_small {l : ℕ} (h : l + 1 < p) : digitL p l 0 = l + 1 := by
  simp [digitL, digits_small h]

lemma Iset_card_small {l : ℕ} (h : l + 1 < p) : (Iset p l).card = 0 := by
  simp [Iset, kTop_small h]

lemma succ_div_eq (hp : 2 ≤ p) {l : ℕ} (h : ¬ l + 1 < p) : (l + 1) / p - 1 + 1 = (l + 1) / p := by
  have : 1 ≤ (l + 1) / p := (Nat.one_le_div_iff (by omega)).mpr (by omega)
  omega

lemma digits_step (hp : 2 ≤ p) {l : ℕ} (h : ¬ l + 1 < p) :
    Nat.digits p (l + 1) = (l + 1) % p :: Nat.digits p ((l + 1) / p - 1 + 1) := by
  rw [succ_div_eq hp h]
  exact Nat.digits_def' (by omega) (by omega)

lemma digitL_step_zero (hp : 2 ≤ p) {l : ℕ} (h : ¬ l + 1 < p) : digitL p l 0 = (l + 1) % p := by
  simp [digitL, digits_step hp h]

lemma digitL_step_succ (hp : 2 ≤ p) {l : ℕ} (h : ¬ l + 1 < p) (t : ℕ) :
    digitL p l (t + 1) = digitL p ((l + 1) / p - 1) t := by
  simp [digitL, digits_step hp h]

lemma kTop_step (hp : 2 ≤ p) {l : ℕ} (h : ¬ l + 1 < p) :
    kTop p l = kTop p ((l + 1) / p - 1) + 1 := by
  have hne : Nat.digits p ((l + 1) / p - 1 + 1) ≠ [] :=
    Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have := List.length_pos_of_ne_nil hne
  simp only [kTop, digits_step hp h, List.length_cons]
  omega

lemma digitL_step_top (hp : 2 ≤ p) {l : ℕ} (h : ¬ l + 1 < p) :
    digitL p l (kTop p l) = digitL p ((l + 1) / p - 1) (kTop p ((l + 1) / p - 1)) := by
  rw [kTop_step hp h, digitL_step_succ hp h]

lemma Iset_card_step (hp : 2 ≤ p) {l : ℕ} (h : ¬ l + 1 < p) :
    (Iset p l).card = (Iset p ((l + 1) / p - 1)).card + (if (l + 1) % p = 0 then 0 else 1) := by
  simp only [Iset, Finset.card_filter]
  rw [kTop_step hp h, Finset.sum_range_succ']
  simp only [digitL_step_succ hp h, digitL_step_zero hp h]
  by_cases hd : (l + 1) % p = 0 <;> simp [hd]

/-- The leading digit is nonzero. -/
lemma digitL_top_ne_zero (p l : ℕ) : digitL p l (kTop p l) ≠ 0 :=
  leading_digit_ne_zero p l

/-- The rank of `danceL p λ` (CSI6 (L2), `card_danceL_digits`): `d_k · p^k · 2^{|I|}`. -/
lemma card_danceL_kTop (p : ℕ) [Fact p.Prime] (l : ℕ) :
    Fintype.card (danceL p l).ι = digitL p l (kTop p l) * p ^ kTop p l * 2 ^ (Iset p l).card :=
  card_danceL_digits p l

end ColouredSand.OddTwist
