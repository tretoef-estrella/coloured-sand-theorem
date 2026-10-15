module

public import RequestProject.OddDance.Additive
public import RequestProject.OddDance.Rule

/-!
# `CSI6_the_dance_lattices.md`, Part L — the dance lattices `L(λ)`

Namespace `ColouredSand.OddTwist`. Reuses C18 `delta`, CSI1 `twist`, CSI3 `psi`.

Encodings:
* The paper's `λ` is written `l`; `d₀ = (l + 1) % p`, `b = (l + 1) / p − 1`.
* **(L1)** `danceL p l : DPLattice ℤ_[p]` is defined by well-founded recursion on `l`:
  `delta ℤ_[p] l` if `l + 1 < p`; otherwise `twist p (danceL p b)` if `d₀ = 0`, and
  `psi p (danceL p b) d₀ _ _` if `d₀ ≠ 0` (then `1 ≤ d₀ ≤ p − 1`; the proof arguments of `psi`
  are irrelevant). The three defining equations are `danceL_lt`, `danceL_d0_zero` and
  `danceL_d0_pos`. The forms `danceL_twist_eq` (`danceL p (p b + p − 1) = twist p (danceL p b)`)
  and `danceL_psi_eq` (`danceL p (d + p (b + 1) − 1) = psi p (danceL p b) d _ _`) are the ones
  used in Part R.
* **(L2)** `card_danceL`: `Fintype.card (danceL p l).ι = rankL p l`, and with `rankL_digits`
  (in `Rule.lean`) the digit formula `card_danceL_digits`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice

variable (p : ℕ) [Fact p.Prime]

lemma two_le_prime : 2 ≤ p := (Fact.out : p.Prime).two_le

/-- **(L1)** (Part L of `CSI6_the_dance_lattices.md`) **the dance lattice** `L(λ)`:
`Δ(λ)` if `λ + 1 < p`; otherwise, writing `λ + 1 = d₀ + p (b + 1)` with `d₀ = (λ + 1) % p`,
`b = (λ + 1)/p − 1`: `Φ_p(L(b)) = twist p (danceL p b)` if `d₀ = 0`, and
`Ψ_{d₀}(L(b)) = psi p (danceL p b) d₀` if `1 ≤ d₀ ≤ p − 1`. -/
def danceL (l : ℕ) : DPLattice ℤ_[p] :=
  if _h : l + 1 < p then delta ℤ_[p] l
  else if _hd : (l + 1) % p = 0 then twist p (danceL ((l + 1) / p - 1))
  else psi p (danceL ((l + 1) / p - 1)) ((l + 1) % p) (by omega)
    (by have := Nat.mod_lt (l + 1) (show 0 < p by have := two_le_prime p; omega); omega)
termination_by l
decreasing_by
  all_goals exact b_lt (two_le_prime p) (by have := two_le_prime p; omega)

/-- **(L1)** first defining equation: `danceL p λ = delta ℤ_[p] λ` if `λ + 1 < p`. -/
theorem danceL_lt {l : ℕ} (h : l + 1 < p) : danceL p l = delta ℤ_[p] l := by
  rw [danceL, dif_pos h]

/-- **(L1)** second defining equation: if `λ + 1 ≥ p` and `d₀ = 0`,
`danceL p λ = twist p (danceL p b)`. -/
theorem danceL_d0_zero {l : ℕ} (h : ¬ l + 1 < p) (hd : (l + 1) % p = 0) :
    danceL p l = twist p (danceL p ((l + 1) / p - 1)) := by
  rw [danceL, dif_neg h, dif_pos hd]

/-- **(L1)** third defining equation: if `λ + 1 ≥ p` and `1 ≤ d₀ ≤ p − 1`,
`danceL p λ = psi p d₀ (danceL p b)`. -/
theorem danceL_d0_pos {l : ℕ} (h : ¬ l + 1 < p) (hd1 : 1 ≤ (l + 1) % p)
    (hd2 : (l + 1) % p ≤ p - 1) :
    danceL p l = psi p (danceL p ((l + 1) / p - 1)) ((l + 1) % p) hd1 hd2 := by
  rw [danceL, dif_neg h, dif_neg (by omega)]

/-- (L1), the form used in Part R: `danceL p (p b + p − 1) = twist p (danceL p b)`. -/
theorem danceL_twist_eq (b : ℕ) : danceL p (p * b + p - 1) = twist p (danceL p b) := by
  have hp := two_le_prime p
  have h1 : p * b + p - 1 + 1 = p * (b + 1) := by rw [Nat.mul_succ]; omega
  rw [danceL_d0_zero p (by rw [h1]; nlinarith) (by rw [h1]; simp), h1,
    Nat.mul_div_cancel_left _ (by omega), Nat.add_sub_cancel]

/-- (L1), the form used in Part R: for `1 ≤ d ≤ p − 1`,
`danceL p (d + p (b + 1) − 1) = psi p (danceL p b) d`. -/
theorem danceL_psi_eq (b d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ p - 1) :
    danceL p (d + p * (b + 1) - 1) = psi p (danceL p b) d hd1 hd2 := by
  have hp := two_le_prime p
  have h1 : d + p * (b + 1) - 1 + 1 = d + p * (b + 1) := by omega
  have hmod : (d + p * (b + 1)) % p = d := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (d + p * (b + 1)) / p = b + 1 := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  rw [danceL_d0_pos p (by rw [h1]; nlinarith) (by rw [h1, hmod]; exact hd1)
    (by rw [h1, hmod]; exact hd2)]
  rw [psi_congr p _ (show (d + p * (b + 1) - 1 + 1) % p = d by rw [h1, hmod]) _ _ hd1 hd2]
  congr 1
  rw [h1, hdiv, Nat.add_sub_cancel]

/-! ### (L2) the rank (with CSI4's `card_twist`, `card_psi`) -/

lemma card_delta (l : ℕ) : Fintype.card (delta ℤ_[p] l).ι = l + 1 := by
  rw [show Fintype.card (delta ℤ_[p] l).ι = Fintype.card (Fin (l + 1)) from
    Fintype.card_congr (Equiv.refl _), Fintype.card_fin]

/-- **(L2)** (Part L of `CSI6_the_dance_lattices.md`), recursive form:
`Fintype.card (danceL p λ).ι = rankL p λ`. -/
theorem card_danceL (l : ℕ) : Fintype.card (danceL p l).ι = rankL p l := by
  have hp := two_le_prime p
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    by_cases h : l + 1 < p
    · rw [rankL_lt h, danceL_lt p h, card_delta]
    · have hb := ih _ (b_lt hp (by omega))
      by_cases hd : (l + 1) % p = 0
      · rw [danceL_d0_zero p h hd, rankL_d0_zero hp h hd, card_twist, hb]
      · have := Nat.mod_lt (l + 1) (show 0 < p by omega)
        rw [danceL_d0_pos p h (by omega) (by omega), rankL_d0_pos hp h hd, card_psi, hb, mul_assoc]

/-- **(L2)** (Part L of `CSI6_the_dance_lattices.md`), the digit formula: write
`λ + 1 = Σ_{t ≤ k} d_t p^t` in base `p` (`Nat.digits p (λ + 1)`, least significant digit first,
`d_k ≠ 0`), and `I = {t < k : d_t ≠ 0}`; then
`Fintype.card (danceL p λ).ι = d_k · p^k · 2^{|I|}`. -/
theorem card_danceL_digits (l : ℕ) :
    let ds := Nat.digits p (l + 1)
    let k := ds.length - 1
    Fintype.card (danceL p l).ι = ds.getD k 0 * p ^ k *
      2 ^ ((Finset.range k).filter (fun t => ds.getD t 0 ≠ 0)).card := by
  rw [card_danceL]
  exact rankL_digits (two_le_prime p) l

end ColouredSand.OddTwist
