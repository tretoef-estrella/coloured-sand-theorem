module

public import RequestProject.Potential.LemmaP

/-!
# Part 2 of `C8_theorem_F_potential.md`: Lemma X and Lemma N (no central flat)

Encodings as in `RequestProject/Potential/Basic.lean`; `c = max I` is `hne : I.Nonempty`,
`hc : c = I.max' hne`, `M = 2 ^ #(I.erase c)`, `N = 2 ^ #I`, and `V'` is a potential for
`H' = (I.erase c, c, ℓ % 2 ^ c, α)`.
-/

@[expose] public section

namespace Potential

open Finset AntitonicFit TheoremF

variable {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} {c : ℕ} {V' : ℕ → ℤ}

/-- **Lemma X** (`C8_theorem_F_potential.md`): `X_1` is non-increasing on `[0, M)`, because
`ŷ'(p) = V'(p) − V'(M − 1 − p)` by (E) for `V'`, which is non-increasing in `p` by (M) for `V'`,
and `d` is non-increasing by (W1) of C7.  (More general than the file: needs no house condition and
no `c = max I`.) -/
theorem lemma_X (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') :
    ∀ p q, p ≤ q → q < 2 ^ #(I.erase c) → X1 I k ℓ α c q ≤ X1 I k ℓ α c p := by
  intro p q hpq hq
  have hEp := hV'.E p (by omega)
  have hEq := hV'.E q hq
  have h1 := hV'.M p q hpq hq
  have h2 := hV'.M (2 ^ #(I.erase c) - 1 - q) (2 ^ #(I.erase c) - 1 - p) (by omega) (by omega)
  have hd : (dWalk I k ℓ α c q : ℝ) ≤ dWalk I k ℓ α c p :=
    (dWalk_nonIncr (I := I) (k := k) (ℓ := ℓ) α c).anti hpq hq
  have hd' : dWalk I k ℓ α c q ≤ dWalk I k ℓ α c p := by exact_mod_cast hd
  simp only [X1]
  linarith

/-- (W3) of C7 on the first half, as used in Part 2 of `C8_theorem_F_potential.md`:
`ŷ_H(p) = max(X_1(p), 0)` for `p < M`. -/
lemma yhat_low (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty)
    (hc : c = I.max' hne) {p : ℕ} (hp : p < 2 ^ #(I.erase c)) :
    yhat I k ℓ α p = max (X1 I k ℓ α c p) 0 := by
  have hN := card_erase_max hne hc
  have := (theorem_F0_W3 hI hℓ hα hne hc).2 p (by omega)
  rw [yhat, this]
  simp [concat, hp, X1, yhat]

/-- (W3) of C7 on the second half, as used in Part 2 of `C8_theorem_F_potential.md`:
`ŷ_H(M + p) = min(−X_1(M − 1 − p), 0)` for `p < M`. -/
lemma yhat_high (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty)
    (hc : c = I.max' hne) {p : ℕ} (hp : p < 2 ^ #(I.erase c)) :
    yhat I k ℓ α (2 ^ #(I.erase c) + p) = min (-X1 I k ℓ α c (2 ^ #(I.erase c) - 1 - p)) 0 := by
  have hN := card_erase_max hne hc
  have := (theorem_F0_W3 hI hℓ hα hne hc).2 (2 ^ #(I.erase c) + p) (by omega)
  rw [yhat, this]
  simp [concat, mirror, X1, yhat]

/-- (E) for `v'` off the central flat (proof of Lemmas N and F, `C8_theorem_F_potential.md`):
for `p < N`, if `X_1(p) > 0` when `p < M` and `X_1(N − 1 − p) > 0` when `p ≥ M`, then
`v'(p) − v'(N − 1 − p) = ŷ_H(p)`.  This is (P2) together with (W3) of C7. -/
lemma vPrime_E_off (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty)
    (hc : c = I.max' hne) (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') {p : ℕ}
    (hp : p < 2 ^ #I) (hlow : p < 2 ^ #(I.erase c) → 0 < X1 I k ℓ α c p)
    (hhigh : 2 ^ #(I.erase c) ≤ p → 0 < X1 I k ℓ α c (2 ^ #I - 1 - p)) :
    vPrime I k ℓ α c V' p - vPrime I k ℓ α c V' (2 ^ #I - 1 - p) = yhat I k ℓ α p := by
  have hN := card_erase_max hne hc
  obtain ⟨hP2a, hP2b⟩ := lemma_P2 (k := k) hne hc hV'
  by_cases hpM : p < 2 ^ #(I.erase c)
  · rw [hP2a p hpM, yhat_low hI hℓ hα hne hc hpM, max_eq_left (hlow hpM).le]
  · push_neg at hpM
    obtain ⟨p₀, rfl⟩ := Nat.exists_eq_add_of_le hpM
    have hp₀ : p₀ < 2 ^ #(I.erase c) := by omega
    have e : 2 ^ #I - 1 - (2 ^ #(I.erase c) + p₀) = 2 ^ #(I.erase c) - 1 - p₀ := by omega
    have h := hhigh hpM
    rw [e] at h ⊢
    rw [hP2b p₀ hp₀, yhat_high hI hℓ hα hne hc hp₀, min_eq_left (by linarith)]

/-- (G) for `v'` (consequence of (P1) of Lemma P, `C8_theorem_F_potential.md`, with `h ≥ 0`):
for every arrow `p → q`, `v'(p) − v'(q) ≤ ĉ_H(p, q)`. -/
lemma vPrime_G (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hne : I.Nonempty)
    (hc : c = I.max' hne) (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') {p q : ℕ}
    (harr : IsArrow I p q) :
    vPrime I k ℓ α c V' p - vPrime I k ℓ α c V' q ≤ cHat I k ℓ α p q := by
  have hqp := harr.lt
  have h0 : (0 : ℤ) ≤ ((k - c : ℕ) : ℤ) := by positivity
  by_cases hp : p < 2 ^ #(I.erase c)
  · have := lemma_P1_low hI hℓ hne hc hV' harr hp (by omega); linarith
  · push_neg at hp
    by_cases hq : q < 2 ^ #(I.erase c)
    · exact lemma_P1_cross hI hℓ hne hc hV' harr hp hq
    · push_neg at hq
      have := lemma_P1_high hI hℓ hne hc hV' harr hp hq; linarith

/-- **Lemma N** (no central flat, step 6 of `C8_theorem_F_potential.md`): if `X_1(M − 1) > 0`,
then `v'` is a potential for `H`. -/
theorem lemma_N (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty)
    (hc : c = I.max' hne) (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V')
    (hX : 0 < X1 I k ℓ α c (2 ^ #(I.erase c) - 1)) :
    IsPotential I k ℓ α (vPrime I k ℓ α c V') := by
  have hN := card_erase_max hne hc
  have hXm := lemma_X (k := k) hV'
  obtain ⟨hP3a, hP3b⟩ := lemma_P3 (k := k) hne hc hV'
  have hP4 := (lemma_P4 hI hα hne hc hV').1
  refine ⟨fun p hp => ?_, fun p q hpq hq => ?_, fun p q harr => vPrime_G hI hℓ hne hc hV' harr⟩
  · apply vPrime_E_off hI hℓ hα hne hc hV' hp
    · intro hpM
      have := hXm p (2 ^ #(I.erase c) - 1) (by omega) (by omega); linarith
    · intro hpM
      have := hXm (2 ^ #I - 1 - p) (2 ^ #(I.erase c) - 1) (by omega) (by omega); linarith
  · by_cases hqM : q < 2 ^ #(I.erase c)
    · exact hP3a p q hpq hqM
    · push_neg at hqM
      by_cases hpM : 2 ^ #(I.erase c) ≤ p
      · exact hP3b p q hpM hpq hq
      · push_neg at hpM
        have h1 := hP3b (2 ^ #(I.erase c)) q le_rfl hqM hq
        have h2 := hP3a p (2 ^ #(I.erase c) - 1) (by omega) (by omega)
        linarith

end Potential
