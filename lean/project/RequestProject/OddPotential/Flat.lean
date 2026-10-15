module

public import RequestProject.OddPotential.LemmaP

/-!
# `CSI16_theorem_F_at_p.md` — *Part P*: Lemma X, Lemma N (no flat) and Lemma F (the central flat)

Base-`p` analogue of `RequestProject/Potential/Junction.lean` and
`RequestProject/Potential/Flat.lean` (C8), with every `α` replaced by `e` (Part Δ, step 4).
Encodings as in `RequestProject/OddPotential/LemmaP.lean`.  In addition:

* `f := min {q < M : X_1(q) ≤ 0}` is a natural number `f` with
  `IsLeast {q | q < M ∧ X_1(q) ≤ 0} f` (it exists exactly when `X_1(M − 1) ≤ 0`:
  `oddF_exists_flat_start`, `oddF_X1_last_nonpos_of_flat`); the flat `F = [f, N − 1 − f]` is the
  set of positions `q` with `f ≤ q ∧ q ≤ N − 1 − f`.
* `loFP … f` and `hiFP … f` are `lo` and `hi` of (F3) (case distinction `f = 0` / `f > 0` as in
  C8); `c_3 = v'(f)`, `c_4 = v'(N − 1 − f)`.
* `flatVP … f cF` is the function `V` of (F4): `cF` on `F` and `v'` elsewhere.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset AntitonicFit TheoremF Potential

/-- (F3) of Lemma F: `lo := max(c_3, v'(N − f))` if `f > 0`, and `lo := c_3` if `f = 0`. -/
def loFP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (c : ℕ) (V' : ℕ → ℤ) (f : ℕ) : ℤ :=
  if f = 0 then vPrimeP p k I dg ℓ e c V' f
  else max (vPrimeP p k I dg ℓ e c V' f) (vPrimeP p k I dg ℓ e c V' (2 ^ #I - f))

/-- (F3) of Lemma F: `hi := min(c_4, v'(f − 1))` if `f > 0`, and `hi := c_4` if `f = 0`. -/
def hiFP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (c : ℕ) (V' : ℕ → ℤ) (f : ℕ) : ℤ :=
  if f = 0 then vPrimeP p k I dg ℓ e c V' (2 ^ #I - 1 - f)
  else min (vPrimeP p k I dg ℓ e c V' (2 ^ #I - 1 - f)) (vPrimeP p k I dg ℓ e c V' (f - 1))

/-- (F4) of Lemma F: `V := c_F` on `F = [f, N − 1 − f]` and `V := v'` elsewhere. -/
def flatVP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) (c : ℕ) (V' : ℕ → ℤ) (f : ℕ)
    (cF : ℤ) : ℕ → ℤ :=
  fun q => if f ≤ q ∧ q ≤ 2 ^ #I - 1 - f then cF else vPrimeP p k I dg ℓ e c V' q

variable {p : ℕ} {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ} {c : ℕ} {V' : ℕ → ℤ}

/-- **Lemma X** (`CSI16_theorem_F_at_p.md`, Part P, as in C8): `X_1` is non-increasing on
`[0, M)`.  (Needs only the digit condition and a potential `V'` for `H'`.) -/
theorem oddF_lemma_X [Fact p.Prime] (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') :
    ∀ q q', q ≤ q' → q' < 2 ^ #(I.erase c) → X1P p k I dg ℓ e c q' ≤ X1P p k I dg ℓ e c q := by
  intro q q' hqq hq'
  have hEp := hV'.E q (by omega)
  have hEq := hV'.E q' hq'
  have h1 := hV'.M q q' hqq hq'
  have h2 := hV'.M (2 ^ #(I.erase c) - 1 - q') (2 ^ #(I.erase c) - 1 - q) (by omega) (by omega)
  have hdd : (dWalkP p k I dg ℓ e c q' : ℝ) ≤ dWalkP p k I dg ℓ e c q :=
    (dWalkP_nonIncr (k := k) (ℓ := ℓ) hd e c).anti hqq hq'
  have hd' : dWalkP p k I dg ℓ e c q' ≤ dWalkP p k I dg ℓ e c q := by exact_mod_cast hdd
  simp only [X1P]
  linarith

section house

variable [Fact p.Prime] (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
  (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (hne : I.Nonempty) (hc : c = I.max' hne)

include hI hd hℓ he hne hc

/-- (W3) on the first half: `ŷ_H(q) = max(X_1(q), 0)` for `q < M`. -/
lemma oddF_yhat_low {q : ℕ} (hq : q < 2 ^ #(I.erase c)) :
    yhatP p k I dg ℓ e q = max (X1P p k I dg ℓ e c q) 0 := by
  have hN := card_erase_max hne hc
  have := (oddF_W3 hI hd hℓ he hne hc).2 q (by omega)
  rw [yhatP, this]
  simp [concat, hq, X1P, yhatP]

/-- (W3) on the second half: `ŷ_H(M + q) = min(−X_1(M − 1 − q), 0)` for `q < M`. -/
lemma oddF_yhat_high {q : ℕ} (hq : q < 2 ^ #(I.erase c)) :
    yhatP p k I dg ℓ e (2 ^ #(I.erase c) + q) =
      min (-X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1 - q)) 0 := by
  have hN := card_erase_max hne hc
  have := (oddF_W3 hI hd hℓ he hne hc).2 (2 ^ #(I.erase c) + q) (by omega)
  rw [yhatP, this]
  simp [concat, mirror, X1P, yhatP]

/-- (E) for `v'` off the central flat ((P2) with (W3)). -/
lemma oddF_vPrime_E_off (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') {q : ℕ}
    (hq : q < 2 ^ #I) (hlow : q < 2 ^ #(I.erase c) → 0 < X1P p k I dg ℓ e c q)
    (hhigh : 2 ^ #(I.erase c) ≤ q → 0 < X1P p k I dg ℓ e c (2 ^ #I - 1 - q)) :
    vPrimeP p k I dg ℓ e c V' q - vPrimeP p k I dg ℓ e c V' (2 ^ #I - 1 - q) =
      yhatP p k I dg ℓ e q := by
  have hN := card_erase_max hne hc
  obtain ⟨hP2a, hP2b⟩ := oddF_P2 (k := k) hne hc hV'
  by_cases hqM : q < 2 ^ #(I.erase c)
  · rw [hP2a q hqM, oddF_yhat_low hI hd hℓ he hne hc hqM, max_eq_left (hlow hqM).le]
  · push_neg at hqM
    obtain ⟨p₀, rfl⟩ := Nat.exists_eq_add_of_le hqM
    have hp₀ : p₀ < 2 ^ #(I.erase c) := by omega
    have e' : 2 ^ #I - 1 - (2 ^ #(I.erase c) + p₀) = 2 ^ #(I.erase c) - 1 - p₀ := by omega
    have h := hhigh hqM
    rw [e'] at h ⊢
    rw [hP2b p₀ hp₀, oddF_yhat_high hI hd hℓ he hne hc hp₀, min_eq_left (by linarith)]

omit he in
/-- (G) for `v'` (consequence of (P1), with `h ≥ 0`). -/
lemma oddF_vPrime_G (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') {q q' : ℕ}
    (harr : IsArrow I q q') :
    vPrimeP p k I dg ℓ e c V' q - vPrimeP p k I dg ℓ e c V' q' ≤ cHatSeqP p k I dg ℓ e q q' := by
  have hqq := harr.lt
  have h0 : (0 : ℤ) ≤ ((k - c : ℕ) : ℤ) := by positivity
  by_cases hq : q < 2 ^ #(I.erase c)
  · have := oddF_P1_low hI hd hℓ hne hc hV' harr hq (by omega); linarith
  · push_neg at hq
    by_cases hq' : q' < 2 ^ #(I.erase c)
    · exact oddF_P1_cross hI hd hℓ hne hc hV' harr hq hq'
    · push_neg at hq'
      have := oddF_P1_high hI hd hℓ hne hc hV' harr hq hq'; linarith

/-- **Lemma N** (no central flat; `CSI16_theorem_F_at_p.md`, Part P): if `X_1(M − 1) > 0`, then
`v'` is a potential for `H`. -/
theorem oddF_lemma_N (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V')
    (hX : 0 < X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1)) :
    IsPotentialP p k I dg ℓ e (vPrimeP p k I dg ℓ e c V') := by
  have hN := card_erase_max hne hc
  have hXm := oddF_lemma_X (k := k) hd hV'
  obtain ⟨hP3a, hP3b⟩ := oddF_P3 (k := k) hd hne hc hV'
  have hP4 := (oddF_P4 hI hd he hne hc hV').1
  refine ⟨fun q hq => ?_, fun q q' hqq hq' => ?_,
    fun q q' harr => oddF_vPrime_G hI hd hℓ hne hc hV' harr⟩
  · apply oddF_vPrime_E_off hI hd hℓ he hne hc hV' hq
    · intro hqM
      have := hXm q (2 ^ #(I.erase c) - 1) (by omega) (by omega); linarith
    · intro hqM
      have := hXm (2 ^ #I - 1 - q) (2 ^ #(I.erase c) - 1) (by omega) (by omega); linarith
  · by_cases hqM : q' < 2 ^ #(I.erase c)
    · exact hP3a q q' hqq hqM
    · push_neg at hqM
      by_cases hpM : 2 ^ #(I.erase c) ≤ q
      · exact hP3b q q' hpM hqq hq'
      · push_neg at hpM
        have h1 := hP3b (2 ^ #(I.erase c)) q' le_rfl hqM hq'
        have h2 := hP3a q (2 ^ #(I.erase c) - 1) (by omega) (by omega)
        linarith

end house

/-- Lemma F: `f = min {q < M : X_1(q) ≤ 0}` exists when `X_1(M − 1) ≤ 0`. -/
theorem oddF_exists_flat_start (hX : X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1) ≤ 0) :
    ∃ f, IsLeast {q | q < 2 ^ #(I.erase c) ∧ X1P p k I dg ℓ e c q ≤ 0} f := by
  have hex : ∃ q, q < 2 ^ #(I.erase c) ∧ X1P p k I dg ℓ e c q ≤ 0 :=
    ⟨_, by have := Nat.two_pow_pos #(I.erase c); omega, hX⟩
  classical
  exact ⟨Nat.find hex, Nat.find_spec hex, fun q hq => Nat.find_min' hex hq⟩

section LemmaF

variable [Fact p.Prime] (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
  (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (hne : I.Nonempty) (hc : c = I.max' hne)
  (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') {f : ℕ}
  (hf : IsLeast {q | q < 2 ^ #(I.erase c) ∧ X1P p k I dg ℓ e c q ≤ 0} f)

include hd hV' hf in
/-- Lemma F: conversely, if `f` exists then `X_1(M − 1) ≤ 0` (by Lemma X); so the hypothesis
`X_1(M − 1) ≤ 0` of Lemma F is equivalent to the existence of `f`. -/
theorem oddF_X1_last_nonpos_of_flat : X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1) ≤ 0 := by
  obtain ⟨⟨hfM, hXf⟩, -⟩ := hf
  have := oddF_lemma_X (k := k) hd hV' f (2 ^ #(I.erase c) - 1) (by omega) (by omega)
  linarith

include hd hV' hf in
/-- `X_1 ≤ 0` exactly on `[f, M)` (proof of (F1)). -/
lemma oddF_X1_nonpos_iff {q : ℕ} (hq : q < 2 ^ #(I.erase c)) :
    X1P p k I dg ℓ e c q ≤ 0 ↔ f ≤ q := by
  obtain ⟨⟨hfM, hXf⟩, hfmin⟩ := hf
  constructor
  · intro h; exact hfmin ⟨hq, h⟩
  · intro h; have := oddF_lemma_X (k := k) hd hV' f q h hq; linarith

include hI hd hℓ he hne hc hV' hf in
/-- **(F1)** of Lemma F (`CSI16_theorem_F_at_p.md`, Part P): for `q < N`, `ŷ_H(q) = 0` if and only
if `q ∈ F = [f, N − 1 − f]`. -/
theorem oddF_F1_flat : ∀ q < 2 ^ #I, yhatP p k I dg ℓ e q = 0 ↔ f ≤ q ∧ q ≤ 2 ^ #I - 1 - f := by
  intro q hq
  have hN := card_erase_max hne hc
  have hfM := hf.1.1
  by_cases hqM : q < 2 ^ #(I.erase c)
  · rw [oddF_yhat_low hI hd hℓ he hne hc hqM, ← oddF_X1_nonpos_iff hd hV' hf hqM]
    constructor
    · intro h; exact ⟨by have := le_max_left (X1P p k I dg ℓ e c q) 0; omega, by omega⟩
    · intro h; exact max_eq_right h.1
  · push_neg at hqM
    obtain ⟨p₀, rfl⟩ := Nat.exists_eq_add_of_le hqM
    have hp₀ : p₀ < 2 ^ #(I.erase c) := by omega
    rw [oddF_yhat_high hI hd hℓ he hne hc hp₀]
    have hiff := oddF_X1_nonpos_iff hd hV' hf (q := 2 ^ #(I.erase c) - 1 - p₀) (by omega)
    constructor
    · intro h
      have : X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1 - p₀) ≤ 0 := by
        by_contra hcon; push_neg at hcon
        have : min (-X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1 - p₀)) 0 < 0 :=
          min_lt_of_left_lt (by linarith)
        omega
      have := hiff.1 this
      omega
    · intro h
      have := hiff.2 (by omega)
      exact min_eq_right (by linarith)

include hd hne hc hV' hf in
/-- **(F2)** of Lemma F (`CSI16_theorem_F_at_p.md`, Part P): `c_3 = v'(f)` is the maximum of `v'`
on `[f, M)`, `c_4 = v'(N − 1 − f)` is the minimum of `v'` on `[M, N − f)`, and
`c_3 − c_4 = X_1(f) ≤ 0`. -/
theorem oddF_F2_flat :
    IsGreatest (vPrimeP p k I dg ℓ e c V' '' Set.Ico f (2 ^ #(I.erase c)))
      (vPrimeP p k I dg ℓ e c V' f) ∧
    IsLeast (vPrimeP p k I dg ℓ e c V' '' Set.Ico (2 ^ #(I.erase c)) (2 ^ #I - f))
      (vPrimeP p k I dg ℓ e c V' (2 ^ #I - 1 - f)) ∧
    vPrimeP p k I dg ℓ e c V' f - vPrimeP p k I dg ℓ e c V' (2 ^ #I - 1 - f) =
      X1P p k I dg ℓ e c f ∧
    X1P p k I dg ℓ e c f ≤ 0 := by
  have hN := card_erase_max hne hc
  obtain ⟨⟨hfM, hXf⟩, -⟩ := hf
  obtain ⟨hP3a, hP3b⟩ := oddF_P3 (k := k) hd hne hc hV'
  refine ⟨⟨⟨f, ⟨le_rfl, hfM⟩, rfl⟩, ?_⟩, ⟨⟨2 ^ #I - 1 - f, ⟨by omega, by omega⟩, rfl⟩, ?_⟩,
    (oddF_P2 (k := k) hne hc hV').1 f hfM, hXf⟩
  · rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    exact hP3a f q hq1 hq2
  · rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    exact hP3b q (2 ^ #I - 1 - f) hq1 (by omega) (by omega)

include hd hne hc hV' hf in
/-- **(F3)** of Lemma F (`CSI16_theorem_F_at_p.md`, Part P): the integer interval `[lo, hi]` is
non-empty, i.e. `lo ≤ hi`. -/
theorem oddF_F3_flat : loFP p k I dg ℓ e c V' f ≤ hiFP p k I dg ℓ e c V' f := by
  have hN := card_erase_max hne hc
  obtain ⟨⟨hfM, hXf⟩, hfmin⟩ := hf
  obtain ⟨hP3a, hP3b⟩ := oddF_P3 (k := k) hd hne hc hV'
  obtain ⟨hP2a, -⟩ := oddF_P2 (k := k) hne hc hV'
  have h34 := hP2a f hfM
  unfold loFP hiFP
  split_ifs with h0
  · linarith
  · have hpos : 0 < X1P p k I dg ℓ e c (f - 1) := by
      by_contra h; push_neg at h; have := hfmin ⟨by omega, h⟩; omega
    have h1 := hP2a (f - 1) (by omega)
    rw [show 2 ^ #I - 1 - (f - 1) = 2 ^ #I - f by omega] at h1
    have h2 := hP3a (f - 1) f (by omega) hfM
    have h3 := hP3b (2 ^ #I - 1 - f) (2 ^ #I - f) (by omega) (by omega) (by omega)
    refine max_le (le_min (by linarith) h2) (le_min h3 (by linarith))

include hI hd hℓ he hne hc hV' hf in
/-- **(F4)** of Lemma F (`CSI16_theorem_F_at_p.md`, Part P): for every integer `c_F` with
`lo ≤ c_F ≤ hi`, the function `V := c_F` on `F`, `V := v'` elsewhere, is a potential for `H`
(the slack `α` of C8 is `e`, through (P4)). -/
theorem oddF_F4_flat (cF : ℤ) (hlo : loFP p k I dg ℓ e c V' f ≤ cF)
    (hhi : cF ≤ hiFP p k I dg ℓ e c V' f) :
    IsPotentialP p k I dg ℓ e (flatVP p k I dg ℓ e c V' f cF) := by
  have hN := card_erase_max hne hc
  have hF1 := oddF_F1_flat hI hd hℓ he hne hc hV' hf
  obtain ⟨⟨hfM, hXf⟩, hfmin⟩ := hf
  have hpos : ∀ q, q < f → 0 < X1P p k I dg ℓ e c q := fun q hq => by
    by_contra h; push_neg at h; have := hfmin ⟨by omega, h⟩; omega
  obtain ⟨hP3a, hP3b⟩ := oddF_P3 (k := k) hd hne hc hV'
  obtain ⟨hP4a, hP4s, hP4t⟩ := oddF_P4 hI hd he hne hc hV'
  have hP4b := hP4s.trans hP4t
  have h34 := (oddF_P2 (k := k) hne hc hV').1 f hfM
  have hc3 : vPrimeP p k I dg ℓ e c V' f ≤ cF := by
    unfold loFP at hlo; split_ifs at hlo
    · exact hlo
    · exact le_trans (le_max_left _ _) hlo
  have hc4 : cF ≤ vPrimeP p k I dg ℓ e c V' (2 ^ #I - 1 - f) := by
    unfold hiFP at hhi; split_ifs at hhi
    · exact hhi
    · exact le_trans hhi (min_le_left _ _)
  have hlo' : 0 < f → vPrimeP p k I dg ℓ e c V' (2 ^ #I - f) ≤ cF := by
    intro h0; unfold loFP at hlo; rw [if_neg (by omega)] at hlo
    exact le_trans (le_max_right _ _) hlo
  have hhi' : 0 < f → cF ≤ vPrimeP p k I dg ℓ e c V' (f - 1) := by
    intro h0; unfold hiFP at hhi; rw [if_neg (by omega)] at hhi
    exact le_trans hhi (min_le_right _ _)
  have hh0 : (0 : ℤ) ≤ ((k - c : ℕ) : ℤ) := by positivity
  set M := 2 ^ #(I.erase c) with hM
  set N := 2 ^ #I with hNdef
  set v := vPrimeP p k I dg ℓ e c V' with hv
  have hc4le : ∀ q, M ≤ q → q < N - f → v (N - 1 - f) ≤ v q := fun q hq1 hq2 =>
    hP3b q (N - 1 - f) hq1 (by omega) (by omega)
  have hlec3 : ∀ q, f ≤ q → q < M → v q ≤ v f := fun q hq1 hq2 => hP3a f q hq1 hq2
  have hvM1 : v (M - 1) ≤ v f := hP3a f (M - 1) (by omega) (by omega)
  have hvM : v (N - 1 - f) ≤ v M := hc4le M le_rfl (by omega)
  refine ⟨fun q hq => ?_, fun q q' hqq hq' => ?_, fun q q' harr => ?_⟩
  · -- (E)
    simp only [flatVP]
    by_cases hqF : f ≤ q ∧ q ≤ N - 1 - f
    · rw [if_pos hqF, if_pos (by omega), sub_self]
      exact ((hF1 q hq).2 hqF).symm
    · rw [if_neg hqF, if_neg (by omega)]
      apply oddF_vPrime_E_off hI hd hℓ he hne hc hV' hq
      · intro hqM; exact hpos q (by omega)
      · intro hqM; exact hpos _ (by omega)
  · -- (M)
    simp only [flatVP]
    by_cases hpF : f ≤ q ∧ q ≤ N - 1 - f <;> by_cases hqF : f ≤ q' ∧ q' ≤ N - 1 - f
    · rw [if_pos hpF, if_pos hqF]
    · rw [if_pos hpF, if_neg hqF]
      have hqf : N - f ≤ q' := by omega
      have := hP3b (N - f) q' (by omega) hqf hq'
      have := hlo' (by omega)
      linarith
    · rw [if_neg hpF, if_pos hqF]
      have hpf : q < f := by omega
      have := hP3a q (f - 1) (by omega) (by omega)
      have := hhi' (by omega)
      linarith
    · rw [if_neg hpF, if_neg hqF]
      by_cases hpf : q < f
      · by_cases hqf : q' < f
        · exact hP3a q q' hqq (by omega)
        · have h1 := hP3b (N - f) q' (by omega) (by omega) hq'
          have h2 := hP3a q (f - 1) (by omega) (by omega)
          have := hlo' (by omega)
          have := hhi' (by omega)
          linarith
      · exact hP3b q q' (by omega) hqq hq'
  · -- (G)
    have hqq := harr.lt
    have hpN := harr.1
    have hG := oddF_vPrime_G hI hd hℓ hne hc hV' harr
    simp only [flatVP]
    by_cases hpF : f ≤ q ∧ q ≤ N - 1 - f <;> by_cases hqF : f ≤ q' ∧ q' ≤ N - 1 - f
    · rw [if_pos hpF, if_pos hqF, sub_self]
      by_cases hpM : q < M
      · have := oddF_P1_low hI hd hℓ hne hc hV' harr hpM (by omega)
        have := hP3a q (M - 1) (by omega) (by omega)
        have := hlec3 q' hqF.1 (by omega)
        linarith
      · push_neg at hpM
        by_cases hqM : q' < M
        · have := hlec3 q' hqF.1 hqM
          have := hc4le q hpM (by omega)
          linarith
        · push_neg at hqM
          have := oddF_P1_high hI hd hℓ hne hc hV' harr hpM hqM
          have := hc4le q hpM (by omega)
          have := hP3b M q' le_rfl hqM (by omega)
          linarith
    · rw [if_pos hpF, if_neg hqF]
      have hqf : q' < f := by omega
      by_cases hpM : q < M
      · have := oddF_P1_low hI hd hℓ hne hc hV' harr hpM (by omega)
        have := hP3a q (M - 1) (by omega) (by omega)
        linarith
      · push_neg at hpM
        have := hc4le q hpM (by omega)
        linarith
    · rw [if_neg hpF, if_pos hqF]
      have hpf : N - f ≤ q := by omega
      by_cases hqM : q' < M
      · have := hlec3 q' hqF.1 hqM
        linarith
      · push_neg at hqM
        have := oddF_P1_high hI hd hℓ hne hc hV' harr (by omega) hqM
        have := hP3b M q' le_rfl hqM (by omega)
        linarith
    · rw [if_neg hpF, if_neg hqF]
      exact hG

include hI hd hℓ he hne hc hV' hf in
/-- **Lemma F** (the central flat; `CSI16_theorem_F_at_p.md`, Part P), all four parts together:
with `f = min {q < M : X_1(q) ≤ 0}` (which exists iff `X_1(M − 1) ≤ 0`), (F1)–(F4) hold. -/
theorem oddF_lemma_F :
    (∀ q < 2 ^ #I, yhatP p k I dg ℓ e q = 0 ↔ f ≤ q ∧ q ≤ 2 ^ #I - 1 - f) ∧
    (IsGreatest (vPrimeP p k I dg ℓ e c V' '' Set.Ico f (2 ^ #(I.erase c)))
        (vPrimeP p k I dg ℓ e c V' f) ∧
      IsLeast (vPrimeP p k I dg ℓ e c V' '' Set.Ico (2 ^ #(I.erase c)) (2 ^ #I - f))
        (vPrimeP p k I dg ℓ e c V' (2 ^ #I - 1 - f)) ∧
      vPrimeP p k I dg ℓ e c V' f - vPrimeP p k I dg ℓ e c V' (2 ^ #I - 1 - f) =
        X1P p k I dg ℓ e c f ∧
      X1P p k I dg ℓ e c f ≤ 0) ∧
    loFP p k I dg ℓ e c V' f ≤ hiFP p k I dg ℓ e c V' f ∧
    (∀ cF : ℤ, loFP p k I dg ℓ e c V' f ≤ cF → cF ≤ hiFP p k I dg ℓ e c V' f →
      IsPotentialP p k I dg ℓ e (flatVP p k I dg ℓ e c V' f cF)) :=
  ⟨oddF_F1_flat hI hd hℓ he hne hc hV' hf, oddF_F2_flat hd hne hc hV' hf,
    oddF_F3_flat hd hne hc hV' hf,
    fun cF h1 h2 => oddF_F4_flat hI hd hℓ he hne hc hV' hf cF h1 h2⟩

end LemmaF

end ColouredSand.OddTwist
