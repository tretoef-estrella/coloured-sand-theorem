module

public import RequestProject.Potential.Junction

/-!
# Part 2 of `C8_theorem_F_potential.md`: Lemma F (the central flat)

Encodings as in `RequestProject/Potential/Basic.lean`.  In addition:

* `f := min {p < M : X_1(p) ≤ 0}` is given as a natural number `f` with
  `IsLeast {p | p < M ∧ X_1(p) ≤ 0} f` (it exists exactly when `X_1(M − 1) ≤ 0`, see
  `exists_flat_start` and `X1_last_nonpos_of_flat`); the flat `F = [f, N − 1 − f]` is the set
  of positions `p` with
  `f ≤ p ∧ p ≤ N − 1 − f`.
* `loF … f` and `hiF … f` are `lo` and `hi` of (F3) (with the case distinction `f = 0` /
  `f > 0` of the file); `c_3 = v'(f)` and `c_4 = v'(N − 1 − f)`.
* `flatV … f cF` is the function `V` of (F4): `cF` on `F` and `v'` elsewhere.
-/

@[expose] public section

namespace Potential

open Finset AntitonicFit TheoremF

/-- (F3) of Lemma F (`C8_theorem_F_potential.md`): `lo := max(c_3, v'(N − f))` if `f > 0`, and
`lo := c_3` if `f = 0`, where `c_3 = v'(f)`. -/
def loF (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c : ℕ) (V' : ℕ → ℤ) (f : ℕ) : ℤ :=
  if f = 0 then vPrime I k ℓ α c V' f
  else max (vPrime I k ℓ α c V' f) (vPrime I k ℓ α c V' (2 ^ #I - f))

/-- (F3) of Lemma F (`C8_theorem_F_potential.md`): `hi := min(c_4, v'(f − 1))` if `f > 0`, and
`hi := c_4` if `f = 0`, where `c_4 = v'(N − 1 − f)`. -/
def hiF (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c : ℕ) (V' : ℕ → ℤ) (f : ℕ) : ℤ :=
  if f = 0 then vPrime I k ℓ α c V' (2 ^ #I - 1 - f)
  else min (vPrime I k ℓ α c V' (2 ^ #I - 1 - f)) (vPrime I k ℓ α c V' (f - 1))

/-- (F4) of Lemma F (`C8_theorem_F_potential.md`): `V := c_F` on `F = [f, N − 1 − f]` and
`V := v'` elsewhere. -/
def flatV (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c : ℕ) (V' : ℕ → ℤ) (f : ℕ) (cF : ℤ) : ℕ → ℤ :=
  fun p => if f ≤ p ∧ p ≤ 2 ^ #I - 1 - f then cF else vPrime I k ℓ α c V' p

variable {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} {c : ℕ} {V' : ℕ → ℤ}

/-- Lemma F (`C8_theorem_F_potential.md`): `f = min {p < M : X_1(p) ≤ 0}` exists when
`X_1(M − 1) ≤ 0`. (Needs nothing else.) -/
theorem exists_flat_start (hX : X1 I k ℓ α c (2 ^ #(I.erase c) - 1) ≤ 0) :
    ∃ f, IsLeast {p | p < 2 ^ #(I.erase c) ∧ X1 I k ℓ α c p ≤ 0} f := by
  have hex : ∃ p, p < 2 ^ #(I.erase c) ∧ X1 I k ℓ α c p ≤ 0 :=
    ⟨_, by have := Nat.two_pow_pos #(I.erase c); omega, hX⟩
  classical
  exact ⟨Nat.find hex, Nat.find_spec hex, fun p hp => Nat.find_min' hex hp⟩

section LemmaF

variable (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty)
  (hc : c = I.max' hne) (hV' : IsPotential (I.erase c) c (ℓ % 2 ^ c) α V') {f : ℕ}
  (hf : IsLeast {p | p < 2 ^ #(I.erase c) ∧ X1 I k ℓ α c p ≤ 0} f)

include hV' hf in
/-- Lemma F (`C8_theorem_F_potential.md`): conversely, if `f = min {p < M : X_1(p) ≤ 0}` exists,
then `X_1(M − 1) ≤ 0` (by Lemma X); so the hypothesis `X_1(M − 1) ≤ 0` of Lemma F is equivalent to
the existence of `f`. -/
theorem X1_last_nonpos_of_flat : X1 I k ℓ α c (2 ^ #(I.erase c) - 1) ≤ 0 := by
  obtain ⟨⟨hfM, hXf⟩, -⟩ := hf
  have := lemma_X (k := k) hV' f (2 ^ #(I.erase c) - 1) (by omega) (by omega)
  linarith

include hV' hf in
/-- `X_1 ≤ 0` exactly on `[f, M)` (proof of (F1), `C8_theorem_F_potential.md`). -/
lemma X1_nonpos_iff {p : ℕ} (hp : p < 2 ^ #(I.erase c)) : X1 I k ℓ α c p ≤ 0 ↔ f ≤ p := by
  obtain ⟨⟨hfM, hXf⟩, hfmin⟩ := hf
  constructor
  · intro h; exact hfmin ⟨hp, h⟩
  · intro h; have := lemma_X (k := k) hV' f p h hp; linarith

include hI hℓ hα hne hc hV' hf in
/-- **(F1)** of Lemma F (`C8_theorem_F_potential.md`): for `p < N`, `ŷ_H(p) = 0` if and only if
`p ∈ F = [f, N − 1 − f]`.  (The hypothesis `X_1(M − 1) ≤ 0` of the file is implied by the
existence of `f`.) -/
theorem lemma_F1 : ∀ p < 2 ^ #I, yhat I k ℓ α p = 0 ↔ f ≤ p ∧ p ≤ 2 ^ #I - 1 - f := by
  intro p hp
  have hN := card_erase_max hne hc
  have hfM := hf.1.1
  by_cases hpM : p < 2 ^ #(I.erase c)
  · rw [yhat_low hI hℓ hα hne hc hpM, ← X1_nonpos_iff hV' hf hpM]
    constructor
    · intro h; exact ⟨by have := le_max_left (X1 I k ℓ α c p) 0; omega, by omega⟩
    · intro h; exact max_eq_right h.1
  · push_neg at hpM
    obtain ⟨p₀, rfl⟩ := Nat.exists_eq_add_of_le hpM
    have hp₀ : p₀ < 2 ^ #(I.erase c) := by omega
    rw [yhat_high hI hℓ hα hne hc hp₀]
    have hiff := X1_nonpos_iff hV' hf (p := 2 ^ #(I.erase c) - 1 - p₀) (by omega)
    constructor
    · intro h
      have : X1 I k ℓ α c (2 ^ #(I.erase c) - 1 - p₀) ≤ 0 := by
        have := min_le_left (-X1 I k ℓ α c (2 ^ #(I.erase c) - 1 - p₀)) 0
        by_contra hcon; push_neg at hcon
        have : min (-X1 I k ℓ α c (2 ^ #(I.erase c) - 1 - p₀)) 0 < 0 :=
          min_lt_of_left_lt (by linarith)
        omega
      have := hiff.1 this
      omega
    · intro h
      have := hiff.2 (by omega)
      exact min_eq_right (by linarith)

include hne hc hV' hf in
/-- **(F2)** of Lemma F (`C8_theorem_F_potential.md`): `c_3 = v'(f)` is the maximum of `v'` on
`[f, M)`, `c_4 = v'(N − 1 − f)` is the minimum of `v'` on `[M, N − f)`, and
`c_3 − c_4 = X_1(f) ≤ 0`.  (Only `c = max I`, (E) and (M) for `V'` are used: no house condition.) -/
theorem lemma_F2 :
    IsGreatest (vPrime I k ℓ α c V' '' Set.Ico f (2 ^ #(I.erase c))) (vPrime I k ℓ α c V' f) ∧
    IsLeast (vPrime I k ℓ α c V' '' Set.Ico (2 ^ #(I.erase c)) (2 ^ #I - f))
      (vPrime I k ℓ α c V' (2 ^ #I - 1 - f)) ∧
    vPrime I k ℓ α c V' f - vPrime I k ℓ α c V' (2 ^ #I - 1 - f) = X1 I k ℓ α c f ∧
    X1 I k ℓ α c f ≤ 0 := by
  have hN := card_erase_max hne hc
  obtain ⟨⟨hfM, hXf⟩, -⟩ := hf
  obtain ⟨hP3a, hP3b⟩ := lemma_P3 (k := k) hne hc hV'
  refine ⟨⟨⟨f, ⟨le_rfl, hfM⟩, rfl⟩, ?_⟩, ⟨⟨2 ^ #I - 1 - f, ⟨by omega, by omega⟩, rfl⟩, ?_⟩,
    (lemma_P2 (k := k) hne hc hV').1 f hfM, hXf⟩
  · rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact hP3a f p hp1 hp2
  · rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact hP3b p (2 ^ #I - 1 - f) hp1 (by omega) (by omega)

include hne hc hV' hf in
/-- **(F3)** of Lemma F (`C8_theorem_F_potential.md`): the integer interval `[lo, hi]` is
non-empty, i.e. `lo ≤ hi`.  (Only `c = max I`, (E) and (M) for `V'` are used: no house
condition.) -/
theorem lemma_F3 : loF I k ℓ α c V' f ≤ hiF I k ℓ α c V' f := by
  have hN := card_erase_max hne hc
  obtain ⟨⟨hfM, hXf⟩, hfmin⟩ := hf
  obtain ⟨hP3a, hP3b⟩ := lemma_P3 (k := k) hne hc hV'
  obtain ⟨hP2a, -⟩ := lemma_P2 (k := k) hne hc hV'
  have h34 := hP2a f hfM
  unfold loF hiF
  split_ifs with h0
  · linarith
  · have hpos : 0 < X1 I k ℓ α c (f - 1) := by
      by_contra h; push_neg at h; have := hfmin ⟨by omega, h⟩; omega
    have h1 := hP2a (f - 1) (by omega)
    rw [show 2 ^ #I - 1 - (f - 1) = 2 ^ #I - f by omega] at h1
    have h2 := hP3a (f - 1) f (by omega) hfM
    have h3 := hP3b (2 ^ #I - 1 - f) (2 ^ #I - f) (by omega) (by omega) (by omega)
    refine max_le (le_min (by linarith) h2) (le_min h3 (by linarith))

include hI hℓ hα hne hc hV' hf in
/-- **(F4)** of Lemma F (`C8_theorem_F_potential.md`): for every integer `c_F` with
`lo ≤ c_F ≤ hi`, the function `V := c_F` on `F`, `V := v'` elsewhere, is a potential for `H`. -/
theorem lemma_F4 (cF : ℤ) (hlo : loF I k ℓ α c V' f ≤ cF) (hhi : cF ≤ hiF I k ℓ α c V' f) :
    IsPotential I k ℓ α (flatV I k ℓ α c V' f cF) := by
  have hN := card_erase_max hne hc
  have hF1 := lemma_F1 hI hℓ hα hne hc hV' hf
  obtain ⟨⟨hfM, hXf⟩, hfmin⟩ := hf
  have hpos : ∀ p, p < f → 0 < X1 I k ℓ α c p := fun p hp => by
    by_contra h; push_neg at h; have := hfmin ⟨by omega, h⟩; omega
  obtain ⟨hP3a, hP3b⟩ := lemma_P3 (k := k) hne hc hV'
  obtain ⟨hP4a, hP4b⟩ := lemma_P4 hI hα hne hc hV'
  have h34 := (lemma_P2 (k := k) hne hc hV').1 f hfM
  have hc3 : vPrime I k ℓ α c V' f ≤ cF := by
    unfold loF at hlo; split_ifs at hlo
    · exact hlo
    · exact le_trans (le_max_left _ _) hlo
  have hc4 : cF ≤ vPrime I k ℓ α c V' (2 ^ #I - 1 - f) := by
    unfold hiF at hhi; split_ifs at hhi
    · exact hhi
    · exact le_trans hhi (min_le_left _ _)
  have hlo' : 0 < f → vPrime I k ℓ α c V' (2 ^ #I - f) ≤ cF := by
    intro h0; unfold loF at hlo; rw [if_neg (by omega)] at hlo
    exact le_trans (le_max_right _ _) hlo
  have hhi' : 0 < f → cF ≤ vPrime I k ℓ α c V' (f - 1) := by
    intro h0; unfold hiF at hhi; rw [if_neg (by omega)] at hhi
    exact le_trans hhi (min_le_right _ _)
  have hh0 : (0 : ℤ) ≤ ((k - c : ℕ) : ℤ) := by positivity
  set M := 2 ^ #(I.erase c) with hM
  set N := 2 ^ #I with hNdef
  set v := vPrime I k ℓ α c V' with hv
  -- `c_4 ≤ v'` on `[M, N − f)`, `v' ≤ c_3` on `[f, M)`
  have hc4le : ∀ p, M ≤ p → p < N - f → v (N - 1 - f) ≤ v p := fun p hp1 hp2 =>
    hP3b p (N - 1 - f) hp1 (by omega) (by omega)
  have hlec3 : ∀ p, f ≤ p → p < M → v p ≤ v f := fun p hp1 hp2 => hP3a f p hp1 hp2
  have hvM1 : v (M - 1) ≤ v f := hP3a f (M - 1) (by omega) (by omega)
  have hvM : v (N - 1 - f) ≤ v M := hc4le M le_rfl (by omega)
  refine ⟨fun p hp => ?_, fun p q hpq hq => ?_, fun p q harr => ?_⟩
  · -- (E)
    simp only [flatV]
    by_cases hpF : f ≤ p ∧ p ≤ N - 1 - f
    · rw [if_pos hpF, if_pos (by omega), sub_self]
      exact ((hF1 p hp).2 hpF).symm
    · rw [if_neg hpF, if_neg (by omega)]
      apply vPrime_E_off hI hℓ hα hne hc hV' hp
      · intro hpM; exact hpos p (by omega)
      · intro hpM; exact hpos _ (by omega)
  · -- (M)
    simp only [flatV]
    by_cases hpF : f ≤ p ∧ p ≤ N - 1 - f <;> by_cases hqF : f ≤ q ∧ q ≤ N - 1 - f
    · rw [if_pos hpF, if_pos hqF]
    · rw [if_pos hpF, if_neg hqF]
      have hqf : N - f ≤ q := by omega
      have := hP3b (N - f) q (by omega) hqf hq
      have := hlo' (by omega)
      linarith
    · rw [if_neg hpF, if_pos hqF]
      have hpf : p < f := by omega
      have := hP3a p (f - 1) (by omega) (by omega)
      have := hhi' (by omega)
      linarith
    · rw [if_neg hpF, if_neg hqF]
      by_cases hpf : p < f
      · by_cases hqf : q < f
        · exact hP3a p q hpq (by omega)
        · have h1 := hP3b (N - f) q (by omega) (by omega) hq
          have h2 := hP3a p (f - 1) (by omega) (by omega)
          have := hlo' (by omega)
          have := hhi' (by omega)
          linarith
      · exact hP3b p q (by omega) hpq hq
  · -- (G)
    have hqp := harr.lt
    have hpN := harr.1
    have hG := vPrime_G hI hℓ hne hc hV' harr
    simp only [flatV]
    by_cases hpF : f ≤ p ∧ p ≤ N - 1 - f <;> by_cases hqF : f ≤ q ∧ q ≤ N - 1 - f
    · rw [if_pos hpF, if_pos hqF, sub_self]
      by_cases hpM : p < M
      · have := lemma_P1_low hI hℓ hne hc hV' harr hpM (by omega)
        have := hP3a p (M - 1) (by omega) (by omega)
        have := hlec3 q hqF.1 (by omega)
        linarith
      · push_neg at hpM
        by_cases hqM : q < M
        · have := hlec3 q hqF.1 hqM
          have := hc4le p hpM (by omega)
          linarith
        · push_neg at hqM
          have := lemma_P1_high hI hℓ hne hc hV' harr hpM hqM
          have := hc4le p hpM (by omega)
          have := hP3b M q le_rfl hqM (by omega)
          linarith
    · rw [if_pos hpF, if_neg hqF]
      have hqf : q < f := by omega
      by_cases hpM : p < M
      · have := lemma_P1_low hI hℓ hne hc hV' harr hpM (by omega)
        have := hP3a p (M - 1) (by omega) (by omega)
        linarith
      · push_neg at hpM
        have := hc4le p hpM (by omega)
        linarith
    · rw [if_neg hpF, if_pos hqF]
      have hpf : N - f ≤ p := by omega
      by_cases hqM : q < M
      · have := hlec3 q hqF.1 hqM
        linarith
      · push_neg at hqM
        have := lemma_P1_high hI hℓ hne hc hV' harr (by omega) hqM
        have := hP3b M q le_rfl hqM (by omega)
        linarith
    · rw [if_neg hpF, if_neg hqF]
      exact hG

include hI hℓ hα hne hc hV' hf in
/-- **Lemma F** (the central flat, step 7 of `C8_theorem_F_potential.md`), all four parts
together: with `f = min {p < M : X_1(p) ≤ 0}` (which exists iff `X_1(M − 1) ≤ 0`,
`exists_flat_start`, `X1_last_nonpos_of_flat`; so the hypothesis `X_1(M − 1) ≤ 0` of the file is
carried by `hf`), (F1)–(F4) hold. -/
theorem lemma_F :
    (∀ p < 2 ^ #I, yhat I k ℓ α p = 0 ↔ f ≤ p ∧ p ≤ 2 ^ #I - 1 - f) ∧
    (IsGreatest (vPrime I k ℓ α c V' '' Set.Ico f (2 ^ #(I.erase c))) (vPrime I k ℓ α c V' f) ∧
      IsLeast (vPrime I k ℓ α c V' '' Set.Ico (2 ^ #(I.erase c)) (2 ^ #I - f))
        (vPrime I k ℓ α c V' (2 ^ #I - 1 - f)) ∧
      vPrime I k ℓ α c V' f - vPrime I k ℓ α c V' (2 ^ #I - 1 - f) = X1 I k ℓ α c f ∧
      X1 I k ℓ α c f ≤ 0) ∧
    loF I k ℓ α c V' f ≤ hiF I k ℓ α c V' f ∧
    (∀ cF : ℤ, loF I k ℓ α c V' f ≤ cF → cF ≤ hiF I k ℓ α c V' f →
      IsPotential I k ℓ α (flatV I k ℓ α c V' f cF)) :=
  ⟨lemma_F1 hI hℓ hα hne hc hV' hf, lemma_F2 hne hc hV' hf, lemma_F3 hne hc hV' hf,
    fun cF h1 h2 => lemma_F4 hI hℓ hα hne hc hV' hf cF h1 h2⟩

end LemmaF

end Potential
