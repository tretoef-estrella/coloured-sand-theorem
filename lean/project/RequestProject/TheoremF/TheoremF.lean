module

public import RequestProject.TheoremF.Walk

/-!
# Theorems F1 and F0 of `C7_theorem_F_walk_and_cut.md` (Theorem 7.8: (Λ), (Cut), the walk)

F1 and F0 are proved together by induction on `|I|`, as in the file: `F1_step` derives F1 for
`H` from F1 for `H' = (I', c, ℓ mod 2^c, α)` and the walk (F0) for `H` (`walk_W3_of_cut`, which
itself uses (Cut) for `H'`).  Encodings as in `RequestProject/TheoremF/Sequences.lean`.
-/

@[expose] public section

namespace TheoremF

open Finset Rulers AntitonicFit

/-- The statement **(Λ)** of Theorem F1 (`C7_theorem_F_walk_and_cut.md`) for the house
`(I, k, ℓ, α)`: `|ŷ_H(p)| ≤ α (2^k − 1)` for every `p < N`. -/
def LamProp (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) : Prop :=
  ∀ p < 2 ^ #I, |ifit (2 ^ #I) (xHseq I k ℓ α) p| ≤ α * (2 ^ k - 1)

/-- The integer fit is below the real fit plus one: `ifit(x)_j < fit(x)_j + 1`.  (Auxiliary for
step 3 of the proof of Theorem F1 in `C7_theorem_F_walk_and_cut.md`.) -/
lemma ifit_lt_fit_add_one {N : ℕ} (x : ℕ → ℤ) {j : ℕ} (hj : j < N) :
    (ifit N x j : ℝ) < fit N (toR x) j + 1 := by
  rw [ifit_of_lt hj]
  have hS := sum_levelSet_fit_int (x := x) hj
  set L := levelSet N (fit N (toR x)) j
  have hjL : j ∈ L := by simp [L, levelSet, hj]
  have hP : 0 < L.card := card_pos.2 ⟨j, hjL⟩
  have hPR : (0 : ℝ) < L.card := by exact_mod_cast hP
  have hfit : fit N (toR x) j = ((∑ i ∈ L, x i : ℤ) : ℝ) / L.card := by
    rw [hS]; field_simp
  have hle : blockF (∑ i ∈ L, x i) L.card (L.filter (· < j)).card ≤
      ⌈((∑ i ∈ L, x i : ℤ) : ℝ) / L.card⌉ := by
    unfold blockF
    split_ifs
    · exact le_rfl
    · exact Int.floor_le_ceil _
  have h1 := Int.ceil_lt_add_one (((∑ i ∈ L, x i : ℤ) : ℝ) / L.card)
  have h2 : ((blockF (∑ i ∈ L, x i) L.card (L.filter (· < j)).card : ℤ) : ℝ) ≤
      ((⌈((∑ i ∈ L, x i : ℤ) : ℝ) / L.card⌉ : ℤ) : ℝ) := by exact_mod_cast hle
  rw [hfit]
  linarith

variable {I : Finset ℕ} {k ℓ : ℕ}

/-- `κ_c ≤ h_c` when `h_c ≥ 1` (step 2 of the proof of Theorem F1, `C7_theorem_F_walk_and_cut.md`). -/
lemma kap_le_h {c : ℕ} (hh : 1 ≤ h k I c) : Houses.kap I k ℓ c ≤ h k I c := by
  unfold Houses.kap; split_ifs <;> omega

/-- **Theorem F1 for `I = ∅`** (base of the induction in `C7_theorem_F_walk_and_cut.md`). -/
lemma F1_empty (hI : I = ∅) (hℓ : ℓ < 2 ^ k) {α : ℤ} (hα : 1 ≤ α) :
    LamProp I k ℓ α ∧ CutProp I k ℓ α := by
  subst hI
  unfold LamProp CutProp
  simp only [card_empty, pow_zero]
  constructor
  · intro p hp
    have hp0 : p = 0 := by omega
    subst hp0
    have h1 := A2 (lemma_0f_antisymm (∅ : Finset ℕ) k ℓ α) 0 (by simp)
    simp only [card_empty, pow_zero] at h1
    have h0 : ifit 1 (xHseq ∅ k ℓ α) 0 = 0 := by simp at h1; omega
    rw [h0, abs_zero]
    have : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  · intro b hb hJ _
    have hb0 : b = 0 := by omega
    subst hb0
    rw [lemma_0f_J0 _ hℓ] at hJ
    exact absurd hJ (by norm_num)

/-- **Theorem F1, induction step** (steps 2 and 3 of the proof in
`C7_theorem_F_walk_and_cut.md`): F1 for `H'` implies F1 for `H`. -/
lemma F1_step (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) {α : ℤ} (hα : 1 ≤ α) (hne : I.Nonempty)
    {c : ℕ} (hc : c = I.max' hne) (hΛ' : LamProp (I.erase c) c (ℓ % 2 ^ c) α)
    (hcut' : CutProp (I.erase c) c (ℓ % 2 ^ c) α) :
    LamProp I k ℓ α ∧ CutProp I k ℓ α := by
  have hcI : c ∈ I := hc ▸ I.max'_mem hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ I.le_max' t ht
  have hck : c < k := hI c hcI
  have hh : h k I c = k - c := Houses.h_max hI hcI hcmax
  have hN := card_erase_max hne hc
  have hW3 := walk_W3_of_cut hI hℓ α hne hc hcut'
  have hκ : Houses.kap I k ℓ c ≤ k - c := hh ▸ kap_le_h (by omega)
  have hτ : Houses.tau I k ℓ α c = ((k - c : ℕ) : ℤ) - α * 2 ^ c -
      (if Houses.typ ℓ c = 1 then (Houses.kap I k ℓ c : ℤ) else 0) := by
    unfold Houses.tau; rw [hh]
  have hT : Houses.typ ℓ c = 0 ∨ Houses.typ ℓ c = 1 := by
    unfold Houses.typ Houses.bit; omega
  have hd := fun p (hp : p < 2 ^ #(I.erase c)) => dWalk_eq (k := k) (ℓ := ℓ) α c hp
  have hJle : ∀ p, JHseq (I.erase c) c (ℓ % 2 ^ c) p ≤ 1 := fun p => JHseq_le_one _ _ _ p
  have hJ'0 : JHseq (I.erase c) c (ℓ % 2 ^ c) 0 = 0 :=
    lemma_0f_J0 _ (Nat.mod_lt _ (by positivity))
  have hJlo : ∀ p < 2 ^ #(I.erase c), JHseq I k ℓ p =
      (if Houses.typ ℓ c = 1 then 1 else 0) * Houses.sat I k ℓ c *
        JHseq (I.erase c) c (ℓ % 2 ^ c) p := by
    intro p hp
    simp only [JHseq]
    rw [(lemma_0e hne hc hp).1]
    exact Houses.lemma_C3 hI hℓ hne hc (lemma_0a _ p)
  have hJhi : ∀ q < 2 ^ #(I.erase c), JHseq I k ℓ (2 ^ #(I.erase c) + q) =
      Houses.sat I k ℓ c * ((if Houses.typ ℓ c = 1 then 1 else 0) +
        (if Houses.typ ℓ c = 0 then 1 else 0) * JHseq (I.erase c) c (ℓ % 2 ^ c) q) := by
    intro q hq
    simp only [JHseq]
    rw [(lemma_0e hne hc hq).2]
    exact Houses.lemma_C4 hI hℓ hne hc (lemma_0a _ q)
  have hsat : Houses.sat I k ℓ c = 1 → Houses.kap I k ℓ c = k - c := by
    unfold Houses.sat; rw [hh]; split_ifs with h1 <;> simp [h1]
  have hanti := lemma_0f_antisymm I k ℓ α
  have hpow : (2 : ℤ) * 2 ^ c ≤ 2 ^ k := by
    rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
  unfold LamProp CutProp
  rw [hN] at hanti ⊢
  rw [hN] at hW3
  set M := 2 ^ #(I.erase c) with hM
  set x' := xHseq (I.erase c) c (ℓ % 2 ^ c) α with hx'
  set J' := JHseq (I.erase c) c (ℓ % 2 ^ c) with hJ'
  set d := dWalk I k ℓ α c with hd_def
  set x := xHseq I k ℓ α with hx
  set T := Houses.typ ℓ c with hT_def
  set κ := Houses.kap I k ℓ c with hκ_def
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  constructor
  · -- (Λ)
    have hdle : ∀ i < M, d i ≤ α * 2 ^ c := by
      intro i hi
      rw [hd i hi, hτ]
      have h1 : (J' i : ℤ) ≤ 1 := by exact_mod_cast hJle i
      have h2 : (J' (M - 1 - i) : ℤ) ≤ 1 := by exact_mod_cast hJle _
      have h3 : (0 : ℤ) ≤ J' i := by positivity
      have h4 : (0 : ℤ) ≤ J' (M - 1 - i) := by positivity
      have hκ' : (κ : ℤ) ≤ ((k - c : ℕ) : ℤ) := by exact_mod_cast hκ
      have hκ0 : (0 : ℤ) ≤ κ := by positivity
      rcases hT with hT | hT <;> simp only [hT] <;> norm_num <;> nlinarith
    have hX : ∀ i < M, ifit M x' i + d i ≤ α * (2 ^ k - 1) := by
      intro i hi
      have h1 := (abs_le.1 (hΛ' i hi)).2
      have h2 := hdle i hi
      nlinarith
    have hB : 0 ≤ α * (2 ^ k - 1) := by
      have : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    intro p hp
    rw [hW3.2 p hp]
    simp only [concat, mirror, Pi.add_apply]
    split_ifs with hpM
    · rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (hX p hpM) hB
    · rw [min_neg_zero_int, abs_neg, abs_of_nonneg (le_max_right _ _)]
      exact max_le (hX _ (by omega)) hB
  · -- (Cut)
    set Z1 : ℕ → ℝ := fun i => fit M (toR x') i + (d i : ℝ) with hZ1
    have hlo : ∀ p < M, fit (2 * M) (toR x) p = max (Z1 p) 0 := by
      intro p hp
      rw [hW3.1 p (by omega)]
      simp only [concat, if_pos hp, Pi.add_apply, toR, hZ1]
    have hhi : ∀ q < M, fit (2 * M) (toR x) (M + q) = min (-(Z1 (M - 1 - q))) 0 := by
      intro q hq
      rw [hW3.1 (M + q) (by omega)]
      simp only [concat, if_neg (show ¬ M + q < M by omega), mirror, Pi.add_apply, toR, hZ1,
        Nat.add_sub_cancel_left]
    have hpos : ∀ u < M, d u = α * 2 ^ c → 0 < Z1 u := by
      intro u hu hdu
      have h1 := (abs_le.1 (hΛ' u hu)).1
      have h2 := ifit_lt_fit_add_one x' hu
      have h1' : -((α : ℝ) * (2 ^ c - 1)) ≤ (ifit M x' u : ℝ) := by exact_mod_cast h1
      have hdu' : (d u : ℝ) = α * 2 ^ c := by exact_mod_cast hdu
      have hα' : (1 : ℝ) ≤ α := by exact_mod_cast hα
      simp only [hZ1, hdu']
      linarith
    have hdrop : ∀ u, u + 1 < M → d (u + 1) < d u → Z1 (u + 1) < Z1 u := by
      intro u hu hlt
      have h1 := fit_nonIncr M (toR x') u hu
      have h2 : (d (u + 1) : ℝ) < d u := by exact_mod_cast hlt
      simp only [hZ1]
      linarith
    intro b hb hJb hJlt
    have key : 0 < b ∧ fit (2 * M) (toR x) b < fit (2 * M) (toR x) (b - 1) := by
      have hkc : (1 : ℤ) ≤ ((k - c : ℕ) : ℤ) := by exact_mod_cast (show 1 ≤ k - c by omega)
      by_cases hbM : b < M
      · -- case (a): the boundary is in the first half
        have hJb' := hJb
        rw [hJlo b hbM] at hJb'
        obtain ⟨h1, hJ1⟩ := mul_eq_one.1 hJb'
        obtain ⟨h1, hs1⟩ := mul_eq_one.1 h1
        have hT1 : T = 1 := by by_contra hne; simp [hne] at h1
        have hκh := hsat hs1
        have hb0 : 0 < b := by
          rcases Nat.eq_zero_or_pos b with rfl | h
          · rw [hJ'0] at hJ1; exact absurd hJ1 (by norm_num)
          · exact h
        have hJm : J' (b - 1) = 0 := by
          have := hJlt (b - 1) (by omega)
          rw [hJlo _ (by omega), h1, hs1] at this; simpa using this
        have hd1 : d (b - 1) = α * 2 ^ c := by
          rw [hd _ (by omega), hτ, hJm]; simp [hT1, hκh]
        have hd2 : d b < d (b - 1) := by
          rw [hd1, hd b hbM, hτ, hJ1]; simp [hT1, hκh]; linarith
        have hp1 := hpos (b - 1) (by omega) hd1
        have hdr := hdrop (b - 1) (by omega) (by rw [show b - 1 + 1 = b by omega]; exact hd2)
        rw [show b - 1 + 1 = b by omega] at hdr
        refine ⟨hb0, ?_⟩
        rw [hlo b hbM, hlo (b - 1) (by omega), max_eq_left hp1.le]
        exact max_lt hdr hp1
      · -- the boundary is in the second half: `b = M + q`
        obtain ⟨q, rfl⟩ : ∃ q, b = M + q := ⟨b - M, by omega⟩
        have hqM : q < M := by omega
        have hJb' := hJb
        rw [hJhi q hqM] at hJb'
        obtain ⟨hs1, h2⟩ := mul_eq_one.1 hJb'
        have hκh := hsat hs1
        rcases hT with hT0 | hT1
        · -- case (c): `T = 0`, the boundary is `M + b'`
          simp only [hT0, zero_ne_one, if_false, if_true, zero_add, one_mul] at h2
          have hq0 : 0 < q := by
            rcases Nat.eq_zero_or_pos q with rfl | h
            · rw [hJ'0] at h2; exact absurd h2 (by norm_num)
            · exact h
          have hJm : J' (q - 1) = 0 := by
            have := hJlt (M + (q - 1)) (by omega)
            rw [hJhi _ (by omega), hs1] at this; simpa [hT0] using this
          have hd1 : d (M - 1 - q) = α * 2 ^ c := by
            rw [hd _ (by omega), hτ, show M - 1 - (M - 1 - q) = q by omega, h2]; simp [hT0, hκh]
          have hd2 : d (M - 1 - q + 1) < d (M - 1 - q) := by
            rw [hd1, hd _ (by omega), hτ, show M - 1 - (M - 1 - q + 1) = q - 1 by omega, hJm]
            simp [hT0, hκh]; linarith
          have hp1 := hpos (M - 1 - q) (by omega) hd1
          have hdr := hdrop (M - 1 - q) (by omega) hd2
          rw [show M - 1 - q + 1 = M - 1 - (q - 1) by omega] at hdr
          refine ⟨by omega, ?_⟩
          rw [show M + q - 1 = M + (q - 1) by omega, hhi q hqM, hhi (q - 1) (by omega),
            min_eq_left (neg_nonpos.2 hp1.le)]
          exact lt_min (neg_lt_neg hdr) (neg_neg_of_pos hp1)
        · -- case (b): `T = 1`, `J' ≡ 0`, the boundary is the middle `M`
          have hJ0 : ∀ p < M, J' p = 0 := by
            intro p hp
            have := hJlt p (by omega)
            rw [hJlo p hp, hs1] at this; simpa [hT1] using this
          have hq0 : q = 0 := by
            by_contra hq
            have := hJlt (M + 0) (by omega)
            rw [hJhi 0 (by omega), hs1] at this; simp [hT1] at this
          subst hq0
          have hd1 : d (M - 1) = α * 2 ^ c := by
            rw [hd _ (by omega), hτ, hJ0 (M - 1) (by omega)]; simp [hT1, hκh]
          have hp1 := hpos (M - 1) (by omega) hd1
          refine ⟨by omega, ?_⟩
          rw [show M + 0 - 1 = M - 1 by omega, hhi 0 (by omega), hlo (M - 1) (by omega),
            max_eq_left hp1.le, Nat.sub_zero]
          exact lt_of_le_of_lt (min_le_right _ _) hp1
    have hs : IsStrictCut (2 * M) (toR x) b := ⟨consequence_D_cut key.1 hb key.2, key.2⟩
    exact ⟨hs, (A3 (toR_antisymm hanti) key.1 hb).2.1 hs⟩

/-- Theorem F1 for all houses, by induction on `|I|` (proof of F0 and F1 in
`C7_theorem_F_walk_and_cut.md`). -/
lemma F1_all : ∀ (n : ℕ) (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ), #I = n → (∀ t ∈ I, t < k) →
    ℓ < 2 ^ k → 1 ≤ α → LamProp I k ℓ α ∧ CutProp I k ℓ α := by
  intro n
  induction n with
  | zero =>
    intro I k ℓ α hn _ hℓ hα
    exact F1_empty (card_eq_zero.1 hn) hℓ hα
  | succ n ih =>
    intro I k ℓ α hn hI hℓ hα
    have hne : I.Nonempty := card_pos.1 (by omega)
    set c := I.max' hne with hc
    have hcI : c ∈ I := I.max'_mem hne
    have hI' : ∀ t ∈ I.erase c, t < c := fun t ht =>
      lt_of_le_of_ne (I.le_max' t (mem_of_mem_erase ht)) (ne_of_mem_erase ht)
    have hcard : #(I.erase c) = n := by rw [card_erase_of_mem hcI]; omega
    obtain ⟨h1, h2⟩ := ih (I.erase c) c (ℓ % 2 ^ c) α hcard hI' (Nat.mod_lt _ (by positivity)) hα
    exact F1_step hI hℓ hα hne hc h1 h2

/-- **Theorem F1** (Theorem 7.8: (Λ) and (Cut)) of `C7_theorem_F_walk_and_cut.md`: for every house
`H = (I, k, ℓ, α)` (`I ⊆ {0,…,k−1}`, `ℓ < 2^k`, `α ≥ 1`), with `N = 2^{|I|}`:
* (Λ) for every `p < N`, `|ŷ_H(p)| ≤ α (2^k − 1)`;
* (Cut) if `b < N` is the first position with `J_H(b) = 1` (i.e. `J_H(b) = 1` and `J_H(p) = 0`
  for all `p < b`), then `x_H` has a strict cut at `b` and a strict cut at `N − b`, in the sense of
  `AntitonicFit.IsStrictCut N (toR x_H)` (which includes `0 < b`). -/
theorem theorem_F1 {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k)
    (hα : 1 ≤ α) :
    (∀ p < 2 ^ #I, |ifit (2 ^ #I) (xHseq I k ℓ α) p| ≤ α * (2 ^ k - 1)) ∧
    (∀ b < 2 ^ #I, JHseq I k ℓ b = 1 → (∀ p < b, JHseq I k ℓ p = 0) →
      IsStrictCut (2 ^ #I) (toR (xHseq I k ℓ α)) b ∧
        IsStrictCut (2 ^ #I) (toR (xHseq I k ℓ α)) (2 ^ #I - b)) :=
  F1_all _ I k ℓ α rfl hI hℓ hα

/-- **Theorem F1**, (Λ) alone (`C7_theorem_F_walk_and_cut.md`). -/
theorem theorem_F1_Lambda {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k)
    (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) :
    ∀ p < 2 ^ #I, |ifit (2 ^ #I) (xHseq I k ℓ α) p| ≤ α * (2 ^ k - 1) :=
  (theorem_F1 hI hℓ hα).1

/-- **Theorem F1**, (Cut) alone (`C7_theorem_F_walk_and_cut.md`); the remark `0 < b` (by
Lemma 0f) is part of the conclusion `IsStrictCut`. -/
theorem theorem_F1_Cut {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k)
    (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) :
    ∀ b < 2 ^ #I, JHseq I k ℓ b = 1 → (∀ p < b, JHseq I k ℓ p = 0) →
      IsStrictCut (2 ^ #I) (toR (xHseq I k ℓ α)) b ∧
        IsStrictCut (2 ^ #I) (toR (xHseq I k ℓ α)) (2 ^ #I - b) :=
  (theorem_F1 hI hℓ hα).2

/-- *Part 2* of `C7_theorem_F_walk_and_cut.md`: (Cut) for the smaller house `H' = (I ∖ {c}, c, ℓ mod 2^c, α)`, from Theorem F1. -/
lemma cut_erase_max {I : Finset ℕ} {ℓ : ℕ} {α : ℤ} (hα : 1 ≤ α) (hne : I.Nonempty) {c : ℕ}
    (hc : c = I.max' hne) : CutProp (I.erase c) c (ℓ % 2 ^ c) α := by
  have hI' : ∀ t ∈ I.erase c, t < c := fun t ht => hc ▸
    lt_of_le_of_ne (I.le_max' t (mem_of_mem_erase ht)) (hc ▸ ne_of_mem_erase ht)
  exact theorem_F1_Cut hI' (Nat.mod_lt _ (by positivity)) hα

/-- **(W2)** of Theorem F0, `C7_theorem_F_walk_and_cut.md`: for `p < M`,
`fit_M(x' + d)(p) = fit_M(x')(p) + d(p)` and `ifit_M(x' + d)(p) = ifit_M(x')(p) + d(p)`.
(Only `α ≥ 1` is used, through (Cut) for `H'`; the house conditions on `I`, `k`, `ℓ` are not
needed, since `H'` is a house in any case.) -/
theorem theorem_F0_W2 {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hα : 1 ≤ α) (hne : I.Nonempty) {c : ℕ}
    (hc : c = I.max' hne) :
    (∀ p < 2 ^ #(I.erase c),
      fit (2 ^ #(I.erase c)) (toR (xHseq (I.erase c) c (ℓ % 2 ^ c) α + dWalk I k ℓ α c)) p =
        fit (2 ^ #(I.erase c)) (toR (xHseq (I.erase c) c (ℓ % 2 ^ c) α)) p +
          dWalk I k ℓ α c p) ∧
    (∀ p < 2 ^ #(I.erase c),
      ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α + dWalk I k ℓ α c) p =
        ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α) p + dWalk I k ℓ α c p) :=
  walk_W2_of_cut α c (cut_erase_max hα hne hc)

/-- **(W3)** of Theorem F0, `C7_theorem_F_walk_and_cut.md`: with `Z_1 := fit_M(x') + d` and
`X_1 := ifit_M(x') + d`, for every `p < N`,
`fit_N(x_H)(p) = concat_M(max(Z_1, 0), min(mirror_M(Z_1), 0))(p)` and
`ŷ_H(p) = concat_M(max(X_1, 0), min(mirror_M(X_1), 0))(p)`. -/
theorem theorem_F0_W3 {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k)
    (hα : 1 ≤ α) (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) :
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
            dWalk I k ℓ α c) i) 0) p) :=
  walk_W3_of_cut hI hℓ α hne hc (cut_erase_max hα hne hc)

/-- **Theorem F0** (the walk, step 1 of Theorem 7.8) of `C7_theorem_F_walk_and_cut.md`, all four
parts together.  For a house `H = (I, k, ℓ, α)` with `I ≠ ∅`, `c = max I`, `I' = I ∖ {c}`,
`M = 2^{|I'|}`, `H' = (I', c, ℓ mod 2^c, α)`, `x' = x_{H'}`, `J' = J_{H'}` and
`d(p) = Houses.d1 I k ℓ α c (dancer_{I'}(p))`:
(W0) `x_H(p) = x'(p) + d(p)` for `p < M`;
(W1) `d` is non-increasing on `[0, M)`, and if `0 < p < M` and `d(p − 1) ≠ d(p)` then `J' ≢ 0`
and `p = b'` or `p = M − b'` for the first position `b'` with `J'(b') = 1`;
(W2) `fit_M(x' + d) = fit_M(x') + d` and `ifit_M(x' + d) = ifit_M(x') + d` on `[0, M)`;
(W3) `fit_N(x_H) = concat_M(max(Z_1, 0), min(mirror_M(Z_1), 0))` and
`ŷ_H = concat_M(max(X_1, 0), min(mirror_M(X_1), 0))` on `[0, N)`, where
`Z_1 = fit_M(x') + d`, `X_1 = ifit_M(x') + d`. -/
theorem theorem_F0 {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k)
    (hα : 1 ≤ α) (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) :
    -- (W0)
    (∀ p < 2 ^ #(I.erase c),
      xHseq I k ℓ α p = xHseq (I.erase c) c (ℓ % 2 ^ c) α p + dWalk I k ℓ α c p) ∧
    -- (W1)
    ((∀ p, p + 1 < 2 ^ #(I.erase c) → dWalk I k ℓ α c (p + 1) ≤ dWalk I k ℓ α c p) ∧
      ∀ p, 0 < p → p < 2 ^ #(I.erase c) → dWalk I k ℓ α c (p - 1) ≠ dWalk I k ℓ α c p →
        ∃ b' < 2 ^ #(I.erase c), JHseq (I.erase c) c (ℓ % 2 ^ c) b' = 1 ∧
          (∀ q < b', JHseq (I.erase c) c (ℓ % 2 ^ c) q = 0) ∧
          (p = b' ∨ p = 2 ^ #(I.erase c) - b')) ∧
    -- (W2)
    ((∀ p < 2 ^ #(I.erase c),
      fit (2 ^ #(I.erase c)) (toR (xHseq (I.erase c) c (ℓ % 2 ^ c) α + dWalk I k ℓ α c)) p =
        fit (2 ^ #(I.erase c)) (toR (xHseq (I.erase c) c (ℓ % 2 ^ c) α)) p +
          dWalk I k ℓ α c p) ∧
    (∀ p < 2 ^ #(I.erase c),
      ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α + dWalk I k ℓ α c) p =
        ifit (2 ^ #(I.erase c)) (xHseq (I.erase c) c (ℓ % 2 ^ c) α) p + dWalk I k ℓ α c p)) ∧
    -- (W3)
    ((∀ p < 2 ^ #I, fit (2 ^ #I) (toR (xHseq I k ℓ α)) p =
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
            dWalk I k ℓ α c) i) 0) p)) :=
  ⟨theorem_F0_W0 hI hℓ α hne hc,
    ⟨theorem_F0_W1_antitone α c, theorem_F0_W1_change α c⟩,
    theorem_F0_W2 hα hne hc, theorem_F0_W3 hI hℓ hα hne hc⟩

end TheoremF
