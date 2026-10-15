module

public import RequestProject.OddPotential.Walk

/-!
# `CSI16_theorem_F_at_p.md` — *Part F1* (Theorem F1_p: `(Λ_p)` and (Cut)) and *Part F0* (the walk)

Base-`p` analogue of `RequestProject/TheoremF/TheoremF.lean` (C7), with the changes of Part Δ
(steps 2 and 3).  F1_p and F0_p are proved together by induction on `|I|`: `oddF_F1_step` derives
F1_p for `H` from F1_p for `H' = (I', c, ℓ mod p^c, e, d)` and the walk for `H`
(`oddF_W3_of_cut`, which uses (Cut) for `H'`).  Encodings as in
`RequestProject/OddPotential/Sequences.lean`; `o_I` is CSI12's `oW p dg I`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset AntitonicFit TheoremF

/-- The statement **(Λ_p)** of Theorem F1_p (`CSI16_theorem_F_at_p.md`, Part F1) for the house
`(I, k, ℓ, e, dg)`: `|ŷ_H(q)| ≤ e·o_I` for every `q < N`. -/
def LamPropP (p k : ℕ) (I : Finset ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) : Prop :=
  ∀ q < 2 ^ #I, |ifit (2 ^ #I) (xHseqP p k I dg ℓ e) q| ≤ e * (oW p dg I : ℤ)

variable {p : ℕ} [hp : Fact p.Prime] {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ}

omit hp in
/-- `κ_c ≤ h_c` when `h_c ≥ 1` (Part Δ, step 2, of `CSI16_theorem_F_at_p.md`). -/
lemma kapP_le_h {c : ℕ} (hh : 1 ≤ Rulers.h k I c) : kapP p k I ℓ c ≤ Rulers.h k I c := by
  unfold kapP; omega

omit hp in
/-- `o_I = o_{I'} + d_c p^c` for `c ∈ I` (Part Δ, step 2, of `CSI16_theorem_F_at_p.md`). -/
lemma oW_erase_add {c : ℕ} (hcI : c ∈ I) : oW p dg I = oW p dg (I.erase c) + dg c * p ^ c :=
  (sum_erase_add I _ hcI).symm

omit hp in
/-- **Theorem F1_p for `I = ∅`** (base of the induction). -/
lemma oddF_F1_empty (hI : I = ∅) (hℓ : ℓ < p ^ k) (e : ℤ) :
    LamPropP p k I dg ℓ e ∧ CutPropP p k I dg ℓ e := by
  subst hI
  unfold LamPropP CutPropP
  simp only [card_empty, pow_zero]
  constructor
  · intro q hq
    have hq0 : q = 0 := by omega
    subst hq0
    have h1 := A2 (oddF_xH_antisymm p k (∅ : Finset ℕ) dg ℓ e) 0 (by simp)
    simp only [card_empty, pow_zero] at h1
    have h0 : ifit 1 (xHseqP p k ∅ dg ℓ e) 0 = 0 := by simp at h1; omega
    rw [h0, abs_zero]
    simp [oW]
  · intro b hb hJ _
    have hb0 : b = 0 := by omega
    subst hb0
    rw [oddF_J0 _ hℓ] at hJ
    exact absurd hJ (by norm_num)

/-- **Theorem F1_p, induction step** (Part Δ, steps 2 and 3, of `CSI16_theorem_F_at_p.md`):
F1_p for `H'` implies F1_p for `H`. -/
lemma oddF_F1_step (hI : ∀ t ∈ I, t < k) (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (hℓ : ℓ < p ^ k) {e : ℤ} (he : 1 ≤ e) (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne)
    (hΛ' : LamPropP p c (I.erase c) dg (ℓ % p ^ c) e)
    (hcut' : CutPropP p c (I.erase c) dg (ℓ % p ^ c) e) :
    LamPropP p k I dg ℓ e ∧ CutPropP p k I dg ℓ e := by
  have hcI : c ∈ I := hc ▸ I.max'_mem hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ I.le_max' t ht
  have hck : c < k := hI c hcI
  have hh : Rulers.h k I c = k - c := Houses.h_max hI hcI hcmax
  have hN := card_erase_max hne hc
  have hW3 := oddF_W3_of_cut hI hd hℓ e hne hc hcut'
  have hκ : kapP p k I ℓ c ≤ k - c := hh ▸ kapP_le_h (by omega)
  have hτ : tauP p k I dg ℓ e c = ((k - c : ℕ) : ℤ) - e * (dg c : ℤ) * (p : ℤ) ^ c -
      (if typP p dg ℓ c = .OR ∨ typP p dg ℓ c = .DIG then (kapP p k I ℓ c : ℤ) else 0) := by
    unfold tauP; rw [hh]
  have hd' := fun q (hq : q < 2 ^ #(I.erase c)) => dWalkP_eq (p := p) (k := k) (ℓ := ℓ) (dg := dg) e c hq
  have hJle : ∀ q, JHseqP p c (I.erase c) dg (ℓ % p ^ c) q ≤ 1 := fun q => JHseqP_le_one _ _ _ _ _ q
  have hJ'0 : JHseqP p c (I.erase c) dg (ℓ % p ^ c) 0 = 0 :=
    oddF_J0 _ (Nat.mod_lt _ (pow_pos hp.out.pos c))
  have hJlo : ∀ q < 2 ^ #(I.erase c), JHseqP p k I dg ℓ q =
      (if typP p dg ℓ c = .OR then 1 else 0) * satP p k I ℓ c *
        JHseqP p c (I.erase c) dg (ℓ % p ^ c) q := by
    intro q hq
    simp only [JHseqP]
    rw [(lemma_0e hne hc hq).1]
    exact houseP_C3 hI hd hℓ hne hc (lemma_0a _ q)
  have hJhi : ∀ q < 2 ^ #(I.erase c), JHseqP p k I dg ℓ (2 ^ #(I.erase c) + q) =
      satP p k I ℓ c * ((if typP p dg ℓ c = .OR ∨ typP p dg ℓ c = .DIG then 1 else 0) +
        (if typP p dg ℓ c = .AND then 1 else 0) * JHseqP p c (I.erase c) dg (ℓ % p ^ c) q) := by
    intro q hq
    simp only [JHseqP]
    rw [(lemma_0e hne hc hq).2]
    exact houseP_C4 hI hd hℓ hne hc (lemma_0a _ q)
  have hsat : satP p k I ℓ c = 1 → kapP p k I ℓ c = k - c := by
    unfold satP; rw [hh]; split_ifs with h1 <;> simp [h1]
  have hanti := oddF_xH_antisymm p k I dg ℓ e
  -- `o_I = o_{I'} + d_c p^c` and `1 ≤ d_c p^c − o_{I'}`
  have hoI : (oW p dg I : ℤ) = oW p dg (I.erase c) + dg c * (p : ℤ) ^ c := by
    rw [oW_erase_add hcI]; push_cast; ring
  have hgap : (1 : ℤ) ≤ dg c * (p : ℤ) ^ c - oW p dg (I.erase c) := by
    have h1 := oW_lt_erase (I := I) hd hcmax (D₀ := I.erase c) subset_rfl
    have h2 := (hd c hcI).1
    have h3 : p ^ c ≤ dg c * p ^ c := Nat.le_mul_of_pos_left _ h2
    have : oW p dg (I.erase c) + 1 ≤ dg c * p ^ c := by omega
    have : ((oW p dg (I.erase c) : ℕ) : ℤ) + 1 ≤ ((dg c * p ^ c : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at this; linarith
  have hgapE : e ≤ e * (dg c * (p : ℤ) ^ c - oW p dg (I.erase c)) := by
    have := mul_le_mul_of_nonneg_left hgap (by omega : (0 : ℤ) ≤ e)
    linarith
  unfold LamPropP CutPropP
  rw [hN] at hanti ⊢
  rw [hN] at hW3
  set M := 2 ^ #(I.erase c) with hM
  set x' := xHseqP p c (I.erase c) dg (ℓ % p ^ c) e with hx'
  set J' := JHseqP p c (I.erase c) dg (ℓ % p ^ c) with hJ'
  set d := dWalkP p k I dg ℓ e c with hd_def
  set x := xHseqP p k I dg ℓ e with hx
  set T := typP p dg ℓ c with hT_def
  set κ := kapP p k I ℓ c with hκ_def
  set A : ℤ := e * (dg c : ℤ) * (p : ℤ) ^ c with hA
  set oI' : ℤ := (oW p dg (I.erase c) : ℤ) with hoI'
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  constructor
  · -- (Λ_p): Part Δ, step 1
    have hdle : ∀ i < M, d i ≤ A := by
      intro i hi
      rw [hd' i hi, hτ]
      have h1 : (J' i : ℤ) ≤ 1 := by exact_mod_cast hJle i
      have h2 : (J' (M - 1 - i) : ℤ) ≤ 1 := by exact_mod_cast hJle _
      have h3 : (0 : ℤ) ≤ J' i := by positivity
      have h4 : (0 : ℤ) ≤ J' (M - 1 - i) := by positivity
      have hκ' : (κ : ℤ) ≤ ((k - c : ℕ) : ℤ) := by exact_mod_cast hκ
      have hκ0 : (0 : ℤ) ≤ κ := by positivity
      have hT4 : T = .OR ∨ T = .DIG ∨ T = .AND ∨ T = .NEV := by cases T <;> simp
      have ha0 : (0 : ℤ) ≤ if T = .OR then (κ : ℤ) else 0 := by split_ifs <;> simp
      have hb0 : (0 : ℤ) ≤ if T = .AND then (κ : ℤ) else 0 := by split_ifs <;> simp
      have hbs : (if T = .AND then (κ : ℤ) else 0) +
          (if T = .OR ∨ T = .DIG then (κ : ℤ) else 0) ≤ κ := by
        rcases hT4 with h | h | h | h <;> simp [h]
      have p1 := mul_nonneg ha0 h3
      have p2 := mul_le_mul_of_nonneg_left h2 hb0
      linarith
    have hX : ∀ i < M, ifit M x' i + d i ≤ e * (oW p dg I : ℤ) := by
      intro i hi
      have h1 := (abs_le.1 (hΛ' i hi)).2
      have h2 := hdle i hi
      rw [hoI]
      have : e * ((oW p dg (I.erase c) : ℤ) + dg c * (p : ℤ) ^ c) = e * oI' + A := by
        rw [hA, hoI']; ring
      rw [this]
      linarith
    have hB : 0 ≤ e * (oW p dg I : ℤ) := mul_nonneg (by omega) (by positivity)
    intro q hq
    rw [hW3.2 q hq]
    simp only [concat, mirror, Pi.add_apply]
    split_ifs with hqM
    · rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (hX q hqM) hB
    · rw [min_neg_zero_int, abs_neg, abs_of_nonneg (le_max_right _ _)]
      exact max_le (hX _ (by omega)) hB
  · -- (Cut): Part Δ, step 2
    set Z1 : ℕ → ℝ := fun i => fit M (toR x') i + (d i : ℝ) with hZ1
    have hlo : ∀ q < M, fit (2 * M) (toR x) q = max (Z1 q) 0 := by
      intro q hq
      rw [hW3.1 q (by omega)]
      simp only [concat, if_pos hq, Pi.add_apply, toR, hZ1]
    have hhi : ∀ q < M, fit (2 * M) (toR x) (M + q) = min (-(Z1 (M - 1 - q))) 0 := by
      intro q hq
      rw [hW3.1 (M + q) (by omega)]
      simp only [concat, if_neg (show ¬ M + q < M by omega), mirror, Pi.add_apply, toR, hZ1,
        Nat.add_sub_cancel_left]
    have hpos : ∀ u < M, d u = A → 0 < Z1 u := by
      intro u hu hdu
      have h1 := (abs_le.1 (hΛ' u hu)).1
      have h2 := ifit_lt_fit_add_one x' hu
      have h1' : -((e : ℝ) * (oW p dg (I.erase c) : ℝ)) ≤ (ifit M x' u : ℝ) := by
        exact_mod_cast h1
      have hdu' : (d u : ℝ) = A := by exact_mod_cast hdu
      have hg : (e : ℝ) ≤ (A : ℝ) - e * (oW p dg (I.erase c) : ℝ) := by
        have : e ≤ A - e * oI' := by rw [hA, hoI']; linarith
        exact_mod_cast this
      have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
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
      · -- case (a): OR, the boundary is in the first half
        have hJb' := hJb
        rw [hJlo b hbM] at hJb'
        obtain ⟨h1, hJ1⟩ := mul_eq_one.1 hJb'
        obtain ⟨h1, hs1⟩ := mul_eq_one.1 h1
        have hT1 : T = .OR := by by_contra hne; simp [hne] at h1
        have hκh := hsat hs1
        have hb0 : 0 < b := by
          rcases Nat.eq_zero_or_pos b with rfl | h
          · rw [hJ'0] at hJ1; exact absurd hJ1 (by norm_num)
          · exact h
        have hJm : J' (b - 1) = 0 := by
          have := hJlt (b - 1) (by omega)
          rw [hJlo _ (by omega), h1, hs1] at this; simpa using this
        have hd1 : d (b - 1) = A := by
          rw [hd' _ (by omega), hτ, hJm]; simp [hT1, hκh]
        have hd2 : d b < d (b - 1) := by
          rw [hd1, hd' b hbM, hτ, hJ1]; simp [hT1, hκh]; linarith
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
        cases hT : T with
        | AND =>
          -- case (c): AND, the boundary is `M + b'`
          simp only [hT, reduceCtorEq, or_self, if_false, if_true, zero_add, one_mul] at h2
          have hq0 : 0 < q := by
            rcases Nat.eq_zero_or_pos q with rfl | h
            · rw [hJ'0] at h2; exact absurd h2 (by norm_num)
            · exact h
          have hJm : J' (q - 1) = 0 := by
            have := hJlt (M + (q - 1)) (by omega)
            rw [hJhi _ (by omega), hs1] at this; simpa [hT] using this
          have hd1 : d (M - 1 - q) = A := by
            rw [hd' _ (by omega), hτ, show M - 1 - (M - 1 - q) = q by omega, h2]; simp [hT, hκh]
          have hd2 : d (M - 1 - q + 1) < d (M - 1 - q) := by
            rw [hd1, hd' _ (by omega), hτ, show M - 1 - (M - 1 - q + 1) = q - 1 by omega, hJm]
            simp [hT, hκh]; linarith
          have hp1 := hpos (M - 1 - q) (by omega) hd1
          have hdr := hdrop (M - 1 - q) (by omega) hd2
          rw [show M - 1 - q + 1 = M - 1 - (q - 1) by omega] at hdr
          refine ⟨by omega, ?_⟩
          rw [show M + q - 1 = M + (q - 1) by omega, hhi q hqM, hhi (q - 1) (by omega),
            min_eq_left (neg_nonpos.2 hp1.le)]
          exact lt_min (neg_lt_neg hdr) (neg_neg_of_pos hp1)
        | NEV =>
          -- case (d): no carry out at all
          simp [hT] at h2
        | OR =>
          -- case (b): OR with `J' ≡ 0`; the boundary is the middle `M`
          have hJ0 : ∀ q' < M, J' q' = 0 := by
            intro q' hq'
            have := hJlt q' (by omega)
            rw [hJlo q' hq', hs1] at this; simpa [hT] using this
          have hq0 : q = 0 := by
            by_contra hq
            have := hJlt (M + 0) (by omega)
            rw [hJhi 0 (by omega), hs1] at this; simp [hT] at this
          subst hq0
          have hd1 : d (M - 1) = A := by
            rw [hd' _ (by omega), hτ, hJ0 (M - 1) (by omega)]; simp [hT, hκh]
          have hp1 := hpos (M - 1) (by omega) hd1
          refine ⟨by omega, ?_⟩
          rw [show M + 0 - 1 = M - 1 by omega, hhi 0 (by omega), hlo (M - 1) (by omega),
            max_eq_left hp1.le, Nat.sub_zero]
          exact lt_of_le_of_lt (min_le_right _ _) hp1
        | DIG =>
          -- case (b): DIG; the first half has no carry out, the boundary is the middle `M`
          have hq0 : q = 0 := by
            by_contra hq
            have := hJlt (M + 0) (by omega)
            rw [hJhi 0 (by omega), hs1] at this; simp [hT] at this
          subst hq0
          have hd1 : d (M - 1) = A := by
            rw [hd' _ (by omega), hτ]; simp [hT, hκh]
          have hp1 := hpos (M - 1) (by omega) hd1
          refine ⟨by omega, ?_⟩
          rw [show M + 0 - 1 = M - 1 by omega, hhi 0 (by omega), hlo (M - 1) (by omega),
            max_eq_left hp1.le, Nat.sub_zero]
          exact lt_of_le_of_lt (min_le_right _ _) hp1
    have hs : IsStrictCut (2 * M) (toR x) b := ⟨consequence_D_cut key.1 hb key.2, key.2⟩
    exact ⟨hs, (A3 (toR_antisymm hanti) key.1 hb).2.1 hs⟩

/-- Theorem F1_p for all houses, by induction on `|I|`. -/
lemma oddF_F1_all : ∀ (n : ℕ) (I : Finset ℕ) (k ℓ : ℕ) (e : ℤ), #I = n → (∀ t ∈ I, t < k) →
    (∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) → ℓ < p ^ k → 1 ≤ e →
      LamPropP p k I dg ℓ e ∧ CutPropP p k I dg ℓ e := by
  intro n
  induction n with
  | zero =>
    intro I k ℓ e hn _ _ hℓ he
    exact oddF_F1_empty (card_eq_zero.1 hn) hℓ e
  | succ n ih =>
    intro I k ℓ e hn hI hd hℓ he
    have hne : I.Nonempty := card_pos.1 (by omega)
    set c := I.max' hne with hc
    have hcI : c ∈ I := I.max'_mem hne
    have hI' : ∀ t ∈ I.erase c, t < c := fun t ht =>
      lt_of_le_of_ne (I.le_max' t (mem_of_mem_erase ht)) (ne_of_mem_erase ht)
    have hcard : #(I.erase c) = n := by rw [card_erase_of_mem hcI]; omega
    obtain ⟨h1, h2⟩ := ih (I.erase c) c (ℓ % p ^ c) e hcard hI' (hd_erase hd c)
      (Nat.mod_lt _ (pow_pos hp.out.pos c)) he
    exact oddF_F1_step hI hd hℓ he hne hc h1 h2

/-- **Theorem F1_p** (`CSI16_theorem_F_at_p.md`, Part F1): for every house
`H = (I, k, ℓ, e, d)` (`I ⊆ {0,…,k−1}`, `ℓ < p^k`, `d_t ∈ [1, p−1]` on `I`, `e ≥ 1`), with
`N = 2^{|I|}`:
* `(Λ_p)` for every `q < N`, `|ŷ_H(q)| ≤ e·o_I`;
* (Cut) if `b < N` is the first position with `J_H(b) = 1` (i.e. `J_H(b) = 1` and `J_H(q) = 0`
  for all `q < b`), then `x_H` has a strict cut at `b` and at `N − b`
  (`AntitonicFit.IsStrictCut N (toR x_H)`, which includes `0 < b`). -/
theorem oddF_theorem_F1 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    (∀ q < 2 ^ #I, |ifit (2 ^ #I) (xHseqP p k I dg ℓ e) q| ≤ e * (oW p dg I : ℤ)) ∧
    (∀ b < 2 ^ #I, JHseqP p k I dg ℓ b = 1 → (∀ q < b, JHseqP p k I dg ℓ q = 0) →
      IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) b ∧
        IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) (2 ^ #I - b)) :=
  oddF_F1_all _ I k ℓ e rfl hI hd hℓ he

/-- **Theorem F1_p**, `(Λ_p)` alone (`CSI16_theorem_F_at_p.md`, Part F1). -/
theorem oddF_F1_Lambda {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    ∀ q < 2 ^ #I, |ifit (2 ^ #I) (xHseqP p k I dg ℓ e) q| ≤ e * (oW p dg I : ℤ) :=
  (oddF_theorem_F1 hI hd hℓ he).1

/-- The remark of Part F1 of `CSI16_theorem_F_at_p.md`: `o_I ≤ p^k − 1`, so `(Λ_p)` gives
`|ŷ_H(q)| ≤ e·(p^k − 1)` (the form of C7's (Λ) with `2` replaced by `p`). -/
theorem oddF_F1_Lambda_pow {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    (oW p dg I : ℤ) ≤ (p : ℤ) ^ k - 1 ∧
      ∀ q < 2 ^ #I, |ifit (2 ^ #I) (xHseqP p k I dg ℓ e) q| ≤ e * ((p : ℤ) ^ k - 1) := by
  have hlt : oW p dg I < p ^ k := oW_lt_pow oddHou_two_le_p dg I hI
    (fun t ht => by have := hd t ht; have := oddHou_two_le_p (p := p); omega)
  have hle : (oW p dg I : ℤ) ≤ (p : ℤ) ^ k - 1 := by
    have : ((oW p dg I : ℕ) : ℤ) + 1 ≤ ((p ^ k : ℕ) : ℤ) := by exact_mod_cast hlt
    push_cast at this; linarith
  refine ⟨hle, fun q hq => (oddF_F1_Lambda hI hd hℓ he q hq).trans ?_⟩
  exact mul_le_mul_of_nonneg_left hle (by omega)

/-- **Theorem F1_p**, (Cut) alone (`CSI16_theorem_F_at_p.md`, Part F1). -/
theorem oddF_F1_Cut {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    ∀ b < 2 ^ #I, JHseqP p k I dg ℓ b = 1 → (∀ q < b, JHseqP p k I dg ℓ q = 0) →
      IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) b ∧
        IsStrictCut (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) (2 ^ #I - b) :=
  (oddF_theorem_F1 hI hd hℓ he).2

/-- (Cut) for the smaller house `H' = (I ∖ {c}, c, ℓ mod p^c, e, d)`, from Theorem F1_p. -/
lemma oddF_cut_erase_max {I : Finset ℕ} {ℓ : ℕ} {e : ℤ} (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (he : 1 ≤ e) (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) :
    CutPropP p c (I.erase c) dg (ℓ % p ^ c) e := by
  have hI' : ∀ t ∈ I.erase c, t < c := fun t ht => hc ▸
    lt_of_le_of_ne (I.le_max' t (mem_of_mem_erase ht)) (hc ▸ ne_of_mem_erase ht)
  exact oddF_F1_Cut hI' (hd_erase hd c) (Nat.mod_lt _ (pow_pos hp.out.pos c)) he

/-- **(W2)** of Theorem F0_p (`CSI16_theorem_F_at_p.md`, Part F0): for `q < M`,
`fit_M(x' + d_1) = fit_M(x') + d_1` and `ifit_M(x' + d_1) = ifit_M(x') + d_1`. -/
theorem oddF_W2 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1)
    (he : 1 ≤ e) (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) :
    (∀ q < 2 ^ #(I.erase c),
      fit (2 ^ #(I.erase c))
          (toR (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e + dWalkP p k I dg ℓ e c)) q =
        fit (2 ^ #(I.erase c)) (toR (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e)) q +
          dWalkP p k I dg ℓ e c q) ∧
    (∀ q < 2 ^ #(I.erase c),
      ifit (2 ^ #(I.erase c)) (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e + dWalkP p k I dg ℓ e c) q =
        ifit (2 ^ #(I.erase c)) (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e) q +
          dWalkP p k I dg ℓ e c q) :=
  oddF_W2_of_cut hd e c (oddF_cut_erase_max hd he hne hc)

/-- **(W3)** of Theorem F0_p (`CSI16_theorem_F_at_p.md`, Part F0): with `Z_1 := fit_M(x') + d_1`
and `X_1 := ifit_M(x') + d_1`, for every `q < N`,
`fit_N(x_H)(q) = concat_M(max(Z_1, 0), min(mirror_M(Z_1), 0))(q)` and
`ŷ_H(q) = concat_M(max(X_1, 0), min(mirror_M(X_1), 0))(q)`. -/
theorem oddF_W3 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (hne : I.Nonempty)
    {c : ℕ} (hc : c = I.max' hne) :
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
            dWalkP p k I dg ℓ e c) i) 0) q) :=
  oddF_W3_of_cut hI hd hℓ e hne hc (oddF_cut_erase_max hd he hne hc)

/-- **Theorem F0_p** (the walk; `CSI16_theorem_F_at_p.md`, Part F0), all four parts together.
For a house `H = (I, k, ℓ, e, d)` with `I ≠ ∅`, `c = max I`, `I' = I ∖ {c}`, `M = 2^{|I'|}`,
`H' = (I', c, ℓ mod p^c, e, d)`, `x' = x_{H'}`, `J' = J_{H'}` and `d_1 = dWalkP`:
(W0) `x_H(q) = x'(q) + d_1(q)` for `q < M`;
(W1) `d_1` is non-increasing on `[0, M)`, and if `0 < q < M` and `d_1(q − 1) ≠ d_1(q)` then
`J' ≢ 0` and `q = b'` or `q = M − b'` for the first position `b'` with `J'(b') = 1`;
(W2) `fit_M(x' + d_1) = fit_M(x') + d_1` and `ifit_M(x' + d_1) = ifit_M(x') + d_1` on `[0, M)`;
(W3) `fit_N(x_H) = concat_M(max(Z_1, 0), min(mirror_M(Z_1), 0))` and
`ŷ_H = concat_M(max(X_1, 0), min(mirror_M(X_1), 0))` on `[0, N)`. -/
theorem oddF_theorem_F0 {I : Finset ℕ} {k ℓ : ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (hne : I.Nonempty)
    {c : ℕ} (hc : c = I.max' hne) :
    -- (W0)
    (∀ q < 2 ^ #(I.erase c),
      xHseqP p k I dg ℓ e q = xHseqP p c (I.erase c) dg (ℓ % p ^ c) e q + dWalkP p k I dg ℓ e c q) ∧
    -- (W1)
    ((∀ q, q + 1 < 2 ^ #(I.erase c) → dWalkP p k I dg ℓ e c (q + 1) ≤ dWalkP p k I dg ℓ e c q) ∧
      ∀ q, 0 < q → q < 2 ^ #(I.erase c) →
        dWalkP p k I dg ℓ e c (q - 1) ≠ dWalkP p k I dg ℓ e c q →
        ∃ b' < 2 ^ #(I.erase c), JHseqP p c (I.erase c) dg (ℓ % p ^ c) b' = 1 ∧
          (∀ q' < b', JHseqP p c (I.erase c) dg (ℓ % p ^ c) q' = 0) ∧
          (q = b' ∨ q = 2 ^ #(I.erase c) - b')) ∧
    -- (W2)
    ((∀ q < 2 ^ #(I.erase c),
      fit (2 ^ #(I.erase c))
          (toR (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e + dWalkP p k I dg ℓ e c)) q =
        fit (2 ^ #(I.erase c)) (toR (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e)) q +
          dWalkP p k I dg ℓ e c q) ∧
    (∀ q < 2 ^ #(I.erase c),
      ifit (2 ^ #(I.erase c)) (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e + dWalkP p k I dg ℓ e c) q =
        ifit (2 ^ #(I.erase c)) (xHseqP p c (I.erase c) dg (ℓ % p ^ c) e) q +
          dWalkP p k I dg ℓ e c q)) ∧
    -- (W3)
    ((∀ q < 2 ^ #I, fit (2 ^ #I) (toR (xHseqP p k I dg ℓ e)) q =
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
            dWalkP p k I dg ℓ e c) i) 0) q)) :=
  ⟨oddF_W0 hI hd hℓ e hne hc,
    ⟨oddF_W1_antitone hd e c, oddF_W1_change hd e c⟩,
    oddF_W2 hd he hne hc, oddF_W3 hI hd hℓ he hne hc⟩

end ColouredSand.OddTwist
