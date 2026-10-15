module

public import RequestProject.Rulers.Family

/-!
# Binary digit counts used in Propositions 5.2–5.4 of `C3_rulers_gold_clocks.md`

Auxiliary facts (encodings as in `Basic.lean` and `Family.lean`):
* `s_2(o_E − 1) = |E| − 1 + min E` for `E ≠ ∅`;
* `s_2(K − 1 + o_E) = |E| + min E` for `E ⊆ {0, …, k − 1}` (with `min ∅ := k`);
* `κ(K − 1, o_E) = k − min E` (with `min ∅ := k`);
* the carry count of Step 1 of Proposition 5.3: `s_2(K − 1 − o_D + o_E) = k − |D| − G(E)`
  for `D ⊆ I` and `E = I ∖ D`.
-/

@[expose] public section

namespace Rulers

open Finset

variable {k : ℕ} {I : Finset ℕ}

lemma s2_oE_sub_one {E : Finset ℕ} (hne : E.Nonempty) :
    s2 (oE E - 1) + 1 = E.card + E.min' hne := by
  set m := E.min' hne
  have hm : m ∈ E := min'_mem _ _
  have hdisj : Disjoint (range m) (E.erase m) := by
    rw [disjoint_left]; intro x hx hx'
    have := min'_le E x (mem_of_mem_erase hx')
    simp at hx; omega
  have h1 : oE E = 2 ^ m + oE (E.erase m) := by
    rw [oE, ← add_sum_erase _ _ hm, ← oE]
  have h2 := oE_range m
  have h3 : oE E - 1 = oE (range m ∪ E.erase m) := by
    rw [oE_union hdisj]; omega
  rw [h3, s2_oE, card_union_of_disjoint hdisj, card_range, card_erase_of_mem hm]
  have := card_pos.2 hne
  omega

lemma s2_two_pow_sub_one (k : ℕ) : s2 (2 ^ k - 1) = k := by
  have := oE_range k
  rw [show 2 ^ k - 1 = oE (range k) by omega, s2_oE, card_range]

/-- `s_2(K − 1 + o_E) = |E| + min E`, with `min ∅ := k`. -/
lemma s2_K_sub_one_add {E : Finset ℕ} (hE : ∀ t ∈ E, t < k) :
    s2 (2 ^ k - 1 + oE E) = E.card + minOr k E := by
  by_cases hne : E.Nonempty
  · have hlt := oE_lt E k hE
    have hpos : 0 < oE E := by
      obtain ⟨x, hx⟩ := hne
      exact lt_of_lt_of_le (Nat.two_pow_pos x) (single_le_sum (by simp) hx)
    have hK : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [show 2 ^ k - 1 + oE E = (oE E - 1) + 2 ^ k * 1 by omega,
      s2_add_two_pow_mul _ _ _ (by omega), s2_one, s2_oE_sub_one hne, minOr, dif_pos hne]
  · rw [not_nonempty_iff_eq_empty] at hne
    subst hne
    simp [oE_empty, minOr_empty, s2_two_pow_sub_one]

/-- `κ(K − 1, o_E) = k − min E`, with `min ∅ := k`. -/
lemma kappa_K_sub_one {E : Finset ℕ} (hE : ∀ t ∈ E, t < k) :
    kappa (2 ^ k - 1) (oE E) = (k : ℤ) - minOr k E := by
  rw [kappa, s2_K_sub_one_add hE, s2_two_pow_sub_one, s2_oE]; push_cast; ring

/-- The carry count of Step 1 of **Proposition 5.3**: for `D ⊆ I` and `E = I ∖ D`, every
`n` with `n = K − 1 − o_D + o_E` has `s_2(n) = k − |D| − G(E)`. -/
lemma s2_core (hI : ∀ t ∈ I, t < k) {D : Finset ℕ} (hD : D ⊆ I) (n : ℕ)
    (hn : (n : ℤ) = 2 ^ k - 1 - oE D + oE (I \ D)) :
    (s2 n : ℤ) = k - D.card - G k I (I \ D) := by
  classical
  -- the blocks of bits
  let B : ℕ → Finset ℕ := fun t => if t ∈ D then Ico (t + 1) (next k I t) else {next k I t}
  have hBsub : ∀ t ∈ I, ∀ x ∈ B t, t + 1 ≤ x ∧ x ≤ next k I t := by
    intro t ht x hx
    have := next_spec hI ht
    by_cases htD : t ∈ D
    · simp only [B, if_pos htD, mem_Ico] at hx; omega
    · simp only [B, if_neg htD, mem_singleton] at hx; omega
  have hpair : (I : Set ℕ).PairwiseDisjoint B := by
    intro t ht t' ht' hne
    rw [Function.onFun, disjoint_left]
    intro x hx hx'
    have h1 := hBsub t ht x hx
    have h2 := hBsub t' ht' x hx'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := next_le_of_mem (k := k) (I := I) ht' hlt; omega
    · have := next_le_of_mem (k := k) (I := I) ht hlt; omega
  have hdisj : Disjoint (range (t1 k I)) (I.biUnion B) := by
    rw [disjoint_left]; intro x hx hx'
    obtain ⟨t, ht, hxt⟩ := mem_biUnion.1 hx'
    have := hBsub t ht x hxt
    have := minOr_le (k := k) ht
    simp [t1] at hx; omega
  set F := range (t1 k I) ∪ I.biUnion B with hF
  -- the value of each block
  have hIco : ∀ a b, a ≤ b → (oE (Ico a b) : ℤ) = 2 ^ b - 2 ^ a := by
    intro a b hab
    have h1 := oE_range a
    have h2 := oE_range b
    have h3 : oE (range b) = oE (range a) + oE (Ico a b) := by
      simp only [oE, range_eq_Ico]; rw [sum_Ico_consecutive _ (Nat.zero_le a) hab]
    have : ((oE (range b) : ℕ) : ℤ) = oE (range a) + oE (Ico a b) := by exact_mod_cast h3
    have e1 : ((oE (range a) : ℕ) : ℤ) = 2 ^ a - 1 := by
      have : ((oE (range a) + 1 : ℕ) : ℤ) = ((2 ^ a : ℕ) : ℤ) := by rw [h1]
      push_cast at this; linarith
    have e2 : ((oE (range b) : ℕ) : ℤ) = 2 ^ b - 1 := by
      have : ((oE (range b) + 1 : ℕ) : ℤ) = ((2 ^ b : ℕ) : ℤ) := by rw [h2]
      push_cast at this; linarith
    linarith
  have hBval : ∀ t ∈ I, (oE (B t) : ℤ) =
      ((2 : ℤ) ^ next k I t - 2 ^ t) + (if t ∈ D then -(2 : ℤ) ^ t else 2 ^ t) := by
    intro t ht
    have := next_spec hI ht
    by_cases htD : t ∈ D
    · simp only [B, if_pos htD]; rw [hIco _ _ (by omega), pow_succ]; ring
    · simp only [B, if_neg htD, oE, sum_singleton]; push_cast; ring
  have hBcard : ∀ t ∈ I, ((B t).card : ℤ) = (if t ∈ D then (h k I t : ℤ) - 1 else 1) := by
    intro t ht
    have := next_spec hI ht
    by_cases htD : t ∈ D
    · simp only [B, if_pos htD, Nat.card_Ico, h]; push_cast [show t + 1 ≤ next k I t by omega,
        show t ≤ next k I t by omega]; ring
    · simp [B, htD]
  -- value of `F`
  have hoF : (oE F : ℤ) = 2 ^ k - 1 - oE D + oE (I \ D) := by
    rw [hF, oE_union hdisj]
    push_cast
    have hr := oE_range (t1 k I)
    have hr' : ((oE (range (t1 k I)) : ℕ) : ℤ) = 2 ^ (t1 k I) - 1 := by
      have : ((oE (range (t1 k I)) + 1 : ℕ) : ℤ) = ((2 ^ t1 k I : ℕ) : ℤ) := by rw [hr]
      push_cast at this; linarith
    have hb : ((oE (I.biUnion B) : ℕ) : ℤ) = ∑ t ∈ I, (oE (B t) : ℤ) := by
      simp only [oE]; rw [sum_biUnion hpair]; push_cast; rfl
    rw [hr', hb, sum_congr rfl hBval, sum_add_distrib,
      telescope_all hI (fun t => (2 : ℤ) ^ t), sum_ite, filter_mem_eq_inter,
      inter_eq_right.2 hD]
    have hfl : I.filter (fun t => t ∉ D) = I \ D := by ext; simp
    rw [hfl]
    simp only [oE, sum_neg_distrib]; push_cast; ring
  have hcard : (F.card : ℤ) = t1 k I + G k I D + (I \ D).card := by
    rw [hF, card_union_of_disjoint hdisj, card_biUnion hpair]
    push_cast
    rw [sum_congr rfl hBcard, sum_ite, filter_mem_eq_inter, inter_eq_right.2 hD]
    have hfl : I.filter (fun t => t ∉ D) = I \ D := by ext; simp
    rw [hfl, card_range]
    simp only [G, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]; ring
  have hnF : n = oE F := by
    have : (n : ℤ) = oE F := by rw [hn, hoF]
    exact_mod_cast this
  rw [hnF, s2_oE, hcard]
  have hk := k_eq_t1_add_sum_h hI
  rw [← sum_sdiff hD] at hk
  have hGE := G_eq (k := k) (I := I) (I \ D)
  have hGD := G_eq (k := k) (I := I) D
  have hcardE : ((I \ D).card : ℤ) = I.card - D.card := by
    rw [card_sdiff_of_subset hD]; push_cast [card_le_card hD]; ring
  simp only [hSum] at hGE hGD
  push_cast at hGE hGD
  linarith

end Rulers
