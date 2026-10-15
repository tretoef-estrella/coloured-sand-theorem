module

public import RequestProject.OddRulers.Digits

/-!
# `CSI13_the_odd_cost_form.md` — **Part L**: (L3) and (L4)

Namespace `ColouredSand.OddTwist`; encodings as in `Digits.lean`.  The digits are `dg : ℕ → ℕ`,
the set `I` satisfies `hI : ∀ t ∈ I, t < k` and `hd : ∀ t ∈ I, 0 < dg t ∧ dg t < p` (implied by
the file's `I = {t < k : d_t ≠ 0}` with all digits `< p`), the top digit is `dk` with
`1 ≤ dk ≤ p − 1`, and `K = d_k p^k` is `dk * p ^ k`.  C3's `Rulers.minOr k E` is `min E` with
`min ∅ := k`; C3's `Rulers.delta`, `Rulers.gamma`, `Rulers.h` are the deficit `δ`, the gold `γ`
and the gaps `h_t` (they only depend on `k` and `I`).
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset

variable {p : ℕ}

/-- `o_E ≥ 1` for a non-empty `E` all of whose digits are non-zero. -/
lemma one_le_oW {dg : ℕ → ℕ} {E : Finset ℕ} (hne : E.Nonempty) (hd : ∀ t ∈ E, 0 < dg t)
    (hp : 1 ≤ p) : 1 ≤ oW p dg E := by
  obtain ⟨t, ht⟩ := hne
  have h1 : dg t * p ^ t ≤ oW p dg E :=
    single_le_sum (f := fun t => dg t * p ^ t) (fun _ _ => Nat.zero_le _) ht
  have h2 : 1 ≤ dg t * p ^ t := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (hd t ht).ne' (pow_ne_zero _ (by omega)))
  omega

/-- `s_p(o_E − 1) + 1 = Σ_{t ∈ E} d_t + (p − 1) min E` for `E ≠ ∅` with digits in `[1, p − 1]`. -/
lemma sP_oW_sub_one (hp : 2 ≤ p) {dg : ℕ → ℕ} {E : Finset ℕ} (hne : E.Nonempty)
    (hd : ∀ t ∈ E, 0 < dg t ∧ dg t < p) :
    sP p (oW p dg E - 1) + 1 = ∑ t ∈ E, dg t + (p - 1) * E.min' hne := by
  set m := E.min' hne with hm_def
  have hm : m ∈ E := min'_mem _ _
  have hmle : ∀ t ∈ E, m ≤ t := fun t ht => min'_le _ _ ht
  let dg' : ℕ → ℕ := fun t => if t < m then p - 1 else if t = m then dg m - 1 else dg t
  have hdisj : Disjoint (range m) E := by
    rw [disjoint_left]; intro t ht ht'; have := hmle t ht'; simp at ht; omega
  have h1 : oW p dg' (range m) = oW p (fun _ => p - 1) (range m) :=
    sum_congr rfl (fun t ht => by simp only [dg', if_pos (mem_range.1 ht)])
  have hrest : ∀ t ∈ E.erase m, dg' t = dg t := by
    intro t ht
    have h1 := hmle t (mem_of_mem_erase ht)
    have h2 := ne_of_mem_erase ht
    simp only [dg', if_neg (show ¬ t < m by omega), if_neg h2]
  have hdm : dg' m = dg m - 1 := by simp [dg']
  have h2 : oW p dg' E + p ^ m = oW p dg E := by
    unfold oW
    rw [← add_sum_erase _ _ hm, ← add_sum_erase _ (fun t => dg t * p ^ t) hm,
      sum_congr rfl (fun t ht => by rw [hrest t ht]), hdm]
    obtain ⟨q, hq⟩ : ∃ q, dg m = q + 1 := ⟨dg m - 1, by have := (hd m hm).1; omega⟩
    rw [hq, Nat.add_sub_cancel]; ring
  have h3 := oW_const_range (p := p) (by omega) m
  have hU : oW p dg' (range m ∪ E) = oW p dg' (range m) + oW p dg' E := by
    unfold oW; exact sum_union hdisj
  have hF : oW p dg E - 1 = oW p dg' (range m ∪ E) := by
    rw [hU, h1]; omega
  have hdF : ∀ t ∈ range m ∪ E, dg' t < p := by
    intro t ht
    rcases mem_union.1 ht with h | h
    · simp only [dg', if_pos (mem_range.1 h)]; omega
    · simp only [dg']
      split_ifs with h' h''
      · omega
      · have := (hd m hm).2; omega
      · exact (hd t h).2
  have hA : ∑ t ∈ range m, dg' t = m * (p - 1) := by
    rw [sum_congr rfl (g := fun _ => p - 1)
      (fun t ht => by simp only [dg', if_pos (mem_range.1 ht)])]
    simp
  have hB : ∑ t ∈ E, dg' t + 1 = ∑ t ∈ E, dg t := by
    rw [← add_sum_erase _ _ hm, ← add_sum_erase _ _ hm, hdm]
    rw [sum_congr rfl hrest]
    have := (hd m hm).1
    have h1 : dg m - 1 + 1 = dg m := by omega
    linarith
  rw [hF, sP_oW hp _ _ hdF, sum_union hdisj, hA, Nat.mul_comm (p - 1) m]
  omega

/-- `s_p(K − 1 + o_E) + 1 = d_k + Σ_{t ∈ E} d_t + (p − 1) min E` for `E ⊆ [0, k)` with digits in
`[1, p − 1]` and `1 ≤ d_k < p` (with `min ∅ := k`: then this is `s_p(K − 1) = k(p − 1) + d_k − 1`). -/
lemma sP_K_sub_one_add (hp : 2 ≤ p) {k dk : ℕ} (hdk1 : 1 ≤ dk) (hdk : dk < p) {dg : ℕ → ℕ}
    {E : Finset ℕ} (hE : ∀ t ∈ E, t < k) (hd : ∀ t ∈ E, 0 < dg t ∧ dg t < p) :
    sP p (dk * p ^ k - 1 + oW p dg E) + 1 =
      dk + ∑ t ∈ E, dg t + (p - 1) * Rulers.minOr k E := by
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
  by_cases hne : E.Nonempty
  · have h1 := one_le_oW (p := p) hne (fun t ht => (hd t ht).1) (by omega)
    have hlt := oW_lt_pow (by omega) dg E hE (fun t ht => (hd t ht).2)
    have hdk' : 1 ≤ p ^ k * dk := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    rw [show dk * p ^ k - 1 + oW p dg E = (oW p dg E - 1) + p ^ k * dk by
      have := Nat.mul_comm dk (p ^ k); omega, sP_add_pow_mul hp k (oW p dg E - 1) dk (by omega), sP_lt hp hdk,
      Rulers.minOr, dif_pos hne]
    have := sP_oW_sub_one hp hne hd
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    subst hne
    have e : dk * p ^ k - 1 = (p ^ k - 1) + p ^ k * (dk - 1) := by
      obtain ⟨q, rfl⟩ : ∃ q, dk = q + 1 := ⟨dk - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; rw [add_mul, one_mul, Nat.mul_comm]; omega
    simp only [oW, sum_empty, add_zero, Rulers.minOr_empty]
    rw [e, sP_add_pow_mul hp k _ _ (by omega), sP_pow_sub_one hp, sP_lt hp (by omega)]
    rw [Nat.mul_comm (p - 1) k]
    omega

section padic

variable [hp : Fact p.Prime]

/-- **(L3)** (*Part L* of `CSI13_the_odd_cost_form.md`), first statement: `s_p(K) = d_k` for
`K = d_k p^k` (here only `d_k ≤ p − 1` is needed). -/
theorem L3_sP_K (k dk : ℕ) (hdk : dk ≤ p - 1) : sP p (dk * p ^ k) = dk := by
  have := hp.out.two_le
  rw [Nat.mul_comm, sP_pow_mul this, sP_lt this (by omega)]

/-- `κ_p(K − 1, o_E) = k − min E`, with the convention `min ∅ := k` (so `κ_p(K − 1, 0) = 0`). -/
theorem kappaP_K_sub_one {k dk : ℕ} (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1) {dg : ℕ → ℕ}
    {E : Finset ℕ} (hE : ∀ t ∈ E, t < k) (hd : ∀ t ∈ E, 0 < dg t ∧ dg t < p) :
    kappaP p (dk * p ^ k - 1) (oW p dg E) = (k : ℤ) - Rulers.minOr k E := by
  have h2 := hp.out.two_le
  have hp1 : ((p : ℤ) - 1) ≠ 0 := by omega
  apply mul_left_cancel₀ hp1
  rw [kappaP_mul, sP_oW h2 dg E (fun t ht => (hd t ht).2)]
  have e1 := sP_K_sub_one_add h2 hdk1 (by omega) hE hd
  have e0 := sP_K_sub_one_add (k := k) (dg := dg) (E := ∅) h2 hdk1 (by omega) (by simp) (by simp)
  simp only [oW, sum_empty, add_zero, Rulers.minOr_empty] at e0 e1
  have e0' : ((sP p (dk * p ^ k - 1) : ℕ) : ℤ) + 1 = dk + ((p : ℤ) - 1) * k := by
    have := congrArg (fun z : ℕ => (z : ℤ)) e0
    push_cast [show 1 ≤ p by omega] at this
    linarith
  have e1' : ((sP p (dk * p ^ k - 1 + ∑ t ∈ E, dg t * p ^ t) : ℕ) : ℤ) + 1 =
      dk + ∑ t ∈ E, (dg t : ℤ) + ((p : ℤ) - 1) * Rulers.minOr k E := by
    have := congrArg (fun z : ℕ => (z : ℤ)) e1
    push_cast [show 1 ≤ p by omega] at this
    linarith
  rw [oW]
  push_cast
  linear_combination e0' - e1'

/-- **(L3)** (*Part L* of `CSI13_the_odd_cost_form.md`), second statement: for `∅ ≠ E ⊆ I`,
`κ_p(K − 1, o_E) = k − min E`. -/
theorem L3_kappa {k : ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k)
    {dg : ℕ → ℕ} (hd : ∀ t ∈ I, 0 < dg t ∧ dg t < p) {dk : ℕ} (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1)
    {E : Finset ℕ} (hne : E.Nonempty) (hE : E ⊆ I) :
    kappaP p (dk * p ^ k - 1) (oW p dg E) = (k : ℤ) - E.min' hne := by
  rw [kappaP_K_sub_one hdk1 hdk (fun t ht => hI t (hE ht)) (fun t ht => hd t (hE ht)),
    Rulers.minOr, dif_pos hne]

end padic

/-- **(L4)** (*Part L* of `CSI13_the_odd_cost_form.md`), from C3's `Rulers.lemma_5_1_a`: for
`b ⊆ a ⊆ I` and `Δ = a ∖ b`, `|Δ| + δ(Δ) = Σ_{t ∈ a} h_t − Σ_{t ∈ b} h_t + γ(Δ)`, where
`δ = Rulers.delta k` (`δ(Δ) = k − |Δ| − min Δ`, `δ(∅) = 0`) and `γ = Rulers.gamma k I`. -/
theorem L4 {k : ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) {a b : Finset ℕ} (hba : b ⊆ a)
    (ha : a ⊆ I) :
    ((a \ b).card : ℤ) + Rulers.delta k (a \ b) =
      ∑ t ∈ a, (Rulers.h k I t : ℤ) - ∑ t ∈ b, (Rulers.h k I t : ℤ) +
        Rulers.gamma k I (a \ b) := by
  rw [Rulers.lemma_5_1_a hI (fun t ht => ha (mem_sdiff.1 ht).1), Rulers.G_sdiff hba,
    Rulers.G_eq, Rulers.G_eq, card_sdiff_of_subset hba]
  simp only [Rulers.hSum]
  push_cast [card_le_card hba]
  ring

end ColouredSand.OddTwist
