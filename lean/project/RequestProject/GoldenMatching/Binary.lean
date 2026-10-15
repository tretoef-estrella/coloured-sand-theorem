module

public import Mathlib

/-!
# Part A of `C4_golden_matching.md`: Theorem A (Theorem O in binary form)

Encodings (namespace `GoldenMatching`):

* `s : ℕ` and `N = 2^s` is written `2 ^ s`.
* `IsGoldenImage s p g` is the file's "`g` is a golden image of `p`": `g = p`, or there is
  `j < s` with `⌊p / 2^j⌋ = 2^{s−j} − 1` and `g = p mod 2^j`.  The file only uses it for
  `p, g ∈ {0, …, N − 1}`; in Theorem A this is guaranteed by the domain and codomain of `β`.
* The rows `{N − r, …, N − 1}` are the `Finset` `Finset.Ico (2^s - r) (2^s)` and the columns
  `{0, …, r − 1}` are `Finset.range r`; a bijection between them is an equivalence
  `β : Finset.Ico (2^s - r) (2^s) ≃ Finset.range r` of the corresponding subtypes.
* "Exactly one bijection" is stated as existence plus uniqueness: any two such bijections agree on
  every row.

The proof follows the file: induction on `s`, with the two cases `r ≤ N/2` and `r = N/2 + q`.
It goes through an auxiliary predicate `Good s r β` on functions `β : ℕ → ℕ` (maps the rows
injectively into the columns, through golden images).
-/

@[expose] public section

namespace GoldenMatching

open Finset

/-- *Part A* of `C4_golden_matching.md`: `g` is a **golden image** of `p` (with `N = 2^s`) if
`g = p`, or if there is `j < s` such that `⌊p / 2^j⌋ = 2^{s−j} − 1` (the bits `j, …, s − 1` of
`p` are all `1`) and `g = p mod 2^j`. -/
def IsGoldenImage (s p g : ℕ) : Prop :=
  g = p ∨ ∃ j < s, p / 2 ^ j = 2 ^ (s - j) - 1 ∧ g = p % 2 ^ j

/-- Arithmetic form of golden images (auxiliary): the block condition is `2^s − 2^j ≤ p`, and
clearing it subtracts `2^s − 2^j`. -/
def GoldA (s p g : ℕ) : Prop :=
  g = p ∨ ∃ j < s, 2 ^ s - 2 ^ j ≤ p ∧ g + (2 ^ s - 2 ^ j) = p

lemma isGoldenImage_iff_goldA {s p g : ℕ} (hp : p < 2 ^ s) :
    IsGoldenImage s p g ↔ GoldA s p g := by
  unfold IsGoldenImage GoldA
  apply or_congr Iff.rfl
  apply exists_congr; intro j
  apply and_congr_right; intro hj
  have hsplit : 2 ^ s = 2 ^ j * 2 ^ (s - j) := by rw [← pow_add]; congr 1; omega
  have hpos : 1 ≤ 2 ^ (s - j) := Nat.one_le_two_pow
  have hj1 : 0 < 2 ^ j := by positivity
  have hdm := Nat.div_add_mod p (2 ^ j)
  have hml := Nat.mod_lt p hj1
  have hdiv_lt : p / 2 ^ j < 2 ^ (s - j) := by
    rw [Nat.div_lt_iff_lt_mul hj1]; rw [hsplit] at hp; linarith
  have key : 2 ^ s - 2 ^ j = 2 ^ j * (2 ^ (s - j) - 1) := by
    rw [Nat.mul_sub, hsplit, mul_one]
  rw [key]
  constructor
  · rintro ⟨h1, rfl⟩
    rw [← h1]; constructor
    · exact Nat.mul_div_le p (2 ^ j)
    · omega
  · rintro ⟨h1, h2⟩
    have hge : 2 ^ (s - j) - 1 ≤ p / 2 ^ j := by
      rw [Nat.le_div_iff_mul_le hj1, mul_comm]; exact h1
    have heq : p / 2 ^ j = 2 ^ (s - j) - 1 := by omega
    refine ⟨heq, ?_⟩
    rw [heq] at hdm; omega

lemma goldA_self (s p : ℕ) : GoldA s p p := Or.inl rfl

/-- First case of the induction (rows with top bit `1`, columns with top bit `0`). -/
lemma goldA_succ_top {s p g : ℕ} (hp1 : 2 ^ s ≤ p) (hp2 : p < 2 ^ (s + 1)) (hg : g < 2 ^ s) :
    GoldA (s + 1) p g ↔ GoldA s (p - 2 ^ s) g := by
  have hN : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
  unfold GoldA
  constructor
  · rintro (rfl | ⟨j, hj, h1, h2⟩)
    · omega
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
      · have : 2 ^ j < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) hj'
        exact Or.inr ⟨j, hj', by omega, by omega⟩
      · left; omega
  · rintro (rfl | ⟨j, hj, h1, h2⟩)
    · exact Or.inr ⟨s, by omega, by omega, by omega⟩
    · have : 2 ^ j < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) hj
      exact Or.inr ⟨j, by omega, by omega, by omega⟩

/-- A golden image with top bit `1` of a number `< 2^{s+1}` is the number itself. -/
lemma goldA_succ_of_top_col {s p g : ℕ} (hp : p < 2 ^ (s + 1)) (hg : 2 ^ s ≤ g)
    (h : GoldA (s + 1) p g) : g = p := by
  rcases h with h | ⟨j, hj, h1, h2⟩
  · exact h
  · have hN : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    have : 2 ^ j ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- The only golden image of a number with top bit `0` is the number itself. -/
lemma goldA_succ_of_low_row {s p g : ℕ} (hp : p < 2 ^ s) (h : GoldA (s + 1) p g) : g = p := by
  rcases h with h | ⟨j, hj, h1, h2⟩
  · exact h
  · have hN : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    have : 2 ^ j ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- Auxiliary: `β` maps the rows `{N − r, …, N − 1}` injectively into the columns
`{0, …, r − 1}`, through golden images. -/
def Good (s r : ℕ) (β : ℕ → ℕ) : Prop :=
  (∀ p, 2 ^ s - r ≤ p → p < 2 ^ s → β p < r ∧ GoldA s p (β p)) ∧
  (∀ p p', 2 ^ s - r ≤ p → p < 2 ^ s → 2 ^ s - r ≤ p' → p' < 2 ^ s → β p = β p' → p = p')

lemma Good.surj {s r : ℕ} {β : ℕ → ℕ} (hβ : Good s r β) (hr : r ≤ 2 ^ s) {g : ℕ}
    (hg : g < r) : ∃ p, 2 ^ s - r ≤ p ∧ p < 2 ^ s ∧ β p = g := by
  obtain ⟨p, hp, hpg⟩ := surj_on_of_inj_on_of_card_le (s := Ico (2 ^ s - r) (2 ^ s))
    (t := range r) (fun p _ => β p)
    (fun p hp => by rw [mem_Ico] at hp; exact mem_range.2 (hβ.1 p hp.1 hp.2).1)
    (fun p p' hp hp' h => by
      rw [mem_Ico] at hp hp'; exact hβ.2 p p' hp.1 hp.2 hp'.1 hp'.2 h)
    (by simp; omega) g (mem_range.2 hg)
  rw [mem_Ico] at hp
  exact ⟨p, hp.1, hp.2, hpg.symm⟩

/-- First case of the induction step: for `r ≤ N/2` the problem `(s+1, r)` is the problem
`(s, r)` shifted by `N/2`. -/
lemma good_succ_iff {s r : ℕ} (hr : r ≤ 2 ^ s) (β : ℕ → ℕ) :
    Good (s + 1) r β ↔ Good s r (fun p => β (2 ^ s + p)) := by
  have hN : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
  unfold Good
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp1 hp2 => ?_, fun p p' hp1 hp2 hp1' hp2' h => ?_⟩
    · obtain ⟨hlt, hg⟩ := h1 (2 ^ s + p) (by omega) (by omega)
      refine ⟨hlt, ?_⟩
      rw [goldA_succ_top (by omega) (by omega) (by omega)] at hg
      simpa using hg
    · have := h2 (2 ^ s + p) (2 ^ s + p') (by omega) (by omega) (by omega) (by omega) h
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp1 hp2 => ?_, fun p p' hp1 hp2 hp1' hp2' h => ?_⟩
    · obtain ⟨hlt, hg⟩ := h1 (p - 2 ^ s) (by omega) (by omega)
      dsimp only at hlt hg
      rw [show 2 ^ s + (p - 2 ^ s) = p by omega] at hlt hg
      refine ⟨hlt, ?_⟩
      rwa [goldA_succ_top (by omega) (by omega) (by omega)]
    · have := h2 (p - 2 ^ s) (p' - 2 ^ s) (by omega) (by omega) (by omega) (by omega)
        (by dsimp only
            rw [show 2 ^ s + (p - 2 ^ s) = p by omega, show 2 ^ s + (p' - 2 ^ s) = p' by omega]
            exact h)
      omega

/-- Second case of the induction step (`r = N/2 + q`): every good `β` fixes the rows
`N/2 − q, …, N/2 + q − 1`, and is good for the problem `(s+1, N/2 − q)` on the other rows. -/
lemma good_second_case {s q : ℕ} (hq : q ≤ 2 ^ s) {β : ℕ → ℕ}
    (hβ : Good (s + 1) (2 ^ s + q) β) :
    (∀ p, 2 ^ s - q ≤ p → p < 2 ^ s + q → β p = p) ∧ Good (s + 1) (2 ^ s - q) β := by
  have hN : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
  have hfix : ∀ p, 2 ^ s - q ≤ p → p < 2 ^ s + q → β p = p := by
    intro p hp1 hp2
    by_cases hp : p < 2 ^ s
    · exact goldA_succ_of_low_row hp (hβ.1 p (by omega) (by omega)).2
    · obtain ⟨p', hp1', hp2', hp'⟩ := hβ.surj (by omega) hp2
      have := goldA_succ_of_top_col hp2' (by omega) (hβ.1 p' hp1' hp2').2
      rw [hp'] at this
      subst this; exact hp'
  refine ⟨hfix, fun p hp1 hp2 => ?_, fun p p' hp1 hp2 hp1' hp2' h => ?_⟩
  · obtain ⟨hlt, hg⟩ := hβ.1 p (by omega) hp2
    refine ⟨?_, hg⟩
    by_contra hcon
    have h2 := hfix (β p) (by omega) hlt
    have := hβ.2 p (β p) (by omega) hp2 (by omega) (by omega) h2.symm
    omega
  · exact hβ.2 p p' (by omega) hp2 (by omega) hp2' h

/-- The core of Theorem A (auxiliary form): for `r ≤ 2^s` there is a good `β`, and any two
good maps agree on the rows. -/
theorem good_existsUnique : ∀ s r : ℕ, r ≤ 2 ^ s →
    (∃ β, Good s r β) ∧
      ∀ β β', Good s r β → Good s r β' → ∀ p, 2 ^ s - r ≤ p → p < 2 ^ s → β p = β' p := by
  intro s
  induction s with
  | zero =>
    intro r hr
    refine ⟨⟨id, fun p hp1 hp2 => ?_, fun p p' _ hp2 _ hp2' _ => by simp at hp2 hp2'; omega⟩,
      fun β β' hβ hβ' p hp1 hp2 => ?_⟩
    · simp at hp2 hr ⊢; subst hp2; exact ⟨by omega, goldA_self _ _⟩
    · have a := (hβ.1 p hp1 hp2).1
      have b := (hβ'.1 p hp1 hp2).1
      simp at hr; omega
  | succ s ih =>
    -- the first case, as a function of `r ≤ 2^s`
    have case1 : ∀ r, r ≤ 2 ^ s → (∃ β, Good (s + 1) r β) ∧
        ∀ β β', Good (s + 1) r β → Good (s + 1) r β' →
          ∀ p, 2 ^ (s + 1) - r ≤ p → p < 2 ^ (s + 1) → β p = β' p := by
      intro r hr
      have hN : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
      obtain ⟨⟨β₀, hβ₀⟩, huniq⟩ := ih r hr
      refine ⟨⟨fun p => β₀ (p - 2 ^ s), ?_⟩, fun β β' hβ hβ' p hp1 hp2 => ?_⟩
      · rw [good_succ_iff hr]; simpa using hβ₀
      · rw [good_succ_iff hr] at hβ hβ'
        have := huniq _ _ hβ hβ' (p - 2 ^ s) (by omega) (by omega)
        simpa [show 2 ^ s + (p - 2 ^ s) = p by omega] using this
    intro r hr
    by_cases hrs : r ≤ 2 ^ s
    · exact case1 r hrs
    · have hN : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
      obtain ⟨q, rfl⟩ : ∃ q, r = 2 ^ s + q := ⟨r - 2 ^ s, by omega⟩
      have hq : q ≤ 2 ^ s := by omega
      obtain ⟨⟨β₁, hβ₁⟩, huniq₁⟩ := case1 (2 ^ s - q) (by omega)
      refine ⟨⟨fun p => if p < 2 ^ s + q then p else β₁ p, ?_, ?_⟩, ?_⟩
      · intro p hp1 hp2
        by_cases hp : p < 2 ^ s + q
        · dsimp only; rw [if_pos hp]; exact ⟨hp, goldA_self _ _⟩
        · dsimp only; rw [if_neg hp]
          obtain ⟨h1, h2⟩ := hβ₁.1 p (by omega) hp2
          exact ⟨by omega, h2⟩
      · intro p p' hp1 hp2 hp1' hp2' h
        by_cases hp : p < 2 ^ s + q <;> by_cases hp' : p' < 2 ^ s + q <;>
          simp only [hp, hp', if_true, if_false] at h
        · exact h
        · have := (hβ₁.1 p' (by omega) hp2').1; omega
        · have := (hβ₁.1 p (by omega) hp2).1; omega
        · exact hβ₁.2 p p' (by omega) hp2 (by omega) hp2' h
      · intro β β' hβ hβ' p hp1 hp2
        obtain ⟨hf, hg⟩ := good_second_case hq hβ
        obtain ⟨hf', hg'⟩ := good_second_case hq hβ'
        by_cases hp : p < 2 ^ s + q
        · rw [hf p (by omega) hp, hf' p (by omega) hp]
        · exact huniq₁ β β' hg hg' p (by omega) hp2

/-- **Theorem A** (Theorem O, binary form) of `C4_golden_matching.md`: for every `s ≥ 0` and
every `0 ≤ r ≤ N = 2^s` there is exactly one bijection
`β : {N − r, …, N − 1} → {0, …, r − 1}` such that `β(p)` is a golden image of `p` for every `p`.
"Exactly one" is stated as existence plus uniqueness (any two such bijections agree on every
row). -/
theorem theorem_A (s r : ℕ) (hr : r ≤ 2 ^ s) :
    (∃ β : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ) ≃ (range r : Finset ℕ),
        ∀ p : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ), IsGoldenImage s p (β p)) ∧
      ∀ β β' : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ) ≃ (range r : Finset ℕ),
        (∀ p : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ), IsGoldenImage s p (β p)) →
        (∀ p : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ), IsGoldenImage s p (β' p)) →
        ∀ p, β p = β' p := by
  obtain ⟨⟨β₀, hβ₀⟩, huniq⟩ := good_existsUnique s r hr
  -- an equivalence gives a good function
  have toGood : ∀ β : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ) ≃ (range r : Finset ℕ),
      (∀ p : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ), IsGoldenImage s p (β p)) →
        Good s r (fun p => if h : p ∈ Ico (2 ^ s - r) (2 ^ s) then (β ⟨p, h⟩ : ℕ) else 0) := by
    intro β hβ
    refine ⟨fun p hp1 hp2 => ?_, fun p p' hp1 hp2 hp1' hp2' h => ?_⟩
    · have hm : p ∈ Ico (2 ^ s - r) (2 ^ s) := mem_Ico.2 ⟨hp1, hp2⟩
      simp only [hm, dif_pos]
      exact ⟨mem_range.1 (β ⟨p, hm⟩).2, (isGoldenImage_iff_goldA hp2).1 (hβ ⟨p, hm⟩)⟩
    · have hm : p ∈ Ico (2 ^ s - r) (2 ^ s) := mem_Ico.2 ⟨hp1, hp2⟩
      have hm' : p' ∈ Ico (2 ^ s - r) (2 ^ s) := mem_Ico.2 ⟨hp1', hp2'⟩
      simp only [hm, hm', dif_pos] at h
      have := β.injective (Subtype.ext h)
      simpa using this
  refine ⟨?_, fun β β' hβ hβ' p => ?_⟩
  · -- build the equivalence from the good function `β₀`
    have hmaps : ∀ p : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ), β₀ p ∈ range r := fun p =>
      mem_range.2 (hβ₀.1 p (mem_Ico.1 p.2).1 (mem_Ico.1 p.2).2).1
    let F : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ) → (range r : Finset ℕ) :=
      fun p => ⟨β₀ p, hmaps p⟩
    have hinj : Function.Injective F := by
      intro p p' h
      have := congrArg Subtype.val h
      exact Subtype.ext (hβ₀.2 p p' (mem_Ico.1 p.2).1 (mem_Ico.1 p.2).2 (mem_Ico.1 p'.2).1
        (mem_Ico.1 p'.2).2 this)
    have hbij : Function.Bijective F := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hinj, by simp only [Fintype.card_coe, Nat.card_Ico, card_range]; omega⟩
    refine ⟨Equiv.ofBijective F hbij, fun p => ?_⟩
    have hp2 := (mem_Ico.1 p.2).2
    rw [isGoldenImage_iff_goldA hp2]
    exact (hβ₀.1 p (mem_Ico.1 p.2).1 hp2).2
  · have := huniq _ _ (toGood β hβ) (toGood β' hβ') p (mem_Ico.1 p.2).1 (mem_Ico.1 p.2).2
    simp only [p.2, dif_pos] at this
    exact Subtype.ext this

end GoldenMatching
