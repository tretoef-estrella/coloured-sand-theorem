module

public import RequestProject.Windows.Basic

/-!
# The dancers of a slot (*Setting* of `C14_windows_and_theorem_D.md`)

Properties of the labels `Dlab P s = {t ∈ P : testBit s (|P| − 1 − rank t)}`:
* `Dlab_split`: if every element of `P` is `< h`, the slots `2s` and `2s + 1` (the slots `A` and
  `C` of a split move at the digit `h`) have the labels `Dlab P s` and `Dlab P s ∪ {h}`;
* `Dlab_mono`: `Dlab P a ⊆ Dlab P b` implies `a ≤ b` (for `a, b < 2^{|P|}`);
* `Dlab_inj`, `Dlab_surj`: `Dlab P` is a bijection from `{0, …, 2^{|P|} − 1}` onto the subsets
  of `P`.
-/

@[expose] public section

namespace Windows

open Finset

/-- `Dlab P s ⊆ P` (*Setting*, "The dancers of a slot", of `C14_windows_and_theorem_D.md`). -/
lemma Dlab_subset (P : Finset ℕ) (s : ℕ) : Dlab P s ⊆ P := filter_subset _ _

/-- The labels of the slots `2s + j` after a split move at the digit `h` (*Setting*, "The dancers
of a slot", of `C14_windows_and_theorem_D.md`). -/
lemma Dlab_split {P : Finset ℕ} {h : ℕ} (hP : ∀ t ∈ P, t < h) (s j : ℕ) (hj : j < 2) :
    Dlab (insert h P) (2 * s + j) = if j = 1 then insert h (Dlab P s) else Dlab P s := by
  have hhP : h ∉ P := fun hh => lt_irrefl _ (hP h hh)
  have hcard : (insert h P).card = P.card + 1 := card_insert_of_notMem hhP
  have hrankh : rank (insert h P) h = P.card := by
    unfold rank
    congr 1
    ext t; simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨rfl | ht, hlt⟩
      · exact absurd hlt (lt_irrefl _)
      · exact ht
    · intro ht; exact ⟨Or.inr ht, hP t ht⟩
  have hrankt : ∀ t ∈ P, rank (insert h P) t = rank P t ∧ rank P t < P.card := by
    intro t ht
    refine ⟨?_, ?_⟩
    · unfold rank
      congr 1
      ext u; simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | hu, hlt⟩
        · exact absurd (lt_trans hlt (hP t ht)) (lt_irrefl _)
        · exact ⟨hu, hlt⟩
      · rintro ⟨hu, hlt⟩; exact ⟨Or.inr hu, hlt⟩
    · unfold rank
      apply card_lt_card
      refine ⟨filter_subset _ _, fun hsub => ?_⟩
      have := hsub ht
      simp at this
  ext t
  by_cases hth : t = h
  · subst hth
    simp only [Dlab, mem_filter, mem_insert, true_or, true_and, hcard, hrankh]
    rw [show P.card + 1 - 1 - P.card = 0 by omega, Nat.testBit_zero]
    interval_cases j <;> simp [hhP, Nat.mul_mod_right]
  · by_cases htP : t ∈ P
    · obtain ⟨hr1, hr2⟩ := hrankt t htP
      simp only [Dlab, mem_filter, mem_insert, hth, false_or, htP, true_and, hcard, hr1]
      rw [show P.card + 1 - 1 - rank P t = (P.card - 1 - rank P t) + 1 by omega,
        Nat.testBit_succ, show (2 * s + j) / 2 = s by omega]
      split_ifs <;> simp [hth, htP]
    · simp only [Dlab, mem_filter, mem_insert, hth, htP, false_or, false_and]
      split_ifs <;> simp [hth, htP]

/-- `Dlab P a ⊆ Dlab P b` implies `a ≤ b` for `a, b < 2^{|P|}` (*Setting*, "The dancers of a
slot", of `C14_windows_and_theorem_D.md`: `D(ds, s') ⊆ D(ds, s)` implies `s' ≤ s`). -/
lemma Dlab_mono (P : Finset ℕ) : ∀ a b : ℕ, a < 2 ^ P.card → b < 2 ^ P.card →
    Dlab P a ⊆ Dlab P b → a ≤ b := by
  induction P using Finset.induction_on_max with
  | h0 => intro a b ha hb _; simp at ha hb; omega
  | step h P hP ih =>
    intro a b ha hb hab
    have hhP : h ∉ P := fun hh => lt_irrefl _ (hP h hh)
    rw [card_insert_of_notMem hhP, pow_succ] at ha hb
    have ea : a = 2 * (a / 2) + a % 2 := by omega
    have eb : b = 2 * (b / 2) + b % 2 := by omega
    rw [ea, eb, Dlab_split hP _ _ (by omega), Dlab_split hP _ _ (by omega)] at hab
    have hsub : Dlab P (a / 2) ⊆ Dlab P (b / 2) := by
      intro t ht
      have ht' : t ∈ (if b % 2 = 1 then insert h (Dlab P (b / 2)) else Dlab P (b / 2)) := by
        apply hab
        split_ifs
        · exact mem_insert_of_mem ht
        · exact ht
      have htP : t ∈ P := Dlab_subset P _ ht
      have hth : t ≠ h := fun e => hhP (e ▸ htP)
      split_ifs at ht'
      · rcases mem_insert.1 ht' with e | e
        · exact absurd e hth
        · exact e
      · exact ht'
    have h1 := ih _ _ (by omega) (by omega) hsub
    have h2 : a % 2 = 1 → b % 2 = 1 := by
      intro ha1
      have hmem := hab (by rw [if_pos ha1]; exact mem_insert_self _ _)
      by_contra hb1
      rw [if_neg hb1] at hmem
      exact hhP (Dlab_subset P _ hmem)
    omega

/-- `Dlab P` is injective on `{0, …, 2^{|P|} − 1}` (*Setting*, "The dancers of a slot", of
`C14_windows_and_theorem_D.md`). -/
lemma Dlab_inj (P : Finset ℕ) {a b : ℕ} (ha : a < 2 ^ P.card) (hb : b < 2 ^ P.card)
    (hab : Dlab P a = Dlab P b) : a = b :=
  le_antisymm (Dlab_mono P a b ha hb hab.le) (Dlab_mono P b a hb ha hab.ge)

/-- Every subset of `P` is `Dlab P s` for some `s < 2^{|P|}` (*Setting*, "The dancers of a slot",
of `C14_windows_and_theorem_D.md`). -/
lemma Dlab_surj (P : Finset ℕ) : ∀ E ⊆ P, ∃ s < 2 ^ P.card, Dlab P s = E := by
  induction P using Finset.induction_on_max with
  | h0 => intro E hE; exact ⟨0, by simp, by simp [subset_empty.1 hE, Dlab]⟩
  | step h P hP ih =>
    intro E hE
    have hhP : h ∉ P := fun hh => lt_irrefl _ (hP h hh)
    have hE' : E.erase h ⊆ P := by
      intro t ht
      rw [mem_erase] at ht
      rcases mem_insert.1 (hE ht.2) with e | e
      · exact absurd e ht.1
      · exact e
    obtain ⟨s, hs, hsE⟩ := ih _ hE'
    refine ⟨2 * s + (if h ∈ E then 1 else 0), ?_, ?_⟩
    · rw [card_insert_of_notMem hhP, pow_succ]; split_ifs <;> omega
    · rw [Dlab_split hP _ _ (by split_ifs <;> omega), hsE]
      by_cases h1 : h ∈ E
      · simp only [h1, if_true]; exact insert_erase h1
      · simp only [h1, if_false, show (0 : ℕ) ≠ 1 by omega]; exact erase_eq_of_notMem h1

/-- Every label is contained in `{t : t < h}` when `P` is (*Setting* of
`C14_windows_and_theorem_D.md`). -/
lemma Dlab_lt {P : Finset ℕ} {h : ℕ} (hP : ∀ t ∈ P, t < h) (s : ℕ) : ∀ t ∈ Dlab P s, t < h :=
  fun t ht => hP t (Dlab_subset P s ht)

end Windows
