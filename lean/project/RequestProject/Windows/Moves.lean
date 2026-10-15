module

public import RequestProject.Windows.Step

/-!
# Part W of `C14_windows_and_theorem_D.md`: the two moves preserve the window form

* `twist_step`: the twist move (`pT`, `κT` of C11) sends window data of level `h` to window data
  of level `h + 1`, with the same labels.
* `split_step`: the split move (`pSp`, `κSp` of C12), relabelled by `(s, j) ↦ 2s + j`, sends window
  data of level `h` labelled by `Dlab P` to window data of level `h + 1` labelled by
  `Dlab (P ∪ {h})`, provided `h ∈ J`.
-/

@[expose] public section

namespace Windows

open Finset Deficit Payment Split Dance

/-- **The twist move** of the proof of (W) (*Part W* of `C14_windows_and_theorem_D.md`). -/
theorem twist_step {J : Finset ℕ} {α : ℤ} {i h : ℕ} {P : Finset ℕ} {r : ℕ}
    {p : Fin r → ℕ → ℚ} {κ : Fin r → Fin r → ℕ → ℚ} (hP : ∀ t ∈ P, t < h)
    (hr : r = 2 ^ P.card) (hW : WinForm J α i h P p κ) :
    WinForm J α i (h + 1) P (pT p) (κT p κ) := by
  have e : ∀ f : ℕ, 2 ^ h * (2 * f) = 2 ^ (h + 1) * f := fun f => by ring
  refine ⟨fun s f => ?_, fun u s' f hlt => ?_⟩
  · have := core_pay hW s (2 * f)
    rw [e] at this
    exact this
  · have := core_coupling hP hr hW (2 * f) u s' hlt
    rw [e] at this
    exact this

/-- **The split move** of the proof of (W) (*Part W* of `C14_windows_and_theorem_D.md`): the
slot `2s` (the slot `A`) keeps the label `L_s`, the slot `2s + 1` (the slot `C`) gets the label
`L_s ∪ {h}`. -/
theorem split_step {J : Finset ℕ} {α : ℤ} {i h : ℕ} {P : Finset ℕ} {r : ℕ}
    {p : Fin r → ℕ → ℚ} {κ : Fin r → Fin r → ℕ → ℚ} (hP : ∀ t ∈ P, t < h)
    (hr : r = 2 ^ P.card) (hJ : h ∈ J) (hW : WinForm J α i h P p κ) :
    WinForm J α i (h + 1) (insert h P) (relabP (splitIso r).symm (pSp p))
      (relabK (splitIso r).symm (κSp p κ)) := by
  have hnot : ∀ s : ℕ, h ∉ Dlab P s := fun s hh => lt_irrefl _ (Dlab_lt hP s h hh)
  have hlab : ∀ (s : Fin r) (j : Fin 2), Dlab (insert h P) (splitIso r (toLex (s, j))) =
      if j = 1 then insert h (Dlab P s) else Dlab P s := by
    intro s j
    rw [splitIso_val, Dlab_split hP _ _ j.isLt]
    simp only [Fin.ext_iff, Fin.val_one]
  have hoins : ∀ s : ℕ, Rulers.oE (insert h (Dlab P s)) = Rulers.oE (Dlab P s) + 2 ^ h := by
    intro s; unfold Rulers.oE; rw [sum_insert (hnot s)]; ring
  have hsymm : ∀ (s : Fin r) (j : Fin 2),
      (splitIso r).symm (splitIso r (toLex (s, j))) = toLex (s, j) :=
    fun _ _ => OrderIso.symm_apply_apply _ _
  have hsurj : ∀ q : Fin (r * 2), ∃ s j, q = splitIso r (toLex (s, j)) := fun q =>
    ⟨(ofLex ((splitIso r).symm q)).1, (ofLex ((splitIso r).symm q)).2, by simp⟩
  have e0 : ∀ f : ℕ, 2 ^ h * (2 * f) = 2 ^ (h + 1) * f := fun f => by ring
  refine ⟨fun q f => ?_, fun Q q f hlt => ?_⟩
  · obtain ⟨s, j, rfl⟩ := hsurj q
    simp only [relabP, hsymm, hlab]
    fin_cases j
    · have := core_pay hW s (2 * f)
      rw [e0] at this
      simpa [pSp] using this
    · have := core_pay hW s (2 * f + 1)
      rw [show 2 * f + 1 + 1 = 2 * f + 2 by ring] at this
      simp only [pSp, ofLex_toLex]
      simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false, if_true, hoins]
      rw [this, show 2 ^ h * (2 * f + 1) = 2 ^ (h + 1) * f + 2 ^ h by ring]
      ring_nf
  · obtain ⟨u, j', rfl⟩ := hsurj Q
    obtain ⟨s, j, rfl⟩ := hsurj q
    have hlt' : toLex (s, j) < toLex (u, j') := (splitIso r).lt_iff_lt.1 hlt
    rw [Prod.Lex.toLex_lt_toLex] at hlt'
    simp only [relabK, hsymm, hlab]
    fin_cases j <;> fin_cases j'
    · -- (A, A)
      have hsu : s < u := by simpa using hlt'
      have := core_coupling hP hr hW (2 * f) u s hsu
      rw [e0] at this
      simp only [κSp, ofLex_toLex]
      simpa [hsu] using this
    · -- (A, C)
      have hsu : s ≤ u := by
        rcases hlt' with h1 | h1
        · exact le_of_lt (by simpa using h1)
        · exact le_of_eq (by simpa using h1.1)
      simp only [κSp, ofLex_toLex]
      simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, if_true, if_false, zero_ne_one,
        one_ne_zero, and_true, and_false]
      rcases eq_or_lt_of_le hsu with rfl | hsu'
      · rw [if_pos rfl, hW.1, if_pos (subset_insert _ _)]
        have hd : insert h (Dlab P s) \ Dlab P s = insert h ∅ := by
          ext t; by_cases hth : t = h
          · subst hth; simp [hnot]
          · simp [hth]
        rw [hd, c_succ_insert hJ (by simp), hoins,
          show 2 ^ h * (2 * f + 1) = 2 ^ (h + 1) * f + 2 ^ h by ring]
        ring_nf
      · rw [if_neg (ne_of_gt hsu'), if_pos hsu', hW.2 u s (2 * f + 1) hsu']
        simp only [subset_insert_iff_of_notMem (hnot s)]
        split_ifs with hn
        · rw [insert_sdiff_of_notMem _ (hnot s),
            c_succ_insert hJ (fun t ht => Dlab_lt hP u t (mem_sdiff.1 ht).1), hoins,
            show 2 ^ h * (2 * f + 1) = 2 ^ (h + 1) * f + 2 ^ h by ring]
          ring_nf
        · simp
    · -- (C, A)
      have hsu : s < u := by simpa using hlt'
      simp only [κSp, ofLex_toLex]
      have : ¬ insert h (Dlab P s) ⊆ Dlab P u := fun hs => hnot u (hs (mem_insert_self _ _))
      simp [this]
    · -- (C, C)
      have hsu : s < u := by simpa using hlt'
      have := core_coupling hP hr hW (2 * f + 1) u s hsu
      rw [show 2 * f + 1 + 1 = 2 * f + 2 by ring] at this
      simp only [κSp, ofLex_toLex]
      simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false, if_true, and_self, hsu,
        false_and]
      rw [this]
      simp only [insert_subset_insert_iff (hnot s), insert_sdiff_insert,
        sdiff_insert_of_notMem (hnot u), hoins,
        show 2 ^ h * (2 * f + 1) = 2 ^ (h + 1) * f + 2 ^ h by ring]
      split_ifs
      · ring_nf
      · rfl

end Windows
