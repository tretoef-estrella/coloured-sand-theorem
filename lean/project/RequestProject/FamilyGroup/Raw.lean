module

public import RequestProject.FamilyGroup.Basic

/-!
# `C16_the_family_group_over_Z2.md`, Part R: the raw clocks (`α = 1`)

(R0) `R0`, (R1) `R1`, (R2) `R2`.
-/

@[expose] public section

namespace FamilyGroup

open Windows TheoremF Finset AntitonicFit

/-- The antitonic fit commutes with adding a constant (proof of (R0) of
`C16_the_family_group_over_Z2.md`). -/
lemma fit_add_const (N : ℕ) (x : ℕ → ℝ) (c : ℝ) :
    ∀ j < N, fit N (fun j => x j + c) j = fit N x j + c := by
  apply fit_unique
  have hf := fit_isFit N x
  refine ⟨fun i hi => by have := hf.1 i hi; simp only; linarith, fun y hy => ?_⟩
  have h2 := hf.2 (fun j => y j - c) (fun i hi => by have := hy i hi; simp only; linarith)
  unfold sqDist at h2 ⊢
  convert h2 using 2 <;> ring

/-- **(R0)** of `C16_the_family_group_over_Z2.md` (Part R): pooling commutes with constants,
`ifit N (j ↦ x j + c) j = ifit N x j + c` for every `j < N`. -/
theorem R0 (N : ℕ) (x : ℕ → ℤ) (c : ℤ) :
    ∀ j < N, AntitonicFit.ifit N (fun j => x j + c) j = AntitonicFit.ifit N x j + c := by
  intro j hj
  have hR : toR (fun j => x j + c) = fun j => toR x j + (c : ℝ) := by
    funext i; simp [toR]
  have hfit := fit_add_const N (toR x) (c : ℝ)
  have hL : levelSet N (fit N (toR (fun j => x j + c))) j = levelSet N (fit N (toR x)) j := by
    unfold levelSet
    refine filter_congr fun i hi => ?_
    rw [mem_range] at hi
    rw [hR, hfit i hi, hfit j hj, add_left_inj]
  rw [ifit_of_lt hj, ifit_of_lt hj, hL, sum_add_distrib, sum_const, nsmul_eq_mul]
  have hpos : 0 < (levelSet N (fit N (toR x)) j).card :=
    card_pos.2 ⟨j, by simp [levelSet, hj]⟩
  exact blockF_add_mul _ _ hpos _

/-- **(R1)** of `C16_the_family_group_over_Z2.md` (Part R, `i ≥ 1`): for `α = 1`, `i ≥ 1` and
`p < N`, `k + C + ŷ p = ŷ_i(p)`, i.e.
`k + K + κ(i − 1, K) + ifit N x p = ifit N (j ↦ Rulers.clock k I i (dancer I j)) p`
(with `C = DanceSmith.Cst ds 1 i`, `ŷ = DanceSmith.yHat ds 1 i`, `x = DanceSmith.xClk ds 1 i`). -/
theorem R1 (ds : List Bool) (i : ℕ) (hi : 1 ≤ i) (p : ℕ) (hp : p < 2 ^ Dance.mCount ds) :
    (ds.length : ℤ) + 2 ^ ds.length + Rulers.kappa (i - 1) (2 ^ ds.length) +
        AntitonicFit.ifit (2 ^ Dance.mCount ds) (DanceSmith.xClk ds 1 i) p =
      AntitonicFit.ifit (2 ^ Dance.mCount ds)
        (fun j => Rulers.clock ds.length (Ids ds) i (dancer (Ids ds) j)) p ∧
    (ds.length : ℤ) + DanceSmith.Cst ds 1 i + DanceSmith.yHat ds 1 i p = yPool ds i p := by
  have hcl : (fun j => Rulers.clock ds.length (Ids ds) i (dancer (Ids ds) j)) =
      fun j => DanceSmith.xClk ds 1 i j +
        ((ds.length : ℤ) + 2 ^ ds.length + Rulers.kappa (i - 1) (2 ^ ds.length)) := by
    funext j
    rw [Rulers.proposition_5_3 (fun t ht => lt_of_mem_Ids ht) (lemma_0a _ j) i hi]
    simp only [DanceSmith.xClk, Rulers.xD, GoldenMatching.xVal, Nat.cast_one]
    ring
  have h1 : (ds.length : ℤ) + 2 ^ ds.length + Rulers.kappa (i - 1) (2 ^ ds.length) +
        AntitonicFit.ifit (2 ^ Dance.mCount ds) (DanceSmith.xClk ds 1 i) p =
      AntitonicFit.ifit (2 ^ Dance.mCount ds)
        (fun j => Rulers.clock ds.length (Ids ds) i (dancer (Ids ds) j)) p := by
    rw [hcl, R0 _ _ _ p hp]
    ring
  refine ⟨h1, ?_⟩
  rw [yPool, ← h1, DanceSmith.yHat, DanceSmith.Cst]
  push_cast
  ring

/-- **(R2)** of `C16_the_family_group_over_Z2.md` (Part R, `i = 0`): for `α = 1` and `q < N − 1`,
`k + K + ŷ^♯ q = ŷ_0(q)`, i.e.
`k + K + CellFloor.yhatSharp I k (K − 1) 1 q = ifit (N − 1) (j ↦ Rulers.clock k I 0
(dancer I (j + 1))) q`.  The hypothesis `I ≠ ∅` of the file is not needed (for `I = ∅` there is no
`q < N − 1 = 0`), so it is omitted. -/
theorem R2 (ds : List Bool) (q : ℕ) (hq : q < 2 ^ Dance.mCount ds - 1) :
    (ds.length : ℤ) + 2 ^ ds.length +
        CellFloor.yhatSharp (Ids ds) ds.length (2 ^ ds.length - 1) 1 q =
      AntitonicFit.ifit (2 ^ Dance.mCount ds - 1)
        (fun j => Rulers.clock ds.length (Ids ds) 0 (dancer (Ids ds) (j + 1))) q ∧
    (ds.length : ℤ) + 2 ^ ds.length + DanceSmith.yHatS ds 1 q = yPool0 ds q := by
  have hcl : ∀ j < 2 ^ Dance.mCount ds - 1,
      Rulers.clock ds.length (Ids ds) 0 (dancer (Ids ds) (j + 1)) =
        CellFloor.xSharp (Ids ds) ds.length (2 ^ ds.length - 1) 1 j +
          ((ds.length : ℤ) + 2 ^ ds.length) := by
    intro j hj
    have hne : dancer (Ids ds) (j + 1) ≠ ∅ := by
      intro h0
      have := DanceSmith.oE_dancer_pos (I := Ids ds) (p := j + 1) (by omega)
        (by rw [card_Ids]; omega)
      rw [h0, Rulers.oE_empty] at this
      exact lt_irrefl _ this
    rw [Rulers.proposition_5_4_c (fun t ht => lt_of_mem_Ids ht) hne (lemma_0a _ _)]
    simp only [CellFloor.xSharp, xHseq, Houses.xH, Houses.RH, Rulers.xSharp, Rulers.rulerSharp,
      Rulers.ruler]
    ring
  have h1 : (ds.length : ℤ) + 2 ^ ds.length +
        CellFloor.yhatSharp (Ids ds) ds.length (2 ^ ds.length - 1) 1 q =
      AntitonicFit.ifit (2 ^ Dance.mCount ds - 1)
        (fun j => Rulers.clock ds.length (Ids ds) 0 (dancer (Ids ds) (j + 1))) q := by
    rw [ifit_congr (x' := fun j => CellFloor.xSharp (Ids ds) ds.length (2 ^ ds.length - 1) 1 j +
          ((ds.length : ℤ) + 2 ^ ds.length)) hcl, R0 _ _ _ q hq, CellFloor.yhatSharp, card_Ids]
    ring
  refine ⟨h1, ?_⟩
  rw [yPool0, ← h1, DanceSmith.yHatS, Nat.cast_one]

end FamilyGroup
