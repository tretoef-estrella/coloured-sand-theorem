module

public import RequestProject.ThmGTwo.Smith

/-!
# `CSX3_theorems_F_G_prime_two.md`, Part B — the blocks at `p = 2`

Namespace `ColouredSand.ThmGTwo`; every new name starts with `two`.

## Encodings

* `FamilyGroup.X (Families.ds λ) e i` is the group of the tower of the family `λ` (C16, C32),
  with `e = v_2(q) = padicValNat 2 q` and `i = c + (m − λ)/2`.
* `ThmG.GBlk 2 q c k λ = (Fin (freeBlk c k) → ℤ_[2]) × ExpGrp 2 (blkList 2 q c k λ)` is CSG7's
  `G_c(λ + 2k, λ)` at `p = 2` (the definitions of CSG7 are generic in `p`); "`≅`" is `≃+`.
* The six digit lists are `ds 0 = []`, `ds 1 = [false]`, `ds 2 = [true]`, `ds 3 = [false, false]`,
  `ds 4 = [true, false]`, `ds 5 = [false, true]` (`twoDs_explicit`).
* `twoW α i t = α + v_2(i + t)`; with `α = v_2(q)` and `i = c + k` this is CSG7's
  `vt 2 q c k t = e + v_2(c + k + t)`.

## Proof

Not through `X1`/`X2`/`ŷ`, but by a direct computation of the cokernel: the final matrix in
o-order `DanceSmith.Mo ds α i` is `1 × 1` (`ds` with no `true`) or `2 × 2` lower triangular
(`ds` with one `true`: the dancers are `∅` and `I`).  Its entries vanish off the nested pairs
(`DanceSmith.Mo_off`), the entry at `(∅, ∅)` vanishes for `i = 0` (`DanceSmith.Mo_row_zero`), and
the `2`-adic valuations of the other entries are given by Theorem D (`DanceSmith.Mo_val`).  An
explicit integer Smith form with odd determinants (`twoSmith2_pos`, `twoSmith2_zero`) then gives
the cokernel (`twoX_N2_pos`, `twoX_N2_zero`, `twoX_N1_pos`; for `i = 0` and no dancer, C16 `X3`),
and the exponents are compared with `blkList` by unfolding CSG7's definitions.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmGTwo

open Windows TheoremF FamilyGroup ColouredSand.ThmG ColouredSand.Blocks ColouredSand.TiltP

/-! ### The six digit lists, and small facts decided by `decide` -/

/-- The digit lists of the families `λ ≤ 5` (Part B of `CSX3_theorems_F_G_prime_two.md`):
`ds 0 = []`, `ds 1 = [false]`, `ds 2 = [true]`, `ds 3 = [false, false]`, `ds 4 = [true, false]`,
`ds 5 = [false, true]`. -/
theorem twoDs_explicit :
    Families.ds 0 = [] ∧ Families.ds 1 = [false] ∧ Families.ds 2 = [true] ∧
      Families.ds 3 = [false, false] ∧ Families.ds 4 = [true, false] ∧
      Families.ds 5 = [false, true] := by
  have h0 := Families.ds_zero
  have h1 : Families.ds 1 = [false] := by rw [Families.ds_odd 0, h0]
  have h2 : Families.ds 2 = [true] := by rw [Families.ds_even 0, h0]
  have h3 : Families.ds 3 = [false, false] := by rw [Families.ds_odd 1, h1]
  have h4 : Families.ds 4 = [true, false] := by rw [Families.ds_even 1, h1]
  have h5 : Families.ds 5 = [false, true] := by rw [Families.ds_odd 2, h2]
  exact ⟨h0, h1, h2, h3, h4, h5⟩

lemma twoIds_f : Ids [false] = ∅ := by decide
lemma twoIds_ff : Ids [false, false] = ∅ := by decide
lemma twoIds_t : Ids [true] = {0} := by decide
lemma twoIds_tf : Ids [true, false] = {0} := by decide
lemma twoIds_ft : Ids [false, true] = {1} := by decide
lemma twoDancer_e0 : dancer ∅ 0 = ∅ := by decide
lemma twoDancer_00 : dancer {0} 0 = ∅ := by decide
lemma twoDancer_01 : dancer {0} 1 = {0} := by decide
lemma twoDancer_10 : dancer {1} 0 = ∅ := by decide
lemma twoDancer_11 : dancer {1} 1 = {1} := by decide
lemma twoOE_0 : Rulers.oE {0} = 1 := by decide
lemma twoOE_1 : Rulers.oE {1} = 2 := by decide
lemma twoDelta_e (k : ℕ) : Rulers.delta k ∅ = 0 := by simp [Rulers.delta]
lemma twoDelta_10 : Rulers.delta 1 {0} = 0 := by decide
lemma twoDelta_20 : Rulers.delta 2 {0} = 1 := by decide
lemma twoDelta_21 : Rulers.delta 2 {1} = 0 := by decide

/-- `twoW α i t = α + v_2(i + t)` (the clock weights; equal to CSG7's `vt 2 q c k t` for
`α = v_2(q)`, `i = c + k`). -/
def twoW (α i t : ℕ) : ℕ := α + padicValNat 2 (i + t)

/-- The computation of a valuation from `DanceSmith.Mo_val` (auxiliary tactic). -/
macro "two_val_tac" h:ident : tactic => `(tactic| (
  simp only [twoIds_f, twoIds_ff, twoIds_t, twoIds_tf, twoIds_ft, twoDancer_e0, twoDancer_00,
    twoDancer_01, twoDancer_10, twoDancer_11, twoOE_0, twoOE_1, twoDelta_e, twoDelta_10,
    twoDelta_20, twoDelta_21, Rulers.oE_empty, Finset.sdiff_self, Finset.sdiff_empty, Rulers.v2,
    Finset.sum_Ico_eq_sum_range, List.length_cons, List.length_nil] at $h:ident
  norm_num [Finset.sum_range_succ, twoDelta_10, twoDelta_20, twoDelta_21] at $h:ident
  simp only [twoW, add_zero]
  omega))

/-! ### The valuations of the entries of the final matrix -/

section Valuations

variable (α i : ℕ) (hα : 1 ≤ α)
include hα

lemma twoVal_f00 (hi : 1 ≤ i) :
    DanceSmith.Mo [false] α i ⟨0, by decide⟩ ⟨0, by decide⟩ ≠ 0 ∧
      padicValInt 2 (DanceSmith.Mo [false] α i ⟨0, by decide⟩ ⟨0, by decide⟩) =
        twoW α i 0 + twoW α i 1 - 1 := by
  have h := DanceSmith.Mo_val [false] (by decide) α i hα ⟨0, by decide⟩ ⟨0, by decide⟩ (by decide)
    (by omega)
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  generalize padicValInt 2 (DanceSmith.Mo [false] α i ⟨0, by decide⟩ ⟨0, by decide⟩) = v at h2 ⊢
  two_val_tac h2

lemma twoVal_ff00 (hi : 1 ≤ i) :
    DanceSmith.Mo [false, false] α i ⟨0, by decide⟩ ⟨0, by decide⟩ ≠ 0 ∧
      padicValInt 2 (DanceSmith.Mo [false, false] α i ⟨0, by decide⟩ ⟨0, by decide⟩) =
        twoW α i 0 + twoW α i 1 + twoW α i 2 + twoW α i 3 - 3 := by
  have h := DanceSmith.Mo_val [false, false] (by decide) α i hα ⟨0, by decide⟩ ⟨0, by decide⟩
    (by decide) (by omega)
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  generalize padicValInt 2 (DanceSmith.Mo [false, false] α i ⟨0, by decide⟩ ⟨0, by decide⟩) = v
    at h2 ⊢
  two_val_tac h2

lemma twoVal_t00 (hi : 1 ≤ i) :
    DanceSmith.Mo [true] α i ⟨0, by decide⟩ ⟨0, by decide⟩ ≠ 0 ∧
      padicValInt 2 (DanceSmith.Mo [true] α i ⟨0, by decide⟩ ⟨0, by decide⟩) =
        twoW α i 0 + twoW α i 1 - 1 := by
  have h := DanceSmith.Mo_val [true] (by decide) α i hα ⟨0, by decide⟩ ⟨0, by decide⟩ (by decide)
    (by omega)
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  generalize padicValInt 2 (DanceSmith.Mo [true] α i ⟨0, by decide⟩ ⟨0, by decide⟩) = v at h2 ⊢
  two_val_tac h2

lemma twoVal_t10 :
    DanceSmith.Mo [true] α i ⟨1, by decide⟩ ⟨0, by decide⟩ ≠ 0 ∧
      padicValInt 2 (DanceSmith.Mo [true] α i ⟨1, by decide⟩ ⟨0, by decide⟩) = twoW α i 1 := by
  have h := DanceSmith.Mo_val [true] (by decide) α i hα ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)
    (lt_add_of_le_of_pos (Nat.zero_le _) (by decide))
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  generalize padicValInt 2 (DanceSmith.Mo [true] α i ⟨1, by decide⟩ ⟨0, by decide⟩) = v at h2 ⊢
  two_val_tac h2

lemma twoVal_t11 :
    DanceSmith.Mo [true] α i ⟨1, by decide⟩ ⟨1, by decide⟩ ≠ 0 ∧
      padicValInt 2 (DanceSmith.Mo [true] α i ⟨1, by decide⟩ ⟨1, by decide⟩) =
        twoW α i 1 + twoW α i 2 - 1 := by
  have h := DanceSmith.Mo_val [true] (by decide) α i hα ⟨1, by decide⟩ ⟨1, by decide⟩ (by decide)
    (lt_add_of_le_of_pos (Nat.zero_le _) (by decide))
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  generalize padicValInt 2 (DanceSmith.Mo [true] α i ⟨1, by decide⟩ ⟨1, by decide⟩) = v at h2 ⊢
  two_val_tac h2

lemma twoVal_tf00 (hi : 1 ≤ i) :
    DanceSmith.Mo [true, false] α i ⟨0, by decide⟩ ⟨0, by decide⟩ ≠ 0 ∧
      padicValInt 2 (DanceSmith.Mo [true, false] α i ⟨0, by decide⟩ ⟨0, by decide⟩) =
        twoW α i 0 + twoW α i 1 + twoW α i 2 + twoW α i 3 - 3 := by
  have h := DanceSmith.Mo_val [true, false] (by decide) α i hα ⟨0, by decide⟩ ⟨0, by decide⟩
    (by decide) (by omega)
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  generalize padicValInt 2 (DanceSmith.Mo [true, false] α i ⟨0, by decide⟩ ⟨0, by decide⟩) = v
    at h2 ⊢
  two_val_tac h2

lemma twoVal_tf10 :
    DanceSmith.Mo [true, false] α i ⟨1, by decide⟩ ⟨0, by decide⟩ ≠ 0 ∧
      padicValInt 2 (DanceSmith.Mo [true, false] α i ⟨1, by decide⟩ ⟨0, by decide⟩) =
        twoW α i 1 + twoW α i 2 + twoW α i 3 - 1 := by
  have h := DanceSmith.Mo_val [true, false] (by decide) α i hα ⟨1, by decide⟩ ⟨0, by decide⟩
    (by decide) (lt_add_of_le_of_pos (Nat.zero_le _) (by decide))
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  generalize padicValInt 2 (DanceSmith.Mo [true, false] α i ⟨1, by decide⟩ ⟨0, by decide⟩) = v
    at h2 ⊢
  two_val_tac h2

lemma twoVal_tf11 :
    DanceSmith.Mo [true, false] α i ⟨1, by decide⟩ ⟨1, by decide⟩ ≠ 0 ∧
      padicValInt 2 (DanceSmith.Mo [true, false] α i ⟨1, by decide⟩ ⟨1, by decide⟩) =
        twoW α i 1 + twoW α i 2 + twoW α i 3 + twoW α i 4 - 3 := by
  have h := DanceSmith.Mo_val [true, false] (by decide) α i hα ⟨1, by decide⟩ ⟨1, by decide⟩
    (by decide) (lt_add_of_le_of_pos (Nat.zero_le _) (by decide))
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  generalize padicValInt 2 (DanceSmith.Mo [true, false] α i ⟨1, by decide⟩ ⟨1, by decide⟩) = v
    at h2 ⊢
  two_val_tac h2

lemma twoVal_ft00 (hi : 1 ≤ i) :
    DanceSmith.Mo [false, true] α i ⟨0, by decide⟩ ⟨0, by decide⟩ ≠ 0 ∧
      padicValInt 2 (DanceSmith.Mo [false, true] α i ⟨0, by decide⟩ ⟨0, by decide⟩) =
        twoW α i 0 + twoW α i 1 + twoW α i 2 + twoW α i 3 - 3 := by
  have h := DanceSmith.Mo_val [false, true] (by decide) α i hα ⟨0, by decide⟩ ⟨0, by decide⟩
    (by decide) (by omega)
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  generalize padicValInt 2 (DanceSmith.Mo [false, true] α i ⟨0, by decide⟩ ⟨0, by decide⟩) = v
    at h2 ⊢
  two_val_tac h2

lemma twoVal_ft10 :
    DanceSmith.Mo [false, true] α i ⟨1, by decide⟩ ⟨0, by decide⟩ ≠ 0 ∧
      padicValInt 2 (DanceSmith.Mo [false, true] α i ⟨1, by decide⟩ ⟨0, by decide⟩) =
        twoW α i 2 + twoW α i 3 - 1 := by
  have h := DanceSmith.Mo_val [false, true] (by decide) α i hα ⟨1, by decide⟩ ⟨0, by decide⟩
    (by decide) (lt_add_of_le_of_pos (Nat.zero_le _) (by decide))
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  generalize padicValInt 2 (DanceSmith.Mo [false, true] α i ⟨1, by decide⟩ ⟨0, by decide⟩) = v
    at h2 ⊢
  two_val_tac h2

lemma twoVal_ft11 :
    DanceSmith.Mo [false, true] α i ⟨1, by decide⟩ ⟨1, by decide⟩ ≠ 0 ∧
      padicValInt 2 (DanceSmith.Mo [false, true] α i ⟨1, by decide⟩ ⟨1, by decide⟩) =
        twoW α i 2 + twoW α i 3 + twoW α i 4 + twoW α i 5 - 3 := by
  have h := DanceSmith.Mo_val [false, true] (by decide) α i hα ⟨1, by decide⟩ ⟨1, by decide⟩
    (by decide) (lt_add_of_le_of_pos (Nat.zero_le _) (by decide))
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  generalize padicValInt 2 (DanceSmith.Mo [false, true] α i ⟨1, by decide⟩ ⟨1, by decide⟩) = v
    at h2 ⊢
  two_val_tac h2

end Valuations

/-! ### Vanishing entries -/

lemma twoMo_t01 (α i : ℕ) (hα : 1 ≤ α) :
    DanceSmith.Mo [true] α i ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 :=
  DanceSmith.Mo_off _ α i hα _ _ (by decide)

lemma twoMo_tf01 (α i : ℕ) (hα : 1 ≤ α) :
    DanceSmith.Mo [true, false] α i ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 :=
  DanceSmith.Mo_off _ α i hα _ _ (by decide)

lemma twoMo_ft01 (α i : ℕ) (hα : 1 ≤ α) :
    DanceSmith.Mo [false, true] α i ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 :=
  DanceSmith.Mo_off _ α i hα _ _ (by decide)

/-! ### Assembling `GBlk` -/

/-- For `c + k ≠ 0`: `⊕_{L₁} × ⊕_{L₂} ≅ ℤ_[2]^{freeBlk c k} × ⊕_{L}` when `L₁ ++ L₂ = L`
(auxiliary for (B1)). -/
def twoAsmPos {c k : ℕ} (hck : c + k ≠ 0) {L₁ L₂ L : List ℕ} (h : L₁ ++ L₂ = L) :
    ExpGrp 2 L₁ × ExpGrp 2 L₂ ≃+ (Fin (freeBlk c k) → ℤ_[2]) × ExpGrp 2 L := by
  unfold freeBlk
  rw [if_neg (by omega)]
  exact ((expAppend 2 L₁ L₂).symm.trans (expCast 2 h)).trans AddEquiv.uniqueProd.symm

/-- For `c = k = 0`: `⊕_{L₁} × (ℤ_[2] × ⊕_{L₂}) ≅ ℤ_[2]^{freeBlk 0 0} × ⊕_{L}` when
`L₁ ++ L₂ = L` (auxiliary for (B1)). -/
def twoAsmZero {L₁ L₂ L : List ℕ} (h : L₁ ++ L₂ = L) :
    ExpGrp 2 L₁ × ((Fin 1 → ℤ_[2]) × ExpGrp 2 L₂) ≃+
      (Fin (freeBlk 0 0) → ℤ_[2]) × ExpGrp 2 L := by
  unfold freeBlk
  rw [if_pos ⟨rfl, rfl⟩]
  exact (AddEquiv.prodAssoc.symm.trans ((AddEquiv.prodComm.prodCongr (AddEquiv.refl _)).trans
    AddEquiv.prodAssoc)).trans
      ((AddEquiv.refl _).prodCongr ((expAppend 2 L₁ L₂).symm.trans (expCast 2 h)))

/-- `ℤ_[2] ≅ ⊕_{[]} × (ℤ_[2]^1 × ⊕_{[]})` (auxiliary for (B1)). -/
def twoFreeOnly : ℤ_[2] ≃+ (Fin 1 → ℤ_[2]) × ExpGrp 2 [] :=
  (AddEquiv.piUnique fun _ : Fin 1 => ℤ_[2]).symm.trans AddEquiv.prodUnique.symm

/-- The simp set unfolding CSG7's `blkList` at `p = 2` (auxiliary tactic). -/
macro "two_blk_tac" : tactic => `(tactic| (
  simp [blkList, IsSimpleWt, rT, aT, chA, blkX, blkY, E11, E12, E22, blkA, blkA', blkAlpha,
    blkTau, lam, mu, vt, twoW, Dance.mCount, Finset.sum_range_succ, Finset.sum_Icc_succ_top] <;>
  omega))

/-- As `two_blk_tac`, also using the hypotheses in context (auxiliary tactic). -/
macro "two_blk_tac'" : tactic => `(tactic| (
  simp [*, blkList, IsSimpleWt, rT, aT, chA, blkX, blkY, E11, E12, E22, blkA, blkA', blkAlpha,
    blkTau, lam, mu, vt, twoW, Dance.mCount, Finset.sum_range_succ, Finset.sum_Icc_succ_top] <;>
  omega))

/-! ### The six blocks -/

section B

variable (q c k : ℕ) (hq : 1 ≤ padicValNat 2 q)
include hq

/-- (B1) for `λ = 0` (`ds 0 = []`). -/
lemma twoB_0 : Nonempty (X [] (padicValNat 2 q) (c + k) ≃+ GBlk 2 q c k 0) := by
  set α := padicValNat 2 q with hαdef
  by_cases hck : c + k = 0
  · obtain ⟨rfl, rfl⟩ : c = 0 ∧ k = 0 := by omega
    obtain ⟨e⟩ := TwoI.twoI_I1_nil_zero α hq
    exact ⟨e.toAddEquiv.trans (twoFreeOnly.trans (AddEquiv.uniqueProd.symm.trans
      (twoAsmZero (L₁ := []) (by two_blk_tac))))⟩
  · have hck' : ¬ (c = 0 ∧ k = 0) := by omega
    obtain ⟨e⟩ := TwoI.twoI_I1_nil_pos α (c + k) hq (by omega)
    exact ⟨e.toAddEquiv.trans ((twoQExp _).trans (AddEquiv.uniqueProd.symm.trans
      (twoAsmPos (L₁ := []) hck (by two_blk_tac'))))⟩

/-- (B1) for `λ = 1` (`ds 1 = [false]`). -/
lemma twoB_1 : Nonempty (X [false] (padicValNat 2 q) (c + k) ≃+ GBlk 2 q c k 1) := by
  set α := padicValNat 2 q with hαdef
  by_cases hck : c + k = 0
  · obtain ⟨rfl, rfl⟩ : c = 0 ∧ k = 0 := by omega
    obtain ⟨e⟩ := X3 [false] α hq twoIds_f
    exact ⟨e.toAddEquiv.trans (((twoSC_one false).prodCongr twoFreeOnly).trans
      (twoAsmZero (by two_blk_tac)))⟩
  · have hck' : ¬ (c = 0 ∧ k = 0) := by omega
    obtain ⟨e⟩ := twoX_N1_pos [false] α (c + k) hq (by decide) (twoVal_f00 α _ hq (by omega)).1
      (twoVal_f00 α _ hq (by omega)).2
    exact ⟨e.trans (((twoSC_one false).prodCongr (AddEquiv.refl _)).trans
      (twoAsmPos hck (by two_blk_tac')))⟩

/-- (B1) for `λ = 2` (`ds 2 = [true]`). -/
lemma twoB_2 : Nonempty (X [true] (padicValNat 2 q) (c + k) ≃+ GBlk 2 q c k 2) := by
  set α := padicValNat 2 q with hαdef
  by_cases hck : c + k = 0
  · obtain ⟨rfl, rfl⟩ : c = 0 ∧ k = 0 := by omega
    obtain ⟨e⟩ := twoX_N2_zero [true] α (0 + 0) hq (by decide) (twoMo_t01 α _ hq)
      (DanceSmith.Mo_row_zero [true] α hq _) (twoVal_t10 α _ hq).1 (twoVal_t11 α _ hq).1
      (twoVal_t10 α _ hq).2 (twoVal_t11 α _ hq).2
    exact ⟨e.trans (((twoSC_one true).prodCongr (AddEquiv.refl _)).trans
      (twoAsmZero (by two_blk_tac)))⟩
  · have hck' : ¬ (c = 0 ∧ k = 0) := by omega
    obtain ⟨e⟩ := twoX_N2_pos [true] α (c + k) hq (by decide) (twoMo_t01 α _ hq)
      (twoVal_t00 α _ hq (by omega)).1 (twoVal_t10 α _ hq).1 (twoVal_t11 α _ hq).1
      (twoVal_t00 α _ hq (by omega)).2 (twoVal_t10 α _ hq).2 (twoVal_t11 α _ hq).2
    exact ⟨e.trans (((twoSC_one true).prodCongr (AddEquiv.refl _)).trans
      (twoAsmPos hck (by two_blk_tac')))⟩

/-- (B1) for `λ = 3` (`ds 3 = [false, false]`). -/
lemma twoB_3 : Nonempty (X [false, false] (padicValNat 2 q) (c + k) ≃+ GBlk 2 q c k 3) := by
  set α := padicValNat 2 q with hαdef
  by_cases hck : c + k = 0
  · obtain ⟨rfl, rfl⟩ : c = 0 ∧ k = 0 := by omega
    obtain ⟨e⟩ := X3 [false, false] α hq twoIds_ff
    exact ⟨e.toAddEquiv.trans (((twoSC_two false false).prodCongr twoFreeOnly).trans
      (twoAsmZero (by two_blk_tac)))⟩
  · have hck' : ¬ (c = 0 ∧ k = 0) := by omega
    obtain ⟨e⟩ := twoX_N1_pos [false, false] α (c + k) hq (by decide)
      (twoVal_ff00 α _ hq (by omega)).1 (twoVal_ff00 α _ hq (by omega)).2
    exact ⟨e.trans (((twoSC_two false false).prodCongr (AddEquiv.refl _)).trans
      (twoAsmPos hck (by two_blk_tac')))⟩

/-- (B1) for `λ = 4` (`ds 4 = [true, false]`). -/
lemma twoB_4 : Nonempty (X [true, false] (padicValNat 2 q) (c + k) ≃+ GBlk 2 q c k 4) := by
  set α := padicValNat 2 q with hαdef
  by_cases hck : c + k = 0
  · obtain ⟨rfl, rfl⟩ : c = 0 ∧ k = 0 := by omega
    obtain ⟨e⟩ := twoX_N2_zero [true, false] α (0 + 0) hq (by decide) (twoMo_tf01 α _ hq)
      (DanceSmith.Mo_row_zero [true, false] α hq _) (twoVal_tf10 α _ hq).1
      (twoVal_tf11 α _ hq).1 (twoVal_tf10 α _ hq).2 (twoVal_tf11 α _ hq).2
    exact ⟨e.trans (((twoSC_two true false).prodCongr (AddEquiv.refl _)).trans
      (twoAsmZero (by two_blk_tac)))⟩
  · have hck' : ¬ (c = 0 ∧ k = 0) := by omega
    obtain ⟨e⟩ := twoX_N2_pos [true, false] α (c + k) hq (by decide) (twoMo_tf01 α _ hq)
      (twoVal_tf00 α _ hq (by omega)).1 (twoVal_tf10 α _ hq).1 (twoVal_tf11 α _ hq).1
      (twoVal_tf00 α _ hq (by omega)).2 (twoVal_tf10 α _ hq).2 (twoVal_tf11 α _ hq).2
    exact ⟨e.trans (((twoSC_two true false).prodCongr (AddEquiv.refl _)).trans
      (twoAsmPos hck (by two_blk_tac')))⟩

/-- (B1) for `λ = 5` (`ds 5 = [false, true]`). -/
lemma twoB_5 : Nonempty (X [false, true] (padicValNat 2 q) (c + k) ≃+ GBlk 2 q c k 5) := by
  set α := padicValNat 2 q with hαdef
  by_cases hck : c + k = 0
  · obtain ⟨rfl, rfl⟩ : c = 0 ∧ k = 0 := by omega
    obtain ⟨e⟩ := twoX_N2_zero [false, true] α (0 + 0) hq (by decide) (twoMo_ft01 α _ hq)
      (DanceSmith.Mo_row_zero [false, true] α hq _) (twoVal_ft10 α _ hq).1
      (twoVal_ft11 α _ hq).1 (twoVal_ft10 α _ hq).2 (twoVal_ft11 α _ hq).2
    exact ⟨e.trans (((twoSC_two false true).prodCongr (AddEquiv.refl _)).trans
      (twoAsmZero (by two_blk_tac)))⟩
  · have hck' : ¬ (c = 0 ∧ k = 0) := by omega
    obtain ⟨e⟩ := twoX_N2_pos [false, true] α (c + k) hq (by decide) (twoMo_ft01 α _ hq)
      (twoVal_ft00 α _ hq (by omega)).1 (twoVal_ft10 α _ hq).1 (twoVal_ft11 α _ hq).1
      (twoVal_ft00 α _ hq (by omega)).2 (twoVal_ft10 α _ hq).2 (twoVal_ft11 α _ hq).2
    exact ⟨e.trans (((twoSC_two false true).prodCongr (AddEquiv.refl _)).trans
      (twoAsmPos hck (by two_blk_tac')))⟩

end B

/-! ### (B1) -/

/-- **(B1)** of `CSX3_theorems_F_G_prime_two.md`, in the general form with `k` in place of
`(m − λ)/2`: for `λ ≤ 5`, `1 ≤ e = v_2(q)` and all `c, k`,
`X(ds λ, e, c + k) ≅ GBlk 2 q c k λ` (`= G_c(λ + 2k, λ)` at `p = 2`). -/
theorem twoB1_gen {lam : ℕ} (hl : lam ≤ 5) {q : ℕ} (hq : 1 ≤ padicValNat 2 q) (c k : ℕ) :
    Nonempty (X (Families.ds lam) (padicValNat 2 q) (c + k) ≃+ GBlk 2 q c k lam) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := twoDs_explicit
  interval_cases lam
  · rw [h0]; exact twoB_0 q c k hq
  · rw [h1]; exact twoB_1 q c k hq
  · rw [h2]; exact twoB_2 q c k hq
  · rw [h3]; exact twoB_3 q c k hq
  · rw [h4]; exact twoB_4 q c k hq
  · rw [h5]; exact twoB_5 q c k hq

/-- **(B1)** of `CSX3_theorems_F_G_prime_two.md`: for `λ ≤ 5`, `λ ≤ m`, `λ ≡ m (mod 2)`,
`e = v_2(q) ≥ 1` (so `q` is even) and every `c`,
`X(ds λ, e, c + (m − λ)/2) ≅ GBlk 2 q c ((m − λ)/2) λ`.  (The hypotheses `λ ≤ m` and
`λ ≡ m (mod 2)` of the file are kept but not needed: `twoB1_gen` holds for every `k`.) -/
theorem twoB1 {lam m q : ℕ} (c : ℕ) (hl : lam ≤ 5) (_hle : lam ≤ m) (_hpar : lam % 2 = m % 2)
    (hq : 1 ≤ padicValNat 2 q) :
    Nonempty (X (Families.ds lam) (padicValNat 2 q) (c + (m - lam) / 2) ≃+
      GBlk 2 q c ((m - lam) / 2) lam) :=
  twoB1_gen hl hq c _

end ColouredSand.ThmGTwo
