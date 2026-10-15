module

public import RequestProject.ThmG.Sylow
public import RequestProject.ThmG.Glue

/-!
# `CSG7_theorem_G.md`, Part X — the Example `Syl_3 K(H(4,3))`

Namespace `ColouredSand.ThmG`.

## Encodings

* `K(H(4,3)) = ColouredSand.TheoremB.sandpile 4 3`; `Syl_3 G` is
  `AddCommGroup.primaryComponent G 3`; `(ℤ/3^e)^n` is `Fin n → ZMod (3^e)` (written with the
  numerals `3, 9, 27, 81`); "`≅`" of abelian groups is `≃+`.

## Proof

(S2) at `p = q = 3`, `d = 4` gives the product over `σ = (j, i)` of the groups of exponents
`gTorList 3 3 j (4 − j)`.  Since `4 − j ≤ 2·3 − 2`, (F1) replaces each `gTorList` by the
explicit list `FList` (multiset equality), which is evaluated with the values of `v_3(n)` for
`n ≤ 8`; with `(q − 2)^j = 1` the exponent multiset over all factors is
`{1:2, 2:7, 3:8, 4:17}` (`X1_multiset`), and `expSum` assembles the groups.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmG

open ColouredSand.TheoremB ColouredSand.TiltDec ColouredSand.Blocks

/-- The values of `v_3(n)` for `n ≤ 8` (auxiliary for (X1)). -/
lemma padicValNat_three_small :
    padicValNat 3 0 = 0 ∧ padicValNat 3 1 = 0 ∧ padicValNat 3 2 = 0 ∧ padicValNat 3 3 = 1 ∧
    padicValNat 3 4 = 0 ∧ padicValNat 3 5 = 0 ∧ padicValNat 3 6 = 1 ∧ padicValNat 3 7 = 0 ∧
    padicValNat 3 8 = 0 := by
  refine ⟨padicValNat.zero, padicValNat.one, padicValNat.eq_zero_of_not_dvd (by norm_num),
    padicValNat_self, padicValNat.eq_zero_of_not_dvd (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by norm_num), ?_, padicValNat.eq_zero_of_not_dvd (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by norm_num)⟩
  rw [show (6 : ℕ) = 3 * 2 by rfl, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- The exponent multiset of the Example (`CSG7_theorem_G.md`, Part X): the union over
`σ = (j, i)` of the lists `gTorList 3 3 j (4 − j)` is `{1:2, 2:7, 3:8, 4:17}`. -/
theorem X1_multiset :
    ∑ σ : (Σ j : Fin (4 + 1), Fin (Nat.choose 4 j * (3 - 2) ^ (j : ℕ))),
      ((gTorList 3 3 σ.1 (4 - σ.1) : List ℕ) : Multiset ℕ) =
    ((List.replicate 2 1 ++ List.replicate 7 2 ++ List.replicate 8 3 ++ List.replicate 17 4 :
      List ℕ) : Multiset ℕ) := by
  have hF : ∀ j : ℕ, j ≤ 4 →
      ((gTorList 3 3 j (4 - j) : List ℕ) : Multiset ℕ) = ((FList 3 3 j (4 - j) : List ℕ)) :=
    fun j hj => Multiset.coe_eq_coe.2 (F1 (p := 3) (by norm_num) j (by simp) (by omega))
  obtain ⟨h0, h1, h2, -, h4, -, -, -, -⟩ := padicValNat_three_small
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Fin.sum_univ_five]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  rw [hF 0 (by norm_num), hF 1 (by norm_num), hF 2 (by norm_num),
    show ((3 : Fin 5) : ℕ) = 3 from rfl, show ((4 : Fin 5) : ℕ) = 4 from rfl,
    hF 3 (by norm_num), hF 4 (by norm_num)]
  simp [FList, FPiece, betaN, betaCG, Ac, chA, vt, Finset.sum_range_succ, h0, h1, h2, h4,
    List.range_succ]
  decide

/-- **(X1) the Example** of `CSG7_theorem_G.md` (Part X):
`Syl_3 K(H(4,3)) ≅ (ℤ/3)^2 ⊕ (ℤ/9)^7 ⊕ (ℤ/27)^8 ⊕ (ℤ/81)^17`.
From (S2) at `p = q = 3`, `d = 4`, the exponent multiset `X1_multiset` and `expSum`. -/
theorem X1 :
    Nonempty (AddCommGroup.primaryComponent (sandpile 4 3) 3 ≃+
      (Fin 2 → ZMod 3) × (Fin 7 → ZMod 9) × (Fin 8 → ZMod 27) × (Fin 17 → ZMod 81)) := by
  obtain ⟨E⟩ := S2 (p := 3) (d := 4) (q := 3) (by norm_num) (by norm_num) (by simp) (by norm_num)
  obtain ⟨E2⟩ := expSum 3 (fun σ : (Σ j : Fin (4 + 1), Fin (Nat.choose 4 j * (3 - 2) ^ (j : ℕ))) =>
    gTorList 3 3 σ.1 (4 - σ.1)) _ X1_multiset
  let E3 : ExpGrp 3 (List.replicate 2 1 ++ List.replicate 7 2 ++ List.replicate 8 3 ++
      List.replicate 17 4) ≃+
      (Fin 2 → ZMod 3) × (Fin 7 → ZMod 9) × (Fin 8 → ZMod 27) × (Fin 17 → ZMod 81) :=
    ((expAppend 3 _ _).trans (((expAppend 3 _ _).trans
      ((expAppend 3 _ _).prodCongr (AddEquiv.refl _))).prodCongr (AddEquiv.refl _))).trans
      ((((AddEquiv.prodAssoc.trans AddEquiv.prodAssoc)).trans
        ((expReplicate 3 1 2).prodCongr ((expReplicate 3 2 7).prodCongr
          ((expReplicate 3 3 8).prodCongr (expReplicate 3 4 17))))).trans
        ((AddEquiv.piCongrRight fun _ => (ZMod.ringEquivCongr (by norm_num)).toAddEquiv).prodCongr
          ((AddEquiv.piCongrRight fun _ =>
              (ZMod.ringEquivCongr (by norm_num)).toAddEquiv).prodCongr
            ((AddEquiv.piCongrRight fun _ =>
                (ZMod.ringEquivCongr (by norm_num)).toAddEquiv).prodCongr
              (AddEquiv.piCongrRight fun _ => (ZMod.ringEquivCongr (by norm_num)).toAddEquiv)))))
  exact ⟨(E.trans E2).trans E3⟩

end ColouredSand.ThmG
