module

public import RequestProject.ThmGTwo.Mult
public import RequestProject.ThmGTwo.Blocks

/-!
# `CSX3_theorems_F_G_prime_two.md`, Part T — Theorems G and F at `p = 2`

Namespace `ColouredSand.ThmGTwo`; every new name starts with `two`.

## Encodings (exactly those of CSG7, `RequestProject/ThmG`, at `p = 2`)

* `X_q(m,c) = ColouredSand.Splitting.Xq q m c`; `tors X` is `Submodule.torsion ℤ X`;
  `Syl_2 G` is `AddCommGroup.primaryComponent G 2`; `ℤ_2^{[c=0]}` is
  `Fin (if c = 0 then 1 else 0) → ℤ_[2]`; "`≅`" of abelian groups is `≃+`.
* The summands of `V^{⊗m}` are the positions `j : Fin (LP 2 m).length` of CSG5's list
  `TiltDec.LP 2 m`, `λ_j = (LP 2 m).get j`; `⊕_λ G_c(m, λ)^{n_λ}` is the product over `j` of
  `GBlk 2 q c ((m − λ_j)/2) λ_j`.
* `gTorList 2 q c m`, `FList 2 q c m` are CSG7's lists of exponents at `p = 2`, and
  `⊕_{e ∈ L} ℤ/2^e` is `(i : Fin L.length) → ZMod (2 ^ L.get i)`.
* The sandpile group of `H(d, q)` is `TheoremB.sandpile d q`; its multiplicities are encoded by the
  product over `σ : Σ j : Fin (d+1), Fin (C(d,j)(q−2)^j)`, as in CSG7.
* "`q` even" is `1 ≤ padicValNat 2 q` (equivalently `q ≠ 0` and `2 ∣ q`).

## Proof

(T1): CSH1 `ThmH.T3` (every even `q`, every `m`), then (M2) to reindex `FamDec.L m` as
`LP 2 m` (`twoPiPerm`), then (B1) factor by factor.  (T2), (F2), (S1), (S2) follow from (T1)
exactly as in CSG7; (F1) is a direct computation for `m ≤ 2`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmGTwo

open ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB ColouredSand.Corollaries
open ColouredSand.TiltP ColouredSand.TiltDec ColouredSand.Blocks ColouredSand.BlockOp
open ColouredSand.ThmG FamDec

/-- A permutation of the list of indices gives isomorphic products:
`Π_{j : Fin L.length} G (L.get j) ≅ Π_{j : Fin L'.length} G (L'.get j)` for `L ~ L'`
(auxiliary for (T1) of `CSX3_theorems_F_G_prime_two.md`). -/
theorem twoPiPerm (G : ℕ → Type*) [∀ n, AddCommGroup (G n)] {L L' : List ℕ} (h : L.Perm L') :
    Nonempty (((j : Fin L.length) → G (L.get j)) ≃+ ((j : Fin L'.length) → G (L'.get j))) := by
  induction h with
  | nil => exact ⟨AddEquiv.refl _⟩
  | @cons x l₁ l₂ _ ih =>
      obtain ⟨e⟩ := ih
      exact ⟨(finConsAddEquiv (fun j : Fin (l₁.length + 1) => G ((x :: l₁).get j))).symm.trans
        (((AddEquiv.refl _).prodCongr e).trans
          (finConsAddEquiv (fun j : Fin (l₂.length + 1) => G ((x :: l₂).get j))))⟩
  | swap x y l =>
      let e1 := (finConsAddEquiv (fun j : Fin (_ + 1) => G ((y :: x :: l).get j))).symm
      let e2 := (finConsAddEquiv (fun j : Fin (_ + 1) => G ((x :: l).get j))).symm
      let e3 := finConsAddEquiv (fun j : Fin (_ + 1) => G ((y :: l).get j))
      let e4 := finConsAddEquiv (fun j : Fin (_ + 1) => G ((x :: y :: l).get j))
      exact ⟨e1.trans (((AddEquiv.refl _).prodCongr e2).trans
        ((AddEquiv.prodAssoc.symm.trans ((AddEquiv.prodComm.prodCongr (AddEquiv.refl _)).trans
          AddEquiv.prodAssoc)).trans (((AddEquiv.refl _).prodCongr e3).trans e4)))⟩
  | trans _ _ ih1 ih2 =>
      obtain ⟨e1⟩ := ih1
      obtain ⟨e2⟩ := ih2
      exact ⟨e1.trans e2⟩

/-! ### (T1) -/

/-- **(T1) Theorem G at `p = 2`** (`CSX3_theorems_F_G_prime_two.md`, Part T; the statement of
`ThmG.T1` at `p = 2`): for `1 ≤ v_2(q)` and `m ≤ 5`,
`ℤ_2^{[c=0]} ⊕ Syl_2 (tors X_q(m,c)) ≅ ⊕_j G_c(m, λ_j)`, `λ_j = (LP 2 m).get j`. -/
theorem twoT1 {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat 2 q) (hm : m ≤ 5) :
    Nonempty (((Fin (if c = 0 then 1 else 0) → ℤ_[2]) ×
        AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2) ≃+
      ((j : Fin (LP 2 m).length) →
        GBlk 2 q c ((m - (LP 2 m).get j) / 2) ((LP 2 m).get j))) := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have heven : Even q := even_iff_two_dvd.2 (dvd_of_one_le_padicValNat hq)
  obtain ⟨e1⟩ := ThmH.T3 q m c (Nat.one_le_iff_ne_zero.2 hq0) heven
  obtain ⟨e2⟩ := twoPiPerm (fun l => FamilyGroup.X (Families.ds l) (padicValNat 2 q)
    (c + (m - l) / 2)) (twoM2 hm).symm
  have hfac : ∀ j : Fin (LP 2 m).length, Nonempty (FamilyGroup.X (Families.ds ((LP 2 m).get j))
      (padicValNat 2 q) (c + (m - (LP 2 m).get j) / 2) ≃+
        GBlk 2 q c ((m - (LP 2 m).get j) / 2) ((LP 2 m).get j)) := fun j =>
    twoB1_gen (((M3 le_rfl m _ (List.get_mem _ _)).1).trans hm) hq c _
  exact ⟨(e1.trans e2).trans (AddEquiv.piCongrRight fun j => (hfac j).some)⟩

/-! ### (T2) -/

/-- **(T2) the torsion form of Theorem G at `p = 2`** (`CSX3_theorems_F_G_prime_two.md`, Part T;
the statement of `ThmG.T2` at `p = 2`): for `1 ≤ v_2(q)` and `m ≤ 5`,
`Syl_2 (tors X_q(m,c)) ≅ ⊕_{e ∈ gTorList 2 q c m} ℤ/2^e`.  As in CSG7: cancel the free parts in
(T1) and flatten the product. -/
theorem twoT2 {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat 2 q) (hm : m ≤ 5) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2 ≃+
      ((i : Fin (gTorList 2 q c m).length) → ZMod (2 ^ (gTorList 2 q c m).get i))) := by
  obtain ⟨E⟩ := twoT1 c hq hm
  let F : Fin (LP 2 m).length → Type := fun j =>
    Fin (freeBlk c ((m - (LP 2 m).get j) / 2)) → ℤ_[2]
  let S : Fin (LP 2 m).length → Type := fun j =>
    ExpGrp 2 (blkList 2 q c ((m - (LP 2 m).get j) / 2) ((LP 2 m).get j))
  let E' : ((Fin (if c = 0 then 1 else 0) → ℤ_[2]) ×
      AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2) ≃+
      (((j : Fin (LP 2 m).length) → F j) × ((j : Fin (LP 2 m).length) → S j)) :=
    E.trans (ThmH.piProdAddEquiv F S)
  have hA : ∀ x : Fin (if c = 0 then 1 else 0) → ℤ_[2], IsOfFinAddOrder x → x = 0 :=
    pi_torsionFree _
  have hB : ∀ x : (j : Fin (LP 2 m).length) → F j, IsOfFinAddOrder x → x = 0 :=
    piFree_torsionFree _
  have hT : ∀ x : (j : Fin (LP 2 m).length) → S j, IsOfFinAddOrder x :=
    pi_torsion fun j => expGrp_torsion two_ne_zero _
  let C : AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2 ≃+
      ((j : Fin (LP 2 m).length) → S j) :=
    cancelFree hA hB primary_isOfFinAddOrder hT E'
  exact ⟨C.trans (expFlatMap 2 (fun l => blkList 2 q c ((m - l) / 2) l) (LP 2 m))⟩

/-! ### (F1), (F2) -/

/-- **(F1)** of `CSX3_theorems_F_G_prime_two.md` (the statement of `ThmG.F1` at `p = 2`): for
`1 ≤ v_2(q)` and `m ≤ 2`, `gTorList 2 q c m` is a permutation of `FList 2 q c m`.  By direct
computation of both lists for `m = 0, 1, 2`. -/
theorem twoF1 {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat 2 q) (hm : m ≤ 2) :
    (gTorList 2 q c m).Perm (FList 2 q c m) := by
  obtain ⟨a0, a1, a2, -⟩ := twoLP_explicit
  interval_cases m
  · rw [gTorList, a0]
    by_cases hc : c = 0
    · subst hc; simp [List.range_succ, blkList, FList, FPiece, betaN, betaCG]
    · simp [List.range_succ, blkList, FList, FPiece, betaN, betaCG, Ac, hc]
  · rw [gTorList, a1]
    by_cases hc : c = 0
    · subst hc; simp [List.range_succ, blkList, FList, FPiece, betaN, betaCG]
    · simp [List.range_succ, blkList, FList, FPiece, betaN, betaCG, Ac, hc]
  · rw [gTorList, a2]
    by_cases hc : c = 0
    · subst hc
      simp [List.range_succ, blkList, FList, FPiece, betaN, betaCG, Ac, IsSimpleWt, rT, aT, chA, E12, E22, blkA',
        blkAlpha, blkTau, Blocks.lam, mu, vt, Finset.sum_range_succ]
    · simp [List.range_succ, blkList, FList, FPiece, betaN, betaCG, Ac, hc, IsSimpleWt, rT, aT, chA, blkX, blkY,
        E11, E12, E22, blkA, blkA', blkAlpha, blkTau, Blocks.lam, mu, vt, Finset.sum_range_succ]
      have key : ∀ a b a' b' : ℕ, a = b' → b = a' → [a, b].Perm [a', b'] := by
        rintro a b a' b' rfl rfl; exact List.Perm.swap _ _ []
      apply key <;> omega

/-- **(F2) Theorem F at `p = 2`** (`CSX3_theorems_F_G_prime_two.md`, Part T; the statement of
`ThmG.F2` at `p = 2`): for `1 ≤ v_2(q)` and `m ≤ 2`,
`Syl_2 (tors X_q(m,c)) ≅ ⊕_{e ∈ FList 2 q c m} ℤ/2^e`.  From (T2), (F1) and `expPerm`. -/
theorem twoF2 {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat 2 q) (hm : m ≤ 2) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2 ≃+
      ((i : Fin (FList 2 q c m).length) → ZMod (2 ^ (FList 2 q c m).get i))) := by
  obtain ⟨e1⟩ := twoT2 c hq (hm.trans (by norm_num))
  obtain ⟨e2⟩ := expPerm 2 (twoF1 c hq hm)
  exact ⟨e1.trans e2⟩

/-! ### (S1), (S2) -/

set_option synthInstance.maxHeartbeats 200000 in
/-- **(S1)** of `CSX3_theorems_F_G_prime_two.md` (the statement of `ThmG.S1` at `p = 2`): for
`2 ≤ q`, `1 ≤ v_2(q)` and `d ≤ 5`,
`ℤ_2 ⊕ Syl_2 K(H(d,q)) ≅ ⊕_{j=0}^{d} (⊕_λ G_j(d − j, λ)^{n_λ(d−j)})^{C(d,j)(q−2)^j}`.
Exactly as `ThmG.S1`, with (T1) at `p = 2` (`twoT1`) on each factor. -/
theorem twoS1 {d q : ℕ} (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat 2 q) (hd : d ≤ 5) :
    Nonempty ((ℤ_[2] × AddCommGroup.primaryComponent (sandpile d q) 2) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (t : Fin (LP 2 (d - σ.1)).length) →
          GBlk 2 q σ.1 ((d - σ.1 - (LP 2 (d - σ.1)).get t) / 2) ((LP 2 (d - σ.1)).get t))) := by
  set e := padicValNat 2 q with he
  obtain ⟨EA⟩ := corollary1_whole 2 d q hq2
  rw [← he] at EA
  have hve : padicValNat 2 (2 ^ e) = e := padicValNat.prime_pow e
  let ι := Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))
  let F : ι → Type := fun σ => Fin (if (σ.1 : ℕ) = 0 then 1 else 0) → ℤ_[2]
  let S : ι → Type := fun σ =>
    AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq (2 ^ e) (d - σ.1) σ.1)) 2
  have hfac : ∀ σ : ι, Nonempty ((F σ × S σ) ≃+
      ((t : Fin (LP 2 (d - σ.1)).length) →
        GBlk 2 q σ.1 ((d - σ.1 - (LP 2 (d - σ.1)).get t) / 2) ((LP 2 (d - σ.1)).get t))) :=
    fun σ => by
      obtain ⟨h⟩ := twoT1 (q := 2 ^ e) (m := d - σ.1) σ.1 (by rw [hve]; exact hq)
        ((Nat.sub_le _ _).trans hd)
      exact ⟨h.trans (AddEquiv.piCongrRight fun t => gBlkCongr (by rw [hve]) _ _ _)⟩
  obtain ⟨hU⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 (ThmH.card_sigma_free d q)
  let eF : ((σ : ι) → F σ) ≃+ ℤ_[2] :=
    (LinearEquiv.piCurry ℤ_[2] (fun (σ : ι) (_ : Fin (if (σ.1 : ℕ) = 0 then 1 else 0)) =>
      ℤ_[2])).symm.toAddEquiv.trans
      (@LinearEquiv.funUnique _ ℤ_[2] ℤ_[2] hU _ _ _).toAddEquiv
  exact ⟨((eF.symm.prodCongr EA).trans (ThmH.piProdAddEquiv F S).symm).trans
    (AddEquiv.piCongrRight fun σ => (hfac σ).some)⟩

/-- **(S2)** of `CSX3_theorems_F_G_prime_two.md` (the statement of `ThmG.S2` at `p = 2`): for
`2 ≤ q`, `1 ≤ v_2(q)` and `d ≤ 5`,
`Syl_2 K(H(d,q)) ≅ Π_{σ = (j, i)} ⊕_{e ∈ gTorList 2 q j (d − j)} ℤ/2^e`.
Exactly as `ThmG.S2`, with (T2) at `p = 2` (`twoT2`). -/
theorem twoS2 {d q : ℕ} (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat 2 q) (hd : d ≤ 5) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) 2 ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin (gTorList 2 q σ.1 (d - σ.1)).length) →
          ZMod (2 ^ (gTorList 2 q σ.1 (d - σ.1)).get i))) := by
  set e := padicValNat 2 q with he
  obtain ⟨EA⟩ := corollary1_whole 2 d q hq2
  rw [← he] at EA
  have hve : padicValNat 2 (2 ^ e) = e := padicValNat.prime_pow e
  have hfac : ∀ σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ)),
      Nonempty (AddCommGroup.primaryComponent
          (Submodule.torsion ℤ (Xq (2 ^ e) (d - σ.1) σ.1)) 2 ≃+
        ExpGrp 2 (gTorList 2 q σ.1 (d - σ.1))) := fun σ => by
    obtain ⟨h⟩ := twoT2 (q := 2 ^ e) (m := d - σ.1) σ.1 (by rw [hve]; exact hq)
      ((Nat.sub_le _ _).trans hd)
    exact ⟨h.trans (expCast 2 (gTorList_congr (by rw [hve]) _ _))⟩
  exact ⟨EA.trans (AddEquiv.piCongrRight fun σ => (hfac σ).some)⟩

end ColouredSand.ThmGTwo
