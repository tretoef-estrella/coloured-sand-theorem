module

public import RequestProject.ThmG.TheoremG

/-!
# `CSG7_theorem_G.md`, Part S — `Syl_p K(H(d,q))` for `d ≤ p² + p − 1`

Namespace `ColouredSand.ThmG`.  The odd-`p` analogue of `ThmH.T4`, following
`RequestProject/ThmH/TheoremH.lean` closely.

## Encodings

* `K(H(d,q)) = ColouredSand.TheoremB.sandpile d q`; `Syl_p G` is
  `AddCommGroup.primaryComponent G p`; "`≅`" of abelian groups is `≃+`.
* The direct sum over `j ≤ d` with multiplicities `C(d,j)(q−2)^j` (Theorem A) is the product over
  `σ : Σ j : Fin (d + 1), Fin (d.choose j * (q − 2) ^ j)`, exactly as in Corollary 1
  (`ColouredSand.Corollaries.corollary1_whole`); within the factor `σ`, the summands are the
  positions `t` of `LP p (d − j)` as in Part T.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmG

open ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB ColouredSand.Corollaries
open ColouredSand.TiltP ColouredSand.TiltDec ColouredSand.Blocks ColouredSand.BlockOp

variable {p : ℕ} [Fact p.Prime]

/-- `GBlk` depends on `q` only through `v_p(q)` (auxiliary for (S1), from (L2)). -/
def gBlkCongr {q q' : ℕ} (h : padicValNat p q = padicValNat p q') (c k l : ℕ) :
    GBlk p q c k l ≃+ GBlk p q' c k l :=
  (AddEquiv.refl _).prodCongr (expCast p (L2_val h c k l))

omit [Fact p.Prime] in
/-- `gTorList` depends on `q` only through `v_p(q)` (auxiliary for (S2), from (L2)). -/
lemma gTorList_congr {q q' : ℕ} (h : padicValNat p q = padicValNat p q') (c m : ℕ) :
    gTorList p q c m = gTorList p q' c m := by
  unfold gTorList
  congr 1
  funext l
  exact L2_val h _ _ _

set_option synthInstance.maxHeartbeats 200000 in
/-- **(S1)** of `CSG7_theorem_G.md`: for `p ≠ 2`, `1 ≤ v_p(q)`, `2 ≤ q` and `d ≤ p² + p − 1`,
`ℤ_p ⊕ Syl_p K(H(d,q)) ≅ ⊕_{j=0}^{d} (⊕_λ G_j(d − j, λ)^{n_λ(d−j)})^{C(d,j)(q−2)^j}`, the
multiplicities being encoded by the product over `σ : Σ j : Fin (d+1), Fin (C(d,j)(q−2)^j)` and
over the positions `t` of `LP p (d − j)`.  Exactly as `ThmH.T4`: `corollary1_whole p d q`,
(T1) at `p^{v_p q}` on each factor, (L2) to replace `p^{v_p q}` by `q`, and the one factor with
`j = 0` carrying the `ℤ_[p]` (`ThmH.card_sigma_free`). -/
theorem S1 (hp2 : p ≠ 2) {d q : ℕ} (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat p q)
    (hd : d ≤ p ^ 2 + p - 1) :
    Nonempty ((ℤ_[p] × AddCommGroup.primaryComponent (sandpile d q) p) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (t : Fin (LP p (d - σ.1)).length) →
          GBlk p q σ.1 ((d - σ.1 - (LP p (d - σ.1)).get t) / 2) ((LP p (d - σ.1)).get t))) := by
  set e := padicValNat p q with he
  obtain ⟨EA⟩ := corollary1_whole p d q hq2
  rw [← he] at EA
  have hve : padicValNat p (p ^ e) = e := padicValNat.prime_pow e
  let ι := Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))
  let F : ι → Type := fun σ => Fin (if (σ.1 : ℕ) = 0 then 1 else 0) → ℤ_[p]
  let S : ι → Type := fun σ =>
    AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq (p ^ e) (d - σ.1) σ.1)) p
  have hfac : ∀ σ : ι, Nonempty ((F σ × S σ) ≃+
      ((t : Fin (LP p (d - σ.1)).length) →
        GBlk p q σ.1 ((d - σ.1 - (LP p (d - σ.1)).get t) / 2) ((LP p (d - σ.1)).get t))) :=
    fun σ => by
      obtain ⟨h⟩ := T1 hp2 (q := p ^ e) (m := d - σ.1) σ.1 (by rw [hve]; exact hq)
        ((Nat.sub_le _ _).trans hd)
      exact ⟨h.trans (AddEquiv.piCongrRight fun t => gBlkCongr (by rw [hve]) _ _ _)⟩
  obtain ⟨hU⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 (ThmH.card_sigma_free d q)
  let eF : ((σ : ι) → F σ) ≃+ ℤ_[p] :=
    (LinearEquiv.piCurry ℤ_[p] (fun (σ : ι) (_ : Fin (if (σ.1 : ℕ) = 0 then 1 else 0)) =>
      ℤ_[p])).symm.toAddEquiv.trans
      (@LinearEquiv.funUnique _ ℤ_[p] ℤ_[p] hU _ _ _).toAddEquiv
  exact ⟨((eF.symm.prodCongr EA).trans (ThmH.piProdAddEquiv F S).symm).trans
    (AddEquiv.piCongrRight fun σ => (hfac σ).some)⟩

/-- **(S2) torsion form** of `CSG7_theorem_G.md`: for `p ≠ 2`, `1 ≤ v_p(q)`, `2 ≤ q` and
`d ≤ p² + p − 1`,
`Syl_p K(H(d,q)) ≅ Π_{σ = (j, i)} ⊕_{e ∈ gTorList p q j (d − j)} ℤ/p^e`.
From `corollary1_whole p d q`, (T2) at `p^{v_p q}` on each factor and (L2). -/
theorem S2 (hp2 : p ≠ 2) {d q : ℕ} (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat p q)
    (hd : d ≤ p ^ 2 + p - 1) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin (gTorList p q σ.1 (d - σ.1)).length) →
          ZMod (p ^ (gTorList p q σ.1 (d - σ.1)).get i))) := by
  set e := padicValNat p q with he
  obtain ⟨EA⟩ := corollary1_whole p d q hq2
  rw [← he] at EA
  have hve : padicValNat p (p ^ e) = e := padicValNat.prime_pow e
  have hfac : ∀ σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ)),
      Nonempty (AddCommGroup.primaryComponent
          (Submodule.torsion ℤ (Xq (p ^ e) (d - σ.1) σ.1)) p ≃+
        ExpGrp p (gTorList p q σ.1 (d - σ.1))) := fun σ => by
    obtain ⟨h⟩ := T2 hp2 (q := p ^ e) (m := d - σ.1) σ.1 (by rw [hve]; exact hq)
      ((Nat.sub_le _ _).trans hd)
    exact ⟨h.trans (expCast p (gTorList_congr (by rw [hve]) _ _))⟩
  exact ⟨EA.trans (AddEquiv.piCongrRight fun σ => (hfac σ).some)⟩

end ColouredSand.ThmG
