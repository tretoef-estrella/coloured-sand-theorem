module

public import RequestProject.ThmG.GroupList
public import RequestProject.ThmH.TheoremH
public import RequestProject.Corollaries.Valuation

/-!
# `CSG7_theorem_G.md`, Part T — Theorem G (two Weyl factors)

Namespace `ColouredSand.ThmG`.  The odd-`p` analogue of `ThmH.T3`, following
`RequestProject/ThmH/TheoremH.lean` closely.

## Encodings

* `X_q(m,c) = ColouredSand.Splitting.Xq q m c`; `tors X` is `Submodule.torsion ℤ X`;
  `Syl_p G` is `AddCommGroup.primaryComponent G p`; `ℤ_p^{[c=0]}` is
  `Fin (if c = 0 then 1 else 0) → ℤ_[p]`; "`≅`" of abelian groups is `≃+`.
* The summands of `V^{⊗m}` are the positions `j : Fin (LP p m).length` of CSG5's list
  `TiltDec.LP p m` (each `λ` repeated `n_λ = mP p λ m` times), `λ_j = (LP p m).get j`; the direct
  sum `⊕_λ G_c(m, λ)^{n_λ}` of the paper is the product over the positions `j` of
  `GBlk p q c ((m − λ_j)/2) λ_j` (Part L).
* (T2) `gTorList p q c m = (LP p m).flatMap (fun l => blkList p q c ((m − l)/2) l)` is the list of
  the exponents of all finite cyclic factors, and the group `⊕_{e ∈ gTorList} ℤ/p^e` is
  `(i : Fin (gTorList p q c m).length) → ZMod (p ^ (gTorList p q c m).get i)`
  (`= ExpGrp p (gTorList p q c m)`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmG

open ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB ColouredSand.Corollaries
open ColouredSand.TiltP ColouredSand.TiltDec ColouredSand.Blocks ColouredSand.BlockOp

variable {p : ℕ} [Fact p.Prime]

/-! ### (T1) -/

/-- **(T1) Theorem G, as printed** (`CSG7_theorem_G.md`, Part T): for `p ≠ 2`, `1 ≤ v_p(q)` and
`m ≤ p² + p − 1`,
`ℤ_p^{[c=0]} ⊕ Syl_p (tors X_q(m,c)) ≅ ⊕_{j} G_c(m, λ_j)`, `λ_j = (LP p m).get j`.
Exactly as `ThmH.T3`: `sylTorsXq_equiv`, `ThmH.freeTorsionEquiv` over `ℤ_[p]`, CSG6 `K4`, and
(L1) on each factor (with CSG5 `M3` for its hypotheses). -/
theorem T1 (hp2 : p ≠ 2) {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ p ^ 2 + p - 1) :
    Nonempty (((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p) ≃+
      ((j : Fin (LP p m).length) →
        GBlk p q c ((m - (LP p m).get j) / 2) ((LP p m).get j))) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨e1⟩ := sylTorsXq_equiv p q m c
  have hcast : opM m ℤ_[p] ((q : ℤ) : ℤ_[p]) ((c : ℤ) : ℤ_[p]) =
      opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]) := by simp only [Int.cast_natCast]
  rw [hcast] at e1
  obtain ⟨e2⟩ := K4 hp2 hm q c
  have hq0' : (q : ℤ_[p]) ≠ 0 := by exact_mod_cast hq0
  have hfac : ∀ j : Fin (LP p m).length, Nonempty (cokT p (Ttilt p ((LP p m).get j)) m q c ≃+
      GBlk p q c ((m - (LP p m).get j) / 2) ((LP p m).get j)) := fun j => by
    obtain ⟨h1, h2⟩ := M3 hp m _ (List.get_mem _ _)
    exact L1 hp2 hq (h1.trans hm) h1 h2
  exact ⟨((AddEquiv.refl _).prodCongr e1).trans
    (((ThmH.freeTorsionEquiv m hq0' c).toAddEquiv.trans e2.toAddEquiv).trans
      (AddEquiv.piCongrRight fun j => (hfac j).some))⟩

/-! ### (T2) -/

variable (p) in
/-- **(T2)** of `CSG7_theorem_G.md`: the exponents of all the finite cyclic factors,
`gTorList p q c m = (LP p m).flatMap (fun l => blkList p q c ((m − l)/2) l)`. -/
def gTorList (q c m : ℕ) : List ℕ := (LP p m).flatMap (fun l => blkList p q c ((m - l) / 2) l)

/-- Every element of a `p`-primary component has finite order (auxiliary for (T2)). -/
lemma primary_isOfFinAddOrder {G : Type*} [AddCommGroup G]
    (s : AddCommGroup.primaryComponent G p) : IsOfFinAddOrder s := by
  have hs : ∃ n : ℕ, addOrderOf (s : G) = p ^ n := s.2
  obtain ⟨n, hn⟩ := hs
  rw [← addOrderOf_pos_iff, ← AddSubgroup.addOrderOf_coe, hn]
  exact pow_pos (Fact.out : p.Prime).pos n

/-- A finite product of groups `ℤ_[p]^{n_j}` has no non-zero element of finite order
(auxiliary for (T2)). -/
lemma piFree_torsionFree {ι : Type*} (n : ι → ℕ) (x : (j : ι) → Fin (n j) → ℤ_[p])
    (hx : IsOfFinAddOrder x) : x = 0 := by
  funext j
  exact pi_torsionFree (n j) (x j) (hx.apply j)

/-- **(T2) the torsion form** of Theorem G (`CSG7_theorem_G.md`, Part T): for `p ≠ 2`,
`1 ≤ v_p(q)` and `m ≤ p² + p − 1`,
`Syl_p (tors X_q(m,c)) ≅ ⊕_{e ∈ gTorList p q c m} ℤ/p^e`.
From (T1) by cancelling the free parts (`cancelFree`: the left side is torsion, `ℤ_[p]` has no
`ℤ`-torsion) and reindexing the product over the positions `j` as a product over the flattened
list (`expFlatMap`). -/
theorem T2 (hp2 : p ≠ 2) {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ p ^ 2 + p - 1) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      ((i : Fin (gTorList p q c m).length) → ZMod (p ^ (gTorList p q c m).get i))) := by
  obtain ⟨E⟩ := T1 hp2 c hq hm
  let F : Fin (LP p m).length → Type := fun j =>
    Fin (freeBlk c ((m - (LP p m).get j) / 2)) → ℤ_[p]
  let S : Fin (LP p m).length → Type := fun j =>
    ExpGrp p (blkList p q c ((m - (LP p m).get j) / 2) ((LP p m).get j))
  let E' : ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
      AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p) ≃+
      (((j : Fin (LP p m).length) → F j) × ((j : Fin (LP p m).length) → S j)) :=
    E.trans (ThmH.piProdAddEquiv F S)
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hA : ∀ x : Fin (if c = 0 then 1 else 0) → ℤ_[p], IsOfFinAddOrder x → x = 0 :=
    pi_torsionFree _
  have hB : ∀ x : (j : Fin (LP p m).length) → F j, IsOfFinAddOrder x → x = 0 :=
    piFree_torsionFree _
  have hT : ∀ x : (j : Fin (LP p m).length) → S j, IsOfFinAddOrder x :=
    pi_torsion fun j => expGrp_torsion hp0 _
  let C : AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      ((j : Fin (LP p m).length) → S j) :=
    cancelFree hA hB primary_isOfFinAddOrder hT E'
  exact ⟨C.trans (expFlatMap p (fun l => blkList p q c ((m - l) / 2) l) (LP p m))⟩

end ColouredSand.ThmG
