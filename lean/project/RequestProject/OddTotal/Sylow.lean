module

public import RequestProject.OddTotal.Exponents

/-!
# `CSI19_theorem_TOTAL.md`, Part S — `Syl_p K(H(d, q))` for every `d` (Theorem TOTAL)

Namespace `ColouredSand.OddTwist`; every new name starts with `oddTotal`.

## Encodings

* `K(H(d,q)) = ColouredSand.TheoremB.sandpile d q` (the torsion of the cokernel of the Laplacian);
  `Syl_p G` is `AddCommGroup.primaryComponent G p`; "`≅`" of abelian groups is `≃+`;
  `X_q(m, c) = ColouredSand.Splitting.Xq q m c`.
* The direct sum over `j ≤ d` with multiplicities `C(d,j)(q−2)^j` (Theorem A) is the product over
  `σ : Σ j : Fin (d + 1), Fin (d.choose j * (q − 2) ^ j)`, exactly as in CSG7 `S1`, `S2`
  (`Corollaries.corollary1_whole`); within the factor `σ`, the summands are the positions `t` of
  CSI6's list `LL p (d − j)`, and the block of `t` is `Y_p(λ_t, j + (d − j − λ_t)/2, e)`,
  `λ_t = (LL p (d − j)).get t`, `e = v_p(q) = padicValNat p q`.
* **(S2)** `oddTotalTotList p q c m` (the file's `totList p q c m`) is the flatMap over
  `λ ∈ LL p m` of `oddTotalYList p λ (c + (m − λ)/2) e` (the exponents of `S_p(λ)`, then
  `k + C + ŷ` for `i ≥ 1`, or `k + eK + ŷ^♯` for `i = 0`), **with the entries `0` removed**: an
  entry `0` stands for a trivial factor `ℤ/p^0` (it occurs, e.g., in `S_p(λ)` for `1 ≤ λ ≤ p − 2`,
  where `k = 0`), and removing it is what makes the list the list of exponents of the non-trivial
  cyclic factors, as CSG7's `gTorList` is, so that (S3) holds.  As in `gTorList`, only torsion
  exponents are listed: the one free `ℤ_[p]` lives in the block `Y_p(d, 0, e)` (`j = 0`, `λ = d`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB ColouredSand.Corollaries
open ColouredSand.BlockOp ColouredSand.ThmG

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- **(S2)** of `CSI19_theorem_TOTAL.md`: the file's `totList p q c m`, the exponents of all the
non-trivial finite cyclic factors of `⊕_{λ ∈ LL p m} Y_p(λ, c + (m − λ)/2, v_p(q))`: the flatMap
over `λ ∈ LL p m` of the exponent list `oddTotalYList` of each block, without the entries `0`
(trivial factors `ℤ/p^0`). -/
def oddTotalTotList (q c m : ℕ) : List ℕ :=
  ((LL p m).flatMap fun l => oddTotalYList p l (c + (m - l) / 2) (padicValNat p q)).filter
    (fun a => a ≠ 0)

omit [Fact p.Prime] in
lemma oddTotalTotList_congr {q q' : ℕ} (h : padicValNat p q = padicValNat p q') (c m : ℕ) :
    oddTotalTotList p q c m = oddTotalTotList p q' c m := by
  unfold oddTotalTotList; rw [h]

/-- Part S of `CSI19_theorem_TOTAL.md`, one factor `X_q(m, c)` (the analogue of CSG7 `T1`, with no
bound on `m`): for an odd prime `p` and `q ≠ 0`,
`ℤ_p^{[c=0]} ⊕ Syl_p (tors X_q(m, c)) ≅ Π_t Y_p(λ_t, c + (m − λ_t)/2, e)`,
`λ_t = (LL p m).get t`, `e = v_p(q)` (stated with any `e = v_p(q)`).  From `sylTorsXq_equiv`,
`ThmH.freeTorsionEquiv`, CSG6 (K2) and (T1). -/
theorem oddTotal_factor (hp2 : p ≠ 2) {q m : ℕ} (c : ℕ) (hq : q ≠ 0) {e : ℕ}
    (he : padicValNat p q = e) :
    Nonempty (((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p) ≃+
      ((t : Fin (LL p m).length) → Yp p ((LL p m).get t) (c + (m - (LL p m).get t) / 2) e)) := by
  subst he
  obtain ⟨e1⟩ := sylTorsXq_equiv p q m c
  have hcast : opM m ℤ_[p] ((q : ℤ) : ℤ_[p]) ((c : ℤ) : ℤ_[p]) =
      opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]) := by simp only [Int.cast_natCast]
  rw [hcast] at e1
  have hq0' : (q : ℤ_[p]) ≠ 0 := by exact_mod_cast hq
  let eK : (B m ℤ_[p] ⧸ LinearMap.range (opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]))) ≃ₗ[ℤ_[p]]
      cokT p (Filt.tpow ℤ_[p] m) m q c :=
    cokerEquivOfConj _ _ (ThmH.Psi ℤ_[p] m) (ThmH.Psi ℤ_[p] m) (fun x => by
      have := LinearMap.congr_fun (K2 hp2 m q c) x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
      exact this.symm)
  obtain ⟨eT⟩ := oddTotal_T1 hp2 m c hq
  exact ⟨((AddEquiv.refl _).prodCongr e1).trans
    ((ThmH.freeTorsionEquiv m hq0' c).toAddEquiv.trans (eK.trans eT).toAddEquiv)⟩

/-- Part S (S2) of `CSI19_theorem_TOTAL.md`, one factor (the analogue of CSG7 `T2`, with no bound
on `m`): for an odd prime `p` and `1 ≤ v_p(q)`,
`Syl_p (tors X_q(m, c)) ≅ ⊕_{a ∈ oddTotalTotList p q c m} ℤ/p^a`.  From `oddTotal_factor`, CSI18
(Y2) on each block (`oddTotal_Yp_split`), cancelling the free parts (CSG7 `cancelFree`) and
flattening (CSG7 `expFlatMap`). -/
theorem oddTotal_factor_tors (hp2 : p ≠ 2) {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      ExpGrp p (oddTotalTotList p q c m)) := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  set e := padicValNat p q with he
  obtain ⟨E⟩ := oddTotal_factor hp2 (m := m) c hq0 he.symm
  let L := LL p m
  let F : Fin L.length → Type := fun t => oddTotalFree (p := p) (c + (m - L.get t) / 2)
  let S : Fin L.length → Type := fun t =>
    ExpGrp p (oddTotalYList p (L.get t) (c + (m - L.get t) / 2) e)
  have hY : ∀ t : Fin L.length, Nonempty (Yp p (L.get t) (c + (m - L.get t) / 2) e ≃+
      (F t × S t)) := fun t => oddTotal_Yp_split hp2 _ _ e hq
  let E' : ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
      AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p) ≃+
      (((t : Fin L.length) → F t) × ((t : Fin L.length) → S t)) :=
    (E.trans (AddEquiv.piCongrRight fun t => (hY t).some)).trans (ThmH.piProdAddEquiv F S)
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hA : ∀ x : Fin (if c = 0 then 1 else 0) → ℤ_[p], IsOfFinAddOrder x → x = 0 :=
    pi_torsionFree _
  have hB : ∀ x : (t : Fin L.length) → F t, IsOfFinAddOrder x → x = 0 :=
    piFree_torsionFree (fun t => if c + (m - L.get t) / 2 = 0 then 1 else 0)
  have hT : ∀ x : (t : Fin L.length) → S t, IsOfFinAddOrder x :=
    pi_torsion fun t => expGrp_torsion hp0 _
  let C : AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      ((t : Fin L.length) → S t) :=
    cancelFree hA hB primary_isOfFinAddOrder hT E'
  exact ⟨(C.trans (expFlatMap p (fun l => oddTotalYList p l (c + (m - l) / 2) e) L)).trans
    (oddTotalExpFilter p _)⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- **(S1) Theorem TOTAL** of `CSI19_theorem_TOTAL.md`: for an odd prime `p`, `q ≥ 2` and
**every** `d` (no bound on `d`),
`ℤ_p ⊕ Syl_p K(H(d,q)) ≅ ⊕_{j=0}^{d} (⊕_{λ ∈ LL p (d−j)} Y_p(λ, j + (d−j−λ)/2, e))^{C(d,j)(q−2)^j}`,
`e = v_p(q)`; the multiplicities are encoded by the product over
`σ : Σ j : Fin (d+1), Fin (C(d,j)(q−2)^j)` and over the positions `t` of `LL p (d − j)` (so the
multiplicity of `λ` inside is `n_λ(d − j)`).  The file's hypothesis `p ∣ q` is not needed (more
general; for `p ∤ q` the blocks have `e = 0`).  Exactly as CSG7 `S1`, with (T1) in place of
CSG6 `K4`. -/
theorem oddTotal_S1 (hp2 : p ≠ 2) {d q : ℕ} (hq2 : 2 ≤ q) :
    Nonempty ((ℤ_[p] × AddCommGroup.primaryComponent (sandpile d q) p) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (t : Fin (LL p (d - σ.1)).length) →
          Yp p ((LL p (d - σ.1)).get t) (σ.1 + (d - σ.1 - (LL p (d - σ.1)).get t) / 2)
            (padicValNat p q))) := by
  set e := padicValNat p q with he
  obtain ⟨EA⟩ := corollary1_whole p d q hq2
  rw [← he] at EA
  have hve : padicValNat p (p ^ e) = e := padicValNat.prime_pow e
  have hpe : p ^ e ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  let ι := Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))
  let F : ι → Type := fun σ => Fin (if (σ.1 : ℕ) = 0 then 1 else 0) → ℤ_[p]
  let S : ι → Type := fun σ =>
    AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq (p ^ e) (d - σ.1) σ.1)) p
  have hfac : ∀ σ : ι, Nonempty ((F σ × S σ) ≃+
      ((t : Fin (LL p (d - σ.1)).length) →
        Yp p ((LL p (d - σ.1)).get t) (σ.1 + (d - σ.1 - (LL p (d - σ.1)).get t) / 2) e)) :=
    fun σ => oddTotal_factor hp2 (m := d - σ.1) σ.1 hpe hve
  obtain ⟨hU⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 (ThmH.card_sigma_free d q)
  let eF : ((σ : ι) → F σ) ≃+ ℤ_[p] :=
    (LinearEquiv.piCurry ℤ_[p] (fun (σ : ι) (_ : Fin (if (σ.1 : ℕ) = 0 then 1 else 0)) =>
      ℤ_[p])).symm.toAddEquiv.trans
      (@LinearEquiv.funUnique _ ℤ_[p] ℤ_[p] hU _ _ _).toAddEquiv
  exact ⟨((eF.symm.prodCongr EA).trans (ThmH.piProdAddEquiv F S).symm).trans
    (AddEquiv.piCongrRight fun σ => (hfac σ).some)⟩

/-- **(S2) Theorem TOTAL, explicit exponents** (`CSI19_theorem_TOTAL.md`, Part S): for an odd
prime `p`, `q ≥ 2` with `p ∣ q` (i.e. `1 ≤ v_p(q)`) and **every** `d`,
`Syl_p K(H(d,q)) ≅ Π_{σ = (j, i)} ⊕_{a ∈ totList p q j (d − j)} ℤ/p^a`, with
`totList = oddTotalTotList` built from CSI18 (Y2).  From `corollary1_whole` and
`oddTotal_factor_tors` on each factor. -/
theorem oddTotal_S2 (hp2 : p ≠ 2) {d q : ℕ} (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat p q) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin (oddTotalTotList p q σ.1 (d - σ.1)).length) →
          ZMod (p ^ (oddTotalTotList p q σ.1 (d - σ.1)).get i))) := by
  set e := padicValNat p q with he
  obtain ⟨EA⟩ := corollary1_whole p d q hq2
  rw [← he] at EA
  have hve : padicValNat p (p ^ e) = e := padicValNat.prime_pow e
  have hfac : ∀ σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ)),
      Nonempty (AddCommGroup.primaryComponent
          (Submodule.torsion ℤ (Xq (p ^ e) (d - σ.1) σ.1)) p ≃+
        ExpGrp p (oddTotalTotList p q σ.1 (d - σ.1))) := fun σ => by
    obtain ⟨h⟩ := oddTotal_factor_tors hp2 (q := p ^ e) (m := d - σ.1) σ.1 (by rw [hve]; exact hq)
    exact ⟨h.trans (expCast p (oddTotalTotList_congr (by rw [hve]) _ _))⟩
  exact ⟨EA.trans (AddEquiv.piCongrRight fun σ => (hfac σ).some)⟩

/-- **(S3) agreement with Theorem G** (`CSI19_theorem_TOTAL.md`, Part S): for an odd prime `p`,
`1 ≤ v_p(q)` and `m ≤ p² + p − 1`, `totList p q c m` is a permutation of CSG7's
`gTorList p q c m`.  Proved from `oddTotal_factor_tors` and CSG7 `T2` (both describe
`Syl_p (tors X_q(m, c))`) by the uniqueness of the exponents of a finite abelian `p`-group
(`oddTotal_perm_of_expGrp`; every entry of either list is `≥ 1`, CSG7 `L2_pos`).  In particular
(S2) contains CSG7 `S2` (see `oddTotal_S3_S2`). -/
theorem oddTotal_S3 (hp2 : p ≠ 2) {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ p ^ 2 + p - 1) : (oddTotalTotList p q c m).Perm (gTorList p q c m) := by
  obtain ⟨A⟩ := oddTotal_factor_tors hp2 (m := m) c hq
  obtain ⟨B⟩ := ThmG.T2 hp2 c hq hm
  refine oddTotal_perm_of_expGrp p oddTotal_ne_zero_of_mem_filter (fun a ha => ?_) (A.symm.trans B)
  unfold gTorList at ha
  obtain ⟨l, -, hl⟩ := List.mem_flatMap.1 ha
  have := L2_pos hq c _ l a hl
  omega

/-- (S3) of `CSI19_theorem_TOTAL.md`, "in particular (S2) contains CSG7 `S2`": for
`d ≤ p² + p − 1`, the groups of (S2) and of CSG7 `S2` are isomorphic factor by factor (the lists
of exponents are permutations of each other). -/
theorem oddTotal_S3_S2 (hp2 : p ≠ 2) {d q : ℕ} (hq : 1 ≤ padicValNat p q)
    (hd : d ≤ p ^ 2 + p - 1) :
    Nonempty (((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin (oddTotalTotList p q σ.1 (d - σ.1)).length) →
          ZMod (p ^ (oddTotalTotList p q σ.1 (d - σ.1)).get i)) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin (gTorList p q σ.1 (d - σ.1)).length) →
          ZMod (p ^ (gTorList p q σ.1 (d - σ.1)).get i))) :=
  ⟨AddEquiv.piCongrRight fun σ =>
    (expPerm p (oddTotal_S3 hp2 σ.1 hq ((Nat.sub_le _ _).trans hd))).some⟩

end ColouredSand.OddTwist
