module

public import RequestProject.OddTotal.Tensor
public import RequestProject.OddTotal.Uniqueness
public import RequestProject.OddSmith.All
public import RequestProject.ThmG.All

/-!
# `CSI19_theorem_TOTAL.md`, Part S (S2), auxiliary — the exponent list of `Y_p(λ, i, e)`

Namespace `ColouredSand.OddTwist`; every new name starts with `oddTotal`.

## Encodings

* A list of exponents `L : List ℕ` encodes `⊕_{a ∈ L} ℤ/p^a`, i.e. CSG7's
  `ExpGrp p L = (j : Fin L.length) → ZMod (p ^ L.get j)` (reused).
* `oddTotalSpList p λ` is the exponent list of CSI10's `S_p(λ)` (`Sp p λ`), in its order: for each
  `t < k − 1`, `(p−1) d_k p^{k−t−2} 2^{|I|}` copies of `t + 1`, then `(d_k − 1) 2^{|I|}` copies of
  `k` (`k = kTop p λ`, `d_k = digitL p λ k`, `I = Iset p λ`).
* `oddTotalCList p λ i e` is the exponent list of the cokernel `C` of CSI18 (Y2), in the order of
  (Y2): for `i ≥ 1`, the `2^{|I|}` exponents `k + (C + ŷ(2^{|I|} − 1 − j)).toNat`; for `i = 0`, the
  `2^{|I|} − 1` exponents `k + (eK + ŷ^♯(2^{|I|} − 2 − j)).toNat` (none when `I = ∅`).  Here
  `C = oddSmithC p λ i e`, `K = oddSmithK p λ`, `ŷ = oddSmithYhat p λ i e`,
  `ŷ^♯ = oddSmithYhatSharp p λ e`; these integers are `≥ 0` (CSI18 (Y2)), so `.toNat` is exact.
* `oddTotalYList p λ i e = oddTotalSpList p λ ++ oddTotalCList p λ i e`: the torsion exponents of
  `Y_p(λ, i, e)`.  Its free part is `ℤ_[p]^{[i = 0]}`, written `Fin (if i = 0 then 1 else 0) → ℤ_[p]`.
* Some entries can be `0` (e.g. `λ = 1 < p − 1` gives `k = 0` and one factor `ℤ/p^0` of
  `S_p(1)`); such a factor is the trivial group, and `oddTotal_expFilter` removes it.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open ColouredSand.ThmG Finset

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The exponents of `S_p(λ)` (Part S (S2) of `CSI19_theorem_TOTAL.md`; CSI10's `Sp p λ`). -/
def oddTotalSpList (l : ℕ) : List ℕ :=
  (List.ofFn fun t : Fin (kTop p l - 1) =>
      List.replicate ((p - 1) * digitL p l (kTop p l) * p ^ (kTop p l - (t + 1) - 1) *
        2 ^ (Iset p l).card) ((t : ℕ) + 1)).flatten ++
    List.replicate ((digitL p l (kTop p l) - 1) * 2 ^ (Iset p l).card) (kTop p l)

variable (p) in
/-- The exponents of the cokernel `C` of CSI18 (Y2) (Part S (S2) of `CSI19_theorem_TOTAL.md`):
`k + C + ŷ(2^{|I|} − 1 − j)` (`j < 2^{|I|}`) for `i ≥ 1`, and `k + eK + ŷ^♯(2^{|I|} − 2 − j)`
(`j < 2^{|I|} − 1`) for `i = 0`. -/
def oddTotalCList (l i e : ℕ) : List ℕ :=
  if i = 0 then
    List.ofFn fun j : Fin (2 ^ #(Iset p l) - 1) => kTop p l +
      ((e : ℤ) * (oddSmithK p l : ℤ) + oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)).toNat
  else
    List.ofFn fun j : Fin (2 ^ #(Iset p l)) => kTop p l +
      (oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)).toNat

variable (p) in
/-- The torsion exponents of `Y_p(λ, i, e)` (Part S (S2) of `CSI19_theorem_TOTAL.md`): the
`S_p(λ)` exponents, then those of CSI18 (Y2). -/
def oddTotalYList (l i e : ℕ) : List ℕ := oddTotalSpList p l ++ oddTotalCList p l i e

/-! ### Small equivalences -/

/-- `ℤ_[p] ⧸ p^a ≃+ ℤ/p^a`. -/
def oddTotalZqEquiv (a : ℕ) : Zq p a ≃+ ZMod (p ^ a) := ColouredSand.Blocks.padicQuotEquiv a

omit [Fact p.Prime] in
lemma oddTotal_flatten_ofFn_single : (n : ℕ) → (f : Fin n → ℕ) →
    (List.ofFn fun j => [f j]).flatten = List.ofFn f
  | 0, _ => rfl
  | n + 1, f => by
      rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, oddTotal_flatten_ofFn_single n]
      rfl

/-- `Π_{j < n} ℤ_[p] ⧸ p^{f j} ≃+ ⊕_{a ∈ ofFn f} ℤ/p^a`. -/
def oddTotalPiZq (n : ℕ) (f : Fin n → ℕ) :
    ((j : Fin n) → Zq p (f j)) ≃+ ExpGrp p (List.ofFn f) :=
  (AddEquiv.piCongrRight fun j => (oddTotalZqEquiv (f j)).trans (expSingle p (f j)).symm).trans
    ((expOfFn p n fun j => [f j]).trans (expCast p (oddTotal_flatten_ofFn_single n f)))

/-- `(Fin n → ℤ_[p] ⧸ p^a) ≃+ ⊕_{replicate n a} ℤ/p^a`. -/
def oddTotalRepZq (n a : ℕ) : (Fin n → Zq p a) ≃+ ExpGrp p (List.replicate n a) :=
  (AddEquiv.piCongrRight fun _ => oddTotalZqEquiv a).trans (expReplicate p a n).symm

/-- `S_p(λ) ≃+ ⊕_{a ∈ oddTotalSpList p λ} ℤ/p^a` (Part S (S2) of `CSI19_theorem_TOTAL.md`). -/
def oddTotalSpEquiv (l : ℕ) : Sp p l ≃+ ExpGrp p (oddTotalSpList p l) :=
  (AddEquiv.prodCongr
    ((AddEquiv.piCongrRight fun _ : Fin (kTop p l - 1) => oddTotalRepZq _ _).trans
      (expOfFn p _ _))
    (oddTotalRepZq _ _)).trans (expAppend p _ _).symm

/-- Dropping the trivial factors `ℤ/p^0`: `ExpGrp p L ≃+ ExpGrp p (L.filter (· ≠ 0))`. -/
def oddTotalExpFilter (p : ℕ) : (L : List ℕ) →
    ExpGrp p L ≃+ ExpGrp p (L.filter (fun a => a ≠ 0))
  | [] => AddEquiv.refl _
  | a :: L =>
      if ha : a = 0 then
        haveI : Unique (ZMod (p ^ a)) := by
          rw [ha, pow_zero]; exact inferInstanceAs (Unique (Fin 1))
        ((expCons p a L).trans (AddEquiv.uniqueProd.trans (oddTotalExpFilter p L))).trans
          (expCast p (by simp [ha]))
      else
        ((expCons p a L).trans ((AddEquiv.refl _).prodCongr (oddTotalExpFilter p L))).trans
          ((expCons p a _).symm.trans (expCast p (by simp [ha])))

lemma oddTotal_ne_zero_of_mem_filter {L : List ℕ} :
    ∀ a ∈ L.filter (fun a => a ≠ 0), a ≠ 0 := fun a ha => by
  simpa using (List.mem_filter.1 ha).2

/-- The free rank of `Y_p(λ, i, e)` as a type (`ℤ_[p]^{[i = 0]}`). -/
abbrev oddTotalFree (i : ℕ) : Type := Fin (if i = 0 then 1 else 0) → ℤ_[p]

/-- Transport of `ℤ_[p]^n` along `n = n'` (auxiliary). -/
def oddTotalFinCongr {n n' : ℕ} (h : n = n') : (Fin n → ℤ_[p]) ≃+ (Fin n' → ℤ_[p]) := by
  subst h; exact AddEquiv.refl _

/-- `A × (B × C) ≃+ B × (A × C)` (auxiliary). -/
def oddTotalSwap {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] :
    (A × (B × C)) ≃+ (B × (A × C)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun y := (y.2.1, (y.1, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-! ### The exponents of `Y_p(λ, i, e)` -/

omit [Fact p.Prime] in
/-- The three cases of `oddTotalCList` (auxiliary). -/
lemma oddTotalCList_zero (l e : ℕ) : oddTotalCList p l 0 e =
    List.ofFn fun j : Fin (2 ^ #(Iset p l) - 1) => kTop p l +
      ((e : ℤ) * (oddSmithK p l : ℤ) + oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)).toNat := by
  simp [oddTotalCList]

omit [Fact p.Prime] in
lemma oddTotalCList_pos (l i e : ℕ) (hi : i ≠ 0) : oddTotalCList p l i e =
    List.ofFn fun j : Fin (2 ^ #(Iset p l)) => kTop p l +
      (oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)).toNat := by
  simp [oddTotalCList, hi]

omit [Fact p.Prime] in
lemma oddTotalCList_zero_empty (l e : ℕ) (hI : Iset p l = ∅) : oddTotalCList p l 0 e = [] := by
  rw [oddTotalCList_zero, List.ofFn_eq_nil_iff]
  simp [hI]

/-- One block, `i ≥ 1` (auxiliary for `oddTotal_Yp_split`): from CSI18 `oddSmith_Y2_pos`. -/
theorem oddTotal_Yp_split_pos (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : i ≠ 0) :
    Nonempty (Yp p l i e ≃+ ExpGrp p (oddTotalYList p l i e)) := by
  obtain ⟨E, hE, ⟨φ⟩⟩ := oddSmith_Y2_pos p hodd l i e he (by omega)
  have hEq : (List.ofFn fun j : Fin (2 ^ #(Iset p l)) => kTop p l + E j) =
      oddTotalCList p l i e := by
    rw [oddTotalCList_pos l i e hi]
    congr 1; funext j; rw [← hE j j.2, Int.toNat_natCast]
  exact ⟨φ.toAddEquiv.trans ((AddEquiv.prodCongr (oddTotalSpEquiv l)
    ((oddTotalPiZq _ _).trans (expCast p hEq))).trans (expAppend p _ _).symm)⟩

/-- One block, `i = 0`, `I ≠ ∅` (auxiliary for `oddTotal_Yp_split`): from CSI18
`oddSmith_Y2_zero`. -/
theorem oddTotal_Yp_split_zero (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hI : (Iset p l).Nonempty) :
    Nonempty (Yp p l 0 e ≃+ (ℤ_[p] × ExpGrp p (oddTotalYList p l 0 e))) := by
  obtain ⟨E, hE, ⟨φ⟩⟩ := oddSmith_Y2_zero p hodd l e he hI
  have hEq : (List.ofFn fun j : Fin (2 ^ #(Iset p l) - 1) => kTop p l + E j) =
      oddTotalCList p l 0 e := by
    rw [oddTotalCList_zero l e]
    congr 1; funext j; rw [← hE j j.2, Int.toNat_natCast]
  let e1 : (Sp p l × (ℤ_[p] × ((j : Fin (2 ^ #(Iset p l) - 1)) → Zq p (kTop p l + E j)))) ≃+
      (ExpGrp p (oddTotalSpList p l) × (ℤ_[p] × ExpGrp p (oddTotalCList p l 0 e))) :=
    AddEquiv.prodCongr (oddTotalSpEquiv l)
      (AddEquiv.prodCongr (AddEquiv.refl ℤ_[p]) ((oddTotalPiZq _ _).trans (expCast p hEq)))
  let e2 : (ExpGrp p (oddTotalSpList p l) × (ℤ_[p] × ExpGrp p (oddTotalCList p l 0 e))) ≃+
      (ℤ_[p] × ExpGrp p (oddTotalYList p l 0 e)) :=
    oddTotalSwap.trans ((AddEquiv.refl ℤ_[p]).prodCongr (expAppend p _ _).symm)
  exact ⟨(φ.toAddEquiv.trans e1).trans e2⟩

/-- One block, `i = 0`, `I = ∅` (auxiliary for `oddTotal_Yp_split`): from CSI18
`oddSmith_Y2_zero_empty`. -/
theorem oddTotal_Yp_split_zero_empty (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hI : Iset p l = ∅) :
    Nonempty (Yp p l 0 e ≃+ (ℤ_[p] × ExpGrp p (oddTotalYList p l 0 e))) := by
  obtain ⟨φ⟩ := oddSmith_Y2_zero_empty p hodd l e he hI
  have hEq : oddTotalSpList p l = oddTotalYList p l 0 e := by
    rw [oddTotalYList, oddTotalCList_zero_empty l e hI, List.append_nil]
  exact ⟨φ.toAddEquiv.trans ((AddEquiv.prodComm).trans
    ((AddEquiv.refl ℤ_[p]).prodCongr ((oddTotalSpEquiv l).trans (expCast p hEq))))⟩

/-- Part S (S2) of `CSI19_theorem_TOTAL.md`, one block: for an odd prime `p` and `e ≥ 1`,
`Y_p(λ, i, e) ≃+ ℤ_[p]^{[i = 0]} ⊕ ⊕_{a ∈ oddTotalYList p λ i e} ℤ/p^a`.  From CSI18 (Y2)
(`oddSmith_Y2_pos`, `oddSmith_Y2_zero`, `oddSmith_Y2_zero_empty`). -/
theorem oddTotal_Yp_split (hp2 : p ≠ 2) (l i e : ℕ) (he : 1 ≤ e) :
    Nonempty (Yp p l i e ≃+ (oddTotalFree (p := p) i × ExpGrp p (oddTotalYList p l i e))) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  by_cases hi : i = 0
  · subst hi
    let eF : ℤ_[p] ≃+ oddTotalFree (p := p) 0 :=
      (LinearEquiv.funUnique (Fin 1) ℤ_[p] ℤ_[p]).toAddEquiv.symm.trans
        (oddTotalFinCongr (by simp))
    by_cases hI : Iset p l = ∅
    · obtain ⟨φ⟩ := oddTotal_Yp_split_zero_empty hodd l e he hI
      exact ⟨φ.trans (eF.prodCongr (AddEquiv.refl _))⟩
    · obtain ⟨φ⟩ := oddTotal_Yp_split_zero hodd l e he (Finset.nonempty_iff_ne_empty.2 hI)
      exact ⟨φ.trans (eF.prodCongr (AddEquiv.refl _))⟩
  · obtain ⟨φ⟩ := oddTotal_Yp_split_pos hodd l i e he hi
    haveI : Unique (oddTotalFree (p := p) i) := by
      unfold oddTotalFree; rw [if_neg hi]; exact Pi.uniqueOfIsEmpty _
    exact ⟨φ.trans AddEquiv.uniqueProd.symm⟩

end ColouredSand.OddTwist
