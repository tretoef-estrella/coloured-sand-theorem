module

public import RequestProject.TheoremB.TheoremB

/-!
# (Q1), (Q2) Corollary 1: only the valuation of `q` matters

This file corresponds to **(Q1) Corollary 1, piece by piece** and **(Q2) Corollary 1, whole
group** of `CS6_corollaries_1_and_6.md`.

## Encoding

* `X_q(m,c) = coker (q (c+H) + U on B_m(ℤ))` is `Xq q m c` of `RequestProject/Splitting/Basic.lean`
  (`B_m(ℤ) = Finset (Fin m) → ℤ`, the cokernel is the quotient by the range).
* For an abelian group (`ℤ`-module) `X`, `tors X` is `Submodule.torsion ℤ X` and `Syl_p G` is
  Mathlib's `AddCommGroup.primaryComponent G p` (elements of `p`-power order).
* `K(H(d,q)) = sandpile d q`, the torsion subgroup of `coker L` (`RequestProject/TheoremB`).
* `v_p(q)` is `padicValNat p q`.
* "`≃+`" is an isomorphism of abelian groups.
* The product in (Q2) is the product over `σ : Σ j : Fin (d+1), Fin (C(d,j) (q−2)^j)` of
  `Syl_p (tors X_{p^e}(d − j, j))`, exactly as in the file.

## Proof

As in the file.  `Syl_p (tors X) ≅ Syl_p X ≅ tors_{ℤ_[p]} (ℤ_[p] ⊗ X)` (`sylTorsion`,
`torsion_tensor_equiv_syl`, from (B1)); `ℤ_[p] ⊗ X_q(m,c) ≅ coker (q(c+H)+U)` over `ℤ_[p]`
(`pieceBaseChange`); and (A4) (`opM_coker_depends_only_on_valuations`).  For (Q2): Theorem A,
torsion and `p`-primary parts commute with finite products, and (Q1) on each factor.
-/

@[expose] public section

open TensorProduct

namespace ColouredSand.Corollaries

open ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB

variable (p : ℕ) [hp : Fact p.Prime]

/-- `Syl_p (tors X_q(m,c)) ≅ tors_{ℤ_[p]} coker (q (c+H) + U on B_m(ℤ_[p]))`. -/
lemma sylTorsXq_equiv (q m c : ℕ) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      Submodule.torsion ℤ_[p] (B m ℤ_[p] ⧸ LinearMap.range
        (opM m ℤ_[p] ((q : ℤ) : ℤ_[p]) ((c : ℤ) : ℤ_[p])))) := by
  have e1 := (sylTorsion (p := p) (Xq q m c)).toAddEquiv
  obtain ⟨e2⟩ := torsion_tensor_equiv_syl (p := p) (Xq q m c)
  have e3 := torsionEquiv (pieceBaseChange (p := p) q m c)
  have hop : (((q : ℤ) : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p]) =
      opM m ℤ_[p] ((q : ℤ) : ℤ_[p]) ((c : ℤ) : ℤ_[p]) := by
    simp only [opM, Int.cast_natCast]
  rw [hop] at e3
  exact ⟨e1.trans (e2.symm.trans e3.toAddEquiv)⟩

/-- **(Q1) Corollary 1, piece by piece.**  Let `p` be a prime, `m, c ∈ ℕ` and `q, q' ≥ 1` with
`v_p(q) = v_p(q')`.  Then `Syl_p (tors X_q(m,c)) ≅ Syl_p (tors X_{q'}(m,c))`. -/
theorem corollary1_piece (m c q q' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hv : padicValNat p q = padicValNat p q') :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q' m c)) p) := by
  obtain ⟨e1⟩ := sylTorsXq_equiv p q m c
  obtain ⟨e2⟩ := sylTorsXq_equiv p q' m c
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hq0' : (q' : ℤ) ≠ 0 := by exact_mod_cast (show q' ≠ 0 by omega)
  obtain ⟨E⟩ := opM_coker_depends_only_on_valuations (p := p) m (q : ℤ) (c : ℤ) (q' : ℤ) (c : ℤ)
    (fun s _ => by simp [show q ≠ 0 by omega, show q' ≠ 0 by omega])
    (fun s _ => by
      by_cases hcs : (c : ℤ) + s = 0
      · simp [hcs]
      · rw [padicValInt.mul hq0 hcs, padicValInt.mul hq0' hcs, padicValInt.of_nat,
          padicValInt.of_nat, hv])
  exact ⟨e1.trans ((torsionEquiv E).toAddEquiv.trans e2.symm)⟩

/-- **(Q1), second form.**  With `e = v_p(q)` and `q ≥ 1`:
`Syl_p (tors X_q(m,c)) ≅ Syl_p (tors X_{p^e}(m,c))`. -/
theorem corollary1_piece_pow (m c q : ℕ) (hq : 1 ≤ q) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      AddCommGroup.primaryComponent
        (Submodule.torsion ℤ (Xq (p ^ padicValNat p q) m c)) p) :=
  corollary1_piece p m c q _ hq (Nat.one_le_pow _ _ hp.out.pos)
    (by rw [padicValNat.prime_pow])

/-- **(Q2) Corollary 1, whole group.**  Let `p` be a prime, `d ∈ ℕ`, `q ≥ 2` and `e = v_p(q)`.
Then `Syl_p K(H(d,q)) ≅ ∏_{(j,i) : Σ j : Fin (d+1), Fin (C(d,j)(q−2)^j)} Syl_p (tors X_{p^e}(d−j, j))`.
So `Syl_p K(H(d,q))` depends on `q` only through `e` and the multiplicities `C(d,j)(q−2)^j`. -/
theorem corollary1_whole (d q : ℕ) (hq : 2 ≤ q) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        AddCommGroup.primaryComponent
          (Submodule.torsion ℤ (Xq (p ^ padicValNat p q) (d - σ.1) σ.1)) p)) := by
  obtain ⟨EA⟩ := theorem_A d q hq
  let X : (Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) → Type :=
    fun σ => Xq q (d - σ.1) σ.1
  let e1 : sylSub p (sandpile d q) ≃ₗ[ℤ] sylSub p (∀ σ, Submodule.torsion ℤ (X σ)) :=
    sylEquiv ((torsionEquiv EA).trans (torsionPi X))
  let e2 := sylPi (p := p) (fun σ => Submodule.torsion ℤ (X σ))
  have e3 : ∀ σ, Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (X σ)) p ≃+
      AddCommGroup.primaryComponent
        (Submodule.torsion ℤ (Xq (p ^ padicValNat p q) (d - σ.1) σ.1)) p) :=
    fun σ => corollary1_piece_pow p (d - σ.1) σ.1 q (by omega)
  exact ⟨(e1.trans e2).toAddEquiv.trans (AddEquiv.piCongrRight fun σ => (e3 σ).some)⟩

end ColouredSand.Corollaries
