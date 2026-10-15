-- Grepy Ship, 15 Oct 2026: written by the cold reader «Grepy Cartas Largas» (mission name «Grepy el Contraste») as checks/G4_L3_paperE.lean (md5 bea9a4803b06cd450cfb0914e49d3f24); copied unchanged below this line. Theorem E in the paper's form, every prime.
import RequestProject.StringsAll.All
import RequestProject.ThmGTwo.All

/-!
# G4_L3 — Grepy el Contraste (COLOURED_SAND_4), Lean run L3

Theorem E **in the paper's form** (`Syl_p X_q(m,c) ≅ ⊕_{k, (c,k) ≠ (0,0)} (ℤ/p^{A_k})^{C(m,k)−C(m,k−1)}`), for every
prime `p` and every natural `q ≠ 0` (so `p ∤ q` is included), derived from the project's
`Strings.strAll_theorem_E` (the `ℤ_p`-cokernel form, CSX1), `Corollaries.sylTorsXq_equiv` (Syl_p of the torsion
of `X_q(m,c)` = torsion of the `ℤ_p`-cokernel), `ThmH.freeTorsionEquiv` (cokernel = free part × torsion) and
`ThmG.cancelFree`.  Then an instance at `(p,q,c,m) = (3,4,1,2)`, with its exponents evaluated.
-/

open ColouredSand

namespace GrepyG4E

open ColouredSand.Strings ColouredSand.Splitting

theorem paperE (p : ℕ) [Fact p.Prime] (q c m : ℕ) (hq : q ≠ 0) (hm : m < p) :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) →
        ZMod (p ^ expA p (q : ℤ) c m t.1))) := by
  obtain ⟨e1⟩ := Corollaries.sylTorsXq_equiv p q m c
  rw [show ((c : ℤ) : ℤ_[p]) = (c : ℤ_[p]) from Int.cast_natCast c] at e1
  have hq' : ((q : ℤ) : ℤ_[p]) ≠ 0 := by exact_mod_cast hq
  let e2 := ThmH.freeTorsionEquiv (R := ℤ_[p]) m hq' c
  obtain ⟨e3⟩ := strAll_theorem_E p (q : ℤ) (by exact_mod_cast hq) c m hm
  let E := ((AddEquiv.refl (Fin (if c = 0 then 1 else 0) → ℤ_[p])).prodCongr e1).trans
    (e2.toAddEquiv.trans e3.toAddEquiv)
  have hA : ∀ x : Fin (if c = 0 then 1 else 0) → ℤ_[p], IsOfFinAddOrder x → x = 0 :=
    ThmG.pi_torsionFree _
  have hT : ∀ x : ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) →
      ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ expA p (q : ℤ) c m t.1}), IsOfFinAddOrder x := by
    refine ThmG.pi_torsion (fun i x => ?_)
    refine (isOfFinAddOrder_iff_nsmul_eq_zero).2
      ⟨p ^ expA p (q : ℤ) c m i.1, pow_pos (Fact.out : p.Prime).pos _, ?_⟩
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, nsmul_eq_mul]
      push_cast
      exact Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self _)
  exact ⟨(ThmG.cancelFree hA hA ThmG.primary_isOfFinAddOrder hT E).trans
    (AddEquiv.piCongrRight fun t => ColouredSand.Blocks.padicQuotEquiv (p := p) (expA p (q : ℤ) c m t.1))⟩

/-- The exponents at `(p, q, c, m) = (3, 4, 1, 2)`: `A_0 = v_3(1)+v_3(2)+v_3(3) = 1`, `A_1 = v_3(2) = 0`. -/
lemma expA_3_4_1_2 : expA 3 (4 : ℤ) 1 2 0 = 1 ∧ expA 3 (4 : ℤ) 1 2 1 = 0 := by
  have h4 : padicValInt 3 4 = 0 := padicValInt.eq_zero_of_not_dvd (by norm_num)
  have h1 : padicValNat 3 1 = 0 := padicValNat.one
  have h2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h3 : padicValNat 3 3 = 1 := padicValNat.self (by norm_num)
  have i0 : Finset.Icc 0 2 = {0, 1, 2} := by decide
  have i1 : Finset.Icc 1 1 = {1} := by decide
  refine ⟨?_, ?_⟩
  · simp [expA, i0, h4, h1, h2, h3]
  · simp [expA, i1, h4, h2]

/-- **Instance (paper form of Theorem E with `p ∤ q`):** `Syl_3 X_4(2,1)`, with `A_0 = 1`, `A_1 = 0`. -/
theorem inst_E_3_4_1_2 : Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq 4 2 1)) 3 ≃+
      ((t : Σ k : {k : Fin (2 / 2 + 1) // (1, (k : ℕ)) ≠ (0, 0)}, Fin (strMult 2 k)) →
        ZMod (3 ^ expA 3 ((4 : ℕ) : ℤ) 1 2 t.1))) :=
  paperE 3 4 1 2 (by norm_num) (by norm_num)

/-- Its order: `3` (the only `3`-part of `det = 4·8·8·12 = 2^10·3`). -/
theorem card_E_3_4_1_2 : Nat.card (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq 4 2 1)) 3) = 3 := by
  obtain ⟨e⟩ := inst_E_3_4_1_2
  rw [Nat.card_congr e.toEquiv, Nat.card_pi]
  simp only [Nat.card_zmod]
  have hE : ∀ k : Fin (2 / 2 + 1), expA 3 ((4 : ℕ) : ℤ) 1 2 k = if (k : ℕ) = 0 then 1 else 0 := by
    intro k
    fin_cases k
    · simpa using expA_3_4_1_2.1
    · simpa using expA_3_4_1_2.2
  simp only [hE]
  decide

end GrepyG4E

#check @GrepyG4E.paperE
#print axioms GrepyG4E.paperE
#print axioms GrepyG4E.expA_3_4_1_2
#print axioms GrepyG4E.inst_E_3_4_1_2
#print axioms GrepyG4E.card_E_3_4_1_2
