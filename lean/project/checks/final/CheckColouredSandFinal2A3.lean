-- CheckColouredSandFinal2A3.lean (part A3 of half A: every import, pieces 9-12) — the final check of the Coloured Sand Lean project (v3 + Theorems I, TOTAL + the three cases CSX1-3).
-- Assembled by assemble_final.py (Grepy Ship, 14 Oct 2026; v2 15 Oct 2026) from the 36 certified per-piece check files, each body unchanged
-- inside its own namespace FinalCheck.<piece>. Every `#print axioms` line must read [propext, Classical.choice, Quot.sound].
import RequestProject.BlockOp.All
import RequestProject.Blocks.All
import RequestProject.Corollaries.All
import RequestProject.Exponent.All
import RequestProject.Glue.All
import RequestProject.NumberOfFactors.All
import RequestProject.OddCeiling.All
import RequestProject.OddCellFloor.All
import RequestProject.OddDance.All
import RequestProject.OddDeficit.All
import RequestProject.OddHouses.All
import RequestProject.OddLevels.All
import RequestProject.OddPayment.All
import RequestProject.OddPotential.All
import RequestProject.OddRulers.All
import RequestProject.OddSES.All
import RequestProject.OddSmith.All
import RequestProject.OddSplit.All
import RequestProject.OddSplitMove.All
import RequestProject.OddSplitting.All
import RequestProject.OddTheoremI.All
import RequestProject.OddTotal.All
import RequestProject.OddTwist.All
import RequestProject.OddTwistModP.All
import RequestProject.OddWindows.All
import RequestProject.Splitting.All
import RequestProject.Strings.All
import RequestProject.StringsAll.All
import RequestProject.TheoremB.All
import RequestProject.ThmG.All
import RequestProject.ThmGTwo.All
import RequestProject.ThmH.All
import RequestProject.TiltDec.All
import RequestProject.TiltP.All
import RequestProject.TiltRules.All
import RequestProject.TwoTheoremI.All

-- ======== piece CSH1 (from lean/proyecto_cubo/checks/CheckCSH1.lean) ========
namespace FinalCheck.CSH1

/-! CheckCSH1 — Grepy Sand, 13 Oct 2026. Theorem H of «The Coloured Sand Theorem» (paper v3,
doi:10.5281/zenodo.23329314): the prime 2, every d. Restated by hand with the objects written on
their face: the operator q(c+H)+U, X_q(m,c) as a quotient, the sandpile group as the torsion of the
cokernel of the Laplacian, and the family group as the cokernel of F + 2^{e−1}(λ + 2i − H) on T(λ). -/

open ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB ColouredSand.Corollaries
open ColouredSand.ThmH FamDec Families Filt

-- the objects, on their face
#print ColouredSand.Strings.opM
#print ColouredSand.Strings.H
#print ColouredSand.Strings.U
#print ColouredSand.Splitting.Xq
#print ColouredSand.Splitting.Mq
#print ColouredSand.TheoremB.sandpile
#print ColouredSand.TheoremB.cokerL
#print FamilyGroup.X
#print Families.sigL
#print ColouredSand.ThmH.Psi
#print ColouredSand.ThmH.beta
#check @FamDec.D2
#check @Families.B2Z

-- (D1)–(D3) as stated
#check @ColouredSand.ThmH.D1
#check @ColouredSand.ThmH.D2
#check @ColouredSand.ThmH.D3

-- (T1) restated by hand: the operator written out, and the family group written as the cokernel of
-- σ = F + 2^{e−1}((λ + 2i)·id − H) on T(λ), with i = c + (m − λ)/2.
example (e m c : ℕ) (he : 1 ≤ e) :
    Nonempty ((B m ℤ_[2] ⧸ LinearMap.range
        (((2 : ℤ_[2]) ^ e) • ((c : ℤ_[2]) • LinearMap.id + H m ℤ_[2]) + U m ℤ_[2])) ≃ₗ[ℤ_[2]]
      ((j : Fin (L m).length) →
        (((T ℤ_[2] ((L m).get j)).ι → ℤ_[2]) ⧸ LinearMap.range
          ((T ℤ_[2] ((L m).get j)).Fd 1 + ((2 : ℤ_[2]) ^ (e - 1)) •
            ((((L m).get j : ℤ_[2]) + 2 * (((c + (m - (L m).get j) / 2 : ℕ)) : ℤ_[2])) •
                LinearMap.id - DPLattice.H (T ℤ_[2] ((L m).get j))))))) := by
  obtain ⟨φ⟩ := T1 e m c he
  exact ⟨φ.trans (LinearEquiv.piCongrRight fun j => (sigEquivZ _ _ _).symm)⟩

-- (T3) restated by hand: X_q(m,c) written as B_m(ℤ) modulo the range of q(c+H)+U.
example (q m c : ℕ) (hq : 1 ≤ q) (heven : Even q) :
    Nonempty (((Fin (if c = 0 then 1 else 0) → ℤ_[2]) ×
        AddCommGroup.primaryComponent (Submodule.torsion ℤ (B m ℤ ⧸ LinearMap.range
          (((q : ℤ)) • (((c : ℤ)) • LinearMap.id + H m ℤ) + U m ℤ))) 2) ≃+
      ((j : Fin (L m).length) →
        FamilyGroup.X (ds ((L m).get j)) (padicValNat 2 q) (c + (m - (L m).get j) / 2))) :=
  T3 q m c hq heven

-- (T4) restated by hand: the sandpile group written as the torsion of the cokernel of the
-- Laplacian of H(d,q), Syl_2 as Mathlib's primary component.
example (d q : ℕ) (hq : 2 ≤ q) (heven : Even q) :
    Nonempty ((ℤ_[2] × AddCommGroup.primaryComponent
        (Submodule.torsion ℤ (((Fin d → Fin q) → ℤ) ⧸ LinearMap.range (laplacian d q))) 2) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (t : Fin (L (d - σ.1)).length) →
          FamilyGroup.X (ds ((L (d - σ.1)).get t)) (padicValNat 2 q)
            (σ.1 + (d - σ.1 - (L (d - σ.1)).get t) / 2))) :=
  T4 d q hq heven

-- (T5) the cube Q_d = H(d,2)
example (d : ℕ) :
    Nonempty ((ℤ_[2] × AddCommGroup.primaryComponent
        (Submodule.torsion ℤ (((Fin d → Fin 2) → ℤ) ⧸ LinearMap.range (laplacian d 2))) 2) ≃+
      ((t : Fin (L d).length) → FamilyGroup.X (ds ((L d).get t)) 1 ((d - (L d).get t) / 2))) :=
  T5 d

#check @ColouredSand.ThmH.T2
#check @ColouredSand.ThmH.N1
#check @ColouredSand.ThmH.N2_lists
#check @ColouredSand.ThmH.N2_halves

#print axioms ColouredSand.ThmH.D1
#print axioms ColouredSand.ThmH.D2
#print axioms ColouredSand.ThmH.D3
#print axioms ColouredSand.ThmH.freeTorsionEquiv
#print axioms ColouredSand.ThmH.T1
#print axioms ColouredSand.ThmH.T2
#print axioms ColouredSand.ThmH.T3
#print axioms ColouredSand.ThmH.T4
#print axioms ColouredSand.ThmH.T5
#print axioms ColouredSand.ThmH.T5_exponent
#print axioms ColouredSand.ThmH.N1
#print axioms ColouredSand.ThmH.N2_lists
#print axioms ColouredSand.ThmH.N2_halves

end FinalCheck.CSH1

-- ======== piece CSG3 (from lean/proyecto_cubo/checks/CheckCSG3.lean) ========
namespace FinalCheck.CSG3

/-!
# CheckCSG3 (Grepy Sand, 13 Oct 2026)

Hand restatement of CSG3 (`CSG3_tilting_lattices_and_clebsch_gordan.md`): the standing hypothesis,
the simple weights, the two numbers `r`, `a` of (T3), and the two formulas of the Clebsch–Gordan
intertwiner `Ψ` are written out again here (as explicit functions of the coordinates, no project
definition), and the statements (T1), (T2), (T3), (C1), (C2), (G1), (G2), (G3), (G4) are checked
against the certified theorems. Then `#print axioms`.
-/

namespace CheckCSG3

open DPLattice WeylFilt Doubling LemmaW Lemma35 ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP

/-- The standing hypothesis, by hand. -/
def hHyp (p r a : ℕ) : Prop := 1 ≤ r ∧ r ≤ p ∧ a ≤ p - 1 ∧ (r = p → a = p - 1)

example (p r a : ℕ) : GlueHyp p r a ↔ hHyp p r a := Iff.rfl

/-- Simple weights, by hand. -/
def hSimple (p l : ℕ) : Prop := l ≤ p - 1 ∨ (p ∣ l + 1 ∧ l ≤ p ^ 2 - 1)

example (p l : ℕ) : IsSimpleWt p l ↔ hSimple p l := Iff.rfl
example (p l : ℕ) : rT p l = (l - p) % p + 1 := rfl
example (p l : ℕ) : aT p l = (l - p) / p := rfl

/-- `Ψ(ℓ_i)`, by hand: `b₀ ⊗ e_i + b₁ ⊗ e_{i−1}`. -/
noncomputable def hPsiL (p : ℕ) [Fact p.Prime] (l i : ℕ) : Fin 2 × Fin (l + 1) → ℚ_[p] := fun k =>
  (if k.1 = 0 ∧ (k.2 : ℕ) = i then 1 else 0) + (if k.1 = 1 ∧ (k.2 : ℕ) + 1 = i then 1 else 0)

/-- `Ψ(s_j)`, by hand: `((l − j) b₁ ⊗ e_j − (j + 1) b₀ ⊗ e_{j+1}) / (l + 1)`. -/
noncomputable def hPsiS (p : ℕ) [Fact p.Prime] (l j : ℕ) : Fin 2 × Fin (l + 1) → ℚ_[p] := fun k =>
  (1 / ((l : ℚ_[p]) + 1)) *
    ((if k.1 = 1 ∧ (k.2 : ℕ) = j then ((l : ℚ_[p]) - j) else 0) -
      (if k.1 = 0 ∧ (k.2 : ℕ) = j + 1 then ((j : ℚ_[p]) + 1) else 0))

lemma hPsiL_eq (p : ℕ) [Fact p.Prime] (l i : ℕ) :
    bvec 0 (eN p l i) + (if 1 ≤ i then bvec 1 (eN p l (i - 1)) else 0) = hPsiL p l i := by
  funext k
  rcases k with ⟨e, m⟩
  by_cases hi : 1 ≤ i
  · rw [if_pos hi]
    fin_cases e <;> simp only [hPsiL, Pi.add_apply, bvec_apply, eN_apply] <;> split_ifs <;>
      (try simp_all) <;> (try omega)
  · rw [if_neg hi]
    fin_cases e <;> simp only [hPsiL, Pi.add_apply, Pi.zero_apply, bvec_apply, eN_apply] <;>
      split_ifs <;> (try simp_all) <;> (try omega)

lemma hPsiS_eq (p : ℕ) [Fact p.Prime] (l j : ℕ) :
    (1 / ((l : ℚ_[p]) + 1)) •
        (((l : ℚ_[p]) - j) • bvec 1 (eN p l j) - ((j : ℚ_[p]) + 1) • bvec 0 (eN p l (j + 1))) =
      hPsiS p l j := by
  funext k
  rcases k with ⟨e, m⟩
  fin_cases e <;> simp [hPsiS, bvec_apply, eN_apply]

/-- (G1) by hand: the two formulas of `Ψ`, its intertwining with every `F t`, `E t`, weights. -/
theorem hG1 (p : ℕ) [Fact p.Prime] {l : ℕ} (hl : 1 ≤ l) :
    (∀ i : ℕ, i ≤ l + 1 → PsiCG p l hl (ell p (l + 1) (l - 1) i) = hPsiL p l i) ∧
    (∀ j : ℕ, j ≤ l - 1 → PsiCG p l hl (ess p (l + 1) (l - 1) j) = hPsiS p l j) ∧
    (∀ t, (PsiCG p l hl).toLinearMap ∘ₗ Fop p (l + 1) (l - 1) t =
      (tensorV (delta ℚ_[p] l)).Fd t ∘ₗ (PsiCG p l hl).toLinearMap) ∧
    (∀ t, (PsiCG p l hl).toLinearMap ∘ₗ Eop p (l + 1) (l - 1) t =
      (tensorV (delta ℚ_[p] l)).Ed t ∘ₗ (PsiCG p l hl).toLinearMap) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := G1 (p := p) hl
  exact ⟨fun i hi => (h1 i hi).trans (hPsiL_eq p l i), fun j hj => (h2 j hj).trans (hPsiS_eq p l j),
    h3, h4⟩

/-- (G2) by hand: `Ψ (Lx (1/(l+1)))` is the `ℤ_[p]`-span of the standard basis. -/
theorem hG2 (p : ℕ) [Fact p.Prime] {l : ℕ} (hl : 1 ≤ l) :
    Submodule.map ((PsiCG p l hl).toLinearMap.restrictScalars ℤ_[p])
        (Lx p (l + 1) (l - 1) 1 (1 / ((l : ℚ_[p]) + 1))) =
      LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin 2 × Fin (l + 1))) := G2 hl

/-- (T1) under the hypothesis: the matrices of `F t`, `E t` in `glueBasis`, and `IsDP`. -/
theorem hT1 (p : ℕ) [Fact p.Prime] {r a : ℕ} (h : hHyp p r a) (t : ℕ)
    (v : Idx (lam p r a) (mu p r a) → ℤ_[p]) :
    (∑ y, (Tglue p r a).Fd t v y •
        (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) y : V p (lam p r a) (mu p r a)) =
      Fop p (lam p r a) (mu p r a) t (∑ y, v y •
        (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) y : V p (lam p r a) (mu p r a)))) ∧
    (∑ y, (Tglue p r a).Ed t v y •
        (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) y : V p (lam p r a) (mu p r a)) =
      Eop p (lam p r a) (mu p r a) t (∑ y, v y •
        (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) y : V p (lam p r a) (mu p r a)))) ∧
    IsDP (Tglue p r a).wt (Tglue p r a).Fd (Tglue p r a).Ed :=
  ⟨T1_Fd h t v, T1_Ed h t v, T1_isDP r a⟩

/-- (T1) the basis and the weights, by hand. -/
example (p : ℕ) [Fact p.Prime] (r a : ℕ) :
    (Tglue p r a).ι = (Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1)) := rfl
example (p : ℕ) [Fact p.Prime] (r a : ℕ) (i : Fin (lam p r a + 1)) :
    (Tglue p r a).wt (Sum.inl i) = (lam p r a : ℤ) - 2 * (i : ℤ) := rfl
example (p : ℕ) [Fact p.Prime] (r a : ℕ) (j : Fin (mu p r a + 1)) :
    (Tglue p r a).wt (Sum.inr j) = (mu p r a : ℤ) - 2 * (j : ℤ) := rfl

/-- (T2) by hand. -/
theorem hT2 (p : ℕ) [Fact p.Prime] (r a : ℕ) :
    ShortExact (Tf p r a) (Tg p r a) ∧ IsWtPres (Tf p r a).toLin ∧ IsWtPres (Tg p r a).toLin ∧
    (∀ i, (Tf p r a).toLin (Pi.single i 1) =
      (Pi.single (Sum.inl i : Idx (lam p r a) (mu p r a)) (1 : ℤ_[p]))) ∧
    (∀ i, (Tg p r a).toLin (Pi.single (Sum.inl i : Idx (lam p r a) (mu p r a)) 1) = 0) ∧
    (∀ j, (Tg p r a).toLin (Pi.single (Sum.inr j : Idx (lam p r a) (mu p r a)) 1) =
      (Pi.single j (1 : ℤ_[p]))) :=
  ⟨(T2 r a).1, (T2 r a).2.1, (T2 r a).2.2, Tf_single r a, Tg_single_inl r a, Tg_single_inr r a⟩

/-- (T3) by hand. -/
theorem hT3 (p : ℕ) [Fact p.Prime] (l : ℕ) :
    (hSimple p l → Ttilt p l = delta ℤ_[p] l) ∧
    (¬ hSimple p l → Ttilt p l = Tglue p ((l - p) % p + 1) ((l - p) / p)) ∧
    (¬ hSimple p l → l ≤ p ^ 2 + p - 1 →
      p ≤ l ∧ 1 ≤ (l - p) % p + 1 ∧ (l - p) % p + 1 ≤ p ∧ (l - p) / p ≤ p - 1 ∧
      ((l - p) % p + 1 = p → (l - p) / p = p - 1) ∧
      lam p ((l - p) % p + 1) ((l - p) / p) = l) :=
  ⟨Ttilt_of_simple p, Ttilt_of_not_simple p,
    fun h hl => T3 (Nat.Prime.two_le (Fact.out)) h hl⟩

/-- (C1), (C2) by hand. -/
theorem hC (p : ℕ) [Fact p.Prime] :
    (∀ (A : Type) [CommRing A] (l : ℕ), (∀ i ≤ l, IsUnit ((l.choose i : ℕ) : A)) →
      Nonempty (Iso (delta A l) (nabla A l))) ∧
    (∀ l, hSimple p l → Nonempty (Iso (delta ℤ_[p] l) (nabla ℤ_[p] l))) :=
  ⟨fun _ _ l hu => C1 l hu, fun _ hl => C2 p hl⟩

/-- (G3), (G4) by hand. -/
theorem hG34 (p : ℕ) [Fact p.Prime] :
    (∀ l, 1 ≤ l → ¬ p ∣ l + 1 →
      Nonempty (Iso (tensorV (delta ℤ_[p] l)) (dsum (delta ℤ_[p] (l + 1)) (delta ℤ_[p] (l - 1))))) ∧
    Nonempty (Iso (tensorV (delta ℤ_[p] (p - 1))) (Tglue p 1 0)) :=
  ⟨fun _ hl hpl => G3 hl hpl, G4⟩

end CheckCSG3

#print axioms CheckCSG3.hPsiL_eq
#print axioms CheckCSG3.hPsiS_eq
#print axioms CheckCSG3.hG1
#print axioms CheckCSG3.hG2
#print axioms CheckCSG3.hT1
#print axioms CheckCSG3.hT2
#print axioms CheckCSG3.hT3
#print axioms CheckCSG3.hC
#print axioms CheckCSG3.hG34
#print axioms ColouredSand.TiltP.T1_isDP
#print axioms ColouredSand.TiltP.T2
#print axioms ColouredSand.TiltP.T3
#print axioms ColouredSand.TiltP.T3_simple_iff
#print axioms ColouredSand.TiltP.C1
#print axioms ColouredSand.TiltP.C2
#print axioms ColouredSand.TiltP.G1
#print axioms ColouredSand.TiltP.G2
#print axioms ColouredSand.TiltP.G3
#print axioms ColouredSand.TiltP.G4
#print axioms ColouredSand.TiltP.iso_tensor_glueDP

end FinalCheck.CSG3

-- ======== piece CSG4 (from lean/proyecto_cubo/checks/CheckCSG4.lean) ========
namespace FinalCheck.CSG4

/-!
# CheckCSG4 (Grepy Sand, 13 Oct 2026)

Hand restatement of CSG4 (`CSG4_tensor_rules.md`): the tensor rules `V ⊗ T(λ)` with every weight
written out by hand (`λ = p − 1 + r + p a`, `μ = λ − 2r`, no `lam`/`mu`), checked against the
certified theorems of `ColouredSand.TiltRules`. Then `#print axioms`.
-/

namespace CheckCSG4

open DPLattice WeylFilt Doubling LemmaW Lemma35 ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP ColouredSand.TiltRules

/-- (S0)–(S2) by hand. -/
theorem hS (p : ℕ) [Fact p.Prime] :
    Nonempty (Iso (tensorV (delta ℤ_[p] 0)) (delta ℤ_[p] 1)) ∧
    (∀ l, 1 ≤ l → l ≤ p - 2 →
      Nonempty (Iso (tensorV (delta ℤ_[p] l)) (dsum (delta ℤ_[p] (l + 1)) (delta ℤ_[p] (l - 1))))) ∧
    (∀ b, b ≤ p - 1 → Nonempty (Iso (tensorV (delta ℤ_[p] ((b + 1) * p - 1))) (Tglue p 1 b))) :=
  ⟨S0, fun _ h1 h2 => S1 h1 h2, fun _ hb => S2 hb rfl⟩

/-- (R1) by hand: `r = 1`, `λ − 1 = p − 1 + 1 + p a − 1`. -/
theorem hR1 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : ℕ) (ha : a ≤ p - 1) :
    Nonempty (Iso (tensorV (Tglue p 1 a)) (dsum (Tglue p 2 a)
      (dsum (delta ℤ_[p] (p - 1 + 1 + p * a - 1)) (delta ℤ_[p] (p - 1 + 1 + p * a - 1))))) :=
  R1 hp2 ⟨le_rfl, (Fact.out : p.Prime).one_le, ha, fun h => by
    have := (Fact.out : p.Prime).two_le; omega⟩

/-- (R2) by hand. -/
theorem hR2 (p : ℕ) [Fact p.Prime] (r a : ℕ) (h : 1 ≤ r ∧ r ≤ p ∧ a ≤ p - 1 ∧ (r = p → a = p - 1))
    (hr : 2 ≤ r) (hrp : r ≤ p - 2) :
    Nonempty (Iso (tensorV (Tglue p r a)) (dsum (Tglue p (r + 1) a) (Tglue p (r - 1) a))) :=
  R2 h hr hrp

/-- (R3) by hand: `λ + 1 = p − 1 + (p − 1) + p a + 1`, `μ − 1 = λ − 2(p − 1) − 1`. -/
theorem hR3 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (∀ a, 1 ≤ a → a ≤ p - 2 →
      Nonempty (Iso (tensorV (Tglue p (p - 1) a))
        (dsum (delta ℤ_[p] (p - 1 + (p - 1) + p * a + 1))
          (dsum (Tglue p (p - 2) a) (delta ℤ_[p] (p - 1 + (p - 1) + p * a - 2 * (p - 1) - 1)))))) ∧
    Nonempty (Iso (tensorV (Tglue p (p - 1) 0))
      (dsum (delta ℤ_[p] (p - 1 + (p - 1) + p * 0 + 1)) (Tglue p (p - 2) 0))) :=
  ⟨fun _ h1 h2 => R3_pos h1 h2, R3_zero hp2⟩

/-- (R4) by hand. -/
theorem hR4 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Nonempty (Iso (tensorV (Tglue p (p - 1) (p - 1)))
      (dsum (Tglue p p (p - 1)) (Tglue p (p - 2) (p - 1)))) := R4 hp2

/-- The index identities of Part R, by hand. -/
theorem hShift (p : ℕ) [Fact p.Prime] (r a : ℕ) (h : GlueHyp p r a) (hrp : r ≤ p - 1) :
    lam p (r + 1) a = (p - 1 + r + p * a) + 1 ∧ mu p (r + 1) a = (p - 1 + r + p * a - 2 * r) - 1 ∧
    lam p (r - 1) a = (p - 1 + r + p * a) - 1 ∧ mu p (r - 1) a = (p - 1 + r + p * a - 2 * r) + 1 :=
  lam_mu_shift h hrp

end CheckCSG4

#print axioms CheckCSG4.hS
#print axioms CheckCSG4.hR1
#print axioms CheckCSG4.hR2
#print axioms CheckCSG4.hR3
#print axioms CheckCSG4.hR4
#print axioms CheckCSG4.hShift
#print axioms ColouredSand.TiltRules.S0
#print axioms ColouredSand.TiltRules.S1
#print axioms ColouredSand.TiltRules.S2
#print axioms ColouredSand.TiltRules.R1
#print axioms ColouredSand.TiltRules.R2
#print axioms ColouredSand.TiltRules.R3_pos
#print axioms ColouredSand.TiltRules.R3_zero
#print axioms ColouredSand.TiltRules.R4

end FinalCheck.CSG4

-- ======== piece CSG5 (from lean/proyecto_cubo/checks/CheckCSG5.lean) ========
namespace FinalCheck.CSG5

/-!
# CheckCSG5 (Grepy Sand, 13 Oct 2026)

Hand restatement of CSG5 (`CSG5_the_induction.md`): the rule (M1) written case by case with every
weight by hand, the recursion (M2), the number β written by hand with `Nat.choose`, and the
statements (D1), (D2), (D3), (W2), (W3), (W4), (W5) checked against the certified theorems of
`ColouredSand.TiltDec`. Then `#print axioms`.
-/

namespace CheckCSG5

open DPLattice WeylFilt Doubling Lemma35 Filt Step36 ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP ColouredSand.TiltRules ColouredSand.TiltDec

/-- β by hand: `C(n,k) − C(n,k−1)`, `k = (n − l)/2`, if `l ≤ n` and `l ≡ n (mod 2)`; else `0`. -/
def hBeta (n l : ℕ) : ℤ :=
  if l ≤ n ∧ l % 2 = n % 2 then
    (Nat.choose n ((n - l) / 2) : ℤ) -
      (if (n - l) / 2 = 0 then 0 else (Nat.choose n ((n - l) / 2 - 1) : ℤ))
  else 0

example (n l : ℕ) : betaCG n l = hBeta n l := rfl
example : hBeta 6 2 = 9 := by decide
example : hBeta 6 0 = 5 := by decide
example : hBeta 6 6 = 1 := by decide
example : hBeta 6 3 = 0 := by decide

/-- (M1) by hand, case by case (`r = (l − p) % p + 1`, `a = (l − p) / p`, `μ = l − 2r`). -/
theorem hM1 (p : ℕ) (hp : 3 ≤ p) :
    VdotP p 0 = [1] ∧
    (∀ l, IsSimpleWt p l → 1 ≤ l → l ≤ p - 2 → VdotP p l = [l + 1, l - 1]) ∧
    (∀ l, IsSimpleWt p l → p - 1 ≤ l → VdotP p l = [l + 1]) ∧
    (∀ l, ¬ IsSimpleWt p l → (l - p) % p + 1 = 1 → VdotP p l = [l + 1, l - 1, l - 1]) ∧
    (∀ l, ¬ IsSimpleWt p l → 2 ≤ (l - p) % p + 1 → (l - p) % p + 1 ≤ p - 2 →
      VdotP p l = [l + 1, l - 1]) ∧
    (∀ l, ¬ IsSimpleWt p l → (l - p) % p + 1 = p - 1 → 1 ≤ (l - p) / p → (l - p) / p ≤ p - 2 →
      VdotP p l = [l + 1, l - 1, l - 2 * ((l - p) % p + 1) - 1]) ∧
    (∀ l, ¬ IsSimpleWt p l → (l - p) % p + 1 = p - 1 → ((l - p) / p = 0 ∨ (l - p) / p = p - 1) →
      VdotP p l = [l + 1, l - 1]) :=
  ⟨VdotP_zero p, fun _ hs h1 h2 => VdotP_simple_small hs h1 h2,
    fun _ hs h => VdotP_simple_large (by omega) hs h, fun _ hs hr => VdotP_r_one hs hr,
    fun _ hs h1 h2 => VdotP_r_mid hs h1 h2, fun _ hs hr h1 h2 => VdotP_r_top_pos hp hs hr h1 h2,
    fun _ hs hr ha => VdotP_r_top_ext hp hs hr ha⟩

/-- (M2) and (M3) by hand. -/
theorem hM23 (p : ℕ) (hp : 2 ≤ p) :
    LP p 0 = [0] ∧ (∀ n, LP p (n + 1) = (LP p n).flatMap (VdotP p)) ∧
    (∀ n lam, mP p lam n = (LP p n).count lam) ∧
    (∀ n, ∀ lam ∈ LP p n, lam ≤ n ∧ lam % 2 = n % 2) :=
  ⟨rfl, fun _ => rfl, fun _ _ => rfl, fun n => M3 hp n⟩

/-- (D1), (D2), (D3) by hand. -/
theorem hD (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (∀ l, l ≤ p ^ 2 + p - 2 →
      Nonempty (Iso (tensorV (Ttilt p l)) (dsumList ((VdotP p l).map (Ttilt p))))) ∧
    (∀ n, n ≤ p ^ 2 + p - 1 →
      Nonempty (Iso (tpow ℤ_[p] n) (dsumList ((LP p n).map (Ttilt p))))) ∧
    (∀ n, n ≤ p ^ 2 + p - 1 →
      Nonempty (Iso (tpow ℤ_[p] n) (dsumList ((List.range (n + 1)).flatMap
        (fun lam => List.replicate ((LP p n).count lam) (Ttilt p lam)))))) :=
  ⟨fun _ h => D1 hp2 h, fun _ h => D2 hp2 h, fun _ h => D3 hp2 h⟩

/-- (W2)–(W5) by hand. -/
theorem hW (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp : 3 ≤ p) :
    (∀ n, n ≤ p ^ 2 + p - 1 → ((LP p n).flatMap (weylP p)).Perm (CG n)) ∧
    (∀ n l, ((CG n).count l : ℤ) = hBeta n l) ∧
    (∀ n l m, n ≤ p ^ 2 + p - 1 → ¬ IsSimpleWt p m → m ≤ n → m - 2 * ((m - p) % p + 1) = l →
      ((LP p n).count l : ℤ) + (LP p n).count m = hBeta n l) ∧
    (∀ n l, n ≤ p ^ 2 + p - 1 →
      (∀ m ≤ n, ¬ IsSimpleWt p m → m - 2 * ((m - p) % p + 1) ≠ l) →
      ((LP p n).count l : ℤ) = hBeta n l) ∧
    (∀ m₁ m₂, ¬ IsSimpleWt p m₁ → ¬ IsSimpleWt p m₂ → m₁ ≤ p ^ 2 + p - 1 → m₂ ≤ p ^ 2 + p - 1 →
      m₁ - 2 * ((m₁ - p) % p + 1) = m₂ - 2 * ((m₂ - p) % p + 1) → m₁ = m₂) ∧
    (∀ n, n ≤ p ^ 2 + p - 1 →
      ((LP p n).map (fun lam => Fintype.card (Ttilt p lam).ι)).sum = 2 ^ n) :=
  ⟨fun _ h => W2 hp h, W3, fun _ _ _ h hs hmn hm => W4_of_plus hp h hs hmn hm,
    fun _ _ h hh => W4_of_no_plus hp h hh,
    fun _ _ h1 h2 h3 h4 h5 => W4_inj (by omega) h1 h2 h3 h4 h5, fun _ h => W5_card hp2 h⟩

end CheckCSG5

#print axioms CheckCSG5.hM1
#print axioms CheckCSG5.hM23
#print axioms CheckCSG5.hD
#print axioms CheckCSG5.hW
#print axioms ColouredSand.TiltDec.D1
#print axioms ColouredSand.TiltDec.D2
#print axioms ColouredSand.TiltDec.D3
#print axioms ColouredSand.TiltDec.W2
#print axioms ColouredSand.TiltDec.W3
#print axioms ColouredSand.TiltDec.W4
#print axioms ColouredSand.TiltDec.W4_inj
#print axioms ColouredSand.TiltDec.W5
#print axioms ColouredSand.TiltDec.W5_card
#print axioms ColouredSand.TiltDec.M3

end FinalCheck.CSG5
