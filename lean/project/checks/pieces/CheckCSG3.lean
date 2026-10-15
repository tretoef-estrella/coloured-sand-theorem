import RequestProject.TiltP.All

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
