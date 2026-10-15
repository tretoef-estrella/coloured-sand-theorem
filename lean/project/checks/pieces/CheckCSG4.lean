import RequestProject.TiltRules.All

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
