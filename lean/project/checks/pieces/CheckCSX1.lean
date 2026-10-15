import RequestProject.StringsAll.All

/-!
# CheckCSX1 (Grepy Ship, 15 Oct 2026)

Hand restatement of CSX1 (`CSX1_theorem_E_every_prime.md`): Theorem E of the Coloured Sand for
every prime `p` and every `q ≠ 0`; the case `p ∤ q` (`e = v_p(q) = 0`) written out with the
exponent `∑_{r=k}^{m−k} v_p(c + r)`; and the old theorem `theorem_E` recovered. Then `#print axioms`.
-/

namespace CheckCSX1

open ColouredSand ColouredSand.Strings Finset

/-- Theorem E, every prime, `q ≠ 0` (restated by hand). -/
theorem hE (p : ℕ) [Fact p.Prime] (q : ℤ) (hq : q ≠ 0) (c m : ℕ) (hm : m < p) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range
        ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ expA p q c m t.1}))) :=
  strAll_theorem_E p q hq c m hm

/-- The case `p ∤ q`, exponents written out with no `v_p(q)` (restated by hand). -/
theorem hCoprime (p : ℕ) [Fact p.Prime] (q : ℤ) (hq : ¬ (p : ℤ) ∣ q) (c m : ℕ) (hm : m < p) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range
        ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) →
          ℤ_[p] ⧸ Ideal.span
            {(p : ℤ_[p]) ^ ∑ r ∈ Icc (t.1 : ℕ) (m - t.1), padicValNat p (c + r)}))) :=
  strAll_theorem_E_coprime_explicit p q hq c m hm

/-- The old statement (CS1) is a special case. -/
theorem hOld (p : ℕ) [Fact p.Prime] (q : ℤ) (hq : 1 ≤ padicValInt p q) (c m : ℕ) (hm : m < p) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range
        ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ expA p q c m t.1}))) :=
  strAll_theorem_E_eq p q hq c m hm

/-- A concrete instance of the new case: `p = 5`, `q = 7` (not divisible by 5). -/
example : ¬ ((5 : ℕ) : ℤ) ∣ (7 : ℤ) := by decide

end CheckCSX1

#print axioms CheckCSX1.hE
#print axioms CheckCSX1.hCoprime
#print axioms CheckCSX1.hOld
#print axioms ColouredSand.Strings.strAll_span_prod_eq
#print axioms ColouredSand.Strings.strAll_theorem_E
#print axioms ColouredSand.Strings.strAll_theorem_E_coprime
#print axioms ColouredSand.Strings.strAll_theorem_E_coprime_explicit
#print axioms ColouredSand.Strings.strAll_theorem_E_eq
