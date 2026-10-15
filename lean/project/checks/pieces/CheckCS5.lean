import RequestProject.NumberOfFactors.All

/-! CheckCS5 — Grepy Altair, 13 Oct 2026. Theorem D of «The Coloured Sand Theorem» (the number of
cyclic factors of the Sylow p-subgroup of the sandpile group of H(d,q), p ∣ q), Wilson's diagonal
form for W_{t,t+1} over ℤ, and the rank of U over F_p, restated by hand. -/

open scoped TensorProduct
open Finset Module ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB
  ColouredSand.NumberOfFactors

#print ColouredSand.NumberOfFactors.inclMat
#print ColouredSand.NumberOfFactors.rPart
#print ColouredSand.NumberOfFactors.rho
#print ColouredSand.NumberOfFactors.nFactors
#print ColouredSand.Strings.strMult

-- (D3) Theorem D restated by hand: the sandpile group as the torsion of coker L, Syl_p as
-- Mathlib's primary component, «number of cyclic factors» = dim_{F_p}(F_p ⊗ Syl_p K), and ρ_p
-- written out with r_p and C(m,i) − C(m,i−1).
example (p : ℕ) [Fact p.Prime] (d q : ℕ) (hq : 2 ≤ q) (hpq : p ∣ q) :
    finrank (ZMod p) (ZMod p ⊗[ℤ] AddCommGroup.primaryComponent
        (Submodule.torsion ℤ (((Fin d → Fin q) → ℤ) ⧸ LinearMap.range (laplacian d q))) p) =
      (∑ j ∈ range (d + 1), d.choose j * (q - 2) ^ j *
        (2 ^ (d - j) - ∑ s ∈ range (d - j),
          ∑ i ∈ (range ((if 2 * s ≤ d - j - 1 then s else d - j - 1 - s) + 1)).filter
              (fun i => ¬ p ∣ ((if 2 * s ≤ d - j - 1 then s else d - j - 1 - s) + 1 - i)),
            ((d - j).choose i - if i = 0 then 0 else (d - j).choose (i - 1)))) - 1 :=
  theorem_D p d q hq hpq

-- (D3′) the other tensor order, as abelian groups
example (p : ℕ) [Fact p.Prime] (d q : ℕ) (hq : 2 ≤ q) (hpq : p ∣ q) :
    Nonempty ((AddCommGroup.primaryComponent (sandpile d q) p ⊗[ℤ] ZMod p) ≃ₗ[ℤ]
      (Fin (nFactors p d q) → ZMod p)) := theorem_D' p d q hq hpq

-- (D1) Wilson's diagonal form, the case k = t + 1, restated by hand (matrix entries on their face)
example (m t : ℕ) (ht : 2 * t + 1 ≤ m) :
    ∃ (P : Matrix {S : Finset (Fin m) // S.card = t} {S : Finset (Fin m) // S.card = t} ℤ)
      (Q : Matrix {T : Finset (Fin m) // T.card = t + 1} {T : Finset (Fin m) // T.card = t + 1} ℤ)
      (φ : {S : Finset (Fin m) // S.card = t} ↪ {T : Finset (Fin m) // T.card = t + 1})
      (lab : {S : Finset (Fin m) // S.card = t} → ℕ),
      IsUnit P.det ∧ IsUnit Q.det ∧ (∀ a, lab a ≤ t) ∧
      P * Matrix.of (fun (S : {S : Finset (Fin m) // S.card = t})
          (T : {T : Finset (Fin m) // T.card = t + 1}) => if (S : Finset (Fin m)) ⊆ T then (1 : ℤ) else 0) * Q =
        Matrix.of (fun a b => if b = φ a then (t : ℤ) + 1 - lab a else 0) ∧
      ∀ i ≤ t, Fintype.card {a // lab a = i} = m.choose i - if i = 0 then 0 else m.choose (i - 1) :=
  wilson_diagonal_form m t ht

-- (D2) the rank of U over F_p
example (p : ℕ) [Fact p.Prime] (m : ℕ) :
    finrank (ZMod p) (LinearMap.range (U m (ZMod p))) = rho p m := rank_U_zmod p m
#check @ColouredSand.Strings.U

-- (D4) checks
example : [nFactors 3 1 3, nFactors 3 2 3, nFactors 3 3 3, nFactors 3 4 3, nFactors 3 5 3,
    nFactors 3 6 3] = [1, 4, 12, 34, 96, 274] := nFactors_three
example (p m : ℕ) (hpm : m < p) : rho p m = 2 ^ m - m.choose (m / 2) := rho_of_lt hpm

#print axioms theorem_D
#print axioms theorem_D'
#print axioms wilson_diagonal_form
#print axioms wilson_bases
#print axioms rank_U_zmod
#print axioms nFactors_three
#print axioms rho_three
#print axioms rho_two
#print axioms cyclic_factors_three
#print axioms rho_of_lt
#print axioms zeta_inj
