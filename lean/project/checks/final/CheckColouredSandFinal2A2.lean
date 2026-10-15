-- CheckColouredSandFinal2A2.lean (part A2 of half A: every import, pieces 5-8) — the final check of the Coloured Sand Lean project (v3 + Theorems I, TOTAL + the three cases CSX1-3).
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

-- ======== piece CS5 (from CONJETURA_HAMMING_2026-10-13/lean/proyecto_cs/checks/CheckCS5.lean) ========
namespace FinalCheck.CS5

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

end FinalCheck.CS5

-- ======== piece CS6 (from CONJETURA_HAMMING_2026-10-13/lean/proyecto_cs/checks/CheckCS6.lean) ========
namespace FinalCheck.CS6

/-! CheckCS6 — Grepy Altair, 13 Oct 2026. Corollaries 1 and 6 of «The Coloured Sand Theorem»
(v3, Zenodo 10.5281/zenodo.23329314) and the Jordan type of U over F_3, restated by hand. -/

open Finset Module TensorProduct
open ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB ColouredSand.Corollaries

#print ColouredSand.TheoremB.sandpile
#print ColouredSand.Splitting.Xq
#print ColouredSand.Corollaries.fCoker

-- (Q2) Corollary 1, whole group, restated by hand
example (p : ℕ) [Fact p.Prime] (d q : ℕ) (hq : 2 ≤ q) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        AddCommGroup.primaryComponent
          (Submodule.torsion ℤ (Xq (p ^ padicValNat p q) (d - σ.1) σ.1)) p)) :=
  corollary1_whole p d q hq

-- (Q1) restated by hand
example (p : ℕ) [Fact p.Prime] (m c q q' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hv : padicValNat p q = padicValNat p q') :
    Nonempty (AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) p ≃+
      AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q' m c)) p) :=
  corollary1_piece p m c q q' hq hq' hv

-- (Q3) restated by hand: f(m) = dim coker U over F_3
example (m : ℕ) :
    U m (ZMod 3) ^ 3 = 0 ∧
    3 * (finrank (ZMod 3) (B m (ZMod 3) ⧸ LinearMap.range (U m (ZMod 3))) - 1) =
      2 ^ m - 1 - m % 2 :=
  ⟨U_cube_zmod_three m, fCoker_formula m⟩

-- (Q4) Corollary 6 restated by hand; N is the left side of theorem_D at p = 3
example (d q : ℕ) (hq : 3 ≤ q) (h3 : 3 ∣ q) :
    6 * (finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile d q) 3) : ℤ) =
      6 * ((q : ℤ) - 1) ^ d + 2 * ((q : ℤ) ^ d - ((q : ℤ) - 1) ^ d) -
        (((q : ℤ) - 1) ^ d - ((q : ℤ) - 3) ^ d) - 6 :=
  corollary6 d q hq h3

example (d : ℕ) (hd : 1 ≤ d) :
    finrank (ZMod 3) (ZMod 3 ⊗[ℤ] AddCommGroup.primaryComponent (sandpile d 3) 3) =
      3 ^ (d - 1) + 2 ^ (d - 1) - 1 :=
  corollary6_q_three d hd

-- (Q5)
#check @cycFactors3_values
#check @fCoker_values

#print axioms corollary1_piece
#print axioms corollary1_piece_pow
#print axioms corollary1_whole
#print axioms jordan_type_U_zmod_three
#print axioms corollary6
#print axioms corollary6_q_three
#print axioms fCoker_values
#print axioms corN_values
#print axioms cycFactors3_values

end FinalCheck.CS6

-- ======== piece CSG1 (from CONJETURA_HAMMING_2026-10-13/lean/proyecto_cs/checks/CheckCSG1.lean) ========
namespace FinalCheck.CSG1

/-!
# CheckCSG1 (Grepy Sand, 13 Oct 2026)

Hand restatement of Lemma 8 (CSG1, `CSG1_lemma_8_the_blocks.md`): the block matrix, the chain
matrix and every number are written out again here from the document, without the project's
definitions, and the four statements (B1), (B2), (S1), (S2) plus (L), (P), (N) are checked against
the certified theorems. Then `#print axioms`.
-/

open Finset

namespace CheckCSG1

open ColouredSand.Blocks

/-- `v t = v_p(q) + v_p(c + k + t)`, by hand. -/
def hv (p q c k t : ℕ) : ℕ := padicValNat p q + padicValNat p (c + k + t)

/-- `N t = q (c + k + t)` in `ℤ_[p]`, by hand. -/
noncomputable def hN (p : ℕ) [Fact p.Prime] (q c k t : ℕ) : ℤ_[p] := ((q * (c + k + t) : ℕ) : ℤ_[p])

/-- The glue entry `u = C(μ+r, μ)(a+1)p / p^ν`, `μ = p − 1 − r + pa` written as `λ − 2r`. -/
def hu (p r a : ℕ) : ℕ :=
  (Nat.choose (p - 1 + r + p * a - 2 * r + r) (p - 1 + r + p * a - 2 * r) * (a + 1) * p) /
    p ^ (if r ≤ p - 1 ∧ a = p - 1 then 2 else 1)

/-- The block matrix of §1, entry by entry, by hand. -/
noncomputable def hM (p : ℕ) [Fact p.Prime] (q c k r a : ℕ) :
    Matrix (Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1))
      (Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1)) ℤ_[p] :=
  Matrix.of fun x y => match x, y with
    | .inl i', .inl i =>
        if i' = i then hN p q c k i else if (i' : ℕ) = i + 1 then ((i : ℕ) + 1 : ℤ_[p]) else 0
    | .inr j', .inr j =>
        if j' = j then hN p q c k (j + r) else if (j' : ℕ) = j + 1 then ((j : ℕ) + 1 : ℤ_[p])
        else 0
    | .inl i', .inr j =>
        if (j : ℕ) = p - 1 + r + p * a - 2 * r ∧ (i' : ℕ) = p - 1 + r + p * a - 2 * r + r + 1
        then (hu p r a : ℤ_[p]) else 0
    | .inr _, .inl _ => 0

/-- `A`, `A'`, `α`, `τ`, `E₁₁`, `E₁₂`, `E₂₂`, `x`, `y`, by hand. -/
def hA (p q c k r a : ℕ) : ℕ := ∑ t ∈ range (p - 1 + r + p * a + 1), hv p q c k t
def hA' (p q c k r a : ℕ) : ℕ := ∑ t ∈ Icc r (r + (p - 1 + r + p * a - 2 * r)), hv p q c k t
def hal (p q c k r a : ℕ) : ℕ := ∑ t ∈ Icc ((a + 1) * p) (p - 1 + r + p * a), hv p q c k t
def htau (p a : ℕ) : ℕ := if a = p - 1 then 2 else 1
def hE11 (p q c k r a : ℕ) : ℕ := hA p q c k r a - hal p q c k r a - a
def hE12 (p q c k r a : ℕ) : ℕ := hA' p q c k r a - a + htau p a
def hE22 (p q c k r a : ℕ) : ℕ := hA' p q c k r a - a + hal p q c k r a
def hx (p q c k r a : ℕ) : ℕ := min (hE11 p q c k r a) (min (hE12 p q c k r a) (hE22 p q c k r a))
def hy (p q c k r a : ℕ) : ℕ := hE11 p q c k r a + hE22 p q c k r a - hx p q c k r a

/-- The chain matrix of §2, by hand. -/
noncomputable def hCh (p : ℕ) [Fact p.Prime] (q c k l : ℕ) :
    Matrix (Fin (l + 1)) (Fin (l + 1)) ℤ_[p] :=
  Matrix.of fun i' i =>
    if i' = i then hN p q c k i else if (i' : ℕ) = i + 1 then ((i : ℕ) + 1 : ℤ_[p]) else 0

def hChA (p q c k l : ℕ) : ℕ := ∑ t ∈ range (l + 1), hv p q c k t

/-- (B1) by hand. -/
theorem hB1 (p : ℕ) [Fact p.Prime] (q c k r a : ℕ) (hq : 1 ≤ padicValNat p q)
    (hck : 1 ≤ c + k) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1) (hra : r = p → a = p - 1) :
    Nonempty (((Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hM p q c k r a))) ≃+
      (Fin (2 * a) → ZMod p) × ZMod (p ^ hx p q c k r a) × ZMod (p ^ hy p q c k r a)) :=
  B1 hq hck hr1 hrp ha hra

/-- (B2) by hand. -/
theorem hB2 (p : ℕ) [Fact p.Prime] (q r a : ℕ) (hq : 1 ≤ padicValNat p q)
    (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1) (hra : r = p → a = p - 1) :
    Nonempty (((Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hM p q 0 0 r a))) ≃+
      ℤ_[p] × (Fin (2 * a) → ZMod p) × ZMod (p ^ min (hE12 p q 0 0 r a) (hE22 p q 0 0 r a))) :=
  B2 (c := 0) (k := 0) hq rfl rfl hr1 hrp ha hra

/-- (S1) by hand, both cases. -/
theorem hS1 (p : ℕ) [Fact p.Prime] (q c k l : ℕ) (hq : 1 ≤ padicValNat p q) (hl : l ≤ p - 1) :
    (1 ≤ c + k → Nonempty (((Fin (l + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hCh p q c k l))) ≃+ ZMod (p ^ hChA p q c k l))) ∧
    (c = 0 → k = 0 → Nonempty (((Fin (l + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hCh p q c k l))) ≃+ ℤ_[p])) :=
  S1 hq hl

/-- (S2) by hand, both cases. -/
theorem hS2 (p : ℕ) [Fact p.Prime] (q c k l a : ℕ) (hq : 1 ≤ padicValNat p q)
    (hl : l + 1 = (a + 1) * p) (ha : a ≤ p - 1) :
    (1 ≤ c + k → a + 1 ≤ hChA p q c k l ∧ Nonempty (((Fin (l + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hCh p q c k l))) ≃+
          (Fin a → ZMod p) × ZMod (p ^ (hChA p q c k l - a)))) ∧
    (c = 0 → k = 0 → Nonempty (((Fin (l + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (hCh p q c k l))) ≃+ ℤ_[p] × (Fin a → ZMod p))) :=
  S2 hq hl ha

/-- (L) by hand. -/
theorem hL (p : ℕ) [Fact p.Prime] (e₁ e₂ e₃ : ℕ) (w : ℤ_[p]) (hw : IsUnit w) :
    Nonempty (((Fin 2 → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin
        !![(p : ℤ_[p]) ^ e₁, w * (p : ℤ_[p]) ^ e₂; 0, (p : ℤ_[p]) ^ e₃])) ≃+
      ZMod (p ^ min e₁ (min e₂ e₃)) × ZMod (p ^ (e₁ + e₃ - min e₁ (min e₂ e₃)))) :=
  lemma_L e₁ e₂ e₃ w hw

/-- (P) by hand. -/
theorem hP (p : ℕ) [Fact p.Prime] (q c k r a : ℕ) (hq : 1 ≤ padicValNat p q) (hr1 : 1 ≤ r)
    (hrp : r ≤ p) (hra : r = p → a = p - 1) :
    a + 1 ≤ hA' p q c k r a ∧ a + 1 ≤ hA p q c k r a - hal p q c k r a :=
  positivity_P (p := p) hq hr1 hrp hra

/-- (N) by hand (the last two clauses: the valuation of the glue entry). -/
theorem hN2 (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) :
    (r ≤ p - 1 → padicValNat p (hu p r a) = 0) ∧ (r = p → padicValNat p (hu p r a) = 1) :=
  ⟨(glue_exponent_N (p := p) hr1 hrp ha hra).2.2.2.1, (glue_exponent_N (p := p) hr1 hrp ha hra).2.2.2.2⟩

end CheckCSG1

#print axioms CheckCSG1.hB1
#print axioms CheckCSG1.hB2
#print axioms CheckCSG1.hS1
#print axioms CheckCSG1.hS2
#print axioms CheckCSG1.hL
#print axioms CheckCSG1.hP
#print axioms CheckCSG1.hN2
#print axioms ColouredSand.Blocks.B1
#print axioms ColouredSand.Blocks.B2
#print axioms ColouredSand.Blocks.S1
#print axioms ColouredSand.Blocks.S2
#print axioms ColouredSand.Blocks.S1_pos
#print axioms ColouredSand.Blocks.S1_zero
#print axioms ColouredSand.Blocks.S2_pos
#print axioms ColouredSand.Blocks.S2_zero
#print axioms ColouredSand.Blocks.lemma_L
#print axioms ColouredSand.Blocks.twoByTwo_nonempty
#print axioms ColouredSand.Blocks.positivity_P
#print axioms ColouredSand.Blocks.glue_exponent_N

end FinalCheck.CSG1

-- ======== piece CSG2 (from CONJETURA_HAMMING_2026-10-13/lean/proyecto_cs/checks/CheckCSG2.lean) ========
namespace FinalCheck.CSG2

/-!
# CheckCSG2 (Grepy Sand, 13 Oct 2026)

Hand restatement of Lemma 7 (CSG2, `CSG2_lemma_7_the_glue.md`): the space, the divided powers,
the weight projections, the glued lattice and the operator `q(c+H)+U` are written out again here
from the document (with `λ = p − 1 + r + p a`, `μ = λ − 2r`, `ν` and `x₀ = p^{−ν}` written
explicitly, no project definition), and (G1), (G2), (G3), (G4), (G5), (G6) are checked against the
certified theorems. Then `#print axioms`.
-/

open Finset
open scoped Pointwise

namespace CheckCSG2

open ColouredSand.Blocks ColouredSand.Glue

/-- `F t` by hand: `F t ℓ_i = C(i+t, t) ℓ_{i+t}`, `F t s_j = C(j+t, t) s_{j+t}`. -/
noncomputable def hF (p : ℕ) [Fact p.Prime] (Λ Μ t : ℕ) :
    (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) →ₗ[ℚ_[p]] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) :=
  Matrix.mulVecLin (Matrix.of fun y z => match y, z with
    | .inl i', .inl i => if (i' : ℕ) = i + t then (((i : ℕ) + t).choose t : ℚ_[p]) else 0
    | .inr j', .inr j => if (j' : ℕ) = j + t then (((j : ℕ) + t).choose t : ℚ_[p]) else 0
    | _, _ => 0)

/-- `E t` by hand: `E t ℓ_i = C(λ−i+t, t) ℓ_{i−t}`, `E t s_j = C(μ−j+t, t) s_{j−t}`. -/
noncomputable def hE (p : ℕ) [Fact p.Prime] (Λ Μ t : ℕ) :
    (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) →ₗ[ℚ_[p]] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) :=
  Matrix.mulVecLin (Matrix.of fun y z => match y, z with
    | .inl i', .inl i => if (i' : ℕ) + t = i then ((Λ - i + t).choose t : ℚ_[p]) else 0
    | .inr j', .inr j => if (j' : ℕ) + t = j then ((Μ - j + t).choose t : ℚ_[p]) else 0
    | _, _ => 0)

/-- Weight of a basis vector, by hand. -/
def hwt (Λ Μ : ℕ) : Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℤ
  | .inl i => (Λ : ℤ) - 2 * (i : ℤ)
  | .inr j => (Μ : ℤ) - 2 * (j : ℤ)

/-- The weight projection `P w`, by hand. -/
noncomputable def hP (p : ℕ) [Fact p.Prime] (Λ Μ : ℕ) (w : ℤ) :
    (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) →ₗ[ℚ_[p]] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) :=
  Matrix.mulVecLin (Matrix.of fun y z => if y = z ∧ hwt Λ Μ z = w then 1 else 0)

/-- `ℓ_i` and `s_j`, by hand. -/
noncomputable def hl (p : ℕ) [Fact p.Prime] (Λ Μ i : ℕ) : Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p] :=
  if h : i ≤ Λ then Pi.single (Sum.inl ⟨i, Nat.lt_succ_of_le h⟩) 1 else 0
noncomputable def hs (p : ℕ) [Fact p.Prime] (Λ Μ j : ℕ) : Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p] :=
  if h : j ≤ Μ then Pi.single (Sum.inr ⟨j, Nat.lt_succ_of_le h⟩) 1 else 0

/-- `s̃ x j = s_j + x C(j+r, j) ℓ_{j+r}`, by hand. -/
noncomputable def hst (p : ℕ) [Fact p.Prime] (Λ Μ r : ℕ) (x : ℚ_[p]) (j : ℕ) :
    Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p] :=
  if j ≤ Μ then hs p Λ Μ j + (x * ((j + r).choose j : ℚ_[p])) • hl p Λ Μ (j + r) else 0

/-- The glued lattice, by hand. -/
noncomputable def hLx (p : ℕ) [Fact p.Prime] (Λ Μ r : ℕ) (x : ℚ_[p]) :
    Submodule ℤ_[p] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) :=
  Submodule.span ℤ_[p] (Set.range (fun i : Fin (Λ + 1) => hl p Λ Μ i) ∪
    Set.range (fun j : Fin (Μ + 1) => hst p Λ Μ r x j))

/-- Stability, by hand. -/
def hStable (p : ℕ) [Fact p.Prime] (Λ Μ : ℕ)
    (L : Submodule ℤ_[p] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p])) : Prop :=
  (∀ t : ℕ, 1 ≤ t → ∀ v ∈ L, hF p Λ Μ t v ∈ L ∧ hE p Λ Μ t v ∈ L) ∧
    ∀ w : ℤ, ∀ v ∈ L, hP p Λ Μ w v ∈ L

/-- `ν`, by hand. -/
def hnu (p r a : ℕ) : ℕ := if r ≤ p - 1 ∧ a = p - 1 then 2 else 1

/-- (G1) by hand, with `λ = p − 1 + r + p a`, `μ = λ − 2r`. -/
theorem hG1 (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (x : ℚ_[p]) :
    hStable p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r)
        (hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x) ↔
      ‖x‖ ≤ (p : ℝ) ^ hnu p r a :=
  G1_stability_threshold hr1 hrp ha hra x

/-- (G2) by hand. -/
theorem hG2 (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1)
    (L : Submodule ℤ_[p] (Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℚ_[p]))
    (hS : hStable p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) L)
    (hi : ∀ v : Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℚ_[p],
      (∀ j, v (.inr j) = 0) →
      (v ∈ L ↔ v ∈ Submodule.span ℤ_[p] (Set.range (fun i : Fin (p - 1 + r + p * a + 1) =>
        hl p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) i))))
    (hii1 : ∀ v ∈ L, ∀ j, ‖v (.inr j)‖ ≤ 1)
    (hii2 : ∀ j : Fin (p - 1 + r + p * a - 2 * r + 1), ∃ v ∈ L,
      ∀ j', v (.inr j') = hs p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) j (.inr j')) :
    ∃ x : ℚ_[p], L = hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x ∧
      ‖x‖ ≤ (p : ℝ) ^ hnu p r a :=
  G2_glue_forced hr1 hrp ha hra L hS hi hii1 hii2

/-- (G3)(b) by hand. -/
theorem hG3b (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (x : ℚ_[p]) (hx : ‖x‖ = (p : ℝ) ^ hnu p r a)
    (w : Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℚ_[p])
    (hwL : w ∈ hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x)
    (hwP : hP p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r)
      ((p - 1 + r + p * a - 2 * r : ℕ) : ℤ) w = w)
    (hw0 : w (.inr ⟨0, Nat.succ_pos _⟩) = 1) :
    ∃ t, 1 ≤ t ∧ t ≤ r ∧ hE p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) t w ∉
      (p : ℤ_[p]) • hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x :=
  G3b_nonsplit hr1 hrp ha hra x hx w hwL hwP hw0

/-- (G3)(a) by hand. -/
theorem hG3a (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (x : ℚ_[p]) (hx : ‖x‖ < (p : ℝ) ^ hnu p r a) (t j : ℕ)
    (hj : j ≤ p - 1 + r + p * a - 2 * r) :
    hE p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) t
        (hst p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x j) -
        (if t ≤ j then ((p - 1 + r + p * a - 2 * r - j + t).choose t : ℚ_[p]) •
          hst p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x (j - t) else 0) ∈
        (p : ℤ_[p]) • hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x ∧
      hF p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) t
          (hst p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x j) -
          ((j + t).choose t : ℚ_[p]) • hst p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x (j + t) ∈
        (p : ℤ_[p]) • hLx p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r x :=
  G3a_split hr1 hrp ha hra x hx t j hj

/-- (G4) by hand (any `Λ`, `Μ`, `r`). -/
theorem hG4 (p : ℕ) [Fact p.Prime] (Λ Μ r : ℕ) (u : ℤ_[p]ˣ) (x : ℚ_[p]) :
    ∃ φ : (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin (Λ + 1) ⊕ Fin (Μ + 1) → ℚ_[p]),
      (∀ t v, φ (hF p Λ Μ t v) = hF p Λ Μ t (φ v)) ∧
      (∀ t v, φ (hE p Λ Μ t v) = hE p Λ Μ t (φ v)) ∧
      (∀ (w : ℤ) v, φ (hP p Λ Μ w v) = hP p Λ Μ w (φ v)) ∧
      (∀ i, φ (hl p Λ Μ i) = hl p Λ Μ i) ∧
      (hLx p Λ Μ r x).map ((φ.restrictScalars ℤ_[p]).toLinearMap) =
        hLx p Λ Μ r (((u : ℤ_[p]) : ℚ_[p]) * x) :=
  G4_rescaling (p := p) (L := Λ) (M := Μ) r u x

/-- (G5)(a) by hand: the basis vectors with `x₀ = p^{−ν}` written explicitly. -/
theorem hG5a (p : ℕ) [Fact p.Prime] (r a : ℕ) :
    (∀ i : Fin (p - 1 + r + p * a + 1),
      (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) (.inl i) : V p (lam p r a) (mu p r a)) =
        hl p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) i) ∧
    (∀ j : Fin (p - 1 + r + p * a - 2 * r + 1),
      (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) (.inr j) : V p (lam p r a) (mu p r a)) =
        hst p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) r
          ((p : ℚ_[p]) ^ (-(hnu p r a : ℤ))) j) :=
  G5a_basis (p := p) r a

/-- The operator `q(c+H)+U` on the block, by hand: diagonal `N_i` on `ℓ_i`, `N_{j+r}` on `s_j`, plus `F 1`. -/
noncomputable def hO (p : ℕ) [Fact p.Prime] (q c k r a : ℕ) :
    (Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℚ_[p]) →ₗ[ℚ_[p]]
      (Fin (p - 1 + r + p * a + 1) ⊕ Fin (p - 1 + r + p * a - 2 * r + 1) → ℚ_[p]) :=
  Matrix.mulVecLin (Matrix.diagonal fun y => match y with
    | .inl i => ((((q * (c + k + (i : ℕ)) : ℕ) : ℤ_[p])) : ℚ_[p])
    | .inr j => ((((q * (c + k + ((j : ℕ) + r)) : ℕ) : ℤ_[p])) : ℚ_[p])) +
  hF p (p - 1 + r + p * a) (p - 1 + r + p * a - 2 * r) 1

/-- The operator `O = q(c+H) + F 1` by hand, for any `Λ`, `Μ`, `r`: diagonal `N_i` on `ℓ_i` and
`N_{j+r}` on `s_j` (`N_t = q(c+k+t)`), plus `F 1`; it is the project's `Oop`. -/
theorem hOop (p : ℕ) [Fact p.Prime] (Λ Μ q c k r : ℕ) :
    Oop p Λ Μ q c k r =
      Matrix.mulVecLin (Matrix.diagonal fun y : Fin (Λ + 1) ⊕ Fin (Μ + 1) => match y with
        | .inl i => ((((q * (c + k + (i : ℕ)) : ℕ) : ℤ_[p])) : ℚ_[p])
        | .inr j => ((((q * (c + k + ((j : ℕ) + r)) : ℕ) : ℤ_[p])) : ℚ_[p])) +
      Matrix.mulVecLin (Matrix.of fun y z => match y, z with
        | .inl i', .inl i => if (i' : ℕ) = i + 1 then (((i : ℕ) + 1).choose 1 : ℚ_[p]) else 0
        | .inr j', .inr j => if (j' : ℕ) = j + 1 then (((j : ℕ) + 1).choose 1 : ℚ_[p]) else 0
        | _, _ => 0) := by
  unfold Oop Hop Fop Hmat Fmat Nt
  congr 2

/-- (G5)(b): `Orestr` is the restriction of `Oop` to `Lx x₀` (by its definition, read), and its
matrix in the glue basis is `Mblk` (the matrix of CSG1, rewritten by hand in `CheckCSG1`). -/
theorem hG5b (p : ℕ) [Fact p.Prime] (r a : ℕ) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) (q c k : ℕ) :
    (∀ v : Lx p (lam p r a) (mu p r a) r (xzero p r a),
      ((Orestr hr1 hrp ha hra q c k v : Lx p (lam p r a) (mu p r a) r (xzero p r a)) :
        V p (lam p r a) (mu p r a)) = Oop p (lam p r a) (mu p r a) q c k r v) ∧
    LinearMap.toMatrix (glueBasis p (lam p r a) (mu p r a) r (xzero p r a))
        (glueBasis p (lam p r a) (mu p r a) r (xzero p r a)) (Orestr hr1 hrp ha hra q c k) =
      Mblk p q c k r a :=
  ⟨fun _ => rfl, G5b_matrix hr1 hrp ha hra q c k⟩

end CheckCSG2

#print axioms CheckCSG2.hG1
#print axioms CheckCSG2.hG2
#print axioms CheckCSG2.hG3a
#print axioms CheckCSG2.hG3b
#print axioms CheckCSG2.hG4
#print axioms CheckCSG2.hG5a
#print axioms CheckCSG2.hOop
#print axioms CheckCSG2.hG5b
#print axioms ColouredSand.Glue.G1_stability_threshold
#print axioms ColouredSand.Glue.G2_glue_forced
#print axioms ColouredSand.Glue.G3a_split
#print axioms ColouredSand.Glue.G3b_nonsplit
#print axioms ColouredSand.Glue.G4_rescaling
#print axioms ColouredSand.Glue.G5a_basis
#print axioms ColouredSand.Glue.G5b_maps
#print axioms ColouredSand.Glue.G5b_matrix
#print axioms ColouredSand.Glue.G6_B1
#print axioms ColouredSand.Glue.G6_B2

end FinalCheck.CSG2
