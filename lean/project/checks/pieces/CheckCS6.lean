import RequestProject.Corollaries.All

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
