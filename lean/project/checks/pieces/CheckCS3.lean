import RequestProject.TheoremB.All

/-! CheckCS3 — Grepy Altair, 13 Oct 2026. Theorem B of «The Coloured Sand Theorem» (the Sylow
p-subgroup of the sandpile group of H(d,q) for p > d, ballot numbers), restated by hand, plus the
definitions read on their face. -/

open scoped TensorProduct
open Finset ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB

-- the objects, on their face
#print ColouredSand.TheoremB.cokerL
#print ColouredSand.TheoremB.sandpile
#print ColouredSand.TheoremB.nCount
#print ColouredSand.TheoremB.ballot
#check @ColouredSand.Splitting.laplacian_apply

-- (B3) Theorem B restated by hand: the sandpile group written out as the torsion of the cokernel of
-- the Laplacian, Syl_p as Mathlib's primary component, n_v written as the explicit double sum.
example (d q p : ℕ) [Fact p.Prime] (hd : 1 ≤ d) (hpd : d < p) (hpq : p ∣ q) (hq : 2 ≤ q) :
    Nonempty (AddCommGroup.primaryComponent
        (Submodule.torsion ℤ (((Fin d → Fin q) → ℤ) ⧸ LinearMap.range (laplacian d q))) p ≃+
      ((s : Σ v : Fin d, Fin (∑ j ∈ range (d + 1), ∑ k ∈ range (d + 1),
          if j + 2 * k = d + 1 - ((v : ℕ) + 1) ∧ (j, k) ≠ (0, 0) then
            d.choose j * (q - 2) ^ j *
              (((v : ℕ) + 1 + 2 * k - 1).choose k -
                if k = 0 then 0 else ((v : ℕ) + 1 + 2 * k - 1).choose (k - 1))
          else 0)) → ZMod (p ^ (padicValNat p q * ((s.1 : ℕ) + 1))))) :=
  theorem_B d q p hd hpd hpq hq

-- (B2) restated by hand
example (v k : ℕ) (hv : 1 ≤ v) :
    ((v + 2 * k - 1).choose k : ℚ) - (if k = 0 then 0 else ((v + 2 * k - 1).choose (k - 1) : ℚ)) =
      (v : ℚ) / (v + 2 * k) * (v + 2 * k).choose k :=
  ballot_identity v k hv

-- (B1) restated by hand
example (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Finite G] :
    Nonempty (AddCommGroup.primaryComponent G p ≃+ ℤ_[p] ⊗[ℤ] G) :=
  sylow_tensor_padic p G

-- (B4), d = 2, with u = q − 2
example (q : ℕ) : nCount 2 q 1 = (q - 2) ^ 2 + 1 ∧ nCount 2 q 2 = 2 * (q - 2) := nCount_two q

-- §0: coker L ≅ ℤ × K, K finite
example (d q : ℕ) (hq : 1 ≤ q) :
    Nonempty (cokerL d q ≃ₗ[ℤ] ℤ × sandpile d q) ∧ Finite (sandpile d q) :=
  cokerL_equiv_int_prod_sandpile d q hq

#print axioms theorem_B
#print axioms ballot_identity
#print axioms ballot_cast
#print axioms sylow_tensor_padic
#print axioms coker_tensor_padic
#print axioms coker_tensor_padic_matrix
#print axioms torsion_tensor_equiv_syl
#print axioms nCount_two
#print axioms nCount_three
#print axioms nCount_four
#print axioms theorem_B_two
#print axioms theorem_B_three
#print axioms theorem_B_four
#print axioms hammingGraph_connected
#print axioms cokerL_equiv_int_prod_sandpile
