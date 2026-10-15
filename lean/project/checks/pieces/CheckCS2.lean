import RequestProject.Splitting.All

/-! CheckCS2 — Grepy Connor, 13 Oct 2026. Theorem A (Jacobson–Niedermaier–Reiner splitting) of
«The Coloured Sand Theorem», restated by hand, plus the definitions read on their face. -/

open Finset ColouredSand.Strings ColouredSand.Splitting

-- the objects, on their face
#print ColouredSand.Splitting.hammingGraph
#print ColouredSand.Splitting.laplacian
#check @laplacian_apply
#check @Mq_apply
#check @hammingGraph_degree
#check @completeGraph_lapMatrix

-- (A2) restated by hand: the cokernel of the Laplacian of H(d,q), written with Mathlib's lapMatrix,
-- against the product of the pieces q(c+H)+U.
example (d q : ℕ) (hq : 2 ≤ q) :
    Nonempty ((((Fin d → Fin q) → ℤ) ⧸
        LinearMap.range ((((hammingGraph d q).lapMatrix ℤ)).mulVecLin)) ≃ₗ[ℤ]
      ∀ σ : (Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))),
        (B (d - σ.1) ℤ ⧸ LinearMap.range
          ((q : ℤ) • (((σ.1 : ℕ) : ℤ) • LinearMap.id + H (d - σ.1) ℤ) + U (d - σ.1) ℤ))) :=
  theorem_A d q hq

-- adjacency is "differ in exactly one coordinate"
example (d q : ℕ) (x y : Fin d → Fin q) : (hammingGraph d q).Adj x y ↔ hammingDist x y = 1 := Iff.rfl

-- (A4) restated by hand
example (p : ℕ) [Fact p.Prime] (m : ℕ) (q c q' c' : ℤ)
    (hzero : ∀ s ≤ m, (q * (c + s) = 0 ↔ q' * (c' + s) = 0))
    (hval : ∀ s ≤ m, padicValInt p (q * (c + s)) = padicValInt p (q' * (c' + s))) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      (B m ℤ_[p] ⧸ LinearMap.range ((q' : ℤ_[p]) • ((c' : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p]))) :=
  opM_coker_depends_only_on_valuations m q c q' c' hzero hval

#print axioms theorem_A
#print axioms basisVec_isBasis
#print axioms K_ev_zero
#print axioms K_sigma
#print axioms K_fv
#print axioms completeGraph_lapMatrix
#print axioms hammingGraph_degree
#print axioms rescaling
#print axioms rescaling_coker
#print axioms rescaling_padic
#print axioms rescaling_padic_coker
#print axioms opM_coker_equiv_valuations
#print axioms opM_coker_depends_only_on_valuations
