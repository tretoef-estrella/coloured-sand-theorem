import RequestProject.Strings.All

/-! CheckCS1 — Grepy Connor, 13 Oct 2026. The headline statements of piece CS1
(strings of the Boolean lattice and Theorem E of «The Coloured Sand Theorem»),
restated by hand and closed by the certified theorems; then their axioms. -/

open Finset ColouredSand.Strings

-- §0: the definitions, read on basis vectors (faithfulness).
#check @H_single
#check @U_single
#check @D_single

-- (S1) restated by hand.
example (m : ℕ) (R : Type) [CommRing R] :
    D m R ∘ₗ U m R - U m R ∘ₗ D m R = (m : R) • LinearMap.id - (2 : R) • H m R :=
  commutator_DU_UD

-- (S2) restated by hand.
example (m : ℕ) (R : Type) [CommRing R] {k : ℕ} {v : B m R} (hv : v ∈ level m R k)
    (hD : D m R v = 0) {i : ℕ} (hi : 1 ≤ i) :
    D m R ((U m R ^ i) v) = ((i : ℤ) * ((m : ℤ) - 2 * k - i + 1)) • (U m R ^ (i - 1)) v :=
  string_relation hv hD hi

-- (S3)(c) restated by hand.
example (m : ℕ) (R : Type) [CommRing R] (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R))
    {k : ℕ} (hk : k ≤ m / 2) : (Lam m R k).map (U m R ^ (m - 2 * k + 1)) = ⊥ :=
  strings_c hR hk

-- (S4) restated by hand.
example {R : Type} [CommRing R] (n : ℕ) (hn : 1 ≤ n) (M : Matrix (Fin n) (Fin n) R)
    (d : Fin n → R) (hdiag : ∀ i, M i i = d i)
    (hsub : ∀ i j : Fin n, (i : ℕ) = j + 1 → IsUnit (M i j))
    (hzero : ∀ i j : Fin n, i ≠ j → (i : ℕ) ≠ j + 1 → M i j = 0) :
    Nonempty (((Fin n → R) ⧸ LinearMap.range (Matrix.mulVecLin M)) ≃ₗ[R]
      (R ⧸ Ideal.span {∏ i, d i})) :=
  bidiagonal_coker n hn M d hdiag hsub hzero

-- (S5) Theorem E restated by hand, with the exponent written out.
example (p : ℕ) [Fact p.Prime] (q : ℤ) (hq : 1 ≤ padicValInt p q) (c m : ℕ) (hm : m < p) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range
        ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)},
            Fin (m.choose k - if (k : ℕ) = 0 then 0 else m.choose ((k : ℕ) - 1))) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^
            (∑ r ∈ Icc (t.1 : ℕ) (m - t.1), (padicValInt p q + padicValNat p (c + r)))}))) :=
  theorem_E p q hq c m hm

#print axioms commutator_DU_UD
#print axioms string_relation
#print axioms Lam_zero
#print axioms strings_a
#print axioms strings_b
#print axioms stringEquiv
#print axioms strings_c
#print axioms Lam_free_finrank
#print axioms Lam_free_finrank_of_isLocalRing
#print axioms bidiagonal_coker
#print axioms coker_opM_equiv
#print axioms theorem_E
