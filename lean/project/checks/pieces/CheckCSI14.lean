import RequestProject.OddCeiling.All

/-!
# CheckCSI14 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI14 (`CSI14_the_ceiling_at_p.md`): the definitions written out (oP, ranks,
Lr/Fr at p, ĉ, x_D, U, minorValsP, ddP); Part A (A1, A2, A3, Theorem O at p); Part B (B1);
Part C (C1); Part D (D0–D3); Part Q (Q1, Q2); Part T (T1). Then `#print axioms`.
-/

namespace CheckCSI14

open ColouredSand.OddTwist Finset Matrix

theorem hDefs (p k r : ℕ) (d : ℕ → ℕ) (I D a b : Finset ℕ) (R₁ R₂ : Finset ℕ → ℤ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℤ) :
    oP p d D = ∑ t ∈ D, d t * p ^ t ∧
    rankP p d I D = #(I.powerset.filter (fun D' => oP p d D' < oP p d D)) ∧
    LrP p d I r = I.powerset.filter (fun D => 2 ^ #I - r ≤ rankP p d I D) ∧
    FrP p d I r = I.powerset.filter (fun D => rankP p d I D < r) ∧
    cHatP k I R₁ R₂ a b = R₁ a - R₂ b + Rulers.gamma k I (a \ b) ∧
    xP I R₁ R₂ D = R₁ D - R₂ (I \ D) ∧
    UP I R₁ R₂ r = ∑ D ∈ GoldenMatching.Lr I r, (R₁ D - R₂ (I \ D)) ∧
    minorValsP p M r = {v | ∃ A B : Finset (Fin n), A.card = r ∧ B.card = r ∧
      Divisors.minor M r A B ≠ 0 ∧ padicValInt p (Divisors.minor M r A B) = v} ∧
    ddP p M r = sInf (minorValsP p M r) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hA (k : ℕ) {p : ℕ} (hp : 2 ≤ p) {d : ℕ → ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ d t ∧ d t ≤ p - 1) {D D' : Finset ℕ} (hD : D ⊆ I) (hD' : D' ⊆ I)
    (r : ℕ) (hr : r ≤ 2 ^ #I) :
    (oP p d D < oP p d D' ↔ Rulers.oE D < Rulers.oE D') ∧
    rankP p d I D = GoldenMatching.rank I D ∧
    LrP p d I r = GoldenMatching.Lr I r ∧ FrP p d I r = GoldenMatching.Fr I r ∧
    oP p d (I \ D) + oP p d D = oP p d I ∧
    (∃ β : LrP p d I r ≃ FrP p d I r,
        ∀ D : LrP p d I r, GoldenMatching.IsGoldenArrow k I D (β D)) :=
  ⟨A1_same_order hp hd hD hD', A2_rank hp hd hD, A2_Lr hp hd r, A2_Fr hp hd r,
    A3_complement p d hD, (theorem_O_P k hp hI hd r hr).1⟩

theorem hB (k : ℕ) (I : Finset ℕ) (R₁ R₂ : Finset ℕ → ℤ) (r : ℕ)
    (β : GoldenMatching.Lr I r ≃ GoldenMatching.Fr I r) :
    ∑ D : GoldenMatching.Lr I r, cHatP k I R₁ R₂ D (β D) =
      UP I R₁ R₂ r + ∑ D : GoldenMatching.Lr I r, (Rulers.gamma k I ((D : Finset ℕ) \ β D) : ℤ) :=
  B1_cost k I R₁ R₂ r β

theorem hC (k : ℕ) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k)
    (R₁ R₂ : Finset ℕ → ℤ) {p : ℕ} (hp : p.Prime) (C : ℤ) (M : Finset ℕ → Finset ℕ → ℤ)
    (hS : ∀ a b, a ⊆ I → b ⊆ I → ¬ b ⊆ a → M a b = 0)
    (hH : ∀ a b, b ⊆ a → a ⊆ I → ∃ n : ℕ, (n : ℤ) = C + cHatP k I R₁ R₂ a b ∧
      (p : ℤ) ^ n ∣ M a b ∧ ¬ (p : ℤ) ^ (n + 1) ∣ M a b)
    (r : ℕ) (hr : r ≤ 2 ^ #I) (e : Fin r ≃ GoldenMatching.Lr I r)
    (f : Fin r ≃ GoldenMatching.Fr I r) :
    ∃ n : ℕ, (n : ℤ) = r * C + UP I R₁ R₂ r ∧
      (p : ℤ) ^ n ∣ (Matrix.of fun i j => M (e i) (f j)).det ∧
      ¬ (p : ℤ) ^ (n + 1) ∣ (Matrix.of fun i j => M (e i) (f j)).det ∧
      (Matrix.of fun i j => M (e i) (f j)).det ≠ 0 :=
  C1_natural_minor k hI R₁ R₂ hp C M hS hH r hr e f

theorem hD {p : ℕ} (hp : p.Prime) {n : ℕ} (M P Q : Matrix (Fin n) (Fin n) ℤ)
    (hP : ¬ (p : ℤ) ∣ det P) (hQ : ¬ (p : ℤ) ∣ det Q) (r : ℕ)
    (e : Fin n → ℕ) (he : Monotone e) (u : Fin n → ℤ) (hu : ∀ i, ¬ (p : ℤ) ∣ u i) (hr : r ≤ n)
    (hD : P * M * Q = diagonal fun i => u i * (p : ℤ) ^ e i) (s : Fin n) (hr2 : r + 2 ≤ n) :
    ddP 2 M r = Divisors.dd M r ∧
    ddP p (P * M * Q) r = ddP p M r ∧
    ddP p (diagonal fun i => u i * (p : ℤ) ^ e i) r =
      ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i ∧
    ddP p M r = ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i ∧
    (e s : ℤ) = (ddP p M (s + 1) : ℤ) - ddP p M s ∧
    (ddP p M (r + 1) : ℤ) - ddP p M r ≤ (ddP p M (r + 2) : ℤ) - ddP p M (r + 1) :=
  ⟨D0_two M r, D1_invariance hp M P Q hP hQ r, D2_diagonal hp e he u hu hr,
    D3_sum hp M P Q hP hQ e he u hu hD hr, D3_increment hp M P Q hP hQ e he u hu hD s,
    D3_convex hp M P Q hP hQ e he u hu hD r hr2⟩

theorem hQ1 {p : ℕ} (hp : p.Prime) (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧
      ∃ ρ ≤ n, ∃ e : ℕ → ℕ, (∀ i j, i ≤ j → j < ρ → e i ≤ e j) ∧
        ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧
          P * A * Q = diagonal (fun j : Fin n =>
            if (j : ℕ) < ρ then u j * (p : ℤ) ^ e j else 0) :=
  Q1_smith hp n A

theorem hQ2 {p n ρ : ℕ} {e : ℕ → ℕ} {u : ℕ → ℤ} (hp : p.Prime)
    (A P Q : Matrix (Fin n) (Fin n) ℤ) (hP : ¬ (p : ℤ) ∣ P.det)
    (hQ : ¬ (p : ℤ) ∣ Q.det) (hρ : ρ ≤ n) (he : ∀ i j, i ≤ j → j < ρ → e i ≤ e j)
    (hu : ∀ j, ¬ (p : ℤ) ∣ u j)
    (hD : P * A * Q = diagonal (fun j : Fin n =>
      if (j : ℕ) < ρ then u j * (p : ℤ) ^ e j else 0)) :
    (∀ r ≤ ρ, ddP p A r = ∑ j ∈ range r, e j) ∧
      (∀ r, ρ < r → ∀ B C : Finset (Fin n), B.card = r → C.card = r →
        Divisors.minor A r B C = 0) ∧
      (A.det ≠ 0 ↔ ρ = n) :=
  Q2_smith hp A P Q hP hQ hρ he hu hD

theorem hT {p : ℕ} (hp : p.Prime) {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : A.det ≠ 0) (x : ℕ → ℤ) (C : ℤ)
    (hF : ∀ r ≤ N, ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N x j ≤ (ddP p A r : ℤ) - r * C)
    (hU : ∀ r ≤ N, (ddP p A r : ℤ) - r * C ≤ ∑ j ∈ Ico (N - r) N, x j) :
    (∀ r ≤ N, (ddP p A r : ℤ) = r * C + ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N x j) ∧
      ∀ (P Q : Matrix (Fin N) (Fin N) ℤ) (ρ : ℕ) (e : ℕ → ℕ) (u : ℕ → ℤ),
        ¬ (p : ℤ) ∣ P.det → ¬ (p : ℤ) ∣ Q.det → ρ ≤ N →
        (∀ i j, i ≤ j → j < ρ → e i ≤ e j) → (∀ j, ¬ (p : ℤ) ∣ u j) →
        P * A * Q = diagonal (fun j : Fin N =>
          if (j : ℕ) < ρ then u j * (p : ℤ) ^ e j else 0) →
        ρ = N ∧ ∀ j < N, (e j : ℤ) = C + AntitonicFit.ifit N x (N - 1 - j) :=
  T1_assembly hp A hA x C hF hU

end CheckCSI14

#print axioms CheckCSI14.hDefs
#print axioms CheckCSI14.hA
#print axioms CheckCSI14.hB
#print axioms CheckCSI14.hC
#print axioms CheckCSI14.hD
#print axioms CheckCSI14.hQ1
#print axioms CheckCSI14.hQ2
#print axioms CheckCSI14.hT
