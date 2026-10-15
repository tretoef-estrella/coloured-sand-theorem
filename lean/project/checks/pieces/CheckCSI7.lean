import RequestProject.OddPayment.All

/-!
# CheckCSI7 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI7 (`CSI7_the_twist_move.md`): the system `Gp` on a generator; the
odd twist `flT`, `NT`, `FT` on generators; `QT` written out as `−p^(p−2) • Π Q(pf + j)`;
Theorem A_p (odd `p`, and every `p ≥ 1` with the sign built in); the `c = 1` and `c = p^h`
corollaries; evenness. Then `#print axioms`.
-/

namespace CheckCSI7

open ColouredSand.OddTwist DirectSum
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]
variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The system on a generator, and the twist written out. -/
theorem hSetting (p : ℕ) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A)
    (s' : S) (i : ι) (x : N i) (q : ι × Fin p) (f : ℕ) :
    Gp p fl F Q (oslot A N S s' i x) = oslotE A N S s' (F (DirectSum.lof A ι N i x)) +
      ∑ s, ((p : A) * Q (fl i) s s') • oslot A N S s i x ∧
    flT p fl q = p * fl q.1 + q.2.val ∧
    QT p Q f = -((p : A) ^ (p - 2)) • ((List.range p).map (fun j => Q (p * f + j))).prod :=
  ⟨Gp_oslot p fl F Q s' i x, rfl, by simp [QT]⟩

/-- `FT` on generators: shift up one layer; from the top layer, `−p • b_0 (F x)`. -/
theorem hFT (p : ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (j : Fin p) (x : N i) :
    (∀ h : j.val + 1 < p, FT p F (DirectSum.lof A (ι × Fin p) (NT p N) (i, j) x) =
      DirectSum.lof A (ι × Fin p) (NT p N) (i, ⟨j.val + 1, h⟩) x) ∧
    (¬ j.val + 1 < p → FT p F (DirectSum.lof A (ι × Fin p) (NT p N) (i, j) x) =
      -(p : A) • embT A N p ⟨0, j.pos⟩ (F (DirectSum.lof A ι N i x))) :=
  ⟨fun h => FT_lof_lt p F i j h x, fun h => FT_lof_last p F i j h x⟩

/-- (A1) Theorem A_p for odd `p`. -/
theorem hA1 (p : ℕ) (hp : Odd p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NT p N) S ⧸ LinearMap.range (c • Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      ((Fin (p - 1) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N S ⧸ LinearMap.range ((c * p) • Gp p fl F (QT p Q))))) :=
  theorem_Ap p hp fl F Q c

/-- (A1) for every `p ≥ 1` with the sign `(−1)^p` built into the data. -/
theorem hA1sign (p : ℕ) (hp : 0 < p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NT p N) S ⧸ LinearMap.range (c • Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      ((Fin (p - 1) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N S ⧸ LinearMap.range ((c * p) • Gp p fl F
          (fun f => ((-1 : A) ^ p * (p : A) ^ (p - 2)) •
            ((List.range p).map (fun j => Q (p * f + j))).prod))))) :=
  theorem_Ap_sign p hp fl F Q c

/-- (A2) powers, and the `c = 1` form. -/
theorem hA2 (p : ℕ) (hp : Odd p) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i))
    (Q : ℕ → Matrix S S A) (h : ℕ) :
    Nonempty ((Payment.Sys (NT p N) S ⧸
        LinearMap.range ((p : A) ^ h • Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      ((Fin (p - 1) → Payment.Sys N S ⧸ (p : A) ^ h • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N S ⧸ LinearMap.range ((p : A) ^ (h + 1) • Gp p fl F (QT p Q))))) ∧
    Nonempty ((Payment.Sys (NT p N) S ⧸ LinearMap.range (Gp p (flT p fl) (FT p F) Q)) ≃ₗ[A]
      (Payment.Sys N S ⧸ LinearMap.range ((p : A) • Gp p fl F (QT p Q)))) :=
  ⟨corollary_Ap2 p hp fl F Q h, corollary_Ap_one p hp fl F Q⟩

/-- (A3) evenness. -/
theorem hA3 (p : ℕ) (Q : ℕ → Matrix S S A) (I : Ideal A)
    (hQ : ∀ φ s s', Q φ s s' ∈ I) (f : ℕ) (s s' : S) :
    QT p Q f s s' ∈ Ideal.span {(p : A)} ^ (p - 2) * I ^ p :=
  evenness_A3 p Q I hQ f s s'

end CheckCSI7

#print axioms CheckCSI7.hSetting
#print axioms CheckCSI7.hFT
#print axioms CheckCSI7.hA1
#print axioms CheckCSI7.hA1sign
#print axioms CheckCSI7.hA2
#print axioms CheckCSI7.hA3
#print axioms ColouredSand.OddTwist.chainCokerEquiv
#print axioms ColouredSand.OddTwist.oslot_eq_slotLof
