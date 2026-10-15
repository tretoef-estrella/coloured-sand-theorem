import RequestProject.OddSplitMove.All

/-!
# CheckCSI8 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI8 (`CSI8_the_split_move.md`): the floors of the split; the operator `FS`
on generators (shift; `A_{p−1} x ↦ −p A_0(Fx) + p C_{p−r} x`; `C_{p−1} x ↦ −p C_0(Fx)`);
`Π(a,b)`, `QA`, `QC`, `K` written out; the blocks of `QS`; Theorem (M1) for odd `p` and,
with the sign built in, for every `p`; (M2). Then `#print axioms`.
-/

namespace CheckCSI8

open ColouredSand.OddTwist DirectSum
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]
variable {S : Type*} [DecidableEq S] [Fintype S]

/-- Floors, products and the data, written out. -/
theorem hData (p r : ℕ) (fl : ι → ℕ) (Q : ℕ → Matrix S S A) (i : ι) (j : Fin p) (f : ℕ)
    (s s' : S) :
    flS p r fl (i, false, j) = p * fl i + j.val ∧
    flS p r fl (i, true, j) = p * fl i + r + j.val ∧
    prodQ Q (p * f + r) (p * f + p) = ((List.range (p * f + p - (p * f + r))).map
      (fun t => Q (p * f + r + t))).prod ∧
    QA p Q f = -((p : A) ^ (p - 2)) • prodQ Q (p * f) (p * f + p) ∧
    QC p r Q f = -((p : A) ^ (p - 2)) • prodQ Q (p * f + r) (p * f + r + p) ∧
    KS p r Q f = ((-1 : A) ^ (p - r + 1) * (p : A) ^ (p - r - 1)) •
      prodQ Q (p * f + r) (p * f + p) ∧
    QS p r Q f (s, false) (s', false) = QA p Q f s s' ∧
    QS p r Q f (s, true) (s', true) = QC p r Q f s s' ∧
    QS p r Q f (s, true) (s', false) = KS p r Q f s s' ∧
    QS p r Q f (s, false) (s', true) = 0 := by
  refine ⟨by simp [flS], by simp [flS], rfl, by simp [QA], by simp [QC], rfl, rfl, rfl, rfl, rfl⟩

/-- `FS` on generators. -/
theorem hFS (p r : ℕ) (hr : 0 < r) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (i : ι) (b : Bool)
    (j : Fin p) (x : N i) :
    (∀ h : j.val + 1 < p, FS p r hr F (DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, b, j) x) =
      DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, b, ⟨j.val + 1, h⟩) x) ∧
    (¬ j.val + 1 < p →
      FS p r hr F (DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, false, j) x) =
        -(p : A) • embS A N p false ⟨0, j.pos⟩ (F (DirectSum.lof A ι N i x)) +
          (p : A) • DirectSum.lof A (ι × Bool × Fin p) (NS p N)
            (i, true, ⟨p - r, Nat.sub_lt j.pos hr⟩) x) ∧
    (¬ j.val + 1 < p →
      FS p r hr F (DirectSum.lof A (ι × Bool × Fin p) (NS p N) (i, true, j) x) =
        -(p : A) • embS A N p true ⟨0, j.pos⟩ (F (DirectSum.lof A ι N i x))) :=
  ⟨fun h => FS_lof_lt p r hr F i b j h x, fun h => FS_lof_lastA p r hr F i j h x,
    fun h => FS_lof_lastC p r hr F i j h x⟩

/-- (M1), odd `p`. -/
theorem hM1 (p r : ℕ) (hp : Odd p) (hr : 0 < r) (hrp : r < p) (fl : ι → ℕ)
    (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NS p N) S ⧸
        LinearMap.range (c • Gp p (flS p r fl) (FS p r hr F) Q)) ≃ₗ[A]
      ((Fin (2 * (p - 1)) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N (S × Bool) ⧸ LinearMap.range ((c * p) • Gp p fl F (QS p r Q))))) :=
  theorem_M1 p r hp hr hrp fl F Q c

/-- (M1), every `p`, with `(−1)^p` on the diagonal blocks. -/
theorem hM1sign (p r : ℕ) (hr : 0 < r) (hrp : r < p) (fl : ι → ℕ)
    (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NS p N) S ⧸
        LinearMap.range (c • Gp p (flS p r fl) (FS p r hr F) Q)) ≃ₗ[A]
      ((Fin (2 * (p - 1)) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N (S × Bool) ⧸
          LinearMap.range ((c * p) • Gp p fl F (QSsign p r Q))))) :=
  theorem_M1_sign p r hr hrp fl F Q c

/-- (M2), `c = p^h`. -/
theorem hM2 (p r : ℕ) (hp : Odd p) (hr : 0 < r) (hrp : r < p) (fl : ι → ℕ)
    (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) (h : ℕ) :
    Nonempty ((Payment.Sys (NS p N) S ⧸
        LinearMap.range ((p : A) ^ h • Gp p (flS p r fl) (FS p r hr F) Q)) ≃ₗ[A]
      ((Fin (2 * (p - 1)) → Payment.Sys N S ⧸ (p : A) ^ h • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N (S × Bool) ⧸
          LinearMap.range ((p : A) ^ (h + 1) • Gp p fl F (QS p r Q))))) :=
  corollary_M2 p r hp hr hrp fl F Q h

end CheckCSI8

#print axioms CheckCSI8.hData
#print axioms CheckCSI8.hFS
#print axioms CheckCSI8.hM1
#print axioms CheckCSI8.hM1sign
#print axioms CheckCSI8.hM2
#print axioms ColouredSand.OddTwist.coupledCokerEquiv
#print axioms ColouredSand.OddTwist.QSsign_of_odd
