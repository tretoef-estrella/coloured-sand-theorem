import RequestProject.OddTotal.All

/-!
# CheckCSI19 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI19 (`CSI19_theorem_TOTAL.md`): (U1) for `q ≠ 0`; (B1) with CSI10's `Yp`
unfolded; (T1) for every `m`; Theorem TOTAL (S1) and (S2) for every `d`, with the exponent list
written out from `S_p(λ)` and CSI18 (Y2), zero exponents removed; (S3) the agreement with CSG7's
`gTorList` for `m ≤ p² + p − 1`. Then `#print axioms`.
-/

namespace CheckCSI19

open ColouredSand ColouredSand.OddTwist ColouredSand.BlockOp ColouredSand.TheoremB ColouredSand.ThmG Finset

variable (p : ℕ) [Fact p.Prime]

/-- The exponent lists written out. -/
theorem hDefs (l i e q c m : ℕ) :
    oddTotalSpList p l =
      (List.ofFn fun t : Fin (kTop p l - 1) =>
          List.replicate ((p - 1) * digitL p l (kTop p l) * p ^ (kTop p l - (t + 1) - 1) *
            2 ^ (Iset p l).card) ((t : ℕ) + 1)).flatten ++
        List.replicate ((digitL p l (kTop p l) - 1) * 2 ^ (Iset p l).card) (kTop p l) ∧
    oddTotalCList p l i e =
      (if i = 0 then
        List.ofFn fun j : Fin (2 ^ #(Iset p l) - 1) => kTop p l +
          ((e : ℤ) * (oddSmithK p l : ℤ) + oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)).toNat
      else
        List.ofFn fun j : Fin (2 ^ #(Iset p l)) => kTop p l +
          (oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)).toNat) ∧
    oddTotalYList p l i e = oddTotalSpList p l ++ oddTotalCList p l i e ∧
    oddTotalTotList p q c m =
      ((LL p m).flatMap fun l => oddTotalYList p l (c + (m - l) / 2) (padicValNat p q)).filter
        (fun a => a ≠ 0) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- (U1). -/
theorem hU1 (M : DPLattice ℤ_[p]) (m c : ℕ) {q : ℕ} (hq : q ≠ 0) :
    Nonempty (((M.ι → ℤ_[p]) ⧸ LinearMap.range (opT p M m q c)) ≃ₗ[ℤ_[p]]
      ((M.ι → ℤ_[p]) ⧸ LinearMap.range (opT p M m (p ^ padicValNat p q) c))) :=
  oddTotal_U1 M m c hq

/-- (B1), with `Yp` unfolded. -/
theorem hB1 (hp2 : p ≠ 2) {l m : ℕ} (hle : l ≤ m) (hpar : l % 2 = m % 2) (e c : ℕ) :
    Nonempty (cokT p (danceL p l) m (p ^ e) c ≃ₗ[ℤ_[p]]
      (((danceL p l).ι → ℤ_[p]) ⧸ LinearMap.range (sigmaOp p l e (c + (m - l) / 2)))) :=
  oddTotal_B1 hp2 hle hpar e c

/-- (T1), every `m`. -/
theorem hT1 (hp2 : p ≠ 2) (m c : ℕ) {q : ℕ} (hq : q ≠ 0) :
    Nonempty (cokT p (Filt.tpow ℤ_[p] m) m q c ≃ₗ[ℤ_[p]]
      ((t : Fin (LL p m).length) →
        Yp p ((LL p m).get t) (c + (m - (LL p m).get t) / 2) (padicValNat p q))) :=
  oddTotal_T1 hp2 m c hq

/-- (S1) Theorem TOTAL, every `d`. -/
theorem hS1 (hp2 : p ≠ 2) {d q : ℕ} (hq2 : 2 ≤ q) :
    Nonempty ((ℤ_[p] × AddCommGroup.primaryComponent (sandpile d q) p) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (t : Fin (LL p (d - σ.1)).length) →
          Yp p ((LL p (d - σ.1)).get t) (σ.1 + (d - σ.1 - (LL p (d - σ.1)).get t) / 2)
            (padicValNat p q))) :=
  oddTotal_S1 hp2 hq2

/-- (S2) Theorem TOTAL with explicit exponents, every `d`. -/
theorem hS2 (hp2 : p ≠ 2) {d q : ℕ} (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat p q) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin (oddTotalTotList p q σ.1 (d - σ.1)).length) →
          ZMod (p ^ (oddTotalTotList p q σ.1 (d - σ.1)).get i))) :=
  oddTotal_S2 hp2 hq2 hq

/-- (S3) agreement with Theorem G. -/
theorem hS3 (hp2 : p ≠ 2) {q m : ℕ} (c : ℕ) (hq : 1 ≤ padicValNat p q)
    (hm : m ≤ p ^ 2 + p - 1) : (oddTotalTotList p q c m).Perm (gTorList p q c m) :=
  oddTotal_S3 hp2 c hq hm

end CheckCSI19

#print axioms CheckCSI19.hDefs
#print axioms CheckCSI19.hU1
#print axioms CheckCSI19.hB1
#print axioms CheckCSI19.hT1
#print axioms CheckCSI19.hS1
#print axioms CheckCSI19.hS2
#print axioms CheckCSI19.hS3
#print axioms ColouredSand.OddTwist.oddTotal_S2
