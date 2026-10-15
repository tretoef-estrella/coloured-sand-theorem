import RequestProject.OddSmith.All

/-!
# CheckCSI18 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI18 (`CSI18_theorem_4_4_smith_form_of_Mp.md`): the definitions written out
(K, the o-order matrix, C, the clocks x, ŷ, x^♯, ŷ^♯); (Z0) existence and uniqueness of the integer
matrix; (S1)–(S3) for `i ≥ 1`; (Z1)–(Z3) for `i = 0`; (Y1) and (Y2) in their three cases, with
CSI10's `Cmod`, `Yp`, `Sp`, `Zq` unfolded where they enter. Then `#print axioms`.
-/

namespace CheckCSI18

open ColouredSand.OddTwist Finset Matrix TheoremF AntitonicFit

variable (p : ℕ) [Fact p.Prime]

theorem hDefs (l i e : ℕ) :
    oddSmithK p l = digitL p l (kTop p l) * p ^ kTop p l ∧
    oddSmithMo p l i e = (Mp p l i e).submatrix (oddSmithSlot p l i e) (oddSmithSlot p l i e) ∧
    oddSmithC p l i e = (e : ℤ) * (oddSmithK p l : ℤ) + kappaP p (i - 1) (oddSmithK p l) ∧
    oddSmithX p l i e = (fun q =>
      rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1) (dancer (Iset p l) q) -
      rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1 + oddSmithK p l)
        (Iset p l \ dancer (Iset p l) q)) ∧
    oddSmithYhat p l i e = ifit (2 ^ #(Iset p l)) (oddSmithX p l i e) ∧
    oddSmithXSharp p l e = (fun q =>
      rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (dancer (Iset p l) (q + 1)) -
      rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (Iset p l \ dancer (Iset p l) (q + 1))) ∧
    oddSmithYhatSharp p l e = ifit (2 ^ #(Iset p l) - 1) (oddSmithXSharp p l e) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The slot of position `q` is labelled by `dancer_I q`. -/
theorem hSlot (l i e : ℕ) (q : Fin (2 ^ #(Iset p l))) :
    labL p l i e (kTop p l) (oddSmithSlot p l i e q) = dancer (Iset p l) q :=
  oddSmith_labL_slot p l i e q

/-- (Z0): the integer matrix exists and is unique. -/
theorem hZ0 (l i e : ℕ) :
    oddSmithMo p l i e = (oddSmithMZ p l i e).map (Int.cast) ∧
    ∀ MZ : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ,
      oddSmithMo p l i e = MZ.map (Int.cast) → MZ = oddSmithMZ p l i e :=
  ⟨oddSmith_Z0 p l i e, fun MZ h => oddSmith_Z0_unique p l i e MZ h⟩

/-- (S1). -/
theorem hS1 (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) (q q' : Fin (2 ^ #(Iset p l))) :
    (¬ dancer (Iset p l) q' ⊆ dancer (Iset p l) q → oddSmithMZ p l i e q q' = 0) ∧
    (dancer (Iset p l) q' ⊆ dancer (Iset p l) q → oddSmithMZ p l i e q q' ≠ 0 ∧
      ∃ n : ℕ, (n : ℤ) = ((e : ℤ) * (digitL p l (kTop p l) * p ^ kTop p l : ℕ) +
            kappaP p (i - 1) (digitL p l (kTop p l) * p ^ kTop p l)) +
          rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1) (dancer (Iset p l) q) -
          rulerP p e (kTop p l) (Iset p l) (digitL p l)
            (i - 1 + digitL p l (kTop p l) * p ^ kTop p l) (dancer (Iset p l) q') +
          Rulers.gamma (kTop p l) (Iset p l) (dancer (Iset p l) q \ dancer (Iset p l) q') ∧
        (p : ℤ) ^ n ∣ oddSmithMZ p l i e q q' ∧ ¬ (p : ℤ) ^ (n + 1) ∣ oddSmithMZ p l i e q q') :=
  oddSmith_S1 p hodd l i e he hi q q'

/-- (S2). -/
theorem hS2 (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    (∀ r ≤ 2 ^ #(Iset p l), (ddP p (oddSmithMZ p l i e) r : ℤ) =
      r * oddSmithC p l i e +
        ∑ j ∈ Ico (2 ^ #(Iset p l) - r) (2 ^ #(Iset p l)),
          ifit (2 ^ #(Iset p l)) (oddSmithX p l i e) j) ∧
    (oddSmithMZ p l i e).det ≠ 0 ∧
    (∀ j, j + 1 < 2 ^ #(Iset p l) →
      ifit (2 ^ #(Iset p l)) (oddSmithX p l i e) (j + 1) ≤
        ifit (2 ^ #(Iset p l)) (oddSmithX p l i e) j) :=
  oddSmith_S2 p hodd l i e he hi

/-- (S3). -/
theorem hS3 (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    ∃ P Q : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ,
      ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l),
            (E j : ℤ) = oddSmithC p l i e +
              ifit (2 ^ #(Iset p l)) (oddSmithX p l i e) (2 ^ #(Iset p l) - 1 - j)) ∧
          P * oddSmithMZ p l i e * Q =
            diagonal (fun j : Fin (2 ^ #(Iset p l)) => u j * (p : ℤ) ^ E j) :=
  oddSmith_S3 p hodd l i e he hi

/-- (Z1): the row of `∅` (position `0`) is zero, `det = 0`, and `MZ = 0` when `I = ∅`. -/
theorem hZ1 (l e : ℕ) (he : 1 ≤ e) :
    (∀ q', oddSmithMZ p l 0 e ⟨0, Nat.two_pow_pos _⟩ q' = 0) ∧ (oddSmithMZ p l 0 e).det = 0 ∧
      (Iset p l = ∅ → oddSmithMZ p l 0 e = 0) :=
  oddSmith_Z1 p l e he

/-- (Z2). -/
theorem hZ2 (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    (∀ r ≤ 2 ^ #(Iset p l) - 1, (ddP p (oddSmithMZ p l 0 e) r : ℤ) =
      r * ((e : ℤ) * (oddSmithK p l : ℤ)) +
        ∑ j ∈ Ico (2 ^ #(Iset p l) - 1 - r) (2 ^ #(Iset p l) - 1),
          ifit (2 ^ #(Iset p l) - 1) (oddSmithXSharp p l e) j) ∧
    (∀ j, j + 1 < 2 ^ #(Iset p l) - 1 →
      ifit (2 ^ #(Iset p l) - 1) (oddSmithXSharp p l e) (j + 1) ≤
        ifit (2 ^ #(Iset p l) - 1) (oddSmithXSharp p l e) j) :=
  oddSmith_Z2 p hodd l e he hne

/-- (Z3). -/
theorem hZ3 (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    ∃ P Q : Matrix (Fin (2 ^ #(Iset p l))) (Fin (2 ^ #(Iset p l))) ℤ,
      ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l) - 1,
            (E j : ℤ) = (e : ℤ) * (oddSmithK p l : ℤ) +
              ifit (2 ^ #(Iset p l) - 1) (oddSmithXSharp p l e) (2 ^ #(Iset p l) - 2 - j)) ∧
          P * oddSmithMZ p l 0 e * Q = diagonal (fun j : Fin (2 ^ #(Iset p l)) =>
            if (j : ℕ) < 2 ^ #(Iset p l) - 1 then u j * (p : ℤ) ^ E j else 0) :=
  oddSmith_Z3 p hodd l e he hne

/-- (Y1), `i ≥ 1`, with `Cmod` and `Zq` unfolded. -/
theorem hY1pos (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l),
        (E j : ℤ) = oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)) ∧
      Nonempty (((slots p l i e → ℤ_[p]) ⧸
          LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l i e).mulVecLin)) ≃ₗ[ℤ_[p]]
        ((j : Fin (2 ^ #(Iset p l))) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + E j)})) :=
  oddSmith_Y1_pos p hodd l i e he hi

/-- (Y1), `i = 0`, `I ≠ ∅`. -/
theorem hY1zero (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l) - 1,
        (E j : ℤ) = (e : ℤ) * (oddSmithK p l : ℤ) +
          oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)) ∧
      Nonempty (((slots p l 0 e → ℤ_[p]) ⧸
          LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l 0 e).mulVecLin)) ≃ₗ[ℤ_[p]]
        (ℤ_[p] × ((j : Fin (2 ^ #(Iset p l) - 1)) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + E j)}))) :=
  oddSmith_Y1_zero p hodd l e he hne

/-- (Y1), `i = 0`, `I = ∅`. -/
theorem hY1empty (l e : ℕ) (he : 1 ≤ e) (hI : Iset p l = ∅) :
    Nonempty (((slots p l 0 e → ℤ_[p]) ⧸
        LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l 0 e).mulVecLin)) ≃ₗ[ℤ_[p]] ℤ_[p]) :=
  oddSmith_Y1_zero_empty p l e he hI

/-- (Y2), `i ≥ 1`. -/
theorem hY2pos (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l),
        (E j : ℤ) = oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)) ∧
      Nonempty (Yp p l i e ≃ₗ[ℤ_[p]]
        (Sp p l × ((j : Fin (2 ^ #(Iset p l))) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + E j)}))) :=
  oddSmith_Y2_pos p hodd l i e he hi

/-- (Y2), `i = 0`, `I ≠ ∅`. -/
theorem hY2zero (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l) - 1,
        (E j : ℤ) = (e : ℤ) * (oddSmithK p l : ℤ) +
          oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)) ∧
      Nonempty (Yp p l 0 e ≃ₗ[ℤ_[p]]
        (Sp p l × (ℤ_[p] × ((j : Fin (2 ^ #(Iset p l) - 1)) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + E j)})))) :=
  oddSmith_Y2_zero p hodd l e he hne

/-- (Y2), `i = 0`, `I = ∅`. -/
theorem hY2empty (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hI : Iset p l = ∅) :
    Nonempty (Yp p l 0 e ≃ₗ[ℤ_[p]] (Sp p l × ℤ_[p])) :=
  oddSmith_Y2_zero_empty p hodd l e he hI

end CheckCSI18

#print axioms CheckCSI18.hDefs
#print axioms CheckCSI18.hSlot
#print axioms CheckCSI18.hZ0
#print axioms CheckCSI18.hS1
#print axioms CheckCSI18.hS2
#print axioms CheckCSI18.hS3
#print axioms CheckCSI18.hZ1
#print axioms CheckCSI18.hZ2
#print axioms CheckCSI18.hZ3
#print axioms CheckCSI18.hY1pos
#print axioms CheckCSI18.hY1zero
#print axioms CheckCSI18.hY1empty
#print axioms CheckCSI18.hY2pos
#print axioms CheckCSI18.hY2zero
#print axioms CheckCSI18.hY2empty
