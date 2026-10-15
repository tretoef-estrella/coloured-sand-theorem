import RequestProject.OddTheoremI.All

/-!
# CheckCSI10 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI10 (`CSI10_theorem_Dp_and_theorem_I.md`): the digits of `λ + 1`, the
halved data and the matrix `Mp` written out, (M1), the slot count, Theorem D_p with `Y_p` written
out as the cokernel of `F + p^e (D_fl + i)` on `danceL p λ` and every `ℤ_[p] ⧸ p^a` written out,
and Theorem I (I1)–(I3) and its invariant form. Then `#print axioms`.
-/

namespace CheckCSI10

open ColouredSand.OddTwist DirectSum DPLattice
open scoped Pointwise

/-- The digits, the leading index and `I` written out. -/
theorem hDigits (p l t : ℕ) :
    digitL p l t = (Nat.digits p (l + 1)).getD t 0 ∧
    kTop p l = (Nat.digits p (l + 1)).length - 1 ∧
    Iset p l = (Finset.range (kTop p l)).filter (fun s => digitL p l s ≠ 0) :=
  ⟨rfl, rfl, rfl⟩

/-- The leading digit is nonzero. -/
theorem hTop (p l : ℕ) : digitL p l (kTop p l) ≠ 0 := digitL_top_ne_zero p l

variable (p : ℕ) [Fact p.Prime]

/-- The halved data and `Mp` written out: start at `(Unit, Q₀)`, one move per digit
(twist `QT` for a zero digit, split `QS` with slots `× Bool` otherwise), then
`Mp = p^{d_k} • Q_k 0 ⋯ Q_k (d_k − 1)`. -/
theorem hMp (l i e : ℕ) :
    Qdata p l i e (kTop p l) = iterD p (digitL p l) (kTop p l) ⟨Unit, Q0 ℤ_[p] p e i⟩ ∧
    (∀ (d : ℕ) (D : SData ℤ_[p]), stepD p d D =
      if d = 0 then ⟨D.S, QT p D.Q⟩ else ⟨D.S × Bool, QS p d D.Q⟩) ∧
    Mp p l i e = (p : ℤ_[p]) ^ digitL p l (kTop p l) •
      ((List.range (digitL p l (kTop p l))).map (Qdata p l i e (kTop p l)).Q).prod :=
  ⟨rfl, fun _ _ => rfl, by simp [Mp, prodQ]⟩

/-- Part M: `2^{|I|}` slots, and (M1). -/
theorem hM (l i e : ℕ) :
    Fintype.card (slots p l i e) = 2 ^ (Iset p l).card ∧
    ∀ s s' : slots p l i e,
      Mp p l i e s s' ∈ Ideal.span {(p : ℤ_[p]) ^ digitL p l (kTop p l)} :=
  ⟨card_slots p l i e, M1 p l i e⟩

/-- **Theorem D_p**, everything written out. -/
theorem hDp (hp : Odd p) (l i e : ℕ) (he : 1 ≤ e) :
    Nonempty ((((danceL p l).ι → ℤ_[p]) ⧸ LinearMap.range ((danceL p l).Fd 1 + (p : ℤ_[p]) ^ e •
        (Dop (flL p l) + (i : ℤ_[p]) • (1 : Module.End ℤ_[p] ((danceL p l).ι → ℤ_[p]))))) ≃ₗ[ℤ_[p]]
      (((t : Fin (kTop p l - 1)) →
          Fin ((p - 1) * digitL p l (kTop p l) * p ^ (kTop p l - (t + 1) - 1) * 2 ^ (Iset p l).card) →
            ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ ((t : ℕ) + 1)}) ×
        (Fin ((digitL p l (kTop p l) - 1) * 2 ^ (Iset p l).card) →
            ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ kTop p l}) ×
        ((slots p l i e → ℤ_[p]) ⧸
          LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l i e).mulVecLin)))) :=
  theorem_Dp p hp l i e he

/-- **Theorem I**: (I1) `Y ≅ S × C`, (I2) `p^k S = 0`, (I3) `C` has `2^{|I|}` generators and
`C ⧸ p^{k+1} C ≅ (ℤ_[p] ⧸ p^{k+1})^{2^{|I|}}`, and the invariant form. -/
theorem hI (hp : Odd p) (l i e : ℕ) (he : 1 ≤ e) :
    Nonempty (Yp p l i e ≃ₗ[ℤ_[p]] (Sp p l × Cmod p l i e)) ∧
    (∀ x : Sp p l, (p : ℤ_[p]) ^ kTop p l • x = 0) ∧
    (∃ g : Fin (2 ^ (Iset p l).card) → Cmod p l i e, Submodule.span ℤ_[p] (Set.range g) = ⊤) ∧
    Nonempty ((Cmod p l i e ⧸ (p : ℤ_[p]) ^ (kTop p l + 1) • (⊤ : Submodule ℤ_[p] (Cmod p l i e)))
      ≃ₗ[ℤ_[p]] (Fin (2 ^ (Iset p l).card) →
        ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + 1)})) ∧
    Nonempty ((Yp p l i e ⧸ (p : ℤ_[p]) ^ (kTop p l + 1) • (⊤ : Submodule ℤ_[p] (Yp p l i e)))
      ≃ₗ[ℤ_[p]] (Sp p l × (Fin (2 ^ (Iset p l).card) →
        ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ (kTop p l + 1)}))) :=
  theorem_I p hp l i e he

/-- `Y`, `S` and `C` are what the spec says. -/
theorem hDefs (l i e : ℕ) :
    Yp p l i e = (((danceL p l).ι → ℤ_[p]) ⧸ LinearMap.range ((danceL p l).Fd 1 + (p : ℤ_[p]) ^ e •
        (Dop (flL p l) + (i : ℤ_[p]) • (1 : Module.End ℤ_[p] ((danceL p l).ι → ℤ_[p]))))) ∧
    Sp p l = (((t : Fin (kTop p l - 1)) →
          Fin ((p - 1) * digitL p l (kTop p l) * p ^ (kTop p l - (t + 1) - 1) * 2 ^ (Iset p l).card) →
            ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ ((t : ℕ) + 1)}) ×
        (Fin ((digitL p l (kTop p l) - 1) * 2 ^ (Iset p l).card) →
            ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ kTop p l})) ∧
    Cmod p l i e = ((slots p l i e → ℤ_[p]) ⧸
          LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l i e).mulVecLin)) :=
  ⟨rfl, rfl, rfl⟩

end CheckCSI10

#print axioms CheckCSI10.hDigits
#print axioms CheckCSI10.hTop
#print axioms CheckCSI10.hMp
#print axioms CheckCSI10.hM
#print axioms CheckCSI10.hDp
#print axioms CheckCSI10.hI
#print axioms CheckCSI10.hDefs
#print axioms ColouredSand.OddTwist.theorem_D_gen
#print axioms ColouredSand.OddTwist.theorem_I_invariant
