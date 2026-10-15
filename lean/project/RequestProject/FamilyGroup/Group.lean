module

public import RequestProject.FamilyGroup.Basic

/-!
# `C16_the_family_group_over_Z2.md`, Part X: the group of a family

(X1) `X1`, (X2) `X2`, (X3) `X3`.  The common first step (`X_equiv_coker`, `X_equiv_diag`) is
`Dance.proposition_4_3` over `ℤ_[2]` with `Windows.theorem_D_iv`, followed by (L2) and (U2).
-/

@[expose] public section

namespace FamilyGroup

open Windows TheoremF Matrix
open scoped Pointwise

/-- `Dance.proposition_4_3` over `ℤ_[2]`, with the final matrix written as the image of the one over
`ℤ` (`Windows.theorem_D_iv`) (proof of Part X of `C16_the_family_group_over_Z2.md`). -/
theorem X_equiv_coker (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) :
    Nonempty (X ds α i ≃ₗ[ℤ_[2]] SC ds × ((Fin (2 ^ Dance.mCount ds) → ℤ_[2]) ⧸
      LinearMap.range ((2 : ℤ_[2]) ^ ds.length •
        Matrix.toLin' ((finalMatrix ℤ ds α i).map (Int.castRingHom ℤ_[2]))))) := by
  obtain ⟨e⟩ := Dance.proposition_4_3 (A := ℤ_[2]) ds α i hα
  rw [← theorem_D_iv]
  exact ⟨e⟩

/-- An integer Smith-type form `P M Q = diagonal d` with odd determinants splits the group of the
tower (proof of Part X of `C16_the_family_group_over_Z2.md`). -/
theorem X_equiv_diag (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α)
    (P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ)
    (hP : Odd P.det) (hQ : Odd Q.det) (d : Fin (2 ^ Dance.mCount ds) → ℤ)
    (h : P * finalMatrix ℤ ds α i * Q = diagonal d) :
    Nonempty (X ds α i ≃ₗ[ℤ_[2]] SC ds × ((j : Fin (2 ^ Dance.mCount ds)) →
      ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ ds.length * ((d j : ℤ) : ℤ_[2])})) := by
  obtain ⟨e1⟩ := X_equiv_coker ds α i hα
  have hmap := (U2 P (finalMatrix ℤ ds α i) Q).2
  rw [h, diagonal_map (map_zero _)] at hmap
  obtain ⟨e2⟩ := L2 ((2 : ℤ_[2]) ^ ds.length) ((finalMatrix ℤ ds α i).map (Int.castRingHom ℤ_[2]))
    (P.map (Int.castRingHom ℤ_[2])) (Q.map (Int.castRingHom ℤ_[2]))
    (fun j => Int.castRingHom ℤ_[2] (d j)) ((U2 P P P).1 hP) ((U2 Q Q Q).1 hQ) hmap.symm
  exact ⟨e1.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _) e2)⟩

lemma span_two_pow_unit {k e : ℕ} {u : ℤ} (hu : Odd u) :
    Ideal.span {(2 : ℤ_[2]) ^ k * (((u * 2 ^ e : ℤ)) : ℤ_[2])} =
      Ideal.span {(2 : ℤ_[2]) ^ (k + e)} := by
  rw [show (2 : ℤ_[2]) ^ k * (((u * 2 ^ e : ℤ)) : ℤ_[2]) = (u : ℤ_[2]) * 2 ^ (k + e) by
    push_cast; ring]
  exact L3_unit (U1 hu) _

/-- **(X1)** of `C16_the_family_group_over_Z2.md` (Part X, `i ≥ 1`): for `k ≥ 1`, `α ≥ 1`,
`i ≥ 1` there is `E` with `(E p : ℤ) = k + C + ŷ p` for `p < N`, and
`X^{(α)}(ds, i) ≅ SC(ds) × Π_{p : Fin N} Q(E p)`. -/
theorem X1 (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ p < 2 ^ Dance.mCount ds,
        (E p : ℤ) = ds.length + DanceSmith.Cst ds α i + DanceSmith.yHat ds α i p) ∧
      Nonempty (X ds α i ≃ₗ[ℤ_[2]] SC ds × ((p : Fin (2 ^ Dance.mCount ds)) → Q (E p))) := by
  obtain ⟨P, Q', hP, hQ, u, hu, E, hE, hD⟩ := DanceSmith.S3 ds hk α i hα hi
  obtain ⟨e1⟩ := X_equiv_diag ds α i hα P Q' hP hQ _ hD
  set N := 2 ^ Dance.mCount ds with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  refine ⟨fun p => ds.length + E (N - 1 - p), fun p hp => ?_, ?_⟩
  · rw [Nat.cast_add, hE _ (by omega), show N - 1 - (N - 1 - p) = p by omega]
    ring
  · obtain ⟨e2⟩ := piQuotReindex (R := ℤ_[2])
      (fun j : Fin N => (2 : ℤ_[2]) ^ ds.length * (((u j * 2 ^ E j : ℤ)) : ℤ_[2]))
      (fun p : Fin N => (2 : ℤ_[2]) ^ (ds.length + E (N - 1 - p))) (Fin.revPerm (n := N))
      (fun p => by
        simp only [Fin.revPerm_apply, Fin.val_rev]
        rw [span_two_pow_unit (hu _), show N - (p + 1) = N - 1 - p by omega])
    exact ⟨e1.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _) e2)⟩

/-- The index equivalence `Unit ⊕ Fin (N − 1) ≃ Fin N`, `() ↦ N − 1`, `q ↦ N − 2 − q`
(auxiliary for (X2) of `C16_the_family_group_over_Z2.md`). -/
def idxX2 (N : ℕ) (hN : 1 ≤ N) : Unit ⊕ Fin (N - 1) ≃ Fin N :=
  (Equiv.sumCongr finOneEquiv.symm (Equiv.refl _)).trans
    (finSumFinEquiv.trans ((finCongr (by omega)).trans Fin.revPerm))

lemma idxX2_inl (N : ℕ) (hN : 1 ≤ N) : ((idxX2 N hN (Sum.inl ())) : ℕ) = N - 1 := by
  simp [idxX2]

lemma idxX2_inr (N : ℕ) (hN : 1 ≤ N) (q : Fin (N - 1)) :
    ((idxX2 N hN (Sum.inr q)) : ℕ) = N - 2 - q := by
  simp [idxX2]; omega

/-- **(X2)** of `C16_the_family_group_over_Z2.md` (Part X, `i = 0`, `I ≠ ∅`): for `k ≥ 1`,
`α ≥ 1`, `I ≠ ∅` there is `E` with `(E q : ℤ) = k + α K + ŷ^♯ q` for `q < N − 1`, and
`X^{(α)}(ds, 0) ≅ SC(ds) × (A × Π_{q : Fin (N − 1)} Q(E q))`. -/
theorem X2 (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) (hne : Ids ds ≠ ∅) :
    ∃ E : ℕ → ℕ, (∀ q < 2 ^ Dance.mCount ds - 1,
        (E q : ℤ) = ds.length + (α : ℤ) * 2 ^ ds.length + DanceSmith.yHatS ds α q) ∧
      Nonempty (X ds α 0 ≃ₗ[ℤ_[2]]
        SC ds × (ℤ_[2] × ((q : Fin (2 ^ Dance.mCount ds - 1)) → Q (E q)))) := by
  obtain ⟨P, Q', hP, hQ, u, hu, E, hE, hD⟩ := DanceSmith.Z3 ds hk α hα hne
  obtain ⟨e1⟩ := X_equiv_diag ds α 0 hα P Q' hP hQ _ hD
  set N := 2 ^ Dance.mCount ds with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  refine ⟨fun q => ds.length + E (N - 2 - q), fun q hq => ?_, ?_⟩
  · rw [Nat.cast_add, hE _ (by omega), show N - 2 - (N - 2 - q) = q by omega]
    ring
  · obtain ⟨e2⟩ := piQuotReindex (R := ℤ_[2])
      (fun j : Fin N => (2 : ℤ_[2]) ^ ds.length *
        (((if (j : ℕ) < N - 1 then u j * 2 ^ E j else 0 : ℤ)) : ℤ_[2]))
      (Sum.elim (fun _ : Unit => (0 : ℤ_[2]))
        (fun q : Fin (N - 1) => (2 : ℤ_[2]) ^ (ds.length + E (N - 2 - q)))) (idxX2 N hN1)
      (fun x => by
        rcases x with ⟨⟩ | q
        · simp only [Sum.elim_inl]
          rw [idxX2_inl, if_neg (by omega)]
          simp
        · simp only [Sum.elim_inr]
          rw [idxX2_inr, if_pos (by omega)]
          exact span_two_pow_unit (hu _))
    let e3 := LinearEquiv.sumPiEquivProdPi ℤ_[2] Unit (Fin (N - 1))
      (fun x => ℤ_[2] ⧸ Ideal.span {Sum.elim (fun _ : Unit => (0 : ℤ_[2]))
        (fun q : Fin (N - 1) => (2 : ℤ_[2]) ^ (ds.length + E (N - 2 - q))) x})
    let e4 : ((_ : Unit) → ℤ_[2] ⧸ Ideal.span {(0 : ℤ_[2])}) ≃ₗ[ℤ_[2]] ℤ_[2] :=
      (LinearEquiv.piUnique ℤ_[2] (fun _ : Unit => ℤ_[2] ⧸ Ideal.span {(0 : ℤ_[2])})).trans
        (Classical.choice L3_zero)
    exact ⟨e1.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
      (e2.trans (e3.trans (LinearEquiv.prodCongr e4 (LinearEquiv.refl _ _)))))⟩

/-- **(X3)** of `C16_the_family_group_over_Z2.md` (Part X, `i = 0`, `I = ∅`): for `α ≥ 1` with
`I = ∅` (so `N = 1`), `X^{(α)}(ds, 0) ≅ SC(ds) × A`. -/
theorem X3 (ds : List Bool) (α : ℕ) (hα : 1 ≤ α) (hI : Ids ds = ∅) :
    Nonempty (X ds α 0 ≃ₗ[ℤ_[2]] SC ds × ℤ_[2]) := by
  obtain ⟨e1⟩ := X_equiv_coker ds α 0 hα
  have h1 : 2 ^ Dance.mCount ds = 1 := by rw [← card_Ids, hI, Finset.card_empty, pow_zero]
  rw [(DanceSmith.Z1 ds α hα).2 hI, Matrix.map_zero _ (map_zero _), map_zero, smul_zero,
    LinearMap.range_zero] at e1
  let e2 : ((Fin (2 ^ Dance.mCount ds) → ℤ_[2]) ⧸ (⊥ : Submodule ℤ_[2] _)) ≃ₗ[ℤ_[2]] ℤ_[2] :=
    (Submodule.quotEquivOfEqBot _ rfl).trans
      ((LinearEquiv.funCongrLeft ℤ_[2] ℤ_[2] (finCongr h1.symm)).trans
        (LinearEquiv.funUnique (Fin 1) ℤ_[2] ℤ_[2]))
  exact ⟨e1.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _) e2)⟩

end FamilyGroup
