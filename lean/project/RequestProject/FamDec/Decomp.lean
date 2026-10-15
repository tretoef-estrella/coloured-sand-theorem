module

public import RequestProject.FamDec.Mult
public import RequestProject.FamDec.Perm

/-!
# `C31_theorem_36_the_family_decomposition.md`: Part D — the decomposition (Theorem 3.6), and
# Part Z — the case of the paper

Encodings (namespace `FamDec`):

* `T A λ` and `tpow A n` are C29's `Filt.T` and `Filt.tpow`; finite direct sums are C30's
  `Step36.dsumList`; "`X ≅ Y`" is `Nonempty (Doubling.Iso X Y)`.
* The hypotheses of C30 (A1) are C28's explicit propositions `H1 φ`, `H2 φ`, `H3 A`,
  `OneAddTwoUnit A` and `h2 : (2 : B) = 0`, passed as arguments, with
  `[IsDomain A] [CharZero A] [OddUnits A]`.
* Part Z: `ℤ_[2]` is `PadicInt 2`, `B = ZMod 2`, `φ = PadicInt.toZMod`; the hypotheses come from
  C28 `Lift2.Z1` and C21 `Twist.C3_hyp`.
-/

@[expose] public section

noncomputable section

namespace FamDec

open DPLattice WeylFilt Doubling Twist Lemma35 Tensor2 Lemma35b Cocycle Lift2 Filt Step36

section D

variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [CharZero A] [OddUnits A]
  {φ : A →+* B}

/-- (D1), auxiliary: `(L.map (T A)).map phi = (L.map (fun ν => 2ν + 1)).map (T A)`
(C29 `T_odd`). -/
lemma map_T_phi (L : List ℕ) :
    (L.map (T A)).map phi = (L.map (fun ν => 2 * ν + 1)).map (T A) := by
  simp only [List.map_map]
  exact List.map_congr_left (fun ν _ => (T_odd A ν).symm)

/-- **(D1)** For every `λ`: `tensorV (T A λ) ≅ dsumList ((Vdot λ).map (T A))`, under the
hypotheses of C30 (A1). Proof by strong induction on `λ`, as in the file: C30 (K1), (K4e) for
`λ = 0`; C29 `T_odd`, `T_even` and (K4e) for `λ = 2l + 1`; C30 (A1) (with C29 (T1)), the induction
hypothesis, C20 `Iso.phi`, C30 (K4d), C29 `T_odd`, C24 `dsumAssoc` and C23 `dsumIso` for
`λ = 2l + 2`. -/
theorem D1 (h1 : H1 φ) (hk : H2 φ) (h3 : H3 A) (hU : OneAddTwoUnit A) (h2 : (2 : B) = 0)
    (lam : ℕ) : Nonempty (Doubling.Iso (tensorV (T A lam)) (dsumList ((Vdot lam).map (T A)))) := by
  induction lam using Nat.strong_induction_on with
  | _ lam ih =>
    rcases nat_cases3 lam with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
    · rw [Vdot_zero, List.map_singleton, T_zero]
      obtain ⟨u⟩ := (K1 (A := A)).2.2
      have hT1 : T A 1 = phi (one A) := by rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, T_odd, T_zero]
      rw [hT1]
      exact ⟨u.trans (dsumListSingletonIso _).symm⟩
    · rw [Vdot_odd, List.map_singleton, T_odd, ← T_even]
      exact ⟨(dsumListSingletonIso _).symm⟩
    · obtain ⟨hΔ, hN⟩ := T1 (A := A) l
      obtain ⟨e, -⟩ := A1 h1 hk h3 hU h2 hΔ hN
      obtain ⟨v⟩ := ih l (by omega)
      have hP : T A (2 * l + 1) = phi (T A l) := T_odd A l
      rw [Vdot_even, T_even, List.map_append, List.map_cons, List.map_cons, List.map_nil,
        List.cons_append, List.cons_append, List.nil_append, dsumList_cons, dsumList_cons, hP,
        ← map_T_phi]
      exact ⟨(e.trans (dsumAssoc _ _ _)).trans
        (dsumIso (Iso.refl _) (dsumIso (Iso.refl _) ((Iso.phi v).trans (phiDsumListIso _))))⟩

/-- **(D2)** Theorem 3.6, list form: for every `n`, `tpow A n ≅ dsumList ((L n).map (T A))`,
under the hypotheses of C30 (A1). Proof by induction on `n`: C29 `tpow_zero`, `T_zero` and C30
(K4e); then C29 `tpow_succ`, C23 `tensorVIso`, C30 (K4c), (D1) and (P2). -/
theorem D2 (h1 : H1 φ) (hk : H2 φ) (h3 : H3 A) (hU : OneAddTwoUnit A) (h2 : (2 : B) = 0)
    (n : ℕ) : Nonempty (Doubling.Iso (tpow A n) (dsumList ((L n).map (T A)))) := by
  induction n with
  | zero =>
    rw [tpow_zero, L_zero, List.map_singleton, T_zero]
    exact ⟨(dsumListSingletonIso _).symm⟩
  | succ n ih =>
    obtain ⟨u⟩ := ih
    obtain ⟨w⟩ := P2 (fun lam => tensorV (T A lam)) (fun lam => (Vdot lam).map (T A)) (L n)
      (fun lam _ => D1 h1 hk h3 hU h2 lam)
    have hmap : (L n).flatMap (fun lam => (Vdot lam).map (T A)) = (L (n + 1)).map (T A) := by
      rw [L_succ, List.map_flatMap]
    have hmap' : ((L n).map (T A)).map tensorV = (L n).map (fun lam => tensorV (T A lam)) := by
      rw [List.map_map]; rfl
    rw [tpow_succ, ← hmap]
    refine ⟨((tensorVIso u).trans (tensorVDsumListIso _)).trans ?_⟩
    rw [hmap']
    exact w

/-- **(D3)** Theorem 3.6, multiplicity form: for every `n`,
`tpow A n ≅ dsumList ((List.range (n + 1)).flatMap (fun λ => List.replicate (m λ n) (T A λ)))`,
i.e. `V^{⊗n} ⊗ A ≅ ⊕_{λ ≤ n} T(λ)^{m_λ(n)}`, under the hypotheses of C30 (A1). From (D2), (M4)
and (P1). -/
theorem D3 (h1 : H1 φ) (hk : H2 φ) (h3 : H3 A) (hU : OneAddTwoUnit A) (h2 : (2 : B) = 0)
    (n : ℕ) : Nonempty (Doubling.Iso (tpow A n)
      (dsumList ((List.range (n + 1)).flatMap
        (fun lam => List.replicate (m lam n) (T A lam))))) := by
  obtain ⟨u⟩ := D2 h1 hk h3 hU h2 n
  have hperm := (M4 n).map (T A)
  have heq : ((List.range (n + 1)).flatMap (fun lam => List.replicate (m lam n) lam)).map (T A) =
      (List.range (n + 1)).flatMap (fun lam => List.replicate (m lam n) (T A lam)) := by
    rw [List.map_flatMap]
    simp only [List.map_replicate]
  rw [heq] at hperm
  obtain ⟨v⟩ := P1 hperm
  exact ⟨u.trans v⟩

end D

/-! ### Part Z -/

/-- **(Z1)**, part (D1): for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod`,
`tensorV (T ℤ_[2] λ) ≅ dsumList ((Vdot λ).map (T ℤ_[2]))` for every `λ`. -/
theorem Z1_D1 (lam : ℕ) :
    Nonempty (Doubling.Iso (tensorV (T ℤ_[2] lam)) (dsumList ((Vdot lam).map (T ℤ_[2])))) :=
  D1 (φ := (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)) Lift2.Z1.1 Lift2.Z1.2.1 Lift2.Z1.2.2.1
    Lift2.Z1.2.2.2 Twist.C3_hyp.2.2.2.2.1 lam

/-- **(Z1)**, part (D2): `tpow ℤ_[2] n ≅ dsumList ((L n).map (T ℤ_[2]))` for every `n`. -/
theorem Z1_D2 (n : ℕ) :
    Nonempty (Doubling.Iso (tpow ℤ_[2] n) (dsumList ((L n).map (T ℤ_[2])))) :=
  D2 (φ := (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)) Lift2.Z1.1 Lift2.Z1.2.1 Lift2.Z1.2.2.1
    Lift2.Z1.2.2.2 Twist.C3_hyp.2.2.2.2.1 n

/-- **(Z1)**, part (D3): `tpow ℤ_[2] n ≅ ⊕_{λ ≤ n} T(λ)^{m_λ(n)}` for every `n`. -/
theorem Z1_D3 (n : ℕ) :
    Nonempty (Doubling.Iso (tpow ℤ_[2] n)
      (dsumList ((List.range (n + 1)).flatMap
        (fun lam => List.replicate (m lam n) (T ℤ_[2] lam))))) :=
  D3 (φ := (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)) Lift2.Z1.1 Lift2.Z1.2.1 Lift2.Z1.2.2.1
    Lift2.Z1.2.2.2 Twist.C3_hyp.2.2.2.2.1 n

/-- **(Z1)** (D1), (D2), (D3) for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod` (the hypotheses
by C28 (Z1) and C21 `C3_hyp`). -/
theorem Z1 :
    (∀ lam : ℕ,
      Nonempty (Doubling.Iso (tensorV (T ℤ_[2] lam)) (dsumList ((Vdot lam).map (T ℤ_[2]))))) ∧
    (∀ n : ℕ, Nonempty (Doubling.Iso (tpow ℤ_[2] n) (dsumList ((L n).map (T ℤ_[2]))))) ∧
    (∀ n : ℕ, Nonempty (Doubling.Iso (tpow ℤ_[2] n)
      (dsumList ((List.range (n + 1)).flatMap
        (fun lam => List.replicate (m lam n) (T ℤ_[2] lam)))))) :=
  ⟨Z1_D1, Z1_D2, Z1_D3⟩

end FamDec
