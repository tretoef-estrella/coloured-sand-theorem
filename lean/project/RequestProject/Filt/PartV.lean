module

public import RequestProject.Filt.PartE
public import RequestProject.WeylFilt.All
public import RequestProject.Doubling.All

/-!
# `C29_filtrations_and_dance_lattices.md`: Part V — the two operations `V ⊗ −` and `Φ`

Encodings (namespace `Filt`):

* `V ⊗ −` is C18's `tensorV` (basis `Fin 2 × M.ι`) with C23's `tensorVHom` on morphisms; `Φ` is
  C20's `phi` (basis `Fin 2 × N.ι`) with `phiHom` on morphisms.
* **[char 0]** is `[IsDomain A] [CharZero A]`; **[Φ]** is `[IsDomain A] [CharZero A]
  [OddUnits A]` (C20's `OddUnits`).
* Weight preservation of all the morphisms used comes from C25 (P1) (`LemmaW.P1`).
-/

@[expose] public section

noncomputable section

namespace Filt

open DPLattice WeylFilt Doubling LemmaW Cocycle Finset

variable {A : Type*} [CommRing A]

/-! ### `tensorVHom` is exact -/

section tensor

variable {X Y Z : DPLattice A}

/-- (V1, auxiliary) `tensorVHom f` is `id ⊠ f`, i.e. C20's `phiLin f` on `Fin 2 × ι → A`. -/
lemma tensorVHom_toLin (f : Hom X Y) : (Tensor2.tensorVHom f).toLin = phiLin f.toLin := by
  refine ext_single fun p => ?_
  obtain ⟨e, i⟩ := p
  change (Tensor2.tensorVHom f).toLin (Pi.single (e, i) 1) = phiLin f.toLin (Pi.single (e, i) 1)
  rw [single_eq_bvec, Tensor2.tensorVHom_bvec, phiLin_bvec]

/-- (V1, auxiliary) `tensorVHom` sends short exact sequences to short exact sequences. -/
lemma tensorV_shortExact {f : Hom X Y} {g : Hom Y Z} (h : ShortExact f g) :
    ShortExact (Tensor2.tensorVHom f) (Tensor2.tensorVHom g) where
  inj := by rw [tensorVHom_toLin]; exact phiLin_injective h.inj
  surj := by rw [tensorVHom_toLin]; exact phiLin_surjective h.surj
  exact := by rw [tensorVHom_toLin, tensorVHom_toLin]; exact phiLin_exact h.exact

end tensor

/-! ### (V1) -/

section V1

variable [IsDomain A] [CharZero A]

/-- (V1, auxiliary) `V ⊗ Δ(l)` has a `Δ`-filtration: C19 (S1) for `l ≥ 1`, C19 (S4) for
`l = 0`. -/
lemma tensorV_delta (l : ℕ) : HasDeltaFilt (tensorV (delta A l)) := by
  rcases l with _ | m
  · obtain ⟨φ, ψ, h1, h2⟩ := (S4 (A := A)).1
    let e : Iso (tensorV (delta A 0)) (V A) := ⟨φ, ψ, h1, h2⟩
    exact I1_delta e.symm (P1 _) (P1 _) I2_delta_V
  · exact E1 _ _ (WeylFilt.S1 (m + 1) (by omega)) (P1 _) (P1 _) (F2_delta _) (F2_delta _)

/-- (V1, auxiliary) `V ⊗ ∇(l)` has a `∇`-filtration: C19 (S2) for `l ≥ 1`, C19 (S4) for
`l = 0`. -/
lemma tensorV_nabla (l : ℕ) : HasNablaFilt (tensorV (nabla A l)) := by
  rcases l with _ | m
  · obtain ⟨φ, ψ, h1, h2⟩ := (S4 (A := A)).2
    let e : Iso (tensorV (nabla A 0)) (V A) := ⟨φ, ψ, h1, h2⟩
    exact I1_nabla e.symm (P1 _) (P1 _) I2_nabla_V
  · exact E2 _ _ (WeylFilt.S2 (m + 1) (by omega)) (P1 _) (P1 _) (F2_nabla _) (F2_nabla _)

variable {M N : DPLattice A}

/-- (V1) **[char 0]** `HasDeltaFilt M → HasDeltaFilt (tensorV M)`. -/
theorem V1_delta (hM : HasDeltaFilt M) : HasDeltaFilt (tensorV M) := by
  induction hM with
  | base h => exact HasDeltaFilt.base (inferInstanceAs (IsEmpty (Fin 2 × _)))
  | step f g hfg _ _ _ ih =>
    exact E1 _ _ (tensorV_shortExact hfg) (P1 _) (P1 _) ih (tensorV_delta _)

/-- (V1) **[char 0]** `HasNablaFilt N → HasNablaFilt (tensorV N)`. -/
theorem V1_nabla (hN : HasNablaFilt N) : HasNablaFilt (tensorV N) := by
  induction hN with
  | base h => exact HasNablaFilt.base (inferInstanceAs (IsEmpty (Fin 2 × _)))
  | step f g hfg _ _ _ ih =>
    exact E2 _ _ (tensorV_shortExact hfg) (P1 _) (P1 _) (tensorV_nabla _) ih

/-- (V1) **[char 0]** `V ⊗ −` preserves both filtrations: `HasDeltaFilt M → HasDeltaFilt
(tensorV M)` and `HasNablaFilt N → HasNablaFilt (tensorV N)`. -/
theorem V1 : (HasDeltaFilt M → HasDeltaFilt (tensorV M)) ∧
    (HasNablaFilt N → HasNablaFilt (tensorV N)) :=
  ⟨V1_delta, V1_nabla⟩

end V1

/-! ### (V2) -/

section V2

variable [IsDomain A] [CharZero A] [OddUnits A] {M N : DPLattice A}

/-- (V2) **[Φ]** `HasDeltaFilt M → HasDeltaFilt (phi M)` (`phiHom` is exact, C20 (A3), and
`phi (delta A l) ≅ delta A (2l+1)`, C20 `deltaIso`). -/
theorem V2_delta (hM : HasDeltaFilt M) : HasDeltaFilt (phi M) := by
  induction hM with
  | base h => exact HasDeltaFilt.base (inferInstanceAs (IsEmpty (Fin 2 × _)))
  | step f g hfg _ _ _ ih =>
    exact E1 _ _ (A3 hfg) (P1 _) (P1 _) ih
      (I1_delta (deltaIso _) (P1 _) (P1 _) (F2_delta _))

/-- (V2) **[Φ]** `HasNablaFilt N → HasNablaFilt (phi N)` (`phiHom` is exact, C20 (A3), and
`phi (nabla A l) ≅ nabla A (2l+1)`, C20 `nablaIso`). -/
theorem V2_nabla (hN : HasNablaFilt N) : HasNablaFilt (phi N) := by
  induction hN with
  | base h => exact HasNablaFilt.base (inferInstanceAs (IsEmpty (Fin 2 × _)))
  | step f g hfg _ _ _ ih =>
    exact E2 _ _ (A3 hfg) (P1 _) (P1 _)
      (I1_nabla (nablaIso _) (P1 _) (P1 _) (F2_nabla _)) ih

/-- (V2) **[Φ]** `Φ` preserves both filtrations: `HasDeltaFilt M → HasDeltaFilt (phi M)` and
`HasNablaFilt N → HasNablaFilt (phi N)`. -/
theorem V2 : (HasDeltaFilt M → HasDeltaFilt (phi M)) ∧ (HasNablaFilt N → HasNablaFilt (phi N)) :=
  ⟨V2_delta, V2_nabla⟩

end V2

end Filt
