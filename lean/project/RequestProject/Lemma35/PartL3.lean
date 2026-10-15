module

public import RequestProject.Lemma35.PartL1
public import RequestProject.Lemma35.PartL2

/-!
# `C22_lemma_35_over_F2.md`: Part L, (L3) the case of the paper, and the remark over `ℤ`

* (L3) For `B = ZMod 2` (`= 𝔽_2`), with `two_eq_zero_zmod2 : (2 : ZMod 2) = 0`, both
  isomorphisms `V^{⊗3} ≅ Δ(3) ⊕ (V ⊕ V)` and `Δ(3) ≅ V ⊗ V^{[1]}` exist.
* Proof sketch, last item ("so `h2` is used"): over `ℤ` the map `g` is not a `Hom`
  (`g_not_hom_int`), because `E^{(1)}(100 + 010) = 2·000` while `E^{(1)} b_0 = 0` in `V`.
-/

@[expose] public section

noncomputable section

namespace Lemma35

open DPLattice Finset WeylFilt

/-- (L3) `2 = 0` in `ZMod 2`. -/
theorem two_eq_zero_zmod2 : (2 : ZMod 2) = 0 := rfl

/-- (L3) The case of the paper: over `B = ZMod 2`, `V^{⊗3} ≅ Δ(3) ⊕ (V ⊕ V)` and
`Δ(3) ≅ V ⊗ V^{[1]}` (isomorphisms in the sense of `Doubling.Iso`). -/
theorem L3 :
    Nonempty (Doubling.Iso (tensorV (tensorV (V (ZMod 2))))
      (dsum (delta (ZMod 2) 3) (dsum (V (ZMod 2)) (V (ZMod 2))))) ∧
    Nonempty (Doubling.Iso (delta (ZMod 2) 3) (tensorV (Twist.frob two_eq_zero_zmod2 (V (ZMod 2))))) :=
  ⟨⟨isoL1 two_eq_zero_zmod2⟩, ⟨isoL2 two_eq_zero_zmod2⟩⟩

/-- Proof sketch of (L1), (L2), last item: over `ℤ` the map `g` of (L1) is not a `Hom`
(`E^{(1)}(100 + 010) = 2·000`, while `E^{(1)} b_0 = 0` in `V`); so the hypothesis `2 = 0` is
needed. -/
theorem g_not_hom_int : ¬ ∃ φ : Hom (D3 ℤ) (T3 ℤ), φ.toLin = gL := by
  rintro ⟨φ, hφ⟩
  have hc : gL ((D3 ℤ).Ed 1 (bD 0 : ID → ℤ)) = (T3 ℤ).Ed 1 (gL (bD 0 : ID → ℤ)) := by
    have := LinearMap.congr_fun (φ.comm_E 1) (bD 0 : ID → ℤ)
    rw [hφ] at this
    exact this
  have hE : (D3 ℤ).Ed 1 (bD 0 : ID → ℤ) = 0 := by
    funext p
    rcases p with p | p | p <;> fin_cases p <;>
      simp [dsum, V, VEd, VmatE, delta, deltaE, deltaMatE, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct, Pi.single_apply]
  rw [hE, map_zero, (g_basis (B := ℤ)).2.2.2.2.1] at hc
  have h := congrFun hc ((0, (0, 0)) : IT)
  simp [tensorV, tensorEd, V, VEd, VmatE, dotProduct, Pi.single_apply, Matrix.toLin'_apply] at h

end Lemma35
