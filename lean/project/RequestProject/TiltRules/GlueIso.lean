module

public import RequestProject.TiltRules.Untw
public import RequestProject.Lemma35b.Basic

/-!
# Isomorphisms between glued DP-lattices (auxiliary for `CSG4_tensor_rules.md`, §3, Step 3)

`glueDP p L M r x h` (from `RequestProject/TiltP/GlueDP.lean`) is the DP-lattice over `ℤ_[p]` of
the glued lattice `Lx p L M r x = span{ℓ_i, s̃_j}`, `s̃_j = s_j + x C(j + r, j) ℓ_{j+r}`, inside
`Δ(L) ⊕ Δ(M)` over `ℚ_[p]` (coordinates in the basis `ℓ_i, s̃_j`).

* `glueIso_unit`: the glued lattices with glues `x` and `u x`, `‖u‖ = 1`, are isomorphic (the
  rescaling `G4_rescaling` of the Glue files); `glueOK_unit` transports the stability hypothesis.
  The parameters `L, M, r` may be given up to (propositional) equality.
* `glueIso_int`: if `‖y‖ ≤ 1` the glue is integral, `Lx y = Lx 0`, and
  `glueDP p L M r y h ≅ Δ(L) ⊕ Δ(M)`; `glueOK_int` gives the stability hypothesis.
* `glueIso_shift0`: for the shift `r = 0` and `L = M = N`, `glueDP p N N 0 y h ≅ Δ(N) ⊕ Δ(N)` for
  every `y` (the untwisting map `Phi` commutes with `F`, `E` when `r = 0`, `L = M`).
* `Tglue_eq`: `Tglue p r a` is `glueDP` with `L = λ`, `M = μ`, shift `r`, glue `xT p r a`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltRules

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP

variable {p : ℕ} [Fact p.Prime]

/-- `Tglue p r a` unfolds to `glueDP`. -/
theorem Tglue_eq (r a : ℕ) :
    Tglue p r a = glueDP p (lam p r a) (mu p r a) r (xT p r a) (glueOK_xT r a) := rfl

/-- Glued lattices with equal parameters are isomorphic. -/
def glueIso_cast {L M r L' M' r' : ℕ} {x x' : ℚ_[p]} (h : GlueOK p L M r x)
    (h' : GlueOK p L' M' r' x') (hL : L = L') (hM : M = M') (hr : r = r') (hx : x = x') :
    Iso (glueDP p L M r x h) (glueDP p L' M' r' x' h') := by
  subst hL hM hr hx; exact Lemma35b.Iso.refl _

/-- The unit of `ℤ_[p]` attached to `u : ℚ_[p]` with `‖u‖ = 1`. -/
def unitOf (u : ℚ_[p]) (hu : ‖u‖ = 1) : ℤ_[p]ˣ :=
  let c : ℤ_[p] := ⟨u, hu.le⟩
  (PadicInt.isUnit_iff.2 (show ‖c‖ = 1 from hu)).unit

lemma unitOf_coe (u : ℚ_[p]) (hu : ‖u‖ = 1) : (((unitOf u hu : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = u := rfl

/-- Stability of `Lx (u x)` from that of `Lx x`, for `‖u‖ = 1`. -/
theorem glueOK_unit {L M r : ℕ} {x : ℚ_[p]} (h : GlueOK p L M r x) (u : ℚ_[p]) (hu : ‖u‖ = 1) :
    GlueOK p L M r (u * x) := by
  obtain ⟨φ, hF, hE, -, -, hmap⟩ := G4_rescaling (L := L) (M := M) r (unitOf u hu) x
  rw [unitOf_coe] at hmap
  refine ⟨?_, fun t v hv => ?_⟩
  · rcases h.wt_ok with h0 | h0
    · left; rw [h0, mul_zero]
    · right; exact h0
  · rw [← hmap] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := hv
    simp only [LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply] at *
    refine ⟨⟨Fop p L M t w, (h.stab t w hw).1, ?_⟩, ⟨Eop p L M t w, (h.stab t w hw).2, ?_⟩⟩
    · simp only [LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]; exact hF t w
    · simp only [LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]; exact hE t w

/-- **Rescaling the glue by a unit** (with the parameters up to equality). -/
theorem glueIso_unit {L M r L' M' r' : ℕ} {x x' : ℚ_[p]} (h : GlueOK p L M r x)
    (h' : GlueOK p L' M' r' x') (hL : L = L') (hM : M = M') (hr : r = r') (u : ℚ_[p])
    (hu : ‖u‖ = 1) (hx : x' = u * x) :
    Nonempty (Iso (glueDP p L M r x h) (glueDP p L' M' r' x' h')) := by
  subst hL hM hr hx
  obtain ⟨φ, hF, hE, -, -, hmap⟩ := G4_rescaling (L := L) (M := M) r (unitOf u hu) x
  rw [unitOf_coe] at hmap
  refine iso_of_untw (untwGlue p L M r x h) (untwGlue p L M r (u * x) h') φ hF hE ?_
  intro v
  show v ∈ Lx p L M r x ↔ φ v ∈ Lx p L M r (u * x)
  rw [← hmap]
  constructor
  · intro hv; exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, hwv⟩
    have : w = v := φ.injective hwv
    rw [← this]; exact hw

/-- An integral glue gives a stable lattice. -/
theorem glueOK_int {L M r : ℕ} {y : ℚ_[p]} (hy : ‖y‖ ≤ 1) (hW : y = 0 ∨ L = M + 2 * r) :
    GlueOK p L M r y := by
  refine ⟨hW, fun t v hv => ?_⟩
  rw [Lx_eq_Lx_zero r y hy] at hv ⊢
  exact (glueOK_zero r).stab t v hv

/-- **An integral glue splits**: `glueDP p L M r y h ≅ Δ(L) ⊕ Δ(M)` if `‖y‖ ≤ 1`. -/
theorem glueIso_int {L M r L' M' : ℕ} {y : ℚ_[p]} (h : GlueOK p L M r y) (hy : ‖y‖ ≤ 1)
    (hL : L = L') (hM : M = M') :
    Nonempty (Iso (glueDP p L M r y h) (dsum (delta ℤ_[p] L') (delta ℤ_[p] M'))) := by
  subst hL hM
  refine iso_of_untw (untwGlue p L M r y h) (untwDsum (untwDelta p L) (untwDelta p M))
    (LinearEquiv.refl _ _) ?_ ?_ ?_
  · intro t v; exact congrFun (congrArg DFunLike.coe (Fop_eq_blk p L M t)) v
  · intro t v; exact congrFun (congrArg DFunLike.coe (Eop_eq_blk p L M t)) v
  · intro v
    show v ∈ Lx p L M r y ↔ (v ∘ Sum.inl ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin (L + 1))) ∧
      v ∘ Sum.inr ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin (M + 1))))
    rw [← mem_range_coeL_sum, Lx_eq_Lx_zero r y hy, mem_Lx_zero_iff, mem_range_coeL_iff]

/-- For `r = 0`, `L = M`: `Phi v = v − y • inl (v ∘ inr)`. -/
lemma Phi_shift0 (N : ℕ) (y : ℚ_[p]) (v : V p N N) :
    Phi p N N 0 y v = v - y • (inlL (v ∘ Sum.inr) : Idx N N → ℚ_[p]) := by
  funext z; rcases z with i | j
  · rw [Phi_inl]
    simp only [Pi.sub_apply, Pi.smul_apply, inlL_apply, Sum.elim_inl, Function.comp, smul_eq_mul,
      gl, Nat.sub_zero, if_pos (Nat.zero_le _), Nat.choose_self, Nat.cast_one, mul_one, cR_fin]
  · rw [Phi_inr]; simp

lemma Phi_shift0_comm (N : ℕ) (y : ℚ_[p]) (T : Module.End ℚ_[p] (Fin (N + 1) → ℚ_[p]))
    (v : V p N N) :
    Phi p N N 0 y (blk T T v) = blk T T (Phi p N N 0 y v) := by
  rw [Phi_shift0, Phi_shift0, map_sub, map_smul]
  congr 2
  rw [← LinearMap.comp_apply (blk T T) inlL, blk_comp_inlL]
  rfl

/-- **Shift `0`**: `glueDP p L M 0 y h ≅ Δ(N) ⊕ Δ(N)` when `L = M = N`, for every `y`. -/
theorem glueIso_shift0 {L M N : ℕ} {y : ℚ_[p]} (h : GlueOK p L M 0 y) (hL : L = N) (hM : M = N) :
    Nonempty (Iso (glueDP p L M 0 y h) (dsum (delta ℤ_[p] N) (delta ℤ_[p] N))) := by
  subst L M
  refine iso_of_untw (untwGlue p N N 0 y h) (untwDsum (untwDelta p N) (untwDelta p N))
    (PhiE p N N 0 y) ?_ ?_ ?_
  · intro t v
    show Phi p N N 0 y (Fop p N N t v) = blk (deltaF N t) (deltaF N t) (Phi p N N 0 y v)
    rw [Fop_eq_blk, Phi_shift0_comm]
  · intro t v
    show Phi p N N 0 y (Eop p N N t v) = blk (deltaE N t) (deltaE N t) (Phi p N N 0 y v)
    rw [Eop_eq_blk, Phi_shift0_comm]
  · intro v
    show v ∈ Lx p N N 0 y ↔ ((Phi p N N 0 y v) ∘ Sum.inl ∈
      LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin (N + 1))) ∧
      (Phi p N N 0 y v) ∘ Sum.inr ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin (N + 1))))
    rw [← mem_range_coeL_sum, mem_Lx_iff, mem_range_coeL_iff]

end ColouredSand.TiltRules
