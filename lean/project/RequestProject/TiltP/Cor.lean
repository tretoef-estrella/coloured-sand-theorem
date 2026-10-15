module

public import RequestProject.TiltP.CGLattice

/-!
# (G3)–(G4) The corollaries of the Clebsch–Gordan lattice (CSG3, Part G)

## Encoding

* (G3) `G3`: if `l ≥ 1` and `p ∤ l + 1`, then
  `Nonempty (Iso (tensorV (delta ℤ_[p] l)) (dsum (delta ℤ_[p] (l + 1)) (delta ℤ_[p] (l − 1))))`.
  Proof: `1/(l + 1)` is a unit, so `Lx (1/(l+1)) = Lx 0 = Dλ ⊕ Dμ` (`Lx_eq_Lx_zero`), and `Ψ⁻¹`
  maps the standard lattice of `W` onto it (G2); `iso_of_model` turns this into an isomorphism of
  DP-lattices over `ℤ_[p]`.
* (G4) `G4`: `Nonempty (Iso (tensorV (delta ℤ_[p] (p − 1))) (Tglue p 1 0))`, from
  `lam p 1 0 = p`, `mu p 1 0 = p − 2`, `nu p 1 0 = 1`, `xzero p 1 0 = 1/p = 1/(l + 1)` for
  `l = p − 1`; the isomorphism is induced by `Phi ∘ Ψ⁻¹`.  (`p ≠ 2` is not needed.)
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltP

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime]

/-! ### Models of `V ⊗ Δ(l)` and of `Δ(L) ⊕ Δ(M)` -/

lemma coeL_bvec {ι : Type*} (e : Fin 2) (m : ι → ℤ_[p]) :
    coeL ℤ_[p] ℚ_[p] (Fin 2 × ι) (bvec e m) = bvec e (coeL ℤ_[p] ℚ_[p] ι m) := by
  funext q; simp only [coeL_apply, bvec_apply]; split_ifs <;> simp

lemma coeL_slice {ι : Type*} (e : Fin 2) (v : Fin 2 × ι → ℤ_[p]) :
    coeL ℤ_[p] ℚ_[p] ι (slice e v) = slice e (coeL ℤ_[p] ℚ_[p] (Fin 2 × ι) v) := rfl

lemma pred_models {ι : Type*} {F : ℕ → Module.End ℤ_[p] (ι → ℤ_[p])}
    {FK : ℕ → Module.End ℚ_[p] (ι → ℚ_[p])} (hF : Models F FK) : Models (pred F) (pred FK) := by
  intro r u
  rcases r with _ | r
  · simp
  · exact hF r u

lemma tensor_models_F {ι : Type*} {F : ℕ → Module.End ℤ_[p] (ι → ℤ_[p])}
    {FK : ℕ → Module.End ℚ_[p] (ι → ℚ_[p])} (hF : Models F FK) :
    Models (tensorFd F) (tensorFd FK) := by
  intro t v
  show coeL ℤ_[p] ℚ_[p] _ (bvec 0 (F t (slice 0 v)) + bvec 1 (F t (slice 1 v)) +
      bvec 1 (pred F t (slice 0 v))) = bvec 0 (FK t (slice 0 (coeL ℤ_[p] ℚ_[p] _ v))) +
      bvec 1 (FK t (slice 1 (coeL ℤ_[p] ℚ_[p] _ v))) +
      bvec 1 (pred FK t (slice 0 (coeL ℤ_[p] ℚ_[p] _ v)))
  rw [map_add, map_add, coeL_bvec, coeL_bvec, coeL_bvec, hF, hF, pred_models hF, coeL_slice,
    coeL_slice]

lemma tensor_models_E {ι : Type*} {E : ℕ → Module.End ℤ_[p] (ι → ℤ_[p])}
    {EK : ℕ → Module.End ℚ_[p] (ι → ℚ_[p])} (hE : Models E EK) :
    Models (tensorEd E) (tensorEd EK) := by
  intro t v
  show coeL ℤ_[p] ℚ_[p] _ (bvec 0 (E t (slice 0 v)) + bvec 1 (E t (slice 1 v)) +
      bvec 0 (pred E t (slice 1 v))) = bvec 0 (EK t (slice 0 (coeL ℤ_[p] ℚ_[p] _ v))) +
      bvec 1 (EK t (slice 1 (coeL ℤ_[p] ℚ_[p] _ v))) +
      bvec 0 (pred EK t (slice 1 (coeL ℤ_[p] ℚ_[p] _ v)))
  rw [map_add, map_add, coeL_bvec, coeL_bvec, coeL_bvec, hE, hE, pred_models hE, coeL_slice,
    coeL_slice]

lemma blk_models {ι κ : Type*} {F : ℕ → Module.End ℤ_[p] (ι → ℤ_[p])}
    {FK : ℕ → Module.End ℚ_[p] (ι → ℚ_[p])} {G : ℕ → Module.End ℤ_[p] (κ → ℤ_[p])}
    {GK : ℕ → Module.End ℚ_[p] (κ → ℚ_[p])} (hF : Models F FK) (hG : Models G GK) :
    Models (fun t => blk (F t) (G t)) (fun t => blk (FK t) (GK t)) := by
  intro t v
  funext y
  rcases y with i | j
  · exact congrFun (hF t (v ∘ Sum.inl)) i
  · exact congrFun (hG t (v ∘ Sum.inr)) j

/-! ### Weights and inverses -/

/-- A weight-preserving linear map commutes with the diagonal operators `H`. -/
lemma comm_Hop_raw {ι κ : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ} {wt' : κ → ℤ}
    (φ : (ι → ℚ_[p]) →ₗ[ℚ_[p]] (κ → ℚ_[p])) (hφ : ∀ i j, wt i ≠ wt' j → φ (Pi.single i 1) j = 0) :
    φ ∘ₗ Hop wt = Hop wt' ∘ₗ φ := by
  refine ext_single fun i => ?_
  have hH : Hop (A := ℚ_[p]) wt (Pi.single i 1) = ((wt i : ℤ) : ℚ_[p]) • (Pi.single i 1 : ι → ℚ_[p]) := by
    funext k; by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  funext j
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hH, map_smul, DPLattice.Hop_apply, Pi.smul_apply,
    smul_eq_mul]
  by_cases hw : wt i = wt' j
  · rw [hw]
  · rw [hφ i j hw]; simp

/-- The inverse of a weight-preserving linear isomorphism is weight-preserving. -/
lemma symm_wt {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {wt : ι → ℤ} {wt' : κ → ℤ} (Ψ : (ι → ℚ_[p]) ≃ₗ[ℚ_[p]] (κ → ℚ_[p]))
    (hΨ : ∀ i j, wt i ≠ wt' j → Ψ (Pi.single i 1) j = 0) (k : κ) :
    InWt wt (wt' k) (Ψ.symm (Pi.single k 1)) := by
  have hH := comm_Hop_raw Ψ.toLinearMap hΨ
  set v := Ψ.symm (Pi.single k 1) with hv
  have hHk : Hop (A := ℚ_[p]) wt' (Pi.single k 1) =
      ((wt' k : ℤ) : ℚ_[p]) • (Pi.single k 1 : κ → ℚ_[p]) := by
    funext k'; by_cases hk : k' = k
    · subst hk; simp
    · simp [hk]
  have key : Hop (A := ℚ_[p]) wt v = ((wt' k : ℤ) : ℚ_[p]) • v := by
    apply Ψ.injective
    have := LinearMap.congr_fun hH v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [this, hv, LinearEquiv.apply_symm_apply, hHk, map_smul, LinearEquiv.apply_symm_apply]
  intro i hi
  have := congrFun key i
  rw [DPLattice.Hop_apply, Pi.smul_apply, smul_eq_mul] at this
  have hne : ((wt i : ℤ) : ℚ_[p]) - ((wt' k : ℤ) : ℚ_[p]) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hi
  have h2 : (((wt i : ℤ) : ℚ_[p]) - ((wt' k : ℤ) : ℚ_[p])) * v i = 0 := by rw [sub_mul, this, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left hne

/-! ### `Lx x = Lx 0` for integral `x` -/

lemma Lx_eq_Lx_zero {L M : ℕ} (r : ℕ) (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) :
    Lx p L M r x = Lx p L M r 0 := by
  have hc : ∀ j : ℕ, ‖x * ((j + r).choose j : ℚ_[p])‖ ≤ 1 := fun j => by
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one ℚ_[p] _)
  have hs : ∀ j : Fin (M + 1), stilde p L M r x j =
      stilde p L M r 0 j + (x * (((j : ℕ) + r).choose j : ℚ_[p])) • ell p L M ((j : ℕ) + r) := by
    intro j
    unfold stilde
    rw [if_pos (Nat.le_of_lt_succ j.2), if_pos (Nat.le_of_lt_succ j.2)]
    simp
  apply le_antisymm
  · rw [Lx, Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ell_mem_Lx r 0 i
    · show stilde p L M r x (j : ℕ) ∈ Lx p L M r 0
      rw [hs j]
      exact Submodule.add_mem _ (stilde_mem_Lx r 0 j) (smul_ell_mem r 0 _ (hc j) _)
  · rw [Lx, Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ell_mem_Lx r x i
    · have : stilde p L M r 0 j = stilde p L M r x j -
          (x * (((j : ℕ) + r).choose j : ℚ_[p])) • ell p L M ((j : ℕ) + r) := by
        rw [hs j]; abel
      show stilde p L M r 0 (j : ℕ) ∈ Lx p L M r x
      rw [this]
      exact Submodule.sub_mem _ (stilde_mem_Lx r x j) (smul_ell_mem r x _ (hc j) _)

/-! ### The common facts about `Ψ⁻¹` -/

lemma PsiCG_symm_F {l : ℕ} (hl : 1 ≤ l) (t : ℕ) (w : Fin 2 × Fin (l + 1) → ℚ_[p]) :
    (PsiCG p l hl).symm (FW l t w) = Fop p (l + 1) (l - 1) t ((PsiCG p l hl).symm w) := by
  apply (PsiCG p l hl).injective
  rw [LinearEquiv.apply_symm_apply, PsiCG_apply, ← LinearMap.comp_apply, PsiLin_F hl,
    LinearMap.comp_apply, ← PsiCG_apply hl, LinearEquiv.apply_symm_apply]

lemma PsiCG_symm_E {l : ℕ} (hl : 1 ≤ l) (t : ℕ) (w : Fin 2 × Fin (l + 1) → ℚ_[p]) :
    (PsiCG p l hl).symm (EW l t w) = Eop p (l + 1) (l - 1) t ((PsiCG p l hl).symm w) := by
  apply (PsiCG p l hl).injective
  rw [LinearEquiv.apply_symm_apply, PsiCG_apply, ← LinearMap.comp_apply, PsiLin_E hl,
    LinearMap.comp_apply, ← PsiCG_apply hl, LinearEquiv.apply_symm_apply]

lemma PsiCG_symm_wt {l : ℕ} (hl : 1 ≤ l) (k : Fin 2 × Fin (l + 1)) :
    InWt (Glue.wt (l + 1) (l - 1)) (tensorWt (weylWt l) k) ((PsiCG p l hl).symm (Pi.single k 1)) :=
  symm_wt (PsiCG p l hl) (fun y k hyk => PsiLin_wt hl y k hyk) k

/-- `w` lies in the standard lattice of `W` iff `Ψ⁻¹ w ∈ Lx (1/(l+1))` (from (G2)). -/
lemma mem_std_iff {l : ℕ} (hl : 1 ≤ l) (w : Fin 2 × Fin (l + 1) → ℚ_[p]) :
    w ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin 2 × Fin (l + 1))) ↔
      (PsiCG p l hl).symm w ∈ Lx p (l + 1) (l - 1) 1 (1 / ((l : ℚ_[p]) + 1)) := by
  rw [← G2_PsiLin hl]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : (PsiCG p l hl).symm (PsiLin p l u) = u := by
      rw [← PsiCG_apply hl, LinearEquiv.symm_apply_apply]
    rw [LinearMap.restrictScalars_apply, this]; exact hu
  · intro h
    refine ⟨_, h, ?_⟩
    rw [LinearMap.restrictScalars_apply, ← PsiCG_apply hl, LinearEquiv.apply_symm_apply]

lemma tensorV_models_F (l : ℕ) :
    Models (tensorV (delta ℤ_[p] l)).Fd (fun t => FW (p := p) l t) :=
  tensor_models_F (delta_models_F l)

lemma tensorV_models_E (l : ℕ) :
    Models (tensorV (delta ℤ_[p] l)).Ed (fun t => EW (p := p) l t) :=
  tensor_models_E (delta_models_E l)

/-! ### (G3) -/

lemma norm_inv_succ_le {l : ℕ} (h : ¬ p ∣ l + 1) : ‖1 / ((l : ℚ_[p]) + 1)‖ ≤ 1 := by
  have h1 : ‖((l + 1 : ℕ) : ℤ_[p])‖ = 1 := by
    rw [PadicInt.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd Fact.out]; exact h
  have h2 : ‖((l : ℚ_[p]) + 1)‖ = 1 := by
    rw [PadicInt.norm_def] at h1; push_cast at h1; exact h1
  rw [norm_div, norm_one, h2]; simp

/-- **(G3)** If `l ≥ 1` and `p ∤ l + 1`, then `V ⊗ Δ(l) ≅ Δ(l + 1) ⊕ Δ(l − 1)` over `ℤ_[p]`. -/
theorem G3 {l : ℕ} (hl : 1 ≤ l) (hpl : ¬ p ∣ l + 1) :
    Nonempty (Iso (tensorV (delta ℤ_[p] l)) (dsum (delta ℤ_[p] (l + 1)) (delta ℤ_[p] (l - 1)))) := by
  have hLx := Lx_eq_Lx_zero (L := l + 1) (M := l - 1) 1 _ (norm_inv_succ_le hpl)
  refine iso_of_model padic_algebraMap_injective (tensorV_models_F l) (tensorV_models_E l)
    (blk_models (delta_models_F (l + 1)) (delta_models_F (l - 1)))
    (blk_models (delta_models_E (l + 1)) (delta_models_E (l - 1))) (PsiCG p l hl).symm
    ?_ ?_ ?_ ?_
  · intro t; refine LinearMap.ext fun w => ?_
    show (PsiCG p l hl).symm (FW l t w) = blk (deltaF (l + 1) t) (deltaF (l - 1) t) _
    rw [PsiCG_symm_F, Fop_eq_blk]; rfl
  · intro t; refine LinearMap.ext fun w => ?_
    show (PsiCG p l hl).symm (EW l t w) = blk (deltaE (l + 1) t) (deltaE (l - 1) t) _
    rw [PsiCG_symm_E, Eop_eq_blk]; rfl
  · intro k y hky
    refine PsiCG_symm_wt hl k y ?_
    intro h; apply hky; rw [glue_wt_eq] at h; exact h.symm
  · intro w
    show w ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin 2 × Fin (l + 1))) ↔
      (PsiCG p l hl).symm w ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Idx (l + 1) (l - 1)))
    rw [mem_std_iff hl, hLx, mem_range_coeL_iff, mem_Lx_zero_iff]

/-! ### (G4) -/

/-- The general form of (G4): `V ⊗ Δ(l) ≅ glueDP (l + 1) (l − 1) 1 (1/(l + 1))`. -/
theorem iso_tensor_glueDP {l L M : ℕ} (hl : 1 ≤ l) (hL : L = l + 1) (hM : M = l - 1) (x : ℚ_[p])
    (hx : x = 1 / ((l : ℚ_[p]) + 1)) (h : GlueOK p L M 1 x) :
    Nonempty (Iso (tensorV (delta ℤ_[p] l)) (glueDP p L M 1 x h)) := by
  subst hL hM hx
  refine iso_of_model padic_algebraMap_injective (tensorV_models_F l) (tensorV_models_E l)
    (glueDP_models_F 1 _ h) (glueDP_models_E 1 _ h)
    ((PsiCG p l hl).symm.trans (PhiE p (l + 1) (l - 1) 1 (1 / ((l : ℚ_[p]) + 1)))) ?_ ?_ ?_ ?_
  · intro t; refine LinearMap.ext fun w => ?_
    show Phi p (l + 1) (l - 1) 1 _ ((PsiCG p l hl).symm (FW l t w)) =
      Phi p (l + 1) (l - 1) 1 _ (Fop p (l + 1) (l - 1) t
        (Psi p (l + 1) (l - 1) 1 _ (Phi p (l + 1) (l - 1) 1 _ ((PsiCG p l hl).symm w))))
    rw [Psi_Phi, PsiCG_symm_F]
  · intro t; refine LinearMap.ext fun w => ?_
    show Phi p (l + 1) (l - 1) 1 _ ((PsiCG p l hl).symm (EW l t w)) =
      Phi p (l + 1) (l - 1) 1 _ (Eop p (l + 1) (l - 1) t
        (Psi p (l + 1) (l - 1) 1 _ (Phi p (l + 1) (l - 1) 1 _ ((PsiCG p l hl).symm w))))
    rw [Psi_Phi, PsiCG_symm_E]
  · intro k y hky
    exact inWt_Phi 1 _ (Or.inr (by omega)) (PsiCG_symm_wt hl k) y (fun h => hky h.symm)
  · intro w
    show w ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin 2 × Fin (l + 1))) ↔
      Phi p (l + 1) (l - 1) 1 _ ((PsiCG p l hl).symm w) ∈
        LinearMap.range (coeL ℤ_[p] ℚ_[p] (Idx (l + 1) (l - 1)))
    rw [mem_std_iff hl, mem_Lx_iff, mem_range_coeL_iff]

omit [Fact p.Prime] in
lemma glueHyp_one_zero (hp : 2 ≤ p) : GlueHyp p 1 0 := ⟨le_rfl, by omega, by omega, by omega⟩

omit [Fact p.Prime] in
lemma nu_one_zero : nu p 1 0 = 1 := by
  unfold nu; rw [if_neg (by omega)]

/-- **(G4)** `V ⊗ Δ(p − 1) ≅ Tglue p 1 0` over `ℤ_[p]` (`p ≠ 2` is not needed). -/
theorem G4 : Nonempty (Iso (tensorV (delta ℤ_[p] (p - 1))) (Tglue p 1 0)) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  refine iso_tensor_glueDP (by omega) ?_ ?_ (xT p 1 0) ?_ _
  · unfold lam; omega
  · unfold mu lam; omega
  · rw [xT_of_hyp (glueHyp_one_zero hp), xzero, nu_one_zero]
    have : ((p - 1 : ℕ) : ℚ_[p]) + 1 = (p : ℚ_[p]) := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel (by omega)]
    rw [this, Nat.cast_one, zpow_neg_one, one_div]

end ColouredSand.TiltP
