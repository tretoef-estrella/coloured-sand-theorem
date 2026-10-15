module

public import RequestProject.TiltP.Descent

/-!
# The glued lattice as a DP-lattice: general construction (CSG3, Part T, (T1)–(T2))

This file proves, for general `L, M, r, x`, the statements (T1) and (T2) of
`CSG3_tilting_lattices_and_clebsch_gordan.md`; the specialisation to `Tglue p r a` is in
`RequestProject/TiltP/Tglue.lean`.

## Encoding

* `V p L M = Idx L M → ℚ_[p]`, `Idx L M = Fin (L + 1) ⊕ Fin (M + 1)` (from the attached Glue files;
  `inl i ↔ ℓ_i`, `inr j ↔ s_j`), with the operators `Fop`, `Eop` of the Glue files.
* `Fop_eq_blk`, `Eop_eq_blk`: over `ℚ_[p]`, `Fop t`, `Eop t` are the divided powers of
  `dsum (delta ℚ_[p] L) (delta ℚ_[p] M)` (the hint of (T1)), hence `isDP_V`.
* `PhiE p L M r x : V ≃ₗ[ℚ_[p]] V` is the untwisting map `Phi` of the Glue files (inverse `Psi`):
  it sends `ℓ_i ↦ ℓ_i`, `s̃ x j ↦ s_j`, i.e. it is the change of coordinates to the basis
  `glueBasis p L M r x` of `Lx p L M r x`.
* `GlueOK p L M r x`: `x = 0` or `L = M + 2 r` (so that `s̃ x j` is a weight vector), and
  `Lx p L M r x` is stable under every `F t`, `E t` (including `t = 0`).
* `glueOp T` is the matrix, in `glueBasis`, of the restriction of a `ℚ_[p]`-linear `T` to `Lx`:
  `v ↦` coordinates of `T (Σ_y v y • b y)`.  `glueDP p L M r x h` is the DP-lattice with basis
  `Idx L M`, weights `wt (inl i) = L − 2i`, `wt (inr j) = M − 2j`, `Fd t = glueOp (Fop t)`,
  `Ed t = glueOp (Eop t)`; (W), (P0), (P1), (K) are proved by conjugation by `PhiE` and descent
  from `ℚ_[p]` to `ℤ_[p]`.
* (T2): `glueF : Hom (delta ℤ_[p] L) (glueDP …)` is `e_i ↦ δ_{inl i}` (`Lemma35.inlL`) and
  `glueG : Hom (glueDP …) (delta ℤ_[p] M)` is `δ_{inl i} ↦ 0`, `δ_{inr j} ↦ e_j`
  (`Lemma35.sndL`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltP

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime] {L M : ℕ}

/-! ### `Fop`, `Eop` are the divided powers of `Δ(L) ⊕ Δ(M)` over `ℚ_[p]` -/

private lemma sum_ite_single {n : ℕ} (u : Fin (n + 1) → ℚ_[p]) (c : ℕ → ℚ_[p]) (k : ℕ)
    (P : ℕ → ℕ → Prop) [∀ a b, Decidable (P a b)] (hP : ∀ a b, P a b ↔ a = b + k) (i' : ℕ) :
    ∑ r : Fin (n + 1), (if P i' r then c r else 0) * u r =
      if k ≤ i' then c (i' - k) * (if h : i' - k < n + 1 then u ⟨i' - k, h⟩ else 0) else 0 := by
  split_ifs with h1 h2
  · rw [Finset.sum_eq_single ⟨i' - k, h2⟩]
    · rw [if_pos ((hP _ _).2 (by simp; omega))]
    · intro b _ hb; rw [if_neg]; · simp
      rw [hP]; intro h; apply hb; ext; simp; omega
    · simp
  · rw [mul_zero]; apply Finset.sum_eq_zero; intro b _; rw [if_neg]; · simp
    rw [hP]; intro h; have := b.2; omega
  · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; · simp
    rw [hP]; omega

variable (p L M) in
/-- (T1, hint) `F t` on `V` is the divided power `F^{(t)}` of `Δ(λ) ⊕ Δ(μ)` over `ℚ_[p]`. -/
theorem Fop_eq_blk (t : ℕ) : Fop p L M t = blk (deltaF L t) (deltaF M t) := by
  refine LinearMap.ext fun v => funext fun z => ?_
  rcases z with i' | j'
  · rw [Fop_inl, blk_inl, deltaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    simp only [deltaMatF, Function.comp]
    rw [sum_ite_single (fun r => v (.inl r)) (fun r => ((r + t).choose t : ℚ_[p])) t
      (fun a b => a = b + t) (fun _ _ => Iff.rfl)]
    split_ifs with h1 h2
    · rw [show (i' : ℕ) - t + t = i' by omega, cL, dif_pos (by omega)]
    · omega
    · rfl
  · rw [Fop_inr, blk_inr, deltaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    simp only [deltaMatF, Function.comp]
    rw [sum_ite_single (fun r => v (.inr r)) (fun r => ((r + t).choose t : ℚ_[p])) t
      (fun a b => a = b + t) (fun _ _ => Iff.rfl)]
    split_ifs with h1 h2
    · rw [show (j' : ℕ) - t + t = j' by omega, cR, dif_pos (by omega)]
    · omega
    · rfl

private lemma sum_ite_single' {n : ℕ} (u : Fin (n + 1) → ℚ_[p]) (c : ℕ → ℚ_[p]) (k : ℕ)
    (i' : ℕ) :
    ∑ r : Fin (n + 1), (if i' + k = (r : ℕ) then c r else 0) * u r =
      c (i' + k) * (if h : i' + k < n + 1 then u ⟨i' + k, h⟩ else 0) := by
  split_ifs with h2
  · rw [Finset.sum_eq_single ⟨i' + k, h2⟩]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg]; · simp
      intro h; apply hb; ext; simp; omega
    · simp
  · rw [mul_zero]; apply Finset.sum_eq_zero; intro b _; rw [if_neg]; · simp
    have := b.2; omega

variable (p L M) in
/-- (T1, hint) `E t` on `V` is the divided power `E^{(t)}` of `Δ(λ) ⊕ Δ(μ)` over `ℚ_[p]`. -/
theorem Eop_eq_blk (t : ℕ) : Eop p L M t = blk (deltaE L t) (deltaE M t) := by
  refine LinearMap.ext fun v => funext fun z => ?_
  rcases z with i' | j'
  · rw [Eop_inl, blk_inl, deltaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    simp only [deltaMatE, Function.comp]
    rw [sum_ite_single' (fun r => v (.inl r)) (fun r => ((L - r + t).choose t : ℚ_[p])) t]
    unfold cL
    split_ifs with h1 h2 <;> first | rfl | omega
  · rw [Eop_inr, blk_inr, deltaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    simp only [deltaMatE, Function.comp]
    rw [sum_ite_single' (fun r => v (.inr r)) (fun r => ((M - r + t).choose t : ℚ_[p])) t]
    unfold cR
    split_ifs with h1 h2 <;> first | rfl | omega

/-- The weights of the Glue files are those of `Δ(λ) ⊕ Δ(μ)`. -/
lemma glue_wt_eq : Glue.wt L M = Sum.elim (weylWt L) (weylWt M) := by
  funext y; cases y <;> rfl

variable (p L M) in
/-- `Fop 0 = id`. -/
lemma Fop_zero : Fop p L M 0 = 1 := by
  rw [Fop_eq_blk]; exact (dsum (delta ℚ_[p] L) (delta ℚ_[p] M)).isDP.P0_F

variable (p L M) in
/-- `Eop 0 = id`. -/
lemma Eop_zero : Eop p L M 0 = 1 := by
  rw [Eop_eq_blk]; exact (dsum (delta ℚ_[p] L) (delta ℚ_[p] M)).isDP.P0_E

variable (p L M) in
/-- (T1, hint) `(wt, F, E)` on `V` satisfies (W), (P0), (P1), (K) over `ℚ_[p]`. -/
theorem isDP_V : IsDP (Glue.wt L M) (Fop p L M) (Eop p L M) := by
  have h := (dsum (delta ℚ_[p] L) (delta ℚ_[p] M)).isDP
  have hF : Fop p L M = fun t => blk (deltaF L t) (deltaF M t) := funext (Fop_eq_blk p L M)
  have hE : Eop p L M = fun t => blk (deltaE L t) (deltaE M t) := funext (Eop_eq_blk p L M)
  rw [hF, hE, glue_wt_eq]
  exact h

/-! ### The change of basis `Phi` -/

variable (p L M) in
/-- The untwisting isomorphism `Phi` (`ℓ_i ↦ ℓ_i`, `s̃ x j ↦ s_j`), inverse `Psi`. -/
def PhiE (r : ℕ) (x : ℚ_[p]) : V p L M ≃ₗ[ℚ_[p]] V p L M :=
  LinearEquiv.ofLinear (Phi p L M r x) (Psi p L M r x)
    (LinearMap.ext (Phi_Psi r x)) (LinearMap.ext (Psi_Phi r x))

@[simp] lemma PhiE_apply (r : ℕ) (x : ℚ_[p]) (v : V p L M) : PhiE p L M r x v = Phi p L M r x v :=
  rfl

@[simp] lemma PhiE_symm_apply (r : ℕ) (x : ℚ_[p]) (v : V p L M) :
    (PhiE p L M r x).symm v = Psi p L M r x v := rfl

lemma inWt_Psi_or_Phi (r : ℕ) (x : ℚ_[p]) (hW : x = 0 ∨ L = M + 2 * r) (σ : ℚ_[p])
    {w : ℤ} {v : V p L M} (hv : InWt (Glue.wt L M) w v) :
    InWt (Glue.wt L M) w (fun y => match y with
      | .inl i => v (.inl i) + σ * x * gl r i * cR v (i - r)
      | .inr j => v (.inr j)) := by
  intro y hy
  rcases y with i | j
  · simp only
    rw [hv _ hy, zero_add]
    rcases hW with rfl | hLM
    · simp
    · unfold gl cR
      split_ifs with h1 h2
      · rw [hv _ (by simp only [Glue.wt] at hy ⊢; push_cast [h1]; omega)]; simp
      all_goals simp
  · exact hv _ hy

lemma inWt_Psi (r : ℕ) (x : ℚ_[p]) (hW : x = 0 ∨ L = M + 2 * r) {w : ℤ} {v : V p L M}
    (hv : InWt (Glue.wt L M) w v) : InWt (Glue.wt L M) w (Psi p L M r x v) := by
  have := inWt_Psi_or_Phi r x hW 1 hv
  intro y hy; rcases y with i | j
  · have h := this (.inl i) hy; simp only [one_mul] at h; rw [Psi_inl]; exact h
  · exact this (.inr j) hy

lemma inWt_Phi (r : ℕ) (x : ℚ_[p]) (hW : x = 0 ∨ L = M + 2 * r) {w : ℤ} {v : V p L M}
    (hv : InWt (Glue.wt L M) w v) : InWt (Glue.wt L M) w (Phi p L M r x v) := by
  have := inWt_Psi_or_Phi r x hW (-1) hv
  intro y hy; rcases y with i | j
  · have h := this (.inl i) hy; rw [Phi_inl, sub_eq_add_neg]; rw [← h]; ring
  · exact this (.inr j) hy

/-! ### The general glued DP-lattice -/

variable (p L M) in
/-- The hypotheses under which the glued lattice `Lx p L M r x` gives a DP-lattice: `x = 0` or
`L = M + 2 r`, and `Lx` is stable under every `F t`, `E t`. -/
structure GlueOK (r : ℕ) (x : ℚ_[p]) : Prop where
  wt_ok : x = 0 ∨ L = M + 2 * r
  stab : ∀ t v, v ∈ Lx p L M r x → Fop p L M t v ∈ Lx p L M r x ∧ Eop p L M t v ∈ Lx p L M r x

variable (p L M) in
/-- The matrix, in `glueBasis p L M r x`, of the restriction to `Lx` of a `ℚ_[p]`-linear `T`
that preserves `Lx`. -/
def glueOp (r : ℕ) (x : ℚ_[p]) (T : V p L M →ₗ[ℚ_[p]] V p L M)
    (hT : ∀ v ∈ Lx p L M r x, T v ∈ Lx p L M r x) : Module.End ℤ_[p] (Idx L M → ℤ_[p]) :=
  (glueEquiv p L M r x).toLinearMap ∘ₗ (T.restrictScalars ℤ_[p]).restrict hT ∘ₗ
    (glueEquiv p L M r x).symm.toLinearMap

lemma coeL_eq (v : Idx L M → ℤ_[p]) :
    coeL ℤ_[p] ℚ_[p] (Idx L M) v = fun y => ((v y : ℤ_[p]) : ℚ_[p]) := by
  funext y; rw [coeL_apply, PadicInt.algebraMap_apply]

lemma coeL_glueOp (r : ℕ) (x : ℚ_[p]) (T : V p L M →ₗ[ℚ_[p]] V p L M)
    (hT : ∀ v ∈ Lx p L M r x, T v ∈ Lx p L M r x) (v : Idx L M → ℤ_[p]) :
    coeL ℤ_[p] ℚ_[p] (Idx L M) (glueOp p L M r x T hT v) =
      Phi p L M r x (T (Psi p L M r x (coeL ℤ_[p] ℚ_[p] (Idx L M) v))) := by
  rw [coeL_eq, coeL_eq]; rfl

/-- `Σ_y c y • b y = Psi (c)` for the basis `b = glueBasis p L M r x`. -/
lemma sum_glueBasis (r : ℕ) (x : ℚ_[p]) (c : Idx L M → ℤ_[p]) :
    ∑ y, c y • (glueBasis p L M r x y : V p L M) =
      Psi p L M r x (coeL ℤ_[p] ℚ_[p] (Idx L M) c) := by
  have hc : coeL ℤ_[p] ℚ_[p] (Idx L M) c = ∑ y, ((c y : ℤ_[p]) : ℚ_[p]) • (Pi.single y 1 : V p L M) := by
    rw [coeL_eq]; funext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [hc, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [glueBasis_coe, padic_smul_vec, map_smul]

variable (p L M) in
/-- **The glued DP-lattice** (general form of (T1)): basis `Idx L M`, weights
`wt (inl i) = L − 2i`, `wt (inr j) = M − 2j`, and `Fd t`, `Ed t` the matrices in
`glueBasis p L M r x` of the restrictions of `Fop t`, `Eop t` to `Lx p L M r x`. -/
def glueDP (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) : DPLattice ℤ_[p] where
  ι := Idx L M
  wt := Glue.wt L M
  Fd t := glueOp p L M r x (Fop p L M t) (fun v hv => (h.stab t v hv).1)
  Ed t := glueOp p L M r x (Eop p L M t) (fun v hv => (h.stab t v hv).2)
  isDP := by
    have hK := IsDP.conj (isDP_V p L M) (PhiE p L M r x)
      (fun _ _ hv => inWt_Phi r x h.wt_ok hv) (fun _ _ hv => inWt_Psi r x h.wt_ok hv)
    refine IsDP.descend padic_algebraMap_injective hK ?_ ?_
    · intro t v; exact coeL_glueOp r x _ _ v
    · intro t v; exact coeL_glueOp r x _ _ v

/-- The `ℚ_[p]`-model of `F^{(t)}` on `glueDP`: `Phi ∘ F t ∘ Psi`. -/
lemma glueDP_models_F (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) :
    Models (glueDP p L M r x h).Fd
      (fun t => (PhiE p L M r x).toLinearMap ∘ₗ Fop p L M t ∘ₗ (PhiE p L M r x).symm.toLinearMap) :=
  fun _ v => coeL_glueOp r x _ _ v

/-- The `ℚ_[p]`-model of `E^{(t)}` on `glueDP`: `Phi ∘ E t ∘ Psi`. -/
lemma glueDP_models_E (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) :
    Models (glueDP p L M r x h).Ed
      (fun t => (PhiE p L M r x).toLinearMap ∘ₗ Eop p L M t ∘ₗ (PhiE p L M r x).symm.toLinearMap) :=
  fun _ v => coeL_glueOp r x _ _ v

/-- (T1, general form) `Fd t v` is the coordinate vector, in the basis `b = glueBasis`, of
`F t (Σ_y v y • b y)`. -/
theorem glueDP_Fd_spec (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) (t : ℕ)
    (v : Idx L M → ℤ_[p]) :
    ∑ y, (glueDP p L M r x h).Fd t v y • (glueBasis p L M r x y : V p L M) =
      Fop p L M t (∑ y, v y • (glueBasis p L M r x y : V p L M)) := by
  rw [sum_glueBasis r x v]
  erw [sum_glueBasis r x, glueDP_models_F]
  show Psi p L M r x (Phi p L M r x (Fop p L M t (Psi p L M r x _))) = _
  rw [Psi_Phi]; rfl

/-- (T1, general form) `Ed t v` is the coordinate vector, in the basis `b = glueBasis`, of
`E t (Σ_y v y • b y)`. -/
theorem glueDP_Ed_spec (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) (t : ℕ)
    (v : Idx L M → ℤ_[p]) :
    ∑ y, (glueDP p L M r x h).Ed t v y • (glueBasis p L M r x y : V p L M) =
      Eop p L M t (∑ y, v y • (glueBasis p L M r x y : V p L M)) := by
  rw [sum_glueBasis r x v]
  erw [sum_glueBasis r x, glueDP_models_E]
  show Psi p L M r x (Phi p L M r x (Eop p L M t (Psi p L M r x _))) = _
  rw [Psi_Phi]; rfl

/-! ### Stability of `Lx 0` -/

lemma Phi_zero (r : ℕ) (v : V p L M) : Phi p L M r 0 v = v := by
  funext y; rcases y with i | j
  · rw [Phi_inl]; ring
  · rfl

lemma mem_Lx_zero_iff (r : ℕ) (v : V p L M) : v ∈ Lx p L M r 0 ↔ ∀ y, ‖v y‖ ≤ 1 := by
  rw [mem_Lx_iff, Phi_zero]

lemma norm_cL_le {v : V p L M} (hv : ∀ y, ‖v y‖ ≤ 1) (n : ℕ) : ‖cL v n‖ ≤ 1 := by
  unfold cL; split_ifs
  · exact hv _
  · simp

lemma norm_cR_le {v : V p L M} (hv : ∀ y, ‖v y‖ ≤ 1) (n : ℕ) : ‖cR v n‖ ≤ 1 := by
  unfold cR; split_ifs
  · exact hv _
  · simp

lemma norm_natCast_mul_le (n : ℕ) {z : ℚ_[p]} (hz : ‖z‖ ≤ 1) : ‖(n : ℚ_[p]) * z‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one ℚ_[p] n) (norm_nonneg _) hz

/-- `Lx p L M r 0 = Dλ ⊕ Dμ` is stable under every `F t`, `E t`. -/
lemma glueOK_zero (r : ℕ) : GlueOK p L M r 0 := by
  refine ⟨Or.inl rfl, fun t v hv => ?_⟩
  rw [mem_Lx_zero_iff] at hv
  rw [mem_Lx_zero_iff, mem_Lx_zero_iff]
  refine ⟨fun y => ?_, fun y => ?_⟩
  · rcases y with i | j
    · rw [Fop_inl]; split_ifs
      · exact norm_natCast_mul_le _ (norm_cL_le hv _)
      · simp
    · rw [Fop_inr]; split_ifs
      · exact norm_natCast_mul_le _ (norm_cR_le hv _)
      · simp
  · rcases y with i | j
    · rw [Eop_inl]; exact norm_natCast_mul_le _ (norm_cL_le hv _)
    · rw [Eop_inr]; exact norm_natCast_mul_le _ (norm_cR_le hv _)

/-! ### (T2) in general -/

/-- `Δ_{ℤ_[p]}(l)` is modelled by `Δ_{ℚ_[p]}(l)` (`F`). -/
lemma delta_models_F (l : ℕ) :
    Models (delta ℤ_[p] l).Fd (fun t => (deltaF l t : Module.End ℚ_[p] (Fin (l + 1) → ℚ_[p]))) := by
  intro t v; funext m
  show algebraMap ℤ_[p] ℚ_[p] (deltaF l t v m) = deltaF l t (coeL ℤ_[p] ℚ_[p] _ v) m
  simp only [deltaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, deltaMatF,
    coeL_apply, apply_ite, map_natCast, map_zero]

/-- `Δ_{ℤ_[p]}(l)` is modelled by `Δ_{ℚ_[p]}(l)` (`E`). -/
lemma delta_models_E (l : ℕ) :
    Models (delta ℤ_[p] l).Ed (fun t => (deltaE l t : Module.End ℚ_[p] (Fin (l + 1) → ℚ_[p]))) := by
  intro t v; funext m
  show algebraMap ℤ_[p] ℚ_[p] (deltaE l t v m) = deltaE l t (coeL ℤ_[p] ℚ_[p] _ v) m
  simp only [deltaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, deltaMatE,
    coeL_apply, apply_ite, map_natCast, map_zero]

lemma Psi_inlL (r : ℕ) (x : ℚ_[p]) (u : Fin (L + 1) → ℚ_[p]) :
    Psi p L M r x (inlL (κ := Fin (M + 1)) u) = inlL u := by
  funext y; rcases y with i | j
  · rw [Psi_inl]; unfold cR; split_ifs <;> simp
  · rfl

lemma Phi_inlL (r : ℕ) (x : ℚ_[p]) (u : Fin (L + 1) → ℚ_[p]) :
    Phi p L M r x (inlL (κ := Fin (M + 1)) u) = inlL u := by
  funext y; rcases y with i | j
  · rw [Phi_inl]; unfold cR; split_ifs <;> simp
  · rfl

lemma blk_inlL (f : Module.End ℚ_[p] (Fin (L + 1) → ℚ_[p]))
    (g : Module.End ℚ_[p] (Fin (M + 1) → ℚ_[p])) (u : Fin (L + 1) → ℚ_[p]) :
    blk f g (inlL u) = inlL (f u) := by
  funext y; rcases y with i | j
  · rfl
  · show g (fun _ => 0) j = 0
    rw [show (fun _ => (0 : ℚ_[p])) = (0 : Fin (M + 1) → ℚ_[p]) from rfl, map_zero]; rfl

variable (p L M) in
/-- (T2, general form) the morphism `f : Δ(L) → glueDP`, `e_i ↦ δ_{inl i}`. -/
def glueF (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) : Hom (delta ℤ_[p] L) (glueDP p L M r x h) :=
  homOfModel padic_algebraMap_injective (delta_models_F L) (delta_models_E L)
    (glueDP_models_F r x h) (glueDP_models_E r x h) (inlL (κ := Fin (M + 1)))
    (inlL (κ := Fin (M + 1)))
    (fun v => by
      funext y; rcases y with i | j
      · rfl
      · show algebraMap ℤ_[p] ℚ_[p] 0 = 0; simp)
    (fun t => LinearMap.ext fun u => by
      show _ = Phi p L M r x (Fop p L M t (Psi p L M r x (inlL u)))
      rw [Psi_inlL, Fop_eq_blk, blk_inlL, Phi_inlL]; rfl)
    (fun t => LinearMap.ext fun u => by
      show _ = Phi p L M r x (Eop p L M t (Psi p L M r x (inlL u)))
      rw [Psi_inlL, Eop_eq_blk, blk_inlL, Phi_inlL]; rfl)
    (fun i j hij => by
      rcases j with i' | j'
      · show (Pi.single i (1 : ℤ_[p]) : Fin (L + 1) → ℤ_[p]) i' = 0
        rw [Pi.single_apply, if_neg]; rintro rfl; exact hij rfl
      · rfl)

variable (p L M) in
/-- (T2, general form) the morphism `g : glueDP → Δ(M)`, `δ_{inl i} ↦ 0`, `δ_{inr j} ↦ e_j`. -/
def glueG (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) : Hom (glueDP p L M r x h) (delta ℤ_[p] M) :=
  homOfModel padic_algebraMap_injective (glueDP_models_F r x h) (glueDP_models_E r x h)
    (delta_models_F M) (delta_models_E M) (sndL (ι := Fin (L + 1)))
    (sndL (ι := Fin (L + 1)))
    (fun v => rfl)
    (fun t => LinearMap.ext fun u => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [Fop_eq_blk]; rfl)
    (fun t => LinearMap.ext fun u => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [Eop_eq_blk]; rfl)
    (fun i j hij => by
      rcases i with i' | j'
      · rfl
      · show (Pi.single (Sum.inr j' : Idx L M) (1 : ℤ_[p]) : Idx L M → ℤ_[p]) (Sum.inr j) = 0
        rw [Pi.single_apply, if_neg]; rintro h; cases h; exact hij rfl)

lemma glueF_toLin (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) :
    (glueF p L M r x h).toLin = inlL (κ := Fin (M + 1)) := rfl

lemma glueG_toLin (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) :
    (glueG p L M r x h).toLin = sndL (ι := Fin (L + 1)) := rfl

/-- (T2, general form) `Δ(L) → glueDP → Δ(M)` is short exact. -/
theorem glue_shortExact (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) :
    ShortExact (glueF p L M r x h) (glueG p L M r x h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v w hvw
    funext i
    exact congrFun hvw (Sum.inl i)
  · intro w
    exact ⟨inrL w, rfl⟩
  · ext z
    constructor
    · rintro ⟨v, rfl⟩
      rw [LinearMap.mem_ker]; rfl
    · intro hz
      rw [LinearMap.mem_ker] at hz
      refine ⟨z ∘ Sum.inl, ?_⟩
      funext y; rcases y with i | j
      · rfl
      · exact (congrFun hz j).symm

/-- (T2, general form) `f` and `g` are weight-preserving. -/
theorem glue_wtPres (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) :
    IsWtPres (glueF p L M r x h).toLin ∧ IsWtPres (glueG p L M r x h).toLin := by
  constructor
  · intro i j hij
    rcases j with i' | j'
    · show (Pi.single i (1 : ℤ_[p]) : Fin (L + 1) → ℤ_[p]) i' = 0
      rw [Pi.single_apply, if_neg]; rintro rfl; exact hij rfl
    · rfl
  · intro i j hij
    rcases i with i' | j'
    · rfl
    · show (Pi.single (Sum.inr j' : Idx L M) (1 : ℤ_[p]) : Idx L M → ℤ_[p]) (Sum.inr j) = 0
      rw [Pi.single_apply, if_neg]; rintro h; cases h; exact hij rfl

end ColouredSand.TiltP
