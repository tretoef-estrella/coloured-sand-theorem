module

public import RequestProject.TiltRules.Main

/-!
# The splitting for `μ = 0` (`CSG4_tensor_rules.md`, (S0) and §3, Steps 1–3 with `D = 0`)

## Encoding

* `s0E : (Fin 2 → K) ≃ (Fin 2 × Fin 1 → K)` is the isomorphism `Δ(1) ≅ V ⊗ Δ(0)` over
  `K = ℚ_[p]`, `e_k ↦ b_k ⊗ e_0` (`f ↦ f ∘ Prod.fst`); `s0E_F`, `s0E_E`: it intertwines the
  divided powers.  Over `ℤ_[p]` this gives **(S0)** (`S0_iso` in `PartS.lean`).
* For `M = 0` the source space is `X₀ = Fin (L + 2) ⊕ Idx (L − 1) 1`, the space of
  `Δ(L + 1) ⊕ (Δ(L − 1) ⊕ Δ(1))` (the pieces `A` and `B ⊕ C`; there is no `D`), and
  `psiW0 = distE ∘ (PsiCG L ⊕ s0E) ∘ reidx eR0 : (X₀ → K) ≃ (Fin 2 × Idx L 0 → K)`, with
  `A_i ↦ AV i`, `B_i ↦ BV i`, `C_j ↦ CV j` (`psiW0_A`, `psiW0_B`, `psiW0_C`).
* `tensor_glue_split0`: for `L = 2 r`, `r ≥ 1`, `L + 1` a unit and `x (r + 1)` integral,
  `Δ(L + 1) ⊕ glueDP (L − 1) 1 (r − 1) (−x) ≅ V ⊗ glueDP L 0 r x` over `ℤ_[p]`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltRules

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP

variable {p : ℕ} [Fact p.Prime]

/-! ### `Δ(1) ≅ V ⊗ Δ(0)` over `K` -/

lemma deltaF_zero_apply (t : ℕ) (g : Fin (0 + 1) → ℚ_[p]) :
    deltaF 0 t g = if t = 0 then g else 0 := by
  funext m; fin_cases m
  simp only [deltaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, deltaMatF]
  split_ifs with h <;> simp_all [eq_comm]

lemma deltaE_zero_apply (t : ℕ) (g : Fin (0 + 1) → ℚ_[p]) :
    deltaE 0 t g = if t = 0 then g else 0 := by
  funext m; fin_cases m
  simp only [deltaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, deltaMatE]
  split_ifs with h <;> simp_all

lemma deltaF_one_apply (t : ℕ) (f : Fin (1 + 1) → ℚ_[p]) (m : Fin (1 + 1)) :
    deltaF 1 t f m = if t = 0 then f m else if t = 1 ∧ (m : ℕ) = 1 then f 0 else 0 := by
  fin_cases m <;>
  · simp only [deltaF, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, deltaMatF]
    rcases t with _ | _ | t <;> simp <;> omega

lemma deltaE_one_apply (t : ℕ) (f : Fin (1 + 1) → ℚ_[p]) (m : Fin (1 + 1)) :
    deltaE 1 t f m = if t = 0 then f m else if t = 1 ∧ (m : ℕ) = 0 then f 1 else 0 := by
  fin_cases m <;>
  · simp only [deltaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, deltaMatE]
    rcases t with _ | _ | t <;> simp

variable (p) in
/-- `Δ(1) ≅ V ⊗ Δ(0)` over `K`: `e_k ↦ b_k ⊗ e_0`. -/
def s0E : (Fin (1 + 1) → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 2 × Fin (0 + 1) → ℚ_[p]) :=
  reidx p (Equiv.prodUnique (Fin 2) (Fin 1) : Fin 2 × Fin (0 + 1) ≃ Fin 2)

@[simp] lemma s0E_apply (f : Fin (1 + 1) → ℚ_[p]) (q : Fin 2 × Fin (0 + 1)) :
    s0E p f q = f q.1 := rfl

lemma s0E_F (t : ℕ) (f : Fin (1 + 1) → ℚ_[p]) :
    s0E p (deltaF 1 t f) = tensorFd (deltaF 0) t (s0E p f) := by
  funext ⟨e, k⟩
  fin_cases k
  rw [s0E_apply, deltaF_one_apply]
  simp only [tensorFd, LinearMap.add_apply, LinearMap.comp_apply, bvec_apply, Pi.add_apply]
  rcases t with _ | _ | t <;> fin_cases e <;>
    simp [deltaF_zero_apply, pred, slice_apply]

lemma s0E_E (t : ℕ) (f : Fin (1 + 1) → ℚ_[p]) :
    s0E p (deltaE 1 t f) = tensorEd (deltaE 0) t (s0E p f) := by
  funext ⟨e, k⟩
  fin_cases k
  rw [s0E_apply, deltaE_one_apply]
  simp only [tensorEd, LinearMap.add_apply, LinearMap.comp_apply, bvec_apply, Pi.add_apply]
  rcases t with _ | _ | t <;> fin_cases e <;>
    simp [deltaE_zero_apply, pred, slice_apply]

/-! ### The splitting map for `μ = 0` -/

/-- Reordering `(A ⊕ B) ⊕ C ≃ A ⊕ (B ⊕ C)`. -/
def eR0 (L : ℕ) : (Idx (L + 1) (L - 1) ⊕ Fin (1 + 1)) ≃ (Fin (L + 1 + 1) ⊕ Idx (L - 1) 1) where
  toFun
    | .inl (.inl a) => .inl a
    | .inl (.inr b) => .inr (.inl b)
    | .inr c => .inr (.inr c)
  invFun
    | .inl a => .inl (.inl a)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr c) => .inr c
  left_inv := by rintro ((a | b) | c) <;> rfl
  right_inv := by rintro (a | (b | c)) <;> rfl

variable (p) in
/-- The splitting map `A ⊕ B ⊕ C → V ⊗ (Δ(L) ⊕ Δ(0))` for `μ = 0`. -/
def psiW0 (L : ℕ) (hL : 1 ≤ L) :
    (Fin (L + 1 + 1) ⊕ Idx (L - 1) 1 → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 2 × Idx L 0 → ℚ_[p]) :=
  (reidx p (eR0 L)).trans ((blkEquiv (PsiCG p L hL) (s0E p)).trans
    (distE p (Fin (L + 1)) (Fin (0 + 1))))

lemma reidx_eR0_blk {L : ℕ} (F1 : Module.End ℚ_[p] (Fin (L + 1 + 1) → ℚ_[p]))
    (F3 : Module.End ℚ_[p] (Fin (L - 1 + 1) → ℚ_[p]))
    (F4 : Module.End ℚ_[p] (Fin (1 + 1) → ℚ_[p]))
    (z : Fin (L + 1 + 1) ⊕ Idx (L - 1) 1 → ℚ_[p]) :
    reidx p (eR0 L) (blk F1 (blk F3 F4) z) = blk (blk F1 F3) F4 (reidx p (eR0 L) z) := by
  funext y; rcases y with ((a | b) | c) <;> rfl

lemma psiW0_F {L : ℕ} (hL : 1 ≤ L) (t : ℕ) (z : Fin (L + 1 + 1) ⊕ Idx (L - 1) 1 → ℚ_[p]) :
    psiW0 p L hL (blk (deltaF (L + 1) t) (Fop p (L - 1) 1 t) z) =
      tensorFd (Fop p L 0) t (psiW0 p L hL z) := by
  have hFL : Fop p L 0 = fun t => blk (deltaF L t) (deltaF 0 t) := funext (Fop_eq_blk p L 0)
  simp only [psiW0, LinearEquiv.trans_apply]
  rw [Fop_eq_blk, reidx_eR0_blk, ← Fop_eq_blk,
    blkEquiv_blk _ _ _ _ (tensorFd (deltaF L) t) (tensorFd (deltaF 0) t)
      (fun v => PsiCG_F hL t v) (fun v => s0E_F t v),
    distE_tensorFd, hFL]

lemma psiW0_E {L : ℕ} (hL : 1 ≤ L) (t : ℕ) (z : Fin (L + 1 + 1) ⊕ Idx (L - 1) 1 → ℚ_[p]) :
    psiW0 p L hL (blk (deltaE (L + 1) t) (Eop p (L - 1) 1 t) z) =
      tensorEd (Eop p L 0) t (psiW0 p L hL z) := by
  have hEL : Eop p L 0 = fun t => blk (deltaE L t) (deltaE 0 t) := funext (Eop_eq_blk p L 0)
  simp only [psiW0, LinearEquiv.trans_apply]
  rw [Eop_eq_blk, reidx_eR0_blk, ← Eop_eq_blk,
    blkEquiv_blk _ _ _ _ (tensorEd (deltaE L) t) (tensorEd (deltaE 0) t)
      (fun v => PsiCG_E hL t v) (fun v => s0E_E t v),
    distE_tensorEd, hEL]

lemma psiW0_A {L : ℕ} (hL : 1 ≤ L) (i : ℕ) :
    psiW0 p L hL (inlL (eN p (L + 1) i)) = AV p L 0 i := by
  have h1 : reidx p (eR0 L) (inlL (eN p (L + 1) i)) = inlL (ell p (L + 1) (L - 1) i) := by
    funext y; rcases y with ((a | b) | c)
    · show eN p (L + 1) i a = ell p (L + 1) (L - 1) i (.inl a)
      rw [ell_inl, eN_apply]
    · show (0 : ℚ_[p]) = ell p (L + 1) (L - 1) i (.inr b)
      rw [ell_inr]
    · rfl
  simp only [psiW0, LinearEquiv.trans_apply]
  rw [h1, blkEquiv_inlL, PsiCG_apply, PsiLin_ell, dist_inl_PsiL]

lemma psiW0_B {L : ℕ} (hL : 1 ≤ L) (i : ℕ) :
    psiW0 p L hL (inrL (ell p (L - 1) 1 i)) = BV p L 0 i := by
  have h1 : reidx p (eR0 L) (inrL (ell p (L - 1) 1 i)) = inlL (ess p (L + 1) (L - 1) i) := by
    funext y; rcases y with ((a | b) | c)
    · show (0 : ℚ_[p]) = ess p (L + 1) (L - 1) i (.inl a)
      rw [ess_inl]
    · show ell p (L - 1) 1 i (.inl b) = ess p (L + 1) (L - 1) i (.inr b)
      rw [ell_inl, ess_inr]
    · show ell p (L - 1) 1 i (.inr c) = 0
      rw [ell_inr]
  simp only [psiW0, LinearEquiv.trans_apply]
  rw [h1, blkEquiv_inlL, PsiCG_apply, PsiLin_ess hL, dist_inl_PsiS]

lemma ess_zero_of_pos {L j : ℕ} (hj : 1 ≤ j) : ess p L 0 j = 0 := by
  unfold ess; rw [dif_neg (by omega)]

lemma s0E_eN (j : ℕ) :
    s0E p (eN p 1 j) = if j = 0 then bvec 0 (eN p 0 0) else if j = 1 then bvec 1 (eN p 0 0)
      else 0 := by
  funext ⟨e, k⟩
  fin_cases k
  rw [s0E_apply, eN_apply]
  fin_cases e <;> split_ifs <;> simp_all [eN_apply]

lemma psiW0_C {L : ℕ} (hL : 1 ≤ L) (j : ℕ) :
    psiW0 p L hL (inrL (ess p (L - 1) 1 j)) = CV p L 0 j := by
  have h1 : reidx p (eR0 L) (inrL (ess p (L - 1) 1 j)) = inrL (eN p 1 j) := by
    funext y; rcases y with ((a | b) | c)
    · rfl
    · show ess p (L - 1) 1 j (.inl b) = 0
      rw [ess_inl]
    · show ess p (L - 1) 1 j (.inr c) = eN p 1 j c
      rw [ess_inr, eN_apply]
  simp only [psiW0, LinearEquiv.trans_apply]
  rw [h1, blkEquiv_inrL, s0E_eN]
  unfold CV
  have hz : ∀ k, 1 ≤ k → ess p L 0 k = 0 := fun k hk => ess_zero_of_pos hk
  rcases j with _ | _ | j
  · rw [if_pos rfl, distE_inr_bvec, inrL_eN, if_neg (by omega), add_zero]
  · simp only [Nat.zero_add, show ¬ ((1 : ℕ) = 0) from by omega, if_false, if_true, le_refl,
      Nat.sub_self]
    rw [distE_inr_bvec, inrL_eN, hz 1 le_rfl]
    simp only [LinearMap.map_zero, zero_add]
  · simp only [show ¬ (j + 1 + 1 = 0) from by omega, show ¬ (j + 1 + 1 = 1) from by omega,
      if_false, show 1 ≤ j + 1 + 1 from by omega, if_true, Nat.add_sub_cancel,
      hz (j + 1 + 1) (by omega), hz (j + 1) (by omega), map_zero, add_zero]

/-! ### The splitting for `μ = 0` over `ℤ_[p]` -/

lemma eN_mem_range (l k : ℕ) : eN p l k ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin (l + 1))) :=
  ⟨fun m => if (m : ℕ) = k then 1 else 0, by
    funext m; rw [coeL_apply, eN_apply]; split_ifs <;> simp⟩

lemma single_zero_eq_eN (l : ℕ) : (Pi.single 0 1 : Fin (l + 1) → ℚ_[p]) = eN p l 0 := by
  simpa using (eN_fin (p := p) l 0).symm

section checks0

variable {L r : ℕ} {x : ℚ_[p]}

lemma img0_A0 :
    slice 0 (AV p L 0 0) ∈ Lx p L 0 r x ∧ slice 1 (AV p L 0 0) ∈ Lx p L 0 r x := by
  rw [slice0_AV, slice1_AV, if_neg (by omega)]
  exact ⟨ell_mem_Lx r x 0, Submodule.zero_mem _⟩

lemma pre0_00 : AV p L 0 0 = bvec 0 (ell p L 0 0) := by
  unfold AV; rw [if_neg (by omega), add_zero]

lemma pre0_11 (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) :
    (x * ((r : ℚ_[p]) + 1) / ((L : ℚ_[p]) + 1)) • AV p L 0 (r + 1) +
      (CV p L 0 1 + x • BV p L 0 r) = bvec 1 (stilde p L 0 r x 0) := by
  have hL0 : (L : ℚ_[p]) + 1 ≠ 0 := by intro h; rw [h, norm_zero] at hL1; exact zero_ne_one hL1
  have hz : ess p L 0 1 = 0 := ess_zero_of_pos le_rfl
  apply ext_slice
  · simp only [map_add, map_smul, slice0_AV, slice0_CV, slice0_BV, slice0_bvec1, hz]
    match_scalars
    field_simp; ring
  · simp only [map_add, map_smul, slice1_AV, slice1_CV, slice1_BV, slice_bvec_self,
      if_pos (show 1 ≤ r + 1 by omega), if_pos (le_refl 1), Nat.add_sub_cancel, Nat.sub_self]
    rw [stilde_zero']
    match_scalars <;> field_simp
    ring

lemma mem0_11 (hr : 1 ≤ r) (hx : ‖x * ((r : ℚ_[p]) + 1)‖ ≤ 1) :
    ess p (L - 1) 1 1 + x • ell p (L - 1) 1 r ∈ Lx p (L - 1) 1 (r - 1) (-x) := by
  have hrc : ((r - 1 : ℕ) : ℚ_[p]) = r - 1 := by rw [Nat.cast_sub hr]; simp
  have hr' : r - 1 + 1 = r := by omega
  have e : ess p (L - 1) 1 1 + x • ell p (L - 1) 1 r =
      (1 : ℚ_[p]) • stilde p (L - 1) 1 (r - 1) (-x) 1 +
        (x * ((r : ℚ_[p]) + 1)) • ell p (L - 1) 1 r := by
    rw [stilde_one' _ _ le_rfl, hr', hrc]
    match_scalars <;> ring
  rw [e]
  exact mem_Lx_comb (by simp) hx 1 r

end checks0

/-- **The splitting for `μ = 0`** (`CSG4_tensor_rules.md`, §3, Steps 1–3 with `D = 0`).  Let
`L = 2 r`, `r ≥ 1`, with `L + 1` a unit of `ℤ_[p]` and `x (r + 1)` integral.  Then
`Δ(L + 1) ⊕ glueDP (L − 1) 1 (r − 1) (−x) ≅ V ⊗ glueDP L 0 r x` as DP-lattices over `ℤ_[p]`. -/
theorem tensor_glue_split0 {L r : ℕ} {x : ℚ_[p]} (hLr : L = 2 * r) (hr : 1 ≤ r)
    (hL1 : ‖(L : ℚ_[p]) + 1‖ = 1) (hx : ‖x * ((r : ℚ_[p]) + 1)‖ ≤ 1) (h : GlueOK p L 0 r x)
    (h2 : GlueOK p (L - 1) 1 (r - 1) (-x)) :
    Nonempty (Iso (dsum (delta ℤ_[p] (L + 1)) (glueDP p (L - 1) 1 (r - 1) (-x) h2))
      (tensorV (glueDP p L 0 r x h))) := by
  have hL : 1 ≤ L := by omega
  have hLM : L = 0 + 2 * r := by omega
  have hx' : ‖x * (((0 : ℕ) : ℚ_[p]) + r + 1)‖ ≤ 1 := by simpa using hx
  set U := untwDsum (untwDelta p (L + 1)) (untwGlue p (L - 1) 1 (r - 1) (-x) h2)
  set W := untwTensor (untwGlue p L 0 r x h)
  refine iso_of_untw U W (psiW0 p L hL) (fun t z => psiW0_F hL t z)
    (fun t z => psiW0_E hL t z) ?_
  refine lat_of_gen (psiW0 p L hL) (fun t z => psiW0_F hL t z) W.stabF U.stabF
    (isGen_dsum (isGen_delta (L + 1))
      (isGen_glue (L - 1) 1 (r - 1) (-x) (by omega)))
    (isGen_tensor (isGen_glue L 0 r x hLM)) ?_ ?_
  · rintro (i | i)
    · show slice 0 (psiW0 p L hL (inlL (Pi.single 0 1))) ∈ Lx p L 0 r x ∧
        slice 1 (psiW0 p L hL (inlL (Pi.single 0 1))) ∈ Lx p L 0 r x
      rw [single_zero_eq_eN, psiW0_A]; exact img0_A0
    fin_cases i
    · show slice 0 (psiW0 p L hL (inrL (ell p (L - 1) 1 0))) ∈ Lx p L 0 r x ∧
        slice 1 (psiW0 p L hL (inrL (ell p (L - 1) 1 0))) ∈ Lx p L 0 r x
      rw [psiW0_B]; exact img_B0v hL1
    · show slice 0 (psiW0 p L hL (inrL (stilde p (L - 1) 1 (r - 1) (-x) 0))) ∈ Lx p L 0 r x ∧
        slice 1 (psiW0 p L hL (inrL (stilde p (L - 1) 1 (r - 1) (-x) 0))) ∈ Lx p L 0 r x
      rw [stilde_zero', map_add, map_smul, map_add, map_smul, psiW0_C, psiW0_B]
      exact img_B1v hLM hr hL1 hx'
  · rintro ⟨e, i⟩; fin_cases e <;> fin_cases i
    · refine ⟨Sum.elim (eN p (L + 1) 0) 0, ?_, ?_⟩
      · exact (mem_untwDsum _ _ _).2 ⟨eN_mem_range (p := p) (L + 1) 0, Submodule.zero_mem _⟩
      · show _ = bvec 0 (ell p L 0 0)
        rw [Sum_elim_eq, map_zero, add_zero, psiW0_A, pre0_00]
    · refine ⟨Sum.elim ((x * (((0 : ℕ) : ℚ_[p]) + r + 1) / ((L : ℚ_[p]) + 1)) • eN p (L + 1) r)
        (stilde p (L - 1) 1 (r - 1) (-x) 0), ?_, ?_⟩
      · exact (mem_untwDsum _ _ _).2
          ⟨smul_mem_of_norm (by rw [norm_div_unit hL1]; exact hx') (eN_mem_range _ _),
            stilde_mem_Lx _ _ 0⟩
      · show _ = bvec 0 (stilde p L 0 r x 0)
        rw [← pre_01v hLM hr hL1, Sum_elim_eq, stilde_zero']
        simp only [map_add, map_smul, psiW0_A, psiW0_B, psiW0_C]
    · refine ⟨Sum.elim ((1 / ((L : ℚ_[p]) + 1)) • eN p (L + 1) 1) (ell p (L - 1) 1 0), ?_, ?_⟩
      · exact (mem_untwDsum _ _ _).2
          ⟨smul_mem_of_norm (norm_one_div_unit hL1).le (eN_mem_range _ _), ell_mem_Lx _ _ 0⟩
      · show _ = bvec 1 (ell p L 0 0)
        rw [← pre_10v (M := 0) hL1, Sum_elim_eq]
        simp only [map_add, map_smul, psiW0_A, psiW0_B]
    · refine ⟨Sum.elim ((x * ((r : ℚ_[p]) + 1) / ((L : ℚ_[p]) + 1)) • eN p (L + 1) (r + 1))
        (ess p (L - 1) 1 1 + x • ell p (L - 1) 1 r), ?_, ?_⟩
      · exact (mem_untwDsum _ _ _).2
          ⟨smul_mem_of_norm (by rw [norm_div_unit hL1]; exact hx) (eN_mem_range _ _), mem0_11 hr hx⟩
      · show _ = bvec 1 (stilde p L 0 r x 0)
        rw [← pre0_11 hL1, Sum_elim_eq]
        simp only [map_add, map_smul, psiW0_A, psiW0_B, psiW0_C]

end ColouredSand.TiltRules
