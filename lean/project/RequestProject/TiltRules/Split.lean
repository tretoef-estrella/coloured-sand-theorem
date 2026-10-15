module

public import RequestProject.TiltRules.Weyl

/-!
# The splitting map `A ⊕ D ⊕ B ⊕ C → V ⊗ (Δ(L) ⊕ Δ(M))`
(auxiliary for `CSG4_tensor_rules.md`, §3, Steps 1–3, case `M ≥ 1`)

Throughout `K = ℚ_[p]`, `1 ≤ L`, `1 ≤ M`.

## Encoding

* The source space is `X = Idx (L + 1) (M − 1) ⊕ Idx (L − 1) (M + 1)`, the space of
  `(Δ(L + 1) ⊕ Δ(M − 1)) ⊕ (Δ(L − 1) ⊕ Δ(M + 1))` (the pieces `A ⊕ D` and `B ⊕ C` of §3,
  Step 3); `inl (ell … i)` is `A_i`, `inl (ess … j)` is `D_j`, `inr (ell … i)` is `B_i`,
  `inr (ess … j)` is `C_j`.
* `eR` reorders `(A ⊕ B) ⊕ (C ⊕ D)` into `(A ⊕ D) ⊕ (B ⊕ C)`.
* `psiW p L M hL hM : (X → K) ≃ (Fin 2 × Idx L M → K)` is
  `distE ∘ (PsiCG L ⊕ PsiCG M) ∘ reidx eR`: on basis vectors
  `A_i ↦ AV i`, `B_i ↦ BV i`, `C_j ↦ CV j`, `D_j ↦ DV j` (`psiW_A`, …, `psiW_D`).
* `psiW_F`, `psiW_E`: `psiW` intertwines the blockwise `Fop`, `Eop` on `X` with the coproducts
  `tensorFd (Fop p L M)`, `tensorEd (Eop p L M)` on `V ⊗ (Δ(L) ⊕ Δ(M))`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltRules

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP

variable {p : ℕ} [Fact p.Prime]

/-- Reordering `(A ⊕ B) ⊕ (C ⊕ D) ≃ (A ⊕ D) ⊕ (B ⊕ C)`. -/
def eR (L M : ℕ) : (Idx (L + 1) (L - 1) ⊕ Idx (M + 1) (M - 1)) ≃
    (Idx (L + 1) (M - 1) ⊕ Idx (L - 1) (M + 1)) where
  toFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr b) => .inr (.inl b)
    | .inr (.inl c) => .inr (.inr c)
    | .inr (.inr d) => .inl (.inr d)
  invFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr d) => .inr (.inr d)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr c) => .inr (.inl c)
  left_inv := by rintro ((a | b) | (c | d)) <;> rfl
  right_inv := by rintro ((a | d) | (b | c)) <;> rfl

variable (p) in
/-- The splitting map `A ⊕ D ⊕ B ⊕ C → V ⊗ (Δ(L) ⊕ Δ(M))`. -/
def psiW (L M : ℕ) (hL : 1 ≤ L) (hM : 1 ≤ M) :
    (Idx (L + 1) (M - 1) ⊕ Idx (L - 1) (M + 1) → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 2 × Idx L M → ℚ_[p]) :=
  (reidx p (eR L M)).trans ((blkEquiv (PsiCG p L hL) (PsiCG p M hM)).trans
    (distE p (Fin (L + 1)) (Fin (M + 1))))

lemma reidx_eR_blk {L M : ℕ} (F1 : Module.End ℚ_[p] (Fin (L + 1 + 1) → ℚ_[p]))
    (F2 : Module.End ℚ_[p] (Fin (M - 1 + 1) → ℚ_[p]))
    (F3 : Module.End ℚ_[p] (Fin (L - 1 + 1) → ℚ_[p]))
    (F4 : Module.End ℚ_[p] (Fin (M + 1 + 1) → ℚ_[p]))
    (z : Idx (L + 1) (M - 1) ⊕ Idx (L - 1) (M + 1) → ℚ_[p]) :
    reidx p (eR L M) (blk (blk F1 F2) (blk F3 F4) z) =
      blk (blk F1 F3) (blk F4 F2) (reidx p (eR L M) z) := by
  funext y; rcases y with ((a | b) | (c | d)) <;> rfl

lemma blkEquiv_blk {ι κ ι' κ' : Type*} (e : (ι → ℚ_[p]) ≃ₗ[ℚ_[p]] (ι' → ℚ_[p]))
    (f : (κ → ℚ_[p]) ≃ₗ[ℚ_[p]] (κ' → ℚ_[p])) (F : Module.End ℚ_[p] (ι → ℚ_[p]))
    (G : Module.End ℚ_[p] (κ → ℚ_[p])) (F' : Module.End ℚ_[p] (ι' → ℚ_[p]))
    (G' : Module.End ℚ_[p] (κ' → ℚ_[p])) (hF : ∀ v, e (F v) = F' (e v))
    (hG : ∀ v, f (G v) = G' (f v)) (z : ι ⊕ κ → ℚ_[p]) :
    blkEquiv e f (blk F G z) = blk F' G' (blkEquiv e f z) := by
  funext y; rcases y with i | k
  · exact congrFun (hF (z ∘ Sum.inl)) i
  · exact congrFun (hG (z ∘ Sum.inr)) k

lemma psiW_F {L M : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M) (t : ℕ)
    (z : Idx (L + 1) (M - 1) ⊕ Idx (L - 1) (M + 1) → ℚ_[p]) :
    psiW p L M hL hM (blk (Fop p (L + 1) (M - 1) t) (Fop p (L - 1) (M + 1) t) z) =
      tensorFd (Fop p L M) t (psiW p L M hL hM z) := by
  have hFL : Fop p L M = fun t => blk (deltaF L t) (deltaF M t) := funext (Fop_eq_blk p L M)
  simp only [psiW, LinearEquiv.trans_apply]
  rw [Fop_eq_blk, Fop_eq_blk, reidx_eR_blk, ← Fop_eq_blk, ← Fop_eq_blk,
    blkEquiv_blk _ _ _ _ (tensorFd (deltaF L) t) (tensorFd (deltaF M) t)
      (fun v => PsiCG_F hL t v) (fun v => PsiCG_F hM t v),
    distE_tensorFd, hFL]

lemma psiW_E {L M : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M) (t : ℕ)
    (z : Idx (L + 1) (M - 1) ⊕ Idx (L - 1) (M + 1) → ℚ_[p]) :
    psiW p L M hL hM (blk (Eop p (L + 1) (M - 1) t) (Eop p (L - 1) (M + 1) t) z) =
      tensorEd (Eop p L M) t (psiW p L M hL hM z) := by
  have hEL : Eop p L M = fun t => blk (deltaE L t) (deltaE M t) := funext (Eop_eq_blk p L M)
  simp only [psiW, LinearEquiv.trans_apply]
  rw [Eop_eq_blk, Eop_eq_blk, reidx_eR_blk, ← Eop_eq_blk, ← Eop_eq_blk,
    blkEquiv_blk _ _ _ _ (tensorEd (deltaE L) t) (tensorEd (deltaE M) t)
      (fun v => PsiCG_E hL t v) (fun v => PsiCG_E hM t v),
    distE_tensorEd, hEL]

/-! ### Values on the basis vectors -/

lemma blkEquiv_inlL {ι κ ι' κ' : Type*} (e : (ι → ℚ_[p]) ≃ₗ[ℚ_[p]] (ι' → ℚ_[p]))
    (f : (κ → ℚ_[p]) ≃ₗ[ℚ_[p]] (κ' → ℚ_[p])) (u : ι → ℚ_[p]) :
    blkEquiv e f (inlL u) = inlL (e u) := by
  rw [blkEquiv_apply, ← LinearMap.comp_apply, blk_comp_inlL]; rfl

lemma blkEquiv_inrL {ι κ ι' κ' : Type*} (e : (ι → ℚ_[p]) ≃ₗ[ℚ_[p]] (ι' → ℚ_[p]))
    (f : (κ → ℚ_[p]) ≃ₗ[ℚ_[p]] (κ' → ℚ_[p])) (u : κ → ℚ_[p]) :
    blkEquiv e f (inrL u) = inrL (f u) := by
  rw [blkEquiv_apply, ← LinearMap.comp_apply, blk_comp_inrL]; rfl

lemma psiW_A {L M : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M) (i : ℕ) :
    psiW p L M hL hM (inlL (ell p (L + 1) (M - 1) i)) = AV p L M i := by
  have h1 : reidx p (eR L M) (inlL (ell p (L + 1) (M - 1) i)) =
      inlL (ell p (L + 1) (L - 1) i) := by
    funext y; rcases y with ((a | b) | (c | d))
    · show ell p (L + 1) (M - 1) i (.inl a) = ell p (L + 1) (L - 1) i (.inl a)
      rw [ell_inl, ell_inl]
    · show (0 : ℚ_[p]) = ell p (L + 1) (L - 1) i (.inr b)
      rw [ell_inr]
    · rfl
    · show ell p (L + 1) (M - 1) i (.inr d) = 0
      rw [ell_inr]
  simp only [psiW, LinearEquiv.trans_apply]
  rw [h1, blkEquiv_inlL, PsiCG_apply, PsiLin_ell, dist_inl_PsiL]

lemma psiW_D {L M : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M) (j : ℕ) :
    psiW p L M hL hM (inlL (ess p (L + 1) (M - 1) j)) = DV p L M j := by
  have h1 : reidx p (eR L M) (inlL (ess p (L + 1) (M - 1) j)) =
      inrL (ess p (M + 1) (M - 1) j) := by
    funext y; rcases y with ((a | b) | (c | d))
    · show ess p (L + 1) (M - 1) j (.inl a) = 0
      rw [ess_inl]
    · rfl
    · show (0 : ℚ_[p]) = ess p (M + 1) (M - 1) j (.inl c)
      rw [ess_inl]
    · show ess p (L + 1) (M - 1) j (.inr d) = ess p (M + 1) (M - 1) j (.inr d)
      rw [ess_inr, ess_inr]
  simp only [psiW, LinearEquiv.trans_apply]
  rw [h1, blkEquiv_inrL, PsiCG_apply, PsiLin_ess hM, dist_inr_PsiS]

lemma psiW_B {L M : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M) (i : ℕ) :
    psiW p L M hL hM (inrL (ell p (L - 1) (M + 1) i)) = BV p L M i := by
  have h1 : reidx p (eR L M) (inrL (ell p (L - 1) (M + 1) i)) =
      inlL (ess p (L + 1) (L - 1) i) := by
    funext y; rcases y with ((a | b) | (c | d))
    · show (0 : ℚ_[p]) = ess p (L + 1) (L - 1) i (.inl a)
      rw [ess_inl]
    · show ell p (L - 1) (M + 1) i (.inl b) = ess p (L + 1) (L - 1) i (.inr b)
      rw [ell_inl, ess_inr]
    · show ell p (L - 1) (M + 1) i (.inr c) = 0
      rw [ell_inr]
    · rfl
  simp only [psiW, LinearEquiv.trans_apply]
  rw [h1, blkEquiv_inlL, PsiCG_apply, PsiLin_ess hL, dist_inl_PsiS]

lemma psiW_C {L M : ℕ} (hL : 1 ≤ L) (hM : 1 ≤ M) (j : ℕ) :
    psiW p L M hL hM (inrL (ess p (L - 1) (M + 1) j)) = CV p L M j := by
  have h1 : reidx p (eR L M) (inrL (ess p (L - 1) (M + 1) j)) =
      inrL (ell p (M + 1) (M - 1) j) := by
    funext y; rcases y with ((a | b) | (c | d))
    · rfl
    · show ess p (L - 1) (M + 1) j (.inl b) = 0
      rw [ess_inl]
    · show ess p (L - 1) (M + 1) j (.inr c) = ell p (M + 1) (M - 1) j (.inl c)
      rw [ess_inr, ell_inl]
    · show (0 : ℚ_[p]) = ell p (M + 1) (M - 1) j (.inr d)
      rw [ell_inr]
  simp only [psiW, LinearEquiv.trans_apply]
  rw [h1, blkEquiv_inrL, PsiCG_apply, PsiLin_ell, dist_inr_PsiL]

end ColouredSand.TiltRules
