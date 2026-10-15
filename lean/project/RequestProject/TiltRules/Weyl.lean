module

public import RequestProject.TiltRules.GlueIso

/-!
# Weyl coordinates of `V ⊗ (Δ(λ) ⊕ Δ(μ))` (auxiliary for `CSG4_tensor_rules.md`, §3, Step 1)

Throughout `K = ℚ_[p]`.  The space of `V ⊗ (Δ(L) ⊕ Δ(M))` over `K` is
`W = Fin 2 × Idx L M → K` (`Idx L M = Fin (L + 1) ⊕ Fin (M + 1)`), with basis
`b_ε ⊗ ℓ_k = bvec ε (ell p L M k)` and `b_ε ⊗ s_k = bvec ε (ess p L M k)`.

## Encoding

* `reidx e : (β → K) ≃ (α → K)`, `f ↦ f ∘ e`, for an equivalence `e : α ≃ β` of index types.
* `distE : ((Fin 2 × ι) ⊕ (Fin 2 × κ) → K) ≃ (Fin 2 × (ι ⊕ κ) → K)` is the distributivity
  `V ⊗ M ⊕ V ⊗ N = V ⊗ (M ⊕ N)` in coordinates (`reidx` along `Equiv.prodSumDistrib`).
  `distE_tensorFd`, `distE_tensorEd`: it intertwines the coproduct operators.
* The highest-weight chains of the four Weyl blocks of §3, Step 1 (`Ψ_L ⊕ Ψ_M` of `PsiCG`), as
  vectors of `W`:
  - `AV i = b_0 ⊗ ℓ_i + b_1 ⊗ ℓ_{i−1}` (`= F^{(i)}(b_0 ⊗ ℓ_0)`, the block `Δ(L + 1)`);
  - `BV i = ((L − i) b_1 ⊗ ℓ_i − (i + 1) b_0 ⊗ ℓ_{i+1})/(L + 1)` (the block `Δ(L − 1)`);
  - `CV j = b_0 ⊗ s_j + b_1 ⊗ s_{j−1}` (the block `Δ(M + 1)`);
  - `DV j = ((M − j) b_1 ⊗ s_j − (j + 1) b_0 ⊗ s_{j+1})/(M + 1)` (the block `Δ(M − 1)`).
  (`b_1 ⊗ ℓ_{−1} := 0` is written with an `if`; out-of-range indices give `0`.)
* `dist_inl_PsiL` etc.: the images of `PsiL`, `PsiS` (the values of `PsiCG`) under
  `distE ∘ inl` / `distE ∘ inr` are `AV`, `BV`, `CV`, `DV`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltRules

open DPLattice WeylFilt Doubling LemmaW Lemma35 Finset ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP

variable {p : ℕ} [Fact p.Prime]

/-! ### Reindexing -/

variable (p) in
/-- Reindexing along `e : α ≃ β`: `f ↦ f ∘ e`. -/
def reidx {α β : Type*} (e : α ≃ β) : (β → ℚ_[p]) ≃ₗ[ℚ_[p]] (α → ℚ_[p]) where
  toFun f := f ∘ e
  invFun g := g ∘ e.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by funext b; simp
  right_inv g := by funext a; simp

@[simp] lemma reidx_apply {α β : Type*} (e : α ≃ β) (f : β → ℚ_[p]) (a : α) :
    reidx p e f a = f (e a) := rfl

/-! ### Distributivity -/

variable (p) in
/-- `V ⊗ M ⊕ V ⊗ N = V ⊗ (M ⊕ N)` in coordinates. -/
def distE (ι κ : Type*) : ((Fin 2 × ι) ⊕ (Fin 2 × κ) → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin 2 × (ι ⊕ κ) → ℚ_[p]) :=
  reidx p (Equiv.prodSumDistrib (Fin 2) ι κ)

lemma slice_distE {ι κ : Type*} (e : Fin 2) (z : (Fin 2 × ι) ⊕ (Fin 2 × κ) → ℚ_[p]) :
    slice e (distE p ι κ z) = Sum.elim (slice e (z ∘ Sum.inl)) (slice e (z ∘ Sum.inr)) := by
  funext y; rcases y with i | k <;> rfl

lemma pred_blk {ι κ : Type*} (F : ℕ → Module.End ℚ_[p] (ι → ℚ_[p]))
    (G : ℕ → Module.End ℚ_[p] (κ → ℚ_[p])) (t : ℕ) :
    pred (fun t => blk (F t) (G t)) t = blk (pred F t) (pred G t) := by
  rcases t with _ | t
  · ext z y; rcases y with i | k <;> rfl
  · rfl

lemma distE_tensorFd {ι κ : Type*} (F : ℕ → Module.End ℚ_[p] (ι → ℚ_[p]))
    (G : ℕ → Module.End ℚ_[p] (κ → ℚ_[p])) (t : ℕ) (z : (Fin 2 × ι) ⊕ (Fin 2 × κ) → ℚ_[p]) :
    distE p ι κ (blk (tensorFd F t) (tensorFd G t) z) =
      tensorFd (fun t => blk (F t) (G t)) t (distE p ι κ z) := by
  apply ext_slice
  · rw [slice0_tensorFd, slice_distE, slice_distE]
    funext y; rcases y with i | k
    · exact congrFun (slice0_tensorFd F t (z ∘ Sum.inl)) i
    · exact congrFun (slice0_tensorFd G t (z ∘ Sum.inr)) k
  · rw [slice1_tensorFd, slice_distE, slice_distE, slice_distE, pred_blk]
    funext y; rcases y with i | k
    · exact congrFun (slice1_tensorFd F t (z ∘ Sum.inl)) i
    · exact congrFun (slice1_tensorFd G t (z ∘ Sum.inr)) k

lemma distE_tensorEd {ι κ : Type*} (F : ℕ → Module.End ℚ_[p] (ι → ℚ_[p]))
    (G : ℕ → Module.End ℚ_[p] (κ → ℚ_[p])) (t : ℕ) (z : (Fin 2 × ι) ⊕ (Fin 2 × κ) → ℚ_[p]) :
    distE p ι κ (blk (tensorEd F t) (tensorEd G t) z) =
      tensorEd (fun t => blk (F t) (G t)) t (distE p ι κ z) := by
  apply ext_slice
  · rw [slice0_tensorEd, slice_distE, slice_distE, slice_distE, pred_blk]
    funext y; rcases y with i | k
    · exact congrFun (slice0_tensorEd F t (z ∘ Sum.inl)) i
    · exact congrFun (slice0_tensorEd G t (z ∘ Sum.inr)) k
  · rw [slice1_tensorEd, slice_distE, slice_distE]
    funext y; rcases y with i | k
    · exact congrFun (slice1_tensorEd F t (z ∘ Sum.inl)) i
    · exact congrFun (slice1_tensorEd G t (z ∘ Sum.inr)) k

lemma distE_inl_bvec {ι κ : Type*} (e : Fin 2) (u : ι → ℚ_[p]) :
    distE p ι κ (inlL (bvec e u)) = bvec e (inlL u) := by
  funext ⟨e', y⟩; rcases y with i | k
  · rfl
  · show (0 : ℚ_[p]) = if e' = e then (0 : ℚ_[p]) else 0
    split_ifs <;> rfl

lemma distE_inr_bvec {ι κ : Type*} (e : Fin 2) (u : κ → ℚ_[p]) :
    distE p ι κ (inrL (bvec e u)) = bvec e (inrL u) := by
  funext ⟨e', y⟩; rcases y with i | k
  · show (0 : ℚ_[p]) = if e' = e then (0 : ℚ_[p]) else 0
    split_ifs <;> rfl
  · rfl

lemma inlL_eN (L M k : ℕ) : (inlL (eN p L k) : Idx L M → ℚ_[p]) = ell p L M k := by
  funext y; rcases y with i | j
  · rw [ell_inl]; exact eN_apply L k i
  · rw [ell_inr]; rfl

lemma inrL_eN (L M k : ℕ) : (inrL (eN p M k) : Idx L M → ℚ_[p]) = ess p L M k := by
  funext y; rcases y with i | j
  · rw [ess_inl]; rfl
  · rw [ess_inr]; exact eN_apply M k j

/-! ### The four Weyl chains in `W` -/

variable (p) in
/-- `AV i = b_0 ⊗ ℓ_i + b_1 ⊗ ℓ_{i−1}`. -/
def AV (L M i : ℕ) : Fin 2 × Idx L M → ℚ_[p] :=
  bvec 0 (ell p L M i) + if 1 ≤ i then bvec 1 (ell p L M (i - 1)) else 0

variable (p) in
/-- `BV i = ((L − i) b_1 ⊗ ℓ_i − (i + 1) b_0 ⊗ ℓ_{i+1})/(L + 1)`. -/
def BV (L M i : ℕ) : Fin 2 × Idx L M → ℚ_[p] :=
  (1 / ((L : ℚ_[p]) + 1)) •
    (((L : ℚ_[p]) - i) • bvec 1 (ell p L M i) - ((i : ℚ_[p]) + 1) • bvec 0 (ell p L M (i + 1)))

variable (p) in
/-- `CV j = b_0 ⊗ s_j + b_1 ⊗ s_{j−1}`. -/
def CV (L M j : ℕ) : Fin 2 × Idx L M → ℚ_[p] :=
  bvec 0 (ess p L M j) + if 1 ≤ j then bvec 1 (ess p L M (j - 1)) else 0

variable (p) in
/-- `DV j = ((M − j) b_1 ⊗ s_j − (j + 1) b_0 ⊗ s_{j+1})/(M + 1)`. -/
def DV (L M j : ℕ) : Fin 2 × Idx L M → ℚ_[p] :=
  (1 / ((M : ℚ_[p]) + 1)) •
    (((M : ℚ_[p]) - j) • bvec 1 (ess p L M j) - ((j : ℚ_[p]) + 1) • bvec 0 (ess p L M (j + 1)))

lemma dist_inl_PsiL (L M i : ℕ) :
    distE p (Fin (L + 1)) (Fin (M + 1)) (inlL (PsiL p L i)) = AV p L M i := by
  unfold PsiL AV
  rw [map_add, map_add]
  split_ifs
  · rw [distE_inl_bvec, distE_inl_bvec, inlL_eN, inlL_eN]
  · rw [map_zero, map_zero, distE_inl_bvec, inlL_eN]

lemma dist_inl_PsiS (L M i : ℕ) :
    distE p (Fin (L + 1)) (Fin (M + 1)) (inlL (PsiS p L i)) = BV p L M i := by
  unfold PsiS BV
  simp only [map_smul, map_sub, distE_inl_bvec, inlL_eN]

lemma dist_inr_PsiL (L M j : ℕ) :
    distE p (Fin (L + 1)) (Fin (M + 1)) (inrL (PsiL p M j)) = CV p L M j := by
  unfold PsiL CV
  rw [map_add, map_add]
  split_ifs
  · rw [distE_inr_bvec, distE_inr_bvec, inrL_eN, inrL_eN]
  · rw [map_zero, map_zero, distE_inr_bvec, inrL_eN]

lemma dist_inr_PsiS (L M j : ℕ) :
    distE p (Fin (L + 1)) (Fin (M + 1)) (inrL (PsiS p M j)) = DV p L M j := by
  unfold PsiS DV
  simp only [map_smul, map_sub, distE_inr_bvec, inrL_eN]

/-! ### `PsiCG` as an intertwiner of the Weyl blocks -/

lemma PsiCG_F {l : ℕ} (hl : 1 ≤ l) (t : ℕ) (v : V p (l + 1) (l - 1)) :
    PsiCG p l hl (Fop p (l + 1) (l - 1) t v) = tensorFd (deltaF l) t (PsiCG p l hl v) :=
  LinearMap.congr_fun (PsiLin_F hl t) v

lemma PsiCG_E {l : ℕ} (hl : 1 ≤ l) (t : ℕ) (v : V p (l + 1) (l - 1)) :
    PsiCG p l hl (Eop p (l + 1) (l - 1) t v) = tensorEd (deltaE l) t (PsiCG p l hl v) :=
  LinearMap.congr_fun (PsiLin_E hl t) v

end ColouredSand.TiltRules
