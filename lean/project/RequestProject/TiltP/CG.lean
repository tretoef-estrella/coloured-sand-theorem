module

public import RequestProject.TiltP.WeylDual

/-!
# The Clebsch–Gordan intertwiner and lattice (CSG3, Part G, (G1)–(G2))

## Encoding

Throughout `K = ℚ_[p]` and `l ≥ 1`.

* `W = tensorV (delta K l)`, whose vectors are functions `Fin 2 × Fin (l + 1) → K`
  (`(tensorV (delta K l)).ι = Fin 2 × Fin (l + 1)`); `b_ε ⊗ e_r` is `bvec ε (eN p l r)`, where
  `eN p l r = Pi.single r 1` for `r ≤ l` and `eN p l r = 0` for `r > l` (so `e_{l+1} = 0`; the
  convention `e_{−1} = 0` is written out with an `if`).
* `V p (l + 1) (l − 1)` is the space of the Glue files, with `ℓ_i = ell …`, `s_j = ess …`.
* `PsiL p l i = b_0 ⊗ e_i + b_1 ⊗ e_{i−1}` and
  `PsiS p l j = ((l − j) • b_1 ⊗ e_j − (j + 1) • b_0 ⊗ e_{j+1}) / (l + 1)`;
  `PsiLin p l : V p (l + 1) (l − 1) →ₗ[K] W` is the linear map with `ℓ_i ↦ PsiL i`,
  `s_j ↦ PsiS j` (`PsiLin_ell`, `PsiLin_ess`), and `PsiCG p l hl` the corresponding linear
  isomorphism (G1).
* `FW_u0`, `FW_y`: `Ψ(ℓ_i) = F^{(i)}(b_0 ⊗ e_0)` and `Ψ(s_j) = F^{(j)} y` with
  `y = (l • b_1 ⊗ e_0 − b_0 ⊗ e_1)/(l + 1)`.
* (G2) the standard lattice of `W` is `LinearMap.range (coeL ℤ_[p] K (Fin 2 × Fin (l + 1)))`,
  the image of `Fin 2 × Fin (l + 1) → ℤ_[p]` in `W`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltP

open DPLattice WeylFilt Doubling LemmaW Finset ColouredSand.Glue ColouredSand.Blocks

variable (p : ℕ) [Fact p.Prime]

/-! ### Vectors of `Δ(l)` and of `W` -/

/-- `e_k` in `Δ_K(l)` (`0` if `k > l`). -/
def eN (l k : ℕ) : Fin (l + 1) → ℚ_[p] :=
  if h : k ≤ l then Pi.single ⟨k, Nat.lt_succ_of_le h⟩ 1 else 0

variable {p}

lemma eN_apply (l k : ℕ) (m : Fin (l + 1)) : eN p l k m = if (m : ℕ) = k then 1 else 0 := by
  unfold eN
  split_ifs with h1 h2 h2
  · rw [Pi.single_apply, if_pos (Fin.ext h2)]
  · rw [Pi.single_apply, if_neg (fun h => h2 (by rw [h]))]
  · omega
  · rfl

lemma eN_of_gt {l k : ℕ} (hk : l < k) : eN p l k = 0 := by
  unfold eN; rw [dif_neg (by omega)]

lemma eN_fin (l : ℕ) (k : Fin (l + 1)) : eN p l k = Pi.single k 1 := by
  unfold eN; rw [dif_pos (Nat.le_of_lt_succ k.2)]

lemma deltaF_eN (l n k : ℕ) :
    deltaF l n (eN p l k) = (((k + n).choose n : ℕ) : ℚ_[p]) • eN p l (k + n) := by
  by_cases hk : k ≤ l
  · have : eN p l k = Pi.single (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (l + 1)) 1 := by
      unfold eN; rw [dif_pos hk]
    rw [this]
    funext m
    rw [deltaF_single_apply, Pi.smul_apply, eN_apply, smul_eq_mul]
    split_ifs <;> simp_all
  · rw [eN_of_gt (by omega), map_zero, eN_of_gt (by omega), smul_zero]

lemma deltaE_eN (l s k : ℕ) (hk : k ≤ l) :
    deltaE l s (eN p l k) =
      if s ≤ k then (((l - k + s).choose s : ℕ) : ℚ_[p]) • eN p l (k - s) else 0 := by
  have : eN p l k = Pi.single (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (l + 1)) 1 := by
    unfold eN; rw [dif_pos hk]
  rw [this]
  funext m
  rw [deltaE_single_apply]
  split_ifs with h1 h2 h2
  · rw [Pi.smul_apply, eN_apply, if_pos (by simp at h1 ⊢; omega), smul_eq_mul, mul_one]
  · simp at h1; omega
  · rw [Pi.smul_apply, eN_apply, if_neg (by simp at h1 ⊢; omega)]; simp
  · simp

lemma deltaE_eN_zero (l s : ℕ) (hs : 1 ≤ s) : deltaE l s (eN p l 0) = 0 := by
  rw [deltaE_eN l s 0 (Nat.zero_le _), if_neg (by omega)]

/-- The coproduct `F^{(t)}` on `W = V ⊗ Δ_K(l)`. -/
abbrev FW (l t : ℕ) : Module.End ℚ_[p] (Fin 2 × Fin (l + 1) → ℚ_[p]) := tensorFd (deltaF l) t

/-- The coproduct `E^{(t)}` on `W = V ⊗ Δ_K(l)`. -/
abbrev EW (l t : ℕ) : Module.End ℚ_[p] (Fin 2 × Fin (l + 1) → ℚ_[p]) := tensorEd (deltaE l) t

lemma isDP_W (l : ℕ) :
    IsDP (tensorWt (weylWt l)) (FW (p := p) l) (EW (p := p) l) :=
  (tensorV (delta ℚ_[p] l)).isDP

variable (p) in
/-- `b_0 ⊗ e_0`. -/
def u0 (l : ℕ) : Fin 2 × Fin (l + 1) → ℚ_[p] := bvec 0 (eN p l 0)

variable (p) in
/-- `y = (l • b_1 ⊗ e_0 − b_0 ⊗ e_1)/(l + 1)`. -/
def yv (l : ℕ) : Fin 2 × Fin (l + 1) → ℚ_[p] :=
  (1 / ((l : ℚ_[p]) + 1)) • ((l : ℚ_[p]) • bvec 1 (eN p l 0) - bvec 0 (eN p l 1))

variable (p) in
/-- (G1) `Ψ(ℓ_i) = b_0 ⊗ e_i + b_1 ⊗ e_{i−1}` (`e_{−1} = 0`, `e_{l+1} = 0`). -/
def PsiL (l i : ℕ) : Fin 2 × Fin (l + 1) → ℚ_[p] :=
  bvec 0 (eN p l i) + if 1 ≤ i then bvec 1 (eN p l (i - 1)) else 0

variable (p) in
/-- (G1) `Ψ(s_j) = ((l − j) • b_1 ⊗ e_j − (j + 1) • b_0 ⊗ e_{j+1})/(l + 1)`. -/
def PsiS (l j : ℕ) : Fin 2 × Fin (l + 1) → ℚ_[p] :=
  (1 / ((l : ℚ_[p]) + 1)) •
    (((l : ℚ_[p]) - j) • bvec 1 (eN p l j) - ((j : ℚ_[p]) + 1) • bvec 0 (eN p l (j + 1)))

/-- `F^{(i)}(b_0 ⊗ e_0) = b_0 ⊗ e_i + b_1 ⊗ e_{i−1}`. -/
theorem FW_u0 (l i : ℕ) : FW l i (u0 p l) = PsiL p l i := by
  unfold u0 PsiL
  rw [tensorFd_bvec0, deltaF_eN]
  rcases i with _ | k
  · simp
  · rw [pred_succ, deltaF_eN, if_pos (by omega), Nat.zero_add, Nat.zero_add, Nat.choose_self,
      Nat.choose_self, Nat.add_sub_cancel]
    simp

/-- `F^{(j)} y = ((l − j) • b_1 ⊗ e_j − (j + 1) • b_0 ⊗ e_{j+1})/(l + 1)`. -/
theorem FW_y (l j : ℕ) : FW l j (yv p l) = PsiS p l j := by
  unfold yv PsiS
  rw [map_smul, map_sub, map_smul, tensorFd_bvec1, tensorFd_bvec0, deltaF_eN, deltaF_eN,
    Nat.zero_add, Nat.choose_self]
  rcases j with _ | k
  · simp
  · rw [pred_succ, deltaF_eN, show 1 + (k + 1) = k + 1 + 1 by omega, Nat.choose_succ_self_right,
      show 1 + k = k + 1 by omega, Nat.choose_succ_self_right]
    simp only [map_smul, Nat.cast_one, one_smul]
    push_cast
    module

lemma EW_u0 (l s : ℕ) (hs : 1 ≤ s) : EW l s (u0 p l) = 0 := by
  unfold u0
  rw [tensorEd_bvec0, deltaE_eN_zero l s hs, map_zero]

lemma EW_y (l s : ℕ) (hl : 1 ≤ l) (hs : 1 ≤ s) : EW l s (yv p l) = 0 := by
  unfold yv
  rw [map_smul, map_sub, map_smul, tensorEd_bvec1, tensorEd_bvec0, deltaE_eN_zero l s hs,
    map_zero, zero_add]
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [pred_succ]
  rcases k with _ | k
  · rw [deltaE_eN l 0 0 (Nat.zero_le _), deltaE_eN l (0 + 1) 1 hl, if_pos le_rfl, if_pos le_rfl]
    simp only [Nat.sub_zero, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, one_smul,
      Nat.sub_self, zero_add, Nat.choose_one_right, show l - 1 + 1 = l by omega, map_smul]
    rw [sub_self, smul_zero]
  · rw [deltaE_eN_zero l (k + 1) (by omega), deltaE_eN l (k + 1 + 1) 1 hl, if_neg (by omega)]
    simp

/-- Weight vectors: closure properties. -/
lemma inWt_add {ι : Type*} {wt : ι → ℤ} {w : ℤ} {u v : ι → ℚ_[p]} (hu : InWt wt w u)
    (hv : InWt wt w v) : InWt wt w (u + v) := fun j hj => by simp [hu j hj, hv j hj]

lemma inWt_sub {ι : Type*} {wt : ι → ℤ} {w : ℤ} {u v : ι → ℚ_[p]} (hu : InWt wt w u)
    (hv : InWt wt w v) : InWt wt w (u - v) := fun j hj => by simp [hu j hj, hv j hj]

lemma inWt_smul {ι : Type*} {wt : ι → ℤ} {w : ℤ} (c : ℚ_[p]) {v : ι → ℚ_[p]}
    (hv : InWt wt w v) : InWt wt w (c • v) := fun j hj => by simp [hv j hj]

lemma inWt_bvec_eN (l : ℕ) (e : Fin 2) (k : ℕ) :
    InWt (tensorWt (weylWt l)) (wtV e + (l - 2 * k)) (bvec e (eN p l k)) := by
  intro j hj
  rw [bvec_apply, eN_apply]
  split_ifs with h1 h2
  · exfalso; apply hj; simp only [tensorWt, weylWt, h1, h2]
  · rfl
  · rfl

lemma inWt_u0 (l : ℕ) : InWt (tensorWt (weylWt l)) ((l : ℤ) + 1) (u0 p l) := by
  have := inWt_bvec_eN (p := p) l 0 0
  simp only [wtV_zero, Nat.cast_zero, mul_zero, sub_zero] at this
  rw [show (l : ℤ) + 1 = 1 + (l : ℤ) from add_comm _ _]; exact this

lemma inWt_yv (l : ℕ) : InWt (tensorWt (weylWt l)) ((l : ℤ) - 1) (yv p l) := by
  have h1 := inWt_bvec_eN (p := p) l 1 0
  have h2 := inWt_bvec_eN (p := p) l 0 1
  simp only [wtV_zero, wtV_one, Nat.cast_zero, Nat.cast_one, mul_zero, sub_zero, mul_one] at h1 h2
  refine inWt_smul _ (inWt_sub (inWt_smul _ ?_) ?_)
  · intro j hj; exact h1 j (by intro h; apply hj; rw [h]; ring)
  · intro j hj; exact h2 j (by intro h; apply hj; rw [h]; ring)

/-- Kostant's formula on a highest-weight vector. -/
lemma K_hw {ι : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ}
    {Fd Ed : ℕ → Module.End ℚ_[p] (ι → ℚ_[p])} (h : IsDP wt Fd Ed) {w : ℤ} {v : ι → ℚ_[p]}
    (hv : InWt wt w v) (hE : ∀ k, 1 ≤ k → Ed k v = 0) (r s : ℕ) :
    Ed s (Fd r v) =
      if s ≤ r then ((Ring.choose (w + s - r) s : ℤ) : ℚ_[p]) • Fd (r - s) v else 0 := by
  rw [IsDP.K_inWt h hv]
  split_ifs with hsr
  · rw [Finset.sum_eq_single s]
    · rw [Nat.sub_self, h.P0_E]; rfl
    · intro j hj hjs
      have : j < s := by simp at hj; omega
      rw [hE (s - j) (by omega), map_zero, smul_zero]
    · intro hs; exfalso; apply hs; simp; omega
  · apply Finset.sum_eq_zero
    intro j hj
    have : j < s := by simp at hj; omega
    rw [hE (s - j) (by omega), map_zero, smul_zero]

end ColouredSand.TiltP
