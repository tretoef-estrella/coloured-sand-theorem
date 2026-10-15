module

public import RequestProject.OddSplit.IotaE

/-!
# `CSI3_the_split.md`: Part I — (I3) a weight-preserving retraction of `ι`

Encodings (`r = s + 1`, `2 ≤ r ≤ p − 1`):

* `sel p N` picks the coordinates of the square block of the hint:
  `A_j e_i ↦ b̂_0 ⊗ A'_j e_i`, `C_j e_i ↦ b̂_0 ⊗ C'_{j+1} e_i` (`j ≤ p − 2`),
  `C_{p−1} e_i ↦ b̂_1 ⊗ C'_{p−1} e_i`; `selProj p N` is the projection on these coordinates
  (`z ↦ z ∘ sel`), and `blk L = selProj ∘ ι` is the square block.
* Modulo `p` the matrix of `blk L` is diagonal with entries `1` and `r − 1 = s` (`blk_entry`),
  so its determinant is a unit of `ℤ_[p]` (`isUnit_det_blk`); `rho L` is
  `(blk L)⁻¹ ∘ selProj` (`Matrix.toLin'` of the inverse matrix).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

/-! ### `F^k` modulo `p` -/

section modp

variable (s : ℕ)

lemma modP_psiF_aV (m : ℕ) (n : N.ι → ℤ_[p]) :
    ModP p (psiF p N s (aV p m n)) (aV p (m + 1) n) := by
  rcases Nat.lt_or_ge (m + 1) p with h | h
  · exact ModP.of_eq (psiF_A_lt s h n)
  · rw [aV_of_ge p h]
    rcases Nat.lt_or_ge m p with h' | h'
    · obtain rfl : m = p - 1 := by omega
      rw [psiF_A_last]
      exact ⟨-aV p 0 (N.Fd 1 n) + cV p (p - s) n, by rw [sub_zero, smul_add, smul_neg, neg_smul]⟩
    · rw [aV_of_ge p h', map_zero]; exact ModP.refl _

lemma modP_psiF_cV (m : ℕ) (n : N.ι → ℤ_[p]) :
    ModP p (psiF p N s (cV p m n)) (cV p (m + 1) n) := by
  rcases Nat.lt_or_ge (m + 1) p with h | h
  · exact ModP.of_eq (psiF_C_lt s h n)
  · rw [cV_of_ge p h]
    rcases Nat.lt_or_ge m p with h' | h'
    · obtain rfl : m = p - 1 := by omega
      rw [psiF_C_last]
      exact ⟨-cV p 0 (N.Fd 1 n), by rw [sub_zero, smul_neg, neg_smul]⟩
    · rw [cV_of_ge p h', map_zero]; exact ModP.refl _

lemma modP_psiF_pow_aV (k m : ℕ) (n : N.ι → ℤ_[p]) :
    ModP p ((psiF p N s ^ k) (aV p m n)) (aV p (m + k) n) := by
  induction k with
  | zero => exact ModP.refl _
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (ih.map _).trans (by rw [← add_assoc]; exact modP_psiF_aV s _ n)

lemma modP_psiF_pow_cV (k m : ℕ) (n : N.ι → ℤ_[p]) :
    ModP p ((psiF p N s ^ k) (cV p m n)) (cV p (m + k) n) := by
  induction k with
  | zero => exact ModP.refl _
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (ih.map _).trans (by rw [← add_assoc]; exact modP_psiF_cV s _ n)

end modp

/-! ### `ι` modulo `p` -/

section iotaModP

variable {s : ℕ} (L : PsiData p N s)

/-- (I3) `ι(A_j n) ≡ b̂_0 ⊗ A'_j n + j·b̂_1 ⊗ A'_{j−1} n` modulo `p`. -/
lemma iota_aV_modP {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    ModP p (iota L (aV p j n)) (tv 0 (aV p j n) + (j : ℤ_[p]) • tv 1 (aV p (j - 1) n)) := by
  rw [iota_aV L hj]
  simp only [alphaL, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_sub,
    map_smul]
  rw [Zs_Fpow_tv0, psiF_pow_aV s (j := 0) (k := j) (by omega),
    psiF_pow_aV s (j := 0) (k := j - 1) (by omega), zero_add, zero_add]
  exact ⟨-((ZF L ^ j) (tv 1 (cV p (p - (s + 1)) (N.Ed 1 n)))), by
    rw [smul_neg]; abel⟩

/-- (I3) `ι(C_j n) ≡ b̂_0 ⊗ C'_{j+1} n + j·b̂_1 ⊗ C'_j n + b̂_1 ⊗ A'_{r−1+j} n + r·b̂_1 ⊗ C'_j n`
modulo `p` (`C'_p = A'_k = 0` for `k ≥ p`). -/
lemma iota_cV_modP {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    ModP p (iota L (cV p j n)) (tv 0 (cV p (j + 1) n) + (j : ℤ_[p]) • tv 1 (cV p j n) +
      tv 1 (aV p (s + j) n) + ((s : ℤ_[p]) + 1) • tv 1 (cV p j n)) := by
  rw [iota_cV L hj hn]
  simp only [gammaL, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul]
  rw [Zs_Fpow_tv0, Zs_Fpow_tv1, Zs_Fpow_tv1, sub_eq_add_neg, ← neg_smul]
  refine ModP.add (ModP.add (ModP.add (by
      have := (modP_psiF_pow_cV (N := N) s j 1 n).map (tv 0)
      rwa [add_comm 1 j] at this) ?_)
    ((modP_psiF_pow_aV s j s n).map (tv 1))) ?_
  · rcases j with _ | j
    · simpa using ModP.refl (0 : Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p])
    · rw [Nat.add_sub_cancel]
      refine ModP.smul _ (ModP.map (tv 1) ?_)
      have := modP_psiF_pow_cV (N := N) s j 1 n
      rwa [add_comm 1 j] at this
  · refine (ModP.smul _ ((modP_psiF_pow_cV s j 0 n).map (tv 1))).trans ?_
    rw [zero_add]
    exact ModP.smul_congr ⟨-((w : ℤ_[p]) + 1), by ring⟩ _

end iotaModP

/-! ### The square block -/

variable (p N) in
/-- (I3) the coordinates of the square block: `A_j e_i ↦ b̂_0 ⊗ A'_j e_i`,
`C_j e_i ↦ b̂_0 ⊗ C'_{j+1} e_i` for `j ≤ p − 2`, `C_{p−1} e_i ↦ b̂_1 ⊗ C'_{p−1} e_i`. -/
def sel (x : Bool × Fin p × N.ι) : Fin 2 × (Bool × Fin p × N.ι) :=
  if x.1 then
    (if h : (x.2.1 : ℕ) + 1 < p then (0, (true, ⟨x.2.1 + 1, h⟩, x.2.2)) else (1, x))
  else (0, x)

variable (p N) in
/-- (I3) the diagonal of the block modulo `p`: `1`, except `r − 1 = s` at `C_{p−1} e_i`. -/
def dval (s : ℕ) (x : Bool × Fin p × N.ι) : ℤ_[p] :=
  if x.1 = true ∧ ¬ ((x.2.1 : ℕ) + 1 < p) then (s : ℤ_[p]) else 1

lemma vA_sel (j : Fin p) (i : N.ι) (k' : Bool × Fin p × N.ι) :
    (tv 0 (aV p j (Pi.single i 1)) + ((j : ℕ) : ℤ_[p]) • tv 1 (aV p ((j : ℕ) - 1) (Pi.single i 1)) :
      Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) (sel p N k') =
      if k' = (false, j, i) then 1 else 0 := by
  obtain ⟨b', j', i'⟩ := k'
  cases b'
  · simp only [sel, Bool.false_eq_true, if_false, Pi.add_apply, Pi.smul_apply, tv_apply,
      aV_apply, Pi.single_apply, Prod.mk.injEq, Fin.ext_iff]
    by_cases h1 : (j' : ℕ) = j <;> by_cases h2 : i' = i <;> simp [h1, h2]
  · by_cases h : (j' : ℕ) + 1 < p
    · simp [sel, h, tv_apply, aV_apply]
    · simp [sel, h, tv_apply, aV_apply]

lemma vC_sel (s : ℕ) (j : Fin p) (i : N.ι) (k' : Bool × Fin p × N.ι) :
    (tv 0 (cV p ((j : ℕ) + 1) (Pi.single i 1)) +
        ((j : ℕ) : ℤ_[p]) • tv 1 (cV p j (Pi.single i 1)) + tv 1 (aV p (s + j) (Pi.single i 1)) +
        ((s : ℤ_[p]) + 1) • tv 1 (cV p j (Pi.single i 1)) :
      Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) (sel p N k') =
      if k' = (true, j, i) then
        (if (j : ℕ) + 1 < p then 1 else ((j : ℕ) : ℤ_[p]) + s + 1) else 0 := by
  obtain ⟨b', j', i'⟩ := k'
  cases b'
  · simp [sel, tv_apply, aV_apply, cV_apply]
  · by_cases hj : j' = j
    · subst hj
      by_cases hi : i' = i
      · subst hi
        by_cases h : (j' : ℕ) + 1 < p
        · simp [sel, h, tv_apply, aV_apply, cV_apply]
        · simp [sel, h, tv_apply, aV_apply, cV_apply]; ring
      · by_cases h : (j' : ℕ) + 1 < p
        · simp [sel, h, tv_apply, aV_apply, cV_apply, hi]
        · simp [sel, h, tv_apply, aV_apply, cV_apply, hi]
    · have hj' : (j' : ℕ) ≠ j := fun h' => hj (Fin.ext h')
      by_cases h : (j' : ℕ) + 1 < p
      · simp [sel, h, tv_apply, aV_apply, cV_apply, hj, hj']
      · simp [sel, h, tv_apply, aV_apply, cV_apply, hj, hj']

section block

variable {s : ℕ} (L : PsiData p N s) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p)
include hs1 hsp

/-- (I3) the entries of the square block are, modulo `p`, those of the diagonal matrix with
entries `dval`. -/
lemma blk_entry (k k' : Bool × Fin p × N.ι) :
    ∃ e, iota L (Pi.single k 1) (sel p N k') - (if k' = k then dval p N s k else 0) =
      (p : ℤ_[p]) * e := by
  obtain ⟨b, j, i⟩ := k
  cases b
  · obtain ⟨e, he⟩ := (iota_aV_modP L j.isLt (Pi.single i 1)).coord (sel p N k')
    rw [vA_sel] at he
    refine ⟨e, ?_⟩
    rw [single_false, ← he]
    by_cases hk : k' = (false, j, i) <;> simp [hk, dval]
  · obtain ⟨e, he⟩ := (iota_cV_modP L j.isLt (inWt_single (A := ℤ_[p]) N.wt i)).coord (sel p N k')
    rw [vC_sel] at he
    rw [single_true]
    by_cases hk : k' = (true, j, i)
    · simp only [hk, if_true, dval, true_and] at he ⊢
      by_cases hj : (j : ℕ) + 1 < p
      · simp only [hj, if_true, not_true_eq_false, if_false] at he ⊢
        exact ⟨e, he⟩
      · simp only [hj, if_false, not_false_eq_true, if_true] at he ⊢
        refine ⟨e + 1, ?_⟩
        have hjp : ((j : ℕ) : ℤ_[p]) + 1 = p := by
          have : (j : ℕ) + 1 = p := by omega
          exact_mod_cast this
        linear_combination he + hjp
    · simp only [hk, if_false] at he ⊢
      exact ⟨e, he⟩

end block

/-! ### The retraction `ρ` -/

variable (p N) in
/-- (I3) the projection on the coordinates `sel` of the square block. -/
def selProj : (Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) →ₗ[ℤ_[p]] (Bool × Fin p × N.ι → ℤ_[p]) :=
  LinearMap.funLeft ℤ_[p] ℤ_[p] (sel p N)

/-- (I3) the matrix of the square block `selProj ∘ ι`. -/
def blkMat {s : ℕ} (L : PsiData p N s) : Matrix (Bool × Fin p × N.ι) (Bool × Fin p × N.ι) ℤ_[p] :=
  LinearMap.toMatrix' (selProj p N ∘ₗ iota L)

lemma blkMat_apply {s : ℕ} (L : PsiData p N s) (k' k : Bool × Fin p × N.ι) :
    blkMat L k' k = iota L (Pi.single k 1) (sel p N k') := by
  simp [blkMat, LinearMap.toMatrix'_apply, selProj, LinearMap.funLeft_apply]

/-- (I3) the selected coordinates have the right weights. -/
lemma wt_sel {s : ℕ} (L : PsiData p N s) (k : Bool × Fin p × N.ι) :
    (Zs L).wt (sel p N k) = psiWt p N (s + 1) k := by
  obtain ⟨b, j, i⟩ := k
  cases b
  · simp [sel, Tensor2.tensor, V, PsiData.lat, psiWt]; ring
  · by_cases h : (j : ℕ) + 1 < p
    · simp [sel, h, Tensor2.tensor, V, PsiData.lat, psiWt]; ring
    · simp [sel, h, Tensor2.tensor, V, PsiData.lat, psiWt]; ring

lemma selProj_H {s : ℕ} (L : PsiData p N s) :
    selProj p N ∘ₗ H (Zs L) = Hop (psiWt p N (s + 1)) ∘ₗ selProj p N := by
  refine LinearMap.ext fun z => funext fun k => ?_
  simp only [LinearMap.comp_apply, selProj, LinearMap.funLeft_apply]
  change ((Zs L).wt (sel p N k) : ℤ_[p]) * z (sel p N k) =
    (psiWt p N (s + 1) k : ℤ_[p]) * z (sel p N k)
  rw [wt_sel L k]

/-- Over `ℤ_[p]`, a linear map commuting with the weight operators is weight-preserving. -/
lemma wtPres_of_comm_Hop {ι κ : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ} {wt' : κ → ℤ}
    (f : (ι → ℤ_[p]) →ₗ[ℤ_[p]] (κ → ℤ_[p])) (h : f ∘ₗ Hop wt = Hop wt' ∘ₗ f) :
    ∀ i j, wt i ≠ wt' j → f (Pi.single i 1) j = 0 := by
  intro i j hij
  have e := congr_fun (LinearMap.congr_fun h (Pi.single i 1)) j
  simp only [LinearMap.comp_apply, Hop_apply] at e
  have hs : Hop (A := ℤ_[p]) wt (Pi.single i 1) = (wt i : ℤ_[p]) • (Pi.single i 1 : ι → ℤ_[p]) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [hs, map_smul, Pi.smul_apply, smul_eq_mul] at e
  have e' : (((wt i - wt' j : ℤ)) : ℤ_[p]) * f (Pi.single i 1) j = 0 := by
    push_cast; linear_combination e
  rcases mul_eq_zero.mp e' with h0 | h0
  · exact absurd (by exact_mod_cast h0) (sub_ne_zero.mpr hij)
  · exact h0

section rho

variable {s : ℕ} (L : PsiData p N s) (hs1 : 1 ≤ s) (hsp : s + 2 ≤ p)
include hs1 hsp

/-- (I3) the block is invertible over `ℤ_[p]`: its determinant is a unit, since modulo `p` the
block is diagonal with entries `1` and `r − 1 = s`, units since `2 ≤ r ≤ p − 1`. -/
lemma isUnit_det_blk : IsUnit (blkMat L).det := by
  have hp0 : (PadicInt.toZMod (p : ℤ_[p]) : ZMod p) = 0 := by simp
  have hmap : (blkMat L).map (PadicInt.toZMod (p := p)) =
      Matrix.diagonal (fun k => PadicInt.toZMod (dval p N s k)) := by
    ext k' k
    obtain ⟨e, he⟩ := blk_entry L hs1 hsp k k'
    rw [Matrix.map_apply, blkMat_apply, Matrix.diagonal_apply]
    have h2 := congrArg (PadicInt.toZMod (p := p)) he
    rw [map_sub, map_mul, hp0, zero_mul, sub_eq_zero] at h2
    rw [h2]
    by_cases hk : k' = k
    · subst hk; simp
    · simp [hk]
  have hdet : PadicInt.toZMod (blkMat L).det ≠ 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
    simp only [dval]
    split_ifs
    · rw [map_natCast]
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · simp
  by_contra hu
  apply hdet
  have hm : (blkMat L).det ∈ IsLocalRing.maximalIdeal ℤ_[p] := hu
  rw [← PadicInt.ker_toZMod] at hm
  exact hm

/-- (I3) the retraction `ρ = block⁻¹ ∘ (projection on the selected coordinates)`. -/
def rho : (Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) →ₗ[ℤ_[p]] (Bool × Fin p × N.ι → ℤ_[p]) :=
  Matrix.toLin' (blkMat L)⁻¹ ∘ₗ selProj p N

omit hs1 hsp in
lemma blk_eq : selProj p N ∘ₗ iota L = Matrix.toLin' (blkMat L) := by
  rw [blkMat, Matrix.toLin'_toMatrix']

/-- (I3) `ρ ∘ ι = id`. -/
theorem rho_iota : rho L ∘ₗ iota L = LinearMap.id := by
  rw [rho, LinearMap.comp_assoc, blk_eq, ← Matrix.toLin'_mul,
    Matrix.nonsing_inv_mul _ (isUnit_det_blk L hs1 hsp), Matrix.toLin'_one]

/-- (I3) `ρ` is weight-preserving. -/
theorem rho_wtPres (z : Fin 2 × (Bool × Fin p × N.ι)) (k : Bool × Fin p × N.ι)
    (h : (Zs L).wt z ≠ psiWt p N (s + 1) k) : rho L (Pi.single z 1) k = 0 := by
  set U := Matrix.toLin' (blkMat L)⁻¹ with hU
  set T := selProj p N ∘ₗ iota L with hT
  have hUT : U ∘ₗ T = LinearMap.id := rho_iota L hs1 hsp
  have hTU : T ∘ₗ U = LinearMap.id := by
    rw [hT, blk_eq, hU, ← Matrix.toLin'_mul,
      Matrix.mul_nonsing_inv _ (isUnit_det_blk L hs1 hsp), Matrix.toLin'_one]
  have hTH : T ∘ₗ Hop (psiWt p N (s + 1)) = Hop (psiWt p N (s + 1)) ∘ₗ T := by
    rw [hT, LinearMap.comp_assoc, iota_H L hs1 hsp, ← LinearMap.comp_assoc, selProj_H,
      LinearMap.comp_assoc]
  have hUH : U ∘ₗ Hop (psiWt p N (s + 1)) = Hop (psiWt p N (s + 1)) ∘ₗ U := by
    calc U ∘ₗ Hop (psiWt p N (s + 1))
        = U ∘ₗ Hop (psiWt p N (s + 1)) ∘ₗ (T ∘ₗ U) := by rw [hTU]; rfl
      _ = U ∘ₗ (T ∘ₗ Hop (psiWt p N (s + 1))) ∘ₗ U := by
          rw [hTH]; rfl
      _ = (U ∘ₗ T) ∘ₗ Hop (psiWt p N (s + 1)) ∘ₗ U := rfl
      _ = Hop (psiWt p N (s + 1)) ∘ₗ U := by rw [hUT]; rfl
  have hrH : rho L ∘ₗ H (Zs L) = Hop (psiWt p N (s + 1)) ∘ₗ rho L := by
    rw [rho, LinearMap.comp_assoc, selProj_H, ← LinearMap.comp_assoc, ← hU, hUH,
      LinearMap.comp_assoc]
  exact wtPres_of_comm_Hop (rho L) hrH z k h

end rho

end ColouredSand.OddTwist
