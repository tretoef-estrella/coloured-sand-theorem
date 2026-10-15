module

public import RequestProject.OddSES.PartP2

/-!
# `CSI4_the_short_exact_sequences.md`: Part P, (P2)–(P3) — the last embedding `ι_p`

Encodings:

* `t` is `p − 1` (we write `t + 1 = p`, `ht`), `Z = Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)`
  is `V ⊗ Ψ_{p−1}(N)` (basis `Fin 2 × (Bool × Fin p × N.ι)`), and `tv e (aV p j n)`,
  `tv e (cV p j n)` are `b̂_e ⊗ A'_j n`, `b̂_e ⊗ C'_j n`.
* `alphaP p N n = α(n) = b̂_0 ⊗ A'_0 n − p·b̂_1 ⊗ C'_0(En)` and
  `gammaP p N w n = γ(n) = b̂_0 ⊗ C'_1 n + b̂_1 ⊗ A'_{p−1} n − pw·b̂_1 ⊗ C'_0 n` (for `n` of
  weight `w`) are the formulas of (P2); they are CSI3's `alphaL p N t`, `gammaL p N t w` for
  `t = p − 1`.
* `iotaP p N t h1 h2 = iota (psiD p N t h1 h2) ∘ Pinv p N` is `ι_p`: by (P1) it sends
  `b_j (b̂_0 ⊗ n) ↦ (Z.Fd 1)^j α(n)` and `b_j (b̂_1 ⊗ n) ↦ −(Z.Fd 1)^j γ(n)` (`P2`).
* `iotaPHom p N t h1 h2 ht : Hom (Psip p N) Z` is `ι_p` as a morphism (by (Q0c)), and
  `rhoP p N t h1 h2 = Pmap p N ∘ rho (psiD p N t h1 h2)` is a weight-preserving left inverse
  (CSI3's retraction `ρ = block⁻¹ ∘ projection`, whose block is `D + pK` with unit diagonal:
  `blk_entry_p`, `isUnit_det_blk_p`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

/-! ### The block (CSI3 (I3) with `r = p`) -/

section block

variable {t : ℕ} (L : PsiData p N t)

/-- (P3) the entries of the square block of `ι` (CSI3 (I3)) are, modulo `p`, those of the
diagonal matrix with entries `dval` (`1`, and `r − 1 = t` at `C_{p−1} e_i`). -/
lemma blk_entry_p (k k' : Bool × Fin p × N.ι) :
    ∃ e, iota L (Pi.single k 1) (sel p N k') - (if k' = k then dval p N t k else 0) =
      (p : ℤ_[p]) * e := by
  obtain ⟨b, j, i⟩ := k
  cases b
  · obtain ⟨e, he⟩ := (iota_aV_modP L j.isLt (Pi.single i 1)).coord (sel p N k')
    rw [vA_sel] at he
    refine ⟨e, ?_⟩
    rw [single_false, ← he]
    by_cases hk : k' = (false, j, i) <;> simp [hk, dval]
  · obtain ⟨e, he⟩ :=
      (iota_cV_modP L j.isLt (inWt_single (A := ℤ_[p]) N.wt i)).coord (sel p N k')
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

variable (ht1 : 1 ≤ t) (htp : t < p)
include ht1 htp

/-- (P3) the block is invertible: modulo `p` it is diagonal with entries `1` and
`r − 1 = t = p − 1`, a unit. -/
lemma isUnit_det_blk_p : IsUnit (blkMat L).det := by
  have hp0 : (PadicInt.toZMod (p : ℤ_[p]) : ZMod p) = 0 := by simp
  have hmap : (blkMat L).map (PadicInt.toZMod (p := p)) =
      Matrix.diagonal (fun k => PadicInt.toZMod (dval p N t k)) := by
    ext k' k
    obtain ⟨e, he⟩ := blk_entry_p L k k'
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

/-- (P3) `ρ ∘ ι = id` (CSI3's `ρ`, for `r − 1 = t`, `1 ≤ t < p`). -/
theorem rho_iota_p : rho L ∘ₗ iota L = LinearMap.id := by
  rw [rho, LinearMap.comp_assoc, blk_eq, ← Matrix.toLin'_mul,
    Matrix.nonsing_inv_mul _ (isUnit_det_blk_p L ht1 htp), Matrix.toLin'_one]

omit ht1 htp in
include ht1 htp in
/-- (P3) `ρ ∘ H = H ∘ ρ` for `r = p` (so `ρ` is weight-preserving). -/
theorem rho_H_p (ht : t + 1 = p) :
    rho L ∘ₗ H (Zs L) = Hop (psiWt p N p) ∘ₗ rho L := by
  set U := Matrix.toLin' (blkMat L)⁻¹ with hU
  set T := selProj p N ∘ₗ iota L with hT
  have hUT : U ∘ₗ T = LinearMap.id := rho_iota_p L ht1 htp
  have hTU : T ∘ₗ U = LinearMap.id := by
    rw [hT, blk_eq, hU, ← Matrix.toLin'_mul,
      Matrix.mul_nonsing_inv _ (isUnit_det_blk_p L ht1 htp), Matrix.toLin'_one]
  have hsel : selProj p N ∘ₗ H (Zs L) = Hop (psiWt p N p) ∘ₗ selProj p N := by
    have := selProj_H L; rwa [ht] at this
  have hTH : T ∘ₗ Hop (psiWt p N p) = Hop (psiWt p N p) ∘ₗ T := by
    rw [hT, LinearMap.comp_assoc, iota_H_p L ht, ← LinearMap.comp_assoc, hsel,
      LinearMap.comp_assoc]
  have hUH : U ∘ₗ Hop (psiWt p N p) = Hop (psiWt p N p) ∘ₗ U := by
    calc U ∘ₗ Hop (psiWt p N p)
        = U ∘ₗ Hop (psiWt p N p) ∘ₗ (T ∘ₗ U) := by rw [hTU]; rfl
      _ = U ∘ₗ (T ∘ₗ Hop (psiWt p N p)) ∘ₗ U := by rw [hTH]; rfl
      _ = (U ∘ₗ T) ∘ₗ Hop (psiWt p N p) ∘ₗ U := rfl
      _ = Hop (psiWt p N p) ∘ₗ U := by rw [hUT]; rfl
  rw [rho, LinearMap.comp_assoc, hsel, ← LinearMap.comp_assoc, ← hU, hUH, LinearMap.comp_assoc]

end block

/-! ### `ι_p` -/

section iotaP

variable (p N)

/-- (P2) `α(n) = b̂_0 ⊗ A'_0 n − p·b̂_1 ⊗ C'_0(En)`. -/
def alphaP : (N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) :=
  tv 0 ∘ₗ aV p 0 - (p : ℤ_[p]) • (tv 1 ∘ₗ cV p 0 ∘ₗ N.Ed 1)

/-- (P2) `γ(n) = b̂_0 ⊗ C'_1 n + b̂_1 ⊗ A'_{p−1} n − pw·b̂_1 ⊗ C'_0 n` (`n` of weight `w`). -/
def gammaP (w : ℤ) : (N.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) :=
  tv 0 ∘ₗ cV p 1 + tv 1 ∘ₗ aV p (p - 1) - ((p : ℤ_[p]) * w) • (tv 1 ∘ₗ cV p 0)

/-- (P2) the map `ι_p : Φ_p(V ⊗ N) → V ⊗ Ψ_{p−1}(N)`: CSI3's `ι` for `r = p`, composed with the
identification (P1). -/
def iotaP (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ p - 1) :
    (Fin p × (Fin 2 × N.ι) → ℤ_[p]) →ₗ[ℤ_[p]] (Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) :=
  iota (psiD p N t h1 h2) ∘ₗ Pinv p N

/-- (P3) the left inverse `ρ_p = Pmap ∘ ρ` of `ι_p`. -/
def rhoP (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ p - 1) :
    (Fin 2 × (Bool × Fin p × N.ι) → ℤ_[p]) →ₗ[ℤ_[p]] (Fin p × (Fin 2 × N.ι) → ℤ_[p]) :=
  Pmap p N ∘ₗ rho (psiD p N t h1 h2)

variable {p N} (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ p - 1) (ht : t + 1 = p)
include ht

lemma alphaL_eq_alphaP : alphaL p N t = alphaP p N := by
  rw [alphaL, alphaP, show p - (t + 1) = 0 by omega]

lemma gammaL_eq_gammaP (w : ℤ) : gammaL p N t w = gammaP p N w := by
  rw [gammaL, gammaP, show t = p - 1 by omega, cast_t_eq (show p - 1 + 1 = p by omega)]
  congr 2; ring

omit ht in
lemma Pinv_Pmap_apply (x : Bool × Fin p × N.ι → ℤ_[p]) : Pinv p N (Pmap p N x) = x :=
  LinearMap.congr_fun Pinv_Pmap x

omit ht in
lemma Pmap_Pinv_apply (y : Fin p × (Fin 2 × N.ι) → ℤ_[p]) : Pmap p N (Pinv p N y) = y :=
  LinearMap.congr_fun Pmap_Pinv y

/-- (P2) **The last embedding `ι_p`.** With `t = p − 1` and `Z = V ⊗ Ψ_{p−1}(N)`:
`ι_p(b_j (b̂_0 ⊗ n)) = (Z.Fd 1)^j α(n)` and `ι_p(b_j (b̂_1 ⊗ n)) = −(Z.Fd 1)^j γ(n)` (`n` of
weight `w`), with `α`, `γ` the formulas of CSI3 (I1) for `r = p`. -/
theorem P2 :
    (∀ (j : ℕ) (n : N.ι → ℤ_[p]), j < p →
      iotaP p N t h1 h2 (bv p j (tv 0 n)) =
        ((Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)).Fd 1 ^ j) (alphaP p N n)) ∧
    (∀ (j : ℕ) (w : ℤ) (n : N.ι → ℤ_[p]), j < p → InWt N.wt w n →
      iotaP p N t h1 h2 (bv p j (tv 1 n)) =
        -((Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)).Fd 1 ^ j) (gammaP p N w n)) := by
  refine ⟨fun j n hj => ?_, fun j w n hj hn => ?_⟩
  · rw [iotaP, LinearMap.comp_apply, Pinv_bv0, iota_aV _ hj, alphaL_eq_alphaP t ht]; rfl
  · rw [iotaP, LinearMap.comp_apply, Pinv_bv1, map_neg, iota_cV _ hj hn,
      gammaL_eq_gammaP t ht]; rfl

lemma Pinv_F : Pinv p N ∘ₗ (Psip p N).Fd 1 = psiF p N p ∘ₗ Pinv p N := by
  refine LinearMap.ext fun y => Pmap_injective ?_
  change Pmap p N (Pinv p N ((Psip p N).Fd 1 y)) = Pmap p N (psiF p N p (Pinv p N y))
  rw [Pmap_Pinv_apply, show Pmap p N (psiF p N p (Pinv p N y)) =
    (Psip p N).Fd 1 (Pmap p N (Pinv p N y)) from LinearMap.congr_fun Pmap_F _, Pmap_Pinv_apply]

lemma Pinv_E : Pinv p N ∘ₗ (Psip p N).Ed 1 = psiE p N p ∘ₗ Pinv p N := by
  refine LinearMap.ext fun y => Pmap_injective ?_
  change Pmap p N (Pinv p N ((Psip p N).Ed 1 y)) = Pmap p N (psiE p N p (Pinv p N y))
  rw [Pmap_Pinv_apply, show Pmap p N (psiE p N p (Pinv p N y)) =
    (Psip p N).Ed 1 (Pmap p N (Pinv p N y)) from LinearMap.congr_fun Pmap_E _, Pmap_Pinv_apply]

lemma Pinv_H : Pinv p N ∘ₗ H (Psip p N) = Hop (psiWt p N p) ∘ₗ Pinv p N := by
  refine LinearMap.ext fun y => Pmap_injective ?_
  change Pmap p N (Pinv p N (H (Psip p N) y)) = Pmap p N (Hop (psiWt p N p) (Pinv p N y))
  rw [Pmap_Pinv_apply, show Pmap p N (Hop (psiWt p N p) (Pinv p N y)) =
    H (Psip p N) (Pmap p N (Pinv p N y)) from LinearMap.congr_fun Pmap_H _, Pmap_Pinv_apply]

lemma iotaP_F : iotaP p N t h1 h2 ∘ₗ (Psip p N).Fd 1 =
    (Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)).Fd 1 ∘ₗ iotaP p N t h1 h2 := by
  rw [iotaP, LinearMap.comp_assoc, Pinv_F t ht, ← LinearMap.comp_assoc,
    iota_F_p _ ht]
  rfl

lemma iotaP_E : iotaP p N t h1 h2 ∘ₗ (Psip p N).Ed 1 =
    (Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)).Ed 1 ∘ₗ iotaP p N t h1 h2 := by
  rw [iotaP, LinearMap.comp_assoc, Pinv_E t ht, ← LinearMap.comp_assoc,
    iota_E_p _ ht]
  rfl

lemma iotaP_H : iotaP p N t h1 h2 ∘ₗ H (Psip p N) =
    H (Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)) ∘ₗ iotaP p N t h1 h2 := by
  rw [iotaP, LinearMap.comp_assoc, Pinv_H t ht, ← LinearMap.comp_assoc,
    iota_H_p _ ht]
  rfl

variable (p N) in
/-- (P3) `ι_p` as a morphism `Hom (Psip p N) (V ⊗ psi p N (p − 1))` (by (Q0c)). -/
def iotaPHom : Hom (Psip p N) (Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)) :=
  Q0c (iotaP p N t h1 h2) (iotaP_F t h1 h2 ht) (iotaP_E t h1 h2 ht) (iotaP_H t h1 h2 ht)

lemma rhoP_iotaP : rhoP p N t h1 h2 ∘ₗ iotaP p N t h1 h2 = LinearMap.id := by
  rw [rhoP, iotaP, LinearMap.comp_assoc, ← LinearMap.comp_assoc (Pinv p N),
    rho_iota_p _ h1 (by omega), LinearMap.id_comp, Pmap_Pinv]

lemma rhoP_H : rhoP p N t h1 h2 ∘ₗ H (Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)) =
    H (Psip p N) ∘ₗ rhoP p N t h1 h2 := by
  rw [rhoP, LinearMap.comp_assoc, show H (Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)) =
    H (Zs (psiD p N t h1 h2)) from rfl, rho_H_p _ h1 (by omega) ht, ← LinearMap.comp_assoc,
    Pmap_H, LinearMap.comp_assoc]

/-- (P3) **`ι_p` is a morphism, injective, with a weight-preserving left inverse.** The
morphism `iotaPHom` has underlying map `ι_p`; `ρ_p ∘ ι_p = id`; `ρ_p` is weight-preserving;
and the block of `ι_p` on the coordinates of CSI3 (I3) (with `r = p`) is `D + pK` with
unit diagonal `D` (entries `1` and `r − 1 = p − 1`), hence invertible. -/
theorem P3 :
    (iotaPHom p N t h1 h2 ht).toLin = iotaP p N t h1 h2 ∧
    Function.Injective (iotaPHom p N t h1 h2 ht).toLin ∧
    rhoP p N t h1 h2 ∘ₗ (iotaPHom p N t h1 h2 ht).toLin = LinearMap.id ∧
    (∀ z k, (Tensor2.tensor (V ℤ_[p]) (psi p N t h1 h2)).wt z ≠ (Psip p N).wt k →
      rhoP p N t h1 h2 (Pi.single z 1) k = 0) ∧
    (∀ k k', ∃ e, iota (psiD p N t h1 h2) (Pi.single k 1) (sel p N k') -
      (if k' = k then dval p N t k else 0) = (p : ℤ_[p]) * e) ∧
    (∀ k, IsUnit (dval p N t k)) ∧
    IsUnit (blkMat (psiD p N t h1 h2)).det := by
  have hl := rhoP_iotaP (N := N) t h1 h2 ht
  refine ⟨rfl, fun x y hxy => ?_, hl, wtPres_of_comm_Hop _ (rhoP_H (N := N) t h1 h2 ht),
    blk_entry_p _, fun k => ?_, isUnit_det_blk_p _ h1 (by omega)⟩
  · have hx := LinearMap.congr_fun hl x
    have hy := LinearMap.congr_fun hl y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
    rw [← hx, ← hy]
    exact congrArg _ hxy
  · simp only [dval]
    split_ifs
    · exact isUnit_natCast_of_not_dvd p fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    · exact isUnit_one

end iotaP

end ColouredSand.OddTwist
