module

public import RequestProject.Blocks.Simple
public import RequestProject.Blocks.Elim
public import RequestProject.Blocks.Numbers

/-!
# The cokernel of `Mblk`, reduced to a `2 × 2` block (CSG1, §3 "Elimination")

This file carries out the elimination of §3 of `CSG1_lemma_8_the_blocks.md` for the matrix
`Mblk` of §1:

1. `range_Mblk`: under `(ι → R) ≃ (Fin (λ+1) → R) × (Fin (μ+1) → R)`
   (`LinearEquiv.sumArrowLequivProdArrow`, `inl` = the `ℓ`-chain, `inr` = the `s̃`-chain), the
   range of `Mblk` is the glued two-chain relation module `gluedRel`;
2. contracting the unit links (`gluedSegRedEquiv`, segment length `p`);
3. treating the glue (`elimUnitEquiv` if `r ≤ p − 1`, `elimReindexEquiv` if `r = p`);
4. clearing the `2a` links `p · unit` (`uPchainEquiv`).

The outcome (`block_core`) is `coker Mblk ≅ (R ⧸ p)^a × (R ⧸ p)^a × R² ⧸ span{(X₁, X₂), (0, Y₂)}`
with `p^a X₁ ≈ ∏_{t < (a+1)p} N t`, `p^a X₂ ≈ p^{τ + A'}` and `p^a Y₂ ≈ p^{α + A'}`
(`≈` = equal up to a unit, Mathlib's `Associated`).
-/

@[expose] public section

open Finset Submodule

namespace ColouredSand.Blocks

variable {p : ℕ} [hp : Fact p.Prime] {q c k r a : ℕ}

/-- The subdiagonal `i ↦ i + 1` of both chains. -/
noncomputable def linkS (i : ℕ) : ℤ_[p] := ((i : ℕ) : ℤ_[p]) + 1

/-- The range of `Mblk`, transported to `R^{λ+1} × R^{μ+1}`, is the glued chain system. -/
lemma range_Mblk :
    (LinearMap.range (Matrix.mulVecLin (Mblk p q c k r a))).map
      ((LinearEquiv.sumArrowLequivProdArrow (Fin (lam p r a + 1)) (Fin (mu p r a + 1)) ℤ_[p]
        ℤ_[p]) : (Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1) → ℤ_[p]) →ₗ[ℤ_[p]]
          (Fin (lam p r a + 1) → ℤ_[p]) × (Fin (mu p r a + 1) → ℤ_[p])) =
      gluedRel (lam p r a) (mu p r a) (Nt p q c k) linkS (fun j => Nt p q c k (j + r))
        linkS (mu p r a + r + 1) (uGlue p r a : ℤ_[p]) := by
  rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp, gluedRel]
  congr 2
  funext y
  rcases y with i | j
  · simp only [Function.comp_apply, LinearEquiv.coe_coe, gluedCol]
    refine Prod.ext ?_ ?_
    · ext i'
      simp only [LinearEquiv.sumArrowLequivProdArrow_apply_fst,
        Matrix.col_apply, Mblk, Matrix.of_apply, chainCol, Pi.add_apply, Pi.smul_apply, ev_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, linkS]
      by_cases h : i' = i
      · subst h; simp
      · have h' : (i' : ℕ) ≠ i := fun h'' => h (Fin.ext h'')
        simp [h, h']
    · ext j'
      simp [Mblk]
  · simp only [Function.comp_apply, LinearEquiv.coe_coe, gluedCol]
    refine Prod.ext ?_ ?_
    · ext i'
      simp only [LinearEquiv.sumArrowLequivProdArrow_apply_fst,
        Matrix.col_apply, Mblk, Matrix.of_apply]
      by_cases hj : (j : ℕ) = mu p r a
      · by_cases hi : (i' : ℕ) = mu p r a + r + 1 <;> simp [hj, hi]
      · simp [hj]
    · ext j'
      simp only [LinearEquiv.sumArrowLequivProdArrow_apply_snd,
        Matrix.col_apply, Mblk, Matrix.of_apply, chainCol, Pi.add_apply, Pi.smul_apply, ev_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, linkS]
      by_cases h : j' = j
      · subst h; simp
      · have h' : (j' : ℕ) ≠ j := fun h'' => h (Fin.ext h'')
        simp [h, h']

/-- The cokernel of `Mblk` as the quotient by the glued chain relations. -/
noncomputable def mblkCokerEquiv :
    ((Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1) → ℤ_[p]) ⧸
      LinearMap.range (Matrix.mulVecLin (Mblk p q c k r a))) ≃ₗ[ℤ_[p]]
    (((Fin (lam p r a + 1) → ℤ_[p]) × (Fin (mu p r a + 1) → ℤ_[p])) ⧸
      gluedRel (lam p r a) (mu p r a) (Nt p q c k) linkS (fun j => Nt p q c k (j + r))
        linkS (mu p r a + r + 1) (uGlue p r a : ℤ_[p])) :=
  Submodule.Quotient.equiv _ _ _ range_Mblk

lemma linkS_unit (i : ℕ) (h : (i + 1) % p ≠ 0) : IsUnit (linkS (p := p) i) :=
  isUnit_link_of_not_dvd i h

lemma linkS_unit_of_lt {i : ℕ} (h : i + 1 < p) : IsUnit (linkS (p := p) i) :=
  isUnit_succ_of_lt h

/-- The broken links `t p` are `p (t + 1)`. -/
lemma segS_linkS (t : ℕ) : segS p linkS t = (p : ℤ_[p]) * (((t : ℕ) : ℤ_[p]) + 1) := by
  have hp0 := hp.out.pos
  simp only [segS, linkS]
  have h1 : t * p + p - 1 + 1 = t * p + p := by omega
  have h2 : (((t * p + p - 1 : ℕ) : ℤ_[p]) + 1) = ((t * p + p - 1 + 1 : ℕ) : ℤ_[p]) := by
    push_cast; ring
  rw [h2, h1]; push_cast; ring

/-- `(a+1) p = p^τ` up to a unit. -/
lemma segS_linkS_assoc (ha : a ≤ p - 1) :
    Associated (segS p linkS a) ((p : ℤ_[p]) ^ blkTau p a) := by
  have h2 := hp.out.two_le
  have h := natCast_associated (p := p) (n := (a + 1) * p) (by positivity)
  rw [padicValNat.mul (by omega) hp.out.ne_zero, val_succ_a ha, padicValNat_self] at h
  rw [segS_linkS]
  have h3 : blkTau p a = (if a = p - 1 then 1 else 0) + 1 := by
    unfold blkTau; split_ifs <;> rfl
  rw [h3]
  convert h using 1
  push_cast; ring

/-- Products of `N t` over sets avoiding `t = 0` (when `c + k = 0`) are `p`-powers up to
units. -/
lemma prod_Nt_associated' (hq : 1 ≤ padicValNat p q) (s : Finset ℕ)
    (hs : ∀ t ∈ s, 1 ≤ c + k + t) :
    Associated (∏ t ∈ s, Nt p q c k t) ((p : ℤ_[p]) ^ ∑ t ∈ s, vt p q c k t) := by
  rw [← prod_pow_eq_pow_sum]
  exact Associated.prod _ _ _ (fun t ht => Nt_associated hq (hs t ht))

/-- The product over the last segment of the `ℓ`-chain is `p^α` up to a unit. -/
lemma prod_alpha_assoc (hq : 1 ≤ padicValNat p q) :
    Associated (∏ t ∈ Ico ((a + 1) * p) (lam p r a + 1), Nt p q c k t)
      ((p : ℤ_[p]) ^ blkAlpha p q c k r a) := by
  have h2 := hp.out.two_le
  have := prod_Nt_associated' (c := c) (k := k) hq (Ico ((a + 1) * p) (lam p r a + 1))
    (fun t ht => by
      rw [mem_Ico] at ht
      have : 1 ≤ (a + 1) * p := Nat.one_le_iff_ne_zero.2 (by positivity)
      omega)
  rwa [Finset.Ico_add_one_right_eq_Icc] at this

/-- The product along the whole `s̃`-chain is `p^{A'}` up to a unit. -/
lemma prod_A'_assoc (hq : 1 ≤ padicValNat p q) (hr1 : 1 ≤ r) :
    Associated (∏ j ∈ range (mu p r a + 1), Nt p q c k (j + r))
      ((p : ℤ_[p]) ^ blkA' p q c k r a) := by
  have h1 : blkA' p q c k r a = ∑ j ∈ range (mu p r a + 1), vt p q c k (j + r) := by
    rw [blkA', ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
      show r + mu p r a + 1 - r = mu p r a + 1 by omega]
    exact sum_congr rfl (fun j _ => by rw [add_comm])
  rw [h1, ← prod_pow_eq_pow_sum]
  exact Associated.prod _ _ _ (fun j _ => Nt_associated hq (by omega))

section segprod

variable {n : ℕ} {d s : ℕ → ℤ_[p]}

/-- The first `m` full segments: `∏_{t<m} segD t ≈ ∏_{i < m p} d i`. -/
lemma seg_prod_assoc (hs : ∀ i < n, (i + 1) % p ≠ 0 → IsUnit (s i)) {m : ℕ}
    (hm : m * p ≤ n + 1) :
    Associated (∏ t ∈ range m, segD n p d s t) (∏ i ∈ range (m * p), d i) := by
  have hp0 := hp.out.pos
  rw [← prod_segments d p m]
  refine Associated.prod _ _ _ (fun t ht => ?_)
  have ht' : t + 1 ≤ m := by simp at ht; omega
  have h3 := Nat.mul_le_mul_right p ht'
  rw [Nat.add_mul, one_mul] at h3
  have h4 : min (t * p + p - 1) n + 1 = t * p + p := by omega
  have := segD_associated hp0 (d := d) hs (t := t)
    (Nat.le_div_iff_mul_le hp0 |>.2 (by omega))
  rwa [h4] at this

/-- All segments, the last one possibly partial: `∏_{t ≤ n/p} segD t ≈ ∏_{i ≤ n} d i`. -/
lemma seg_prod_full_assoc (hs : ∀ i < n, (i + 1) % p ≠ 0 → IsUnit (s i)) {m : ℕ}
    (hm : n / p = m) :
    Associated (∏ t ∈ range (m + 1), segD n p d s t) (∏ i ∈ range (n + 1), d i) := by
  have hp0 := hp.out.pos
  have h1 : m * p ≤ n := by rw [← hm]; exact Nat.div_mul_le_self n p
  have h2 : n < m * p + p := by
    rw [← hm]; have := Nat.lt_div_mul_add (a := n) hp0; linarith
  rw [prod_range_succ, ← prod_range_mul_prod_Ico d (show m * p ≤ n + 1 by omega)]
  refine (seg_prod_assoc hs (by omega)).mul_mul ?_
  have h4 : min (m * p + p - 1) n + 1 = n + 1 := by omega
  have := segD_associated hp0 (d := d) hs (t := m) (by omega)
  rwa [h4] at this

/-- The `ϖ`-chain coefficient after contracting: `p^a (segD a · κ_a) ≈ ∏_{i < (a+1) p} d i`. -/
lemma pchain_prod_assoc (hs : ∀ i < n, (i + 1) % p ≠ 0 → IsUnit (s i)) {a : ℕ}
    {P w : ℕ → ℤ_[p]} (hD : ∀ t < a, segD n p d s t = p * P t) (hw : ∀ t < a, IsUnit (w t))
    (hn : (a + 1) * p ≤ n + 1) :
    Associated ((p : ℤ_[p]) ^ a * (segD n p d s a * pcCoef P w a))
      (∏ i ∈ range ((a + 1) * p), d i) := by
  have h1 : (p : ℤ_[p]) ^ a * (segD n p d s a * pcCoef P w a) =
      segD n p d s a * ((p : ℤ_[p]) ^ a * pcCoef P w a) := by ring
  rw [h1]
  refine ((pcCoef_associated (p : ℤ_[p]) a hD hw).mul_left _).trans ?_
  rw [mul_comm, ← prod_range_succ]
  exact seg_prod_assoc hs hn

end segprod

lemma uGlue_ne_zero (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1) (hra : r = p → a = p - 1) :
    uGlue p r a ≠ 0 := by
  have hdvd := (glue_exponent_N hr1 hrp ha hra).2.1
  have hC0 : Nat.choose (mu p r a + r) (mu p r a) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hn0 : Nat.choose (mu p r a + r) (mu p r a) * (a + 1) * p ≠ 0 := by
    have := hp.out.ne_zero; positivity
  intro h
  have := Nat.div_mul_cancel hdvd
  rw [← uGlue, h, zero_mul] at this
  exact hn0 this.symm

/-- For `r ≤ p − 1` the glue entry is a unit. -/
lemma uGlue_isUnit (hr1 : 1 ≤ r) (hrp : r ≤ p - 1) (ha : a ≤ p - 1) :
    IsUnit (uGlue p r a : ℤ_[p]) := by
  have h2 := hp.out.two_le
  have hra : r = p → a = p - 1 := fun h => by omega
  have h := natCast_associated (p := p) (uGlue_ne_zero hr1 (by omega) ha hra)
  rw [(glue_exponent_N hr1 (by omega) ha hra).2.2.2.1 hrp, pow_zero] at h
  exact associated_one_iff_isUnit.1 h

/-- For `r = p` the glue entry is `p · unit`. -/
lemma uGlue_eq_p_mul (hr1 : 1 ≤ r) (hrp : r = p) (ha : a = p - 1) :
    ∃ v : ℤ_[p], IsUnit v ∧ (uGlue p r a : ℤ_[p]) = p * v := by
  have hra : r = p → a = p - 1 := fun _ => ha
  have h := natCast_associated (p := p) (uGlue_ne_zero hr1 (by omega) (by omega) hra)
  rw [(glue_exponent_N hr1 (by omega) (by omega) hra).2.2.2.2 hrp, pow_one] at h
  obtain ⟨v, hv⟩ := h.symm
  exact ⟨v, v.isUnit, hv.symm⟩

/-- `segD (a+1)` on the `ℓ`-chain (its last segment) is `p^α` up to a unit. -/
lemma segD_last_assoc (hq : 1 ≤ padicValNat p q) (hr1 : 1 ≤ r) (hrp : r ≤ p) :
    Associated (segD (lam p r a) p (Nt p q c k) linkS (a + 1))
      ((p : ℤ_[p]) ^ blkAlpha p q c k r a) := by
  have hp0 := hp.out.pos
  have hl := lam_eq (p := p) r a
  have hring2 : (a + 1 + 1) * p = (a + 1) * p + p := by ring
  have hlp : lam p r a / p = a + 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h4 : min ((a + 1) * p + p - 1) (lam p r a) + 1 = lam p r a + 1 := by omega
  have := segD_associated hp0 (n := lam p r a) (d := Nt p q c k) (s := linkS)
    (fun i _ h => linkS_unit i h) (t := a + 1) (by omega)
  rw [h4] at this
  exact this.trans (prod_alpha_assoc hq)

/-- The statement shape shared by both glue cases. -/
def BlockCoreSpec (p : ℕ) [Fact p.Prime] (q c k r a : ℕ) : Prop :=
  ∃ X1 X2 Y2 : ℤ_[p],
    Associated ((p : ℤ_[p]) ^ a * X1) (∏ t ∈ range ((a + 1) * p), Nt p q c k t) ∧
    Associated ((p : ℤ_[p]) ^ a * X2) ((p : ℤ_[p]) ^ (blkTau p a + blkA' p q c k r a)) ∧
    Associated ((p : ℤ_[p]) ^ a * Y2)
      ((p : ℤ_[p]) ^ (blkAlpha p q c k r a + blkA' p q c k r a)) ∧
    Nonempty (((Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (Mblk p q c k r a))) ≃ₗ[ℤ_[p]]
      (((Fin a → ℤ_[p]) ⧸ piSpan a (p : ℤ_[p])) × ((Fin a → ℤ_[p]) ⧸ piSpan a (p : ℤ_[p]))) ×
        ((ℤ_[p] × ℤ_[p]) ⧸ span ℤ_[p] {((X1, X2) : ℤ_[p] × ℤ_[p]), (0, Y2)}))

/-- The elimination when the glue entry is a unit (`r ≤ p − 1`). -/
lemma block_core_lt (hq : 1 ≤ padicValNat p q) (hr1 : 1 ≤ r) (hrp : r ≤ p - 1)
    (ha : a ≤ p - 1) : BlockCoreSpec p q c k r a := by
  have h2 := hp.out.two_le
  have hp0 : 0 < p := by omega
  have hra : r = p → a = p - 1 := fun h => by omega
  have hl := lam_eq (p := p) r a
  obtain ⟨hmu, h2r⟩ := mu_add (p := p) r a (by omega) hra
  have hring : (a + 1) * p = a * p + p := by ring
  have hring2 : (a + 1 + 1) * p = a * p + p + p := by ring
  have hlp : lam p r a / p = a + 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hmp : mu p r a / p = a := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hgp : (mu p r a + r + 1) / p = a + 1 := by rw [hmu]; exact Nat.mul_div_cancel _ hp0
  have hs : ∀ i < lam p r a, (i + 1) % p ≠ 0 → IsUnit (linkS (p := p) i) :=
    fun i _ h => linkS_unit i h
  have hs' : ∀ i < mu p r a, (i + 1) % p ≠ 0 → IsUnit (linkS (p := p) i) :=
    fun i _ h => linkS_unit i h
  have hg : mu p r a + r + 1 ≤ lam p r a := by omega
  have hgL : (mu p r a + r + 1) % p = 0 := by rw [hmu]; simp
  set d₁ := Nt p q c k
  set d₂ : ℕ → ℤ_[p] := fun j => Nt p q c k (j + r)
  set D := segD (lam p r a) p d₁ linkS
  set S := segS p (linkS (p := p))
  set D' := segD (mu p r a) p d₂ linkS
  set u : ℤ_[p] := (uGlue p r a : ℤ_[p])
  obtain ⟨E1⟩ : Nonempty (((Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1) → ℤ_[p]) ⧸
          LinearMap.range (Matrix.mulVecLin (Mblk p q c k r a))) ≃ₗ[ℤ_[p]]
      (((Fin (lam p r a / p + 1) → ℤ_[p]) × (Fin (mu p r a / p + 1) → ℤ_[p])) ⧸
        gluedRel (lam p r a / p) (mu p r a / p) D S D' S ((mu p r a + r + 1) / p) u)) :=
    ⟨mblkCokerEquiv.trans (gluedSegRedEquiv hp0 hs hs' hg hgL)⟩
  rw [hlp, hmp, hgp] at E1
  have hu : IsUnit u := uGlue_isUnit (p := p) hr1 hrp ha
  have hiu : IsUnit (-Ring.inverse u) := (isUnit_ringInverse.mpr hu).neg
  set cc : ℤ_[p] := -Ring.inverse u * D' a
  set D₂ : ℕ → ℤ_[p] := fun t => if t = a then D (a + 1) * cc else D' t
  set β : ℤ_[p] := S a * cc
  have hDv : ∀ t, (p : ℤ_[p]) ∣ D t := fun t => p_dvd_segD hq _ p t _
  have hDv' : ∀ t, (p : ℤ_[p]) ∣ D' t := fun t => Dvd.dvd.mul_right (p_dvd_Nt hq _) _
  set P₁ : ℕ → ℤ_[p] := fun t => (hDv t).choose
  set P₂ : ℕ → ℤ_[p] := fun t => (hDv' t).choose
  set w : ℕ → ℤ_[p] := fun t => ((t : ℕ) : ℤ_[p]) + 1
  have hD₁ : ∀ t < a, D t = p * P₁ t := fun t _ => (hDv t).choose_spec
  have hD₂ : ∀ t < a, D₂ t = p * P₂ t := fun t ht => by
    simp only [D₂, if_neg (show t ≠ a by omega)]; exact (hDv' t).choose_spec
  have hw : ∀ t < a, IsUnit (w t) := fun t ht => isUnit_succ_of_lt (by omega)
  have hS : ∀ t < a, S t = p * w t := fun t _ => segS_linkS t
  have hSa : S a = p * (((a : ℕ) : ℤ_[p]) + 1) := segS_linkS a
  have hβ : (p : ℤ_[p]) ∣ β :=
    Dvd.dvd.mul_right (by rw [hSa]; exact dvd_mul_right _ _) _
  have hDa₂ : (p : ℤ_[p]) ∣ D₂ a := by
    simp only [D₂, if_pos rfl]; exact Dvd.dvd.mul_right (hDv _) _
  have hW : Associated (D' a * ((p : ℤ_[p]) ^ a * pcCoef P₂ w a))
      ((p : ℤ_[p]) ^ blkA' p q c k r a) := by
    have hk := pcCoef_associated (p : ℤ_[p]) a hD₂ hw
    have h3 : ∏ t ∈ range a, D₂ t = ∏ t ∈ range a, D' t :=
      prod_congr rfl (fun t ht => by
        simp only [mem_range] at ht; simp only [D₂, if_neg (show t ≠ a by omega)])
    rw [h3] at hk
    refine (hk.mul_left (D' a)).trans ?_
    rw [mul_comm, ← prod_range_succ]
    exact (seg_prod_full_assoc hs' hmp).trans (prod_A'_assoc hq hr1)
  refine ⟨D a * pcCoef P₁ w a, β * pcCoef P₂ w a, D₂ a * pcCoef P₂ w a, ?_, ?_, ?_,
    ⟨(E1.trans (elimUnitEquiv hu)).trans
      (uPchainEquiv (p : ℤ_[p]) D S D₂ S β hD₁ hS hw hD₂ hS hw (hDv a) hβ hDa₂)⟩⟩
  · exact pchain_prod_assoc hs hD₁ hw (by omega)
  · have h3 : (p : ℤ_[p]) ^ a * (β * pcCoef P₂ w a) =
        (S a * -Ring.inverse u) * (D' a * ((p : ℤ_[p]) ^ a * pcCoef P₂ w a)) := by
      simp only [β, cc]; ring
    rw [h3, pow_add]
    exact ((associated_mul_unit_left _ _ hiu).trans (segS_linkS_assoc ha)).mul_mul hW
  · have h3 : (p : ℤ_[p]) ^ a * (D₂ a * pcCoef P₂ w a) =
        (D (a + 1) * -Ring.inverse u) * (D' a * ((p : ℤ_[p]) ^ a * pcCoef P₂ w a)) := by
      simp only [D₂, if_pos rfl, cc]; ring
    rw [h3, pow_add]
    exact ((associated_mul_unit_left _ _ hiu).trans
      (segD_last_assoc hq hr1 (by omega))).mul_mul hW

/-- The elimination when the glue is a `p`-link (`r = p`, hence `a = p − 1`). -/
lemma block_core_eq (hq : 1 ≤ padicValNat p q) (hr : r = p) (ha : a = p - 1) :
    BlockCoreSpec p q c k r a := by
  have h2 := hp.out.two_le
  have hp0 : 0 < p := by omega
  have hr1 : 1 ≤ r := by omega
  have hra : r = p → a = p - 1 := fun _ => ha
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hl := lam_eq (p := p) r (b + 1)
  obtain ⟨hmu, h2r⟩ := mu_add (p := p) r (b + 1) (by omega) hra
  have hring : (b + 1 + 1) * p = b * p + p + p := by ring
  have hring2 : (b + 2 + 1) * p = b * p + p + p + p := by ring
  have hring3 : (b + 1) * p = b * p + p := by ring
  have hring4 : (b + 2) * p = b * p + p + p := by ring
  have hlp : lam p r (b + 1) / p = b + 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hmp : mu p r (b + 1) / p = b := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hgp : (mu p r (b + 1) + r + 1) / p = b + 2 := by
    rw [hmu, Nat.mul_div_cancel _ hp0]
  have hs : ∀ i < lam p r (b + 1), (i + 1) % p ≠ 0 → IsUnit (linkS (p := p) i) :=
    fun i _ h => linkS_unit i h
  have hs' : ∀ i < mu p r (b + 1), (i + 1) % p ≠ 0 → IsUnit (linkS (p := p) i) :=
    fun i _ h => linkS_unit i h
  have hg : mu p r (b + 1) + r + 1 ≤ lam p r (b + 1) := by omega
  have hgL : (mu p r (b + 1) + r + 1) % p = 0 := by rw [hmu]; simp
  set d₁ := Nt p q c k
  set d₂ : ℕ → ℤ_[p] := fun j => Nt p q c k (j + r)
  set D := segD (lam p r (b + 1)) p d₁ linkS
  set S := segS p (linkS (p := p))
  set D' := segD (mu p r (b + 1)) p d₂ linkS
  set u : ℤ_[p] := (uGlue p r (b + 1) : ℤ_[p])
  obtain ⟨E1⟩ : Nonempty (((Fin (lam p r (b + 1) + 1) ⊕ Fin (mu p r (b + 1) + 1) → ℤ_[p]) ⧸
          LinearMap.range (Matrix.mulVecLin (Mblk p q c k r (b + 1)))) ≃ₗ[ℤ_[p]]
      (((Fin (lam p r (b + 1) / p + 1) → ℤ_[p]) × (Fin (mu p r (b + 1) / p + 1) → ℤ_[p])) ⧸
        gluedRel (lam p r (b + 1) / p) (mu p r (b + 1) / p) D S D' S
          ((mu p r (b + 1) + r + 1) / p) u)) :=
    ⟨mblkCokerEquiv.trans (gluedSegRedEquiv hp0 hs hs' hg hgL)⟩
  rw [hlp, hmp, hgp] at E1
  obtain ⟨v, hv, huv⟩ := uGlue_eq_p_mul (p := p) hr1 hr ha
  set D₂ : ℕ → ℤ_[p] := fun t => if t = b + 1 then D (b + 2) else D' t
  set S₂ : ℕ → ℤ_[p] := fun t => if t = b then u else S t
  have hDv : ∀ t, (p : ℤ_[p]) ∣ D t := fun t => p_dvd_segD hq _ p t _
  have hDv' : ∀ t, (p : ℤ_[p]) ∣ D' t := fun t => Dvd.dvd.mul_right (p_dvd_Nt hq _) _
  set P₁ : ℕ → ℤ_[p] := fun t => (hDv t).choose
  set P₂ : ℕ → ℤ_[p] := fun t => (hDv' t).choose
  set w : ℕ → ℤ_[p] := fun t => ((t : ℕ) : ℤ_[p]) + 1
  set w₂ : ℕ → ℤ_[p] := fun t => if t = b then v else ((t : ℕ) : ℤ_[p]) + 1
  have hD₁ : ∀ t < b + 1, D t = p * P₁ t := fun t _ => (hDv t).choose_spec
  have hD₂ : ∀ t < b + 1, D₂ t = p * P₂ t := fun t ht => by
    simp only [D₂, if_neg (show t ≠ b + 1 by omega)]; exact (hDv' t).choose_spec
  have hw : ∀ t < b + 1, IsUnit (w t) := fun t ht => isUnit_succ_of_lt (by omega)
  have hw₂ : ∀ t < b + 1, IsUnit (w₂ t) := fun t ht => by
    simp only [w₂]
    split_ifs
    · exact hv
    · exact isUnit_succ_of_lt (by omega)
  have hS : ∀ t < b + 1, S t = p * w t := fun t _ => segS_linkS t
  have hS₂ : ∀ t < b + 1, S₂ t = p * w₂ t := fun t _ => by
    simp only [S₂, w₂]
    split_ifs
    · exact huv
    · exact segS_linkS t
  have hSa : S (b + 1) = p * (((b + 1 : ℕ) : ℤ_[p]) + 1) := segS_linkS (b + 1)
  have hβ : (p : ℤ_[p]) ∣ S (b + 1) := by rw [hSa]; exact dvd_mul_right _ _
  have hDa₂ : (p : ℤ_[p]) ∣ D₂ (b + 1) := by
    simp only [D₂, if_pos rfl]; exact hDv _
  have hK : Associated ((p : ℤ_[p]) ^ (b + 1) * pcCoef P₂ w₂ (b + 1))
      ((p : ℤ_[p]) ^ blkA' p q c k r (b + 1)) := by
    have hk := pcCoef_associated (p : ℤ_[p]) (b + 1) hD₂ hw₂
    have h3 : ∏ t ∈ range (b + 1), D₂ t = ∏ t ∈ range (b + 1), D' t :=
      prod_congr rfl (fun t ht => by
        simp only [mem_range] at ht; simp only [D₂, if_neg (show t ≠ b + 1 by omega)])
    rw [h3] at hk
    exact (hk.trans (seg_prod_full_assoc hs' hmp)).trans (prod_A'_assoc hq hr1)
  refine ⟨D (b + 1) * pcCoef P₁ w (b + 1), S (b + 1) * pcCoef P₂ w₂ (b + 1),
    D₂ (b + 1) * pcCoef P₂ w₂ (b + 1), ?_, ?_, ?_,
    ⟨(E1.trans elimReindexEquiv).trans
      (uPchainEquiv (p : ℤ_[p]) D S D₂ S₂ (S (b + 1)) hD₁ hS hw hD₂ hS₂ hw₂ (hDv _) hβ
        hDa₂)⟩⟩
  · exact pchain_prod_assoc (n := lam p r (b + 1)) hs hD₁ hw (by omega)
  · have h3 : (p : ℤ_[p]) ^ (b + 1) * (S (b + 1) * pcCoef P₂ w₂ (b + 1)) =
        S (b + 1) * ((p : ℤ_[p]) ^ (b + 1) * pcCoef P₂ w₂ (b + 1)) := by ring
    rw [h3, pow_add (p : ℤ_[p]) (blkTau p (b + 1))]
    exact (segS_linkS_assoc (by omega)).mul_mul hK
  · have h3 : (p : ℤ_[p]) ^ (b + 1) * (D₂ (b + 1) * pcCoef P₂ w₂ (b + 1)) =
        D (b + 1 + 1) * ((p : ℤ_[p]) ^ (b + 1) * pcCoef P₂ w₂ (b + 1)) := by
      simp only [D₂, if_pos rfl]; ring
    rw [h3, pow_add (p : ℤ_[p]) (blkAlpha p q c k r (b + 1))]
    exact (segD_last_assoc (c := c) (k := k) (a := b + 1) hq hr1 (by omega)).mul_mul hK

/-- **The elimination for `Mblk`** (§3): both glue cases. -/
theorem block_core (hq : 1 ≤ padicValNat p q) (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1) : BlockCoreSpec p q c k r a := by
  by_cases h : r = p
  · exact block_core_eq hq h (hra h)
  · exact block_core_lt hq hr1 (by omega) ha

end ColouredSand.Blocks
