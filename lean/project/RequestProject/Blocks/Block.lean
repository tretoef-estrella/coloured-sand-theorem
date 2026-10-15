module

public import RequestProject.Blocks.BlockCore

/-!
# Lemma 8, two Weyl factors (CSG1, §1, (B1) and (B2))

This file proves **(B1)** and **(B2)** of `CSG1_lemma_8_the_blocks.md`: the cokernel of the
block matrix `Mblk` of §1 (defined in `RequestProject/Blocks/Defs.lean`).

## Encoding

* `R = ℤ_[p]`; `Mblk p q c k r a : Matrix ι ι ℤ_[p]` with `ι = Fin (λ+1) ⊕ Fin (μ+1)`, exactly as
  in §1; the cokernel is `(ι → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin (Mblk …))` and the
  isomorphisms are additive-group isomorphisms `≃+`, wrapped in `Nonempty`.
* `(Fin (2 * a) → ZMod p)` is the direct sum `(ℤ/p)^{2a}`; `×` is the direct sum of two groups.
* The numbers `x, y, E₁₂, E₂₂` are `blkX`, `blkY`, `E12`, `E22` of `Defs.lean`.
* Hypotheses (preamble and §1): `[Fact p.Prime]`, `1 ≤ padicValNat p q`, `1 ≤ r ≤ p`,
  `a ≤ p − 1`, `r = p → a = p − 1`; for (B1) `1 ≤ c + k`, for (B2) `c = 0` and `k = 0`.

## Proof

`block_core` (`RequestProject/Blocks/BlockCore.lean`) gives
`coker Mblk ≅ (R ⧸ p)^a × (R ⧸ p)^a × R² ⧸ span{(X₁, X₂), (0, Y₂)}` with
`p^a X₁ ≈ ∏_{t<(a+1)p} N t`, `p^a X₂ ≈ p^{τ + A'}`, `p^a Y₂ ≈ p^{α + A'}`.  Cancelling `p^a`
gives `X₁ ≈ p^{E₁₁}` (if `c + k ≥ 1`) or `X₁ = 0` (if `c = k = 0`), `X₂ ≈ p^{E₁₂}`,
`Y₂ ≈ p^{E₂₂}`, and the `2 × 2` lemma (`twoByTwo_nonempty`) finishes (B1).
-/

@[expose] public section

open Finset Submodule

namespace ColouredSand.Blocks

variable {p : ℕ} [hp : Fact p.Prime] {q c k r a : ℕ}

/-- `(ℤ_[p]^a ⧸ p)² ≃+ (ℤ/p)^{2a}`. -/
noncomputable def piSpanPairEquiv (a : ℕ) :
    (((Fin a → ℤ_[p]) ⧸ piSpan a (p : ℤ_[p])) × ((Fin a → ℤ_[p]) ⧸ piSpan a (p : ℤ_[p]))) ≃+
      (Fin (2 * a) → ZMod p) :=
  ((piSpanEquiv a).prodCongr (piSpanEquiv a)).trans
    (((LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin a) (ZMod p) (ZMod p)).symm.trans
      (LinearEquiv.funCongrLeft (ZMod p) (ZMod p)
        ((finCongr (two_mul a)).trans finSumFinEquiv.symm))).toAddEquiv)

/-- Cancelling `p^a`: if `p^a X ≈ p^{a + E}` then `X = u p^E` for a unit `u`. -/
lemma exists_unit_of_assoc {X : ℤ_[p]} {E : ℕ}
    (h : Associated ((p : ℤ_[p]) ^ a * X) ((p : ℤ_[p]) ^ (a + E))) :
    ∃ u : ℤ_[p]ˣ, X = (u : ℤ_[p]) * (p : ℤ_[p]) ^ E := by
  rw [pow_add] at h
  have hpne : (p : ℤ_[p]) ^ a ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  obtain ⟨u, hu⟩ := (Associated.of_mul_left h (Associated.refl _) hpne).symm
  exact ⟨u, by rw [← hu, mul_comm]⟩

/-- The three valuations, from `block_core`. -/
lemma block_exponents (hq : 1 ≤ padicValNat p q) (hr1 : 1 ≤ r) (hrp : r ≤ p)
    (hra : r = p → a = p - 1) :
    blkTau p a + blkA' p q c k r a = a + E12 p q c k r a ∧
    blkAlpha p q c k r a + blkA' p q c k r a = a + E22 p q c k r a ∧
    ∑ t ∈ range ((a + 1) * p), vt p q c k t = a + E11 p q c k r a := by
  obtain ⟨hA', hA⟩ := positivity_P (c := c) (k := k) hq hr1 hrp hra
  have hl := lam_eq (p := p) r a
  have hsplit : blkA p q c k r a = (∑ t ∈ range ((a + 1) * p), vt p q c k t) +
      blkAlpha p q c k r a := by
    unfold blkA blkAlpha
    rw [← Finset.sum_range_add_sum_Ico _ (show (a + 1) * p ≤ lam p r a + 1 by omega),
      Finset.Ico_add_one_right_eq_Icc]
  unfold E11 E12 E22
  refine ⟨by omega, by omega, by omega⟩

/-- **(B1) Lemma 8, two Weyl factors, `c + k ≥ 1`.**
`coker Mblk ≃+ (ℤ/p)^{2a} ⊕ ℤ/p^x ⊕ ℤ/p^y`. -/
theorem B1 (hq : 1 ≤ padicValNat p q) (hck : 1 ≤ c + k) (hr1 : 1 ≤ r) (hrp : r ≤ p)
    (ha : a ≤ p - 1) (hra : r = p → a = p - 1) :
    Nonempty (((Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (Mblk p q c k r a))) ≃+
      (Fin (2 * a) → ZMod p) × ZMod (p ^ blkX p q c k r a) × ZMod (p ^ blkY p q c k r a)) := by
  obtain ⟨X1, X2, Y2, h1, h2, h3, ⟨E⟩⟩ := block_core (c := c) (k := k) hq hr1 hrp ha hra
  obtain ⟨e12, e22, e11⟩ := block_exponents (c := c) (k := k) hq hr1 hrp hra
  rw [e12] at h2
  rw [e22] at h3
  have h1' := h1.trans (prod_Nt_associated hq hck _)
  rw [e11] at h1'
  obtain ⟨u1, rfl⟩ := exists_unit_of_assoc h1'
  obtain ⟨u2, rfl⟩ := exists_unit_of_assoc h2
  obtain ⟨u3, rfl⟩ := exists_unit_of_assoc h3
  obtain ⟨F⟩ := twoByTwo_nonempty (p : ℤ_[p]) u1 u2 u3 (E11 p q c k r a) (E12 p q c k r a)
    (E22 p q c k r a)
  exact ⟨E.toAddEquiv.trans ((piSpanPairEquiv a).prodCongr
    (F.toAddEquiv.trans ((padicQuotEquiv _).prodCongr (padicQuotEquiv _))))⟩

/-- `span {(0, u p^m), (0, v p^n)} = 0 × (p^{min m n})` in `R²`. -/
lemma span_zero_pair (u v : ℤ_[p]ˣ) (m n : ℕ) :
    span ℤ_[p] {((0, (u : ℤ_[p]) * (p : ℤ_[p]) ^ m) : ℤ_[p] × ℤ_[p]),
      (0, (v : ℤ_[p]) * (p : ℤ_[p]) ^ n)} =
      Submodule.prod ⊥ (Ideal.span {(p : ℤ_[p]) ^ min m n} : Submodule ℤ_[p] ℤ_[p]) := by
  apply le_antisymm
  · rw [span_le]
    rintro _ (rfl | rfl)
    · refine ⟨rfl, Ideal.mem_span_singleton.2 ?_⟩
      exact Dvd.dvd.mul_left (pow_dvd_pow _ (min_le_left _ _)) _
    · refine ⟨rfl, Ideal.mem_span_singleton.2 ?_⟩
      exact Dvd.dvd.mul_left (pow_dvd_pow _ (min_le_right _ _)) _
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hx0 : x = 0 := hx
    subst hx0
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mem_span_pair]
    rcases le_total m n with hmn | hmn
    · refine ⟨z * (u⁻¹ : ℤ_[p]ˣ), 0, ?_⟩
      ext
      · simp
      · simp only [Prod.smul_mk, smul_eq_mul, zero_smul, add_zero,
          min_eq_left hmn]
        rw [mul_assoc, ← mul_assoc ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), Units.inv_mul, one_mul]
    · refine ⟨0, z * (v⁻¹ : ℤ_[p]ˣ), ?_⟩
      ext
      · simp
      · simp only [Prod.smul_mk, smul_eq_mul, zero_smul, zero_add,
          min_eq_right hmn]
        rw [mul_assoc, ← mul_assoc ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), Units.inv_mul, one_mul]

/-- `R² ⧸ span {(0, u p^m), (0, v p^n)} ≃+ R × ℤ/p^{min m n}`. -/
noncomputable def zeroPairEquiv (u v : ℤ_[p]ˣ) (m n : ℕ) :
    ((ℤ_[p] × ℤ_[p]) ⧸ span ℤ_[p] {((0, (u : ℤ_[p]) * (p : ℤ_[p]) ^ m) : ℤ_[p] × ℤ_[p]),
      (0, (v : ℤ_[p]) * (p : ℤ_[p]) ^ n)}) ≃+ ℤ_[p] × ZMod (p ^ min m n) :=
  ((Submodule.quotEquivOfEq _ _ (span_zero_pair u v m n)).trans
    (quotProdEquiv _ _)).toAddEquiv.trans
    ((Submodule.quotEquivOfEqBot ⊥ rfl).toAddEquiv.prodCongr (padicQuotEquiv _))

/-- **(B2) Lemma 8, two Weyl factors, `c = 0` and `k = 0`.**
`coker Mblk ≃+ ℤ_[p] ⊕ (ℤ/p)^{2a} ⊕ ℤ/p^{min E₁₂ E₂₂}`. -/
theorem B2 (hq : 1 ≤ padicValNat p q) (hc : c = 0) (hk : k = 0) (hr1 : 1 ≤ r) (hrp : r ≤ p)
    (ha : a ≤ p - 1) (hra : r = p → a = p - 1) :
    Nonempty (((Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (Mblk p q c k r a))) ≃+
      ℤ_[p] × (Fin (2 * a) → ZMod p) × ZMod (p ^ min (E12 p q c k r a) (E22 p q c k r a))) := by
  obtain ⟨X1, X2, Y2, h1, h2, h3, ⟨E⟩⟩ := block_core (c := c) (k := k) hq hr1 hrp ha hra
  obtain ⟨e12, e22, -⟩ := block_exponents (c := c) (k := k) hq hr1 hrp hra
  rw [e12] at h2
  rw [e22] at h3
  have h0 : ∏ t ∈ range ((a + 1) * p), Nt p q c k t = 0 :=
    Finset.prod_eq_zero (i := 0) (by simp [hp.out.pos]) (Nt_zero_of hc hk)
  rw [h0, associated_zero_iff_eq_zero] at h1
  have hpne : (p : ℤ_[p]) ^ a ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hX1 : X1 = 0 := (mul_eq_zero.1 h1).resolve_left hpne
  subst hX1
  obtain ⟨u2, rfl⟩ := exists_unit_of_assoc h2
  obtain ⟨u3, rfl⟩ := exists_unit_of_assoc h3
  let reorder : (Fin (2 * a) → ZMod p) × (ℤ_[p] × ZMod (p ^ min (E12 p q c k r a)
      (E22 p q c k r a))) ≃+ ℤ_[p] × (Fin (2 * a) → ZMod p) ×
        ZMod (p ^ min (E12 p q c k r a) (E22 p q c k r a)) :=
    { toFun := fun x => (x.2.1, x.1, x.2.2)
      invFun := fun y => (y.2.1, y.1, y.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  exact ⟨E.toAddEquiv.trans (((piSpanPairEquiv a).prodCongr
    (zeroPairEquiv u2 u3 _ _)).trans reorder)⟩

end ColouredSand.Blocks
