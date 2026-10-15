module

public import RequestProject.TiltP.CG

/-!
# (G1)–(G2) The Clebsch–Gordan intertwiner `Ψ` and the Clebsch–Gordan lattice (CSG3, Part G)

## Encoding

(See also `RequestProject/TiltP/CG.lean`.)  `K = ℚ_[p]`, `l ≥ 1`.

* `PsiLin p l : V p (l + 1) (l − 1) →ₗ[K] (Fin 2 × Fin (l + 1) → K)` is the linear map with
  `ℓ_i ↦ b_0 ⊗ e_i + b_1 ⊗ e_{i−1}` and `s_j ↦ ((l − j) • b_1 ⊗ e_j − (j + 1) • b_0 ⊗ e_{j+1})/(l+1)`
  (defined on the standard basis `Pi.single y 1` of `V` by `Basis.constr`).  The codomain is the
  space of vectors of `tensorV (delta K l)` (its basis is `Fin 2 × Fin (l + 1)`).
* `PsiCG p l hl : V p (l + 1) (l − 1) ≃ₗ[K] (Fin 2 × Fin (l + 1) → K)` is `PsiLin` as a linear
  isomorphism (bijective since it is surjective between spaces of the same dimension `2l + 2`).
* (G1) `G1`: the values on `ℓ_i`, `s_j`; `Ψ ∘ F t = F t ∘ Ψ`, `Ψ ∘ E t = E t ∘ Ψ` (with `Fop`,
  `Eop` on `V` and the divided powers of `tensorV (delta K l)` on `W`); and `Ψ` preserves weights
  (`wt ℓ_i = l + 1 − 2i`, `wt s_j = l − 1 − 2j` in `V`; `wt (ε, r) = wt_V ε + l − 2r` in `W`).
  `G1_hw`: `Ψ(ℓ_i) = F^{(i)}(b_0 ⊗ e_0)` and `Ψ(s_j) = F^{(j)} y`.
* (G2) `G2`: `Ψ` maps `Lx p (l + 1) (l − 1) 1 (1/(l+1))` onto the standard lattice
  `LinearMap.range (coeL ℤ_[p] K (Fin 2 × Fin (l + 1)))` (the `ℤ_[p]`-span of the `b_ε ⊗ e_r`);
  `PsiLin_stilde`: `Ψ(s̃_j) = b_1 ⊗ e_j`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltP

open DPLattice WeylFilt Doubling LemmaW Finset ColouredSand.Glue ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The images of the basis vectors: `inl i ↦ PsiL p l i`, `inr j ↦ PsiS p l j`. -/
def PsiImg (l : ℕ) : Idx (l + 1) (l - 1) → (Fin 2 × Fin (l + 1) → ℚ_[p]) :=
  Sum.elim (fun i : Fin (l + 1 + 1) => PsiL p l (i : ℕ)) (fun j : Fin (l - 1 + 1) => PsiS p l (j : ℕ))

variable (p) in
/-- (G1) The intertwiner `Ψ : V p (l + 1) (l − 1) → W` as a linear map. -/
def PsiLin (l : ℕ) : V p (l + 1) (l - 1) →ₗ[ℚ_[p]] (Fin 2 × Fin (l + 1) → ℚ_[p]) :=
  (Pi.basisFun ℚ_[p] (Idx (l + 1) (l - 1))).constr ℚ_[p] (PsiImg p l)

lemma PsiLin_single (l : ℕ) (y : Idx (l + 1) (l - 1)) :
    PsiLin p l (Pi.single y 1) = PsiImg p l y := by
  rw [← Pi.basisFun_apply, PsiLin, Module.Basis.constr_basis]

lemma PsiL_of_gt {l i : ℕ} (hi : l + 1 < i) : PsiL p l i = 0 := by
  unfold PsiL
  rw [eN_of_gt (by omega), eN_of_gt (by omega), if_pos (by omega)]
  simp

lemma PsiS_of_ge {l j : ℕ} (hj : l ≤ j) : PsiS p l j = 0 := by
  unfold PsiS
  rw [eN_of_gt (k := j + 1) (by omega)]
  rcases Nat.eq_or_lt_of_le hj with rfl | hlt
  · simp
  · rw [eN_of_gt hlt]; simp

lemma ell_single' {L M : ℕ} (i : Fin (L + 1)) :
    (Pi.single (Sum.inl i) 1 : V p L M) = ell p L M i := by
  unfold ell; rw [dif_pos (Nat.le_of_lt_succ i.2)]

lemma ess_single' {L M : ℕ} (j : Fin (M + 1)) :
    (Pi.single (Sum.inr j) 1 : V p L M) = ess p L M j := by
  unfold ess; rw [dif_pos (Nat.le_of_lt_succ j.2)]

lemma PsiLin_ell (l i : ℕ) : PsiLin p l (ell p (l + 1) (l - 1) i) = PsiL p l i := by
  unfold ell
  split_ifs with h
  · rw [PsiLin_single]; rfl
  · rw [map_zero, PsiL_of_gt (by omega)]

lemma PsiLin_ess {l : ℕ} (hl : 1 ≤ l) (j : ℕ) : PsiLin p l (ess p (l + 1) (l - 1) j) = PsiS p l j := by
  unfold ess
  split_ifs with h
  · rw [PsiLin_single]; rfl
  · rw [map_zero, PsiS_of_ge (by omega)]

/-- **(G1)**, closed forms: `Ψ(ℓ_i) = F^{(i)}(b_0 ⊗ e_0)` and `Ψ(s_j) = F^{(j)} y`, with
`y = (l • b_1 ⊗ e_0 − b_0 ⊗ e_1)/(l + 1)`. -/
theorem G1_hw {l : ℕ} (hl : 1 ≤ l) (i j : ℕ) :
    PsiLin p l (ell p (l + 1) (l - 1) i) = (tensorV (delta ℚ_[p] l)).Fd i (u0 p l) ∧
      PsiLin p l (ess p (l + 1) (l - 1) j) = (tensorV (delta ℚ_[p] l)).Fd j (yv p l) := by
  rw [PsiLin_ell, PsiLin_ess hl]
  exact ⟨(FW_u0 l i).symm, (FW_y l j).symm⟩

lemma choose_cast_eq (a b : ℕ) (z : ℤ) (h : z = (a : ℤ)) :
    ((Ring.choose z b : ℤ) : ℚ_[p]) = ((a.choose b : ℕ) : ℚ_[p]) := by
  rw [h, Ring.choose_natCast, Int.cast_natCast]

theorem PsiLin_F {l : ℕ} (hl : 1 ≤ l) (t : ℕ) :
    PsiLin p l ∘ₗ Fop p (l + 1) (l - 1) t = FW l t ∘ₗ PsiLin p l := by
  refine ext_single fun y => ?_
  rcases y with i | j
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, ell_single', F_ell t i (Nat.le_of_lt_succ i.2),
      map_smul, PsiLin_ell, PsiLin_ell, ← FW_u0, ← FW_u0, ← LinearMap.comp_apply (FW l t),
      (isDP_W (p := p) l).P1_F t i, LinearMap.smul_apply,
      choose_cast_eq (t + i) t _ (by push_cast; ring), add_comm (i : ℕ) t]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, ess_single', F_ess t j (Nat.le_of_lt_succ j.2),
      map_smul, PsiLin_ess hl, PsiLin_ess hl, ← FW_y, ← FW_y, ← LinearMap.comp_apply (FW l t),
      (isDP_W (p := p) l).P1_F t j, LinearMap.smul_apply,
      choose_cast_eq (t + j) t _ (by push_cast; ring), add_comm (j : ℕ) t]

theorem PsiLin_E {l : ℕ} (hl : 1 ≤ l) (s : ℕ) :
    PsiLin p l ∘ₗ Eop p (l + 1) (l - 1) s = EW l s ∘ₗ PsiLin p l := by
  refine ext_single fun y => ?_
  rcases y with i | j
  · have hi := Nat.le_of_lt_succ i.2
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ell_single', E_ell s i hi, PsiLin_ell, ← FW_u0,
      K_hw (isDP_W l) (inWt_u0 l) (fun k hk => EW_u0 l k hk)]
    split_ifs with h
    · rw [map_smul, PsiLin_ell, ← FW_u0, choose_cast_eq (l + 1 - i + s) s _ (by push_cast; omega)]
    · rw [map_zero]
  · have hj := Nat.le_of_lt_succ j.2
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ess_single', E_ess s j hj, PsiLin_ess hl,
      ← FW_y, K_hw (isDP_W l) (inWt_yv l) (fun k hk => EW_y l k hl hk)]
    split_ifs with h
    · rw [map_smul, PsiLin_ess hl, ← FW_y,
        choose_cast_eq (l - 1 - j + s) s _ (by push_cast [Nat.cast_sub hl]; omega)]
    · rw [map_zero]

theorem PsiLin_wt {l : ℕ} (hl : 1 ≤ l) (y : Idx (l + 1) (l - 1)) (k : Fin 2 × Fin (l + 1))
    (hyk : Glue.wt (l + 1) (l - 1) y ≠ tensorWt (weylWt l) k) : PsiLin p l (Pi.single y 1) k = 0 := by
  rcases y with i | j
  · rw [PsiLin_single]
    show PsiL p l (i : ℕ) k = 0
    rw [← FW_u0]
    refine (isDP_W l).inWt_Fd i (inWt_u0 l) k ?_
    intro h; apply hyk; rw [h]; simp only [Glue.wt]; push_cast; ring
  · rw [PsiLin_single]
    show PsiS p l (j : ℕ) k = 0
    rw [← FW_y]
    refine (isDP_W l).inWt_Fd j (inWt_yv l) k ?_
    intro h; apply hyk; rw [h]; simp only [Glue.wt]; push_cast [Nat.cast_sub hl]; ring

/-! ### The lattice -/

lemma bvec_eN_mem (l : ℕ) (e : Fin 2) (k : ℕ) :
    bvec e (eN p l k) ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin 2 × Fin (l + 1))) := by
  rw [mem_range_coeL_iff]
  intro q
  rw [bvec_apply]
  split_ifs
  · rw [eN_apply]; split_ifs <;> simp
  · simp

lemma PsiL_mem (l i : ℕ) :
    PsiL p l i ∈ LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin 2 × Fin (l + 1))) := by
  unfold PsiL
  refine Submodule.add_mem _ (bvec_eN_mem l 0 i) ?_
  split_ifs
  · exact bvec_eN_mem l 1 _
  · exact Submodule.zero_mem _

/-- (G2) `Ψ(s̃_j) = b_1 ⊗ e_j`, where `s̃_j = s_j + (j + 1)/(l + 1) • ℓ_{j+1}`. -/
theorem PsiLin_stilde {l : ℕ} (hl : 1 ≤ l) (j : ℕ) (hj : j ≤ l - 1) :
    PsiLin p l (stilde p (l + 1) (l - 1) 1 (1 / ((l : ℚ_[p]) + 1)) j) = bvec 1 (eN p l j) := by
  have hl1 : (l : ℚ_[p]) + 1 ≠ 0 := Nat.cast_add_one_ne_zero l
  unfold stilde
  rw [if_pos hj, map_add, map_smul, PsiLin_ess hl, PsiLin_ell, Nat.choose_succ_self_right]
  unfold PsiS PsiL
  rw [if_pos (by omega), Nat.add_sub_cancel]
  push_cast
  match_scalars <;> field_simp <;> ring

variable (p) in
/-- The image `Ψ(Lx p (l + 1) (l − 1) 1 (1/(l+1)))`. -/
abbrev PsiImage (l : ℕ) : Submodule ℤ_[p] (Fin 2 × Fin (l + 1) → ℚ_[p]) :=
  Submodule.map ((PsiLin p l).restrictScalars ℤ_[p])
    (Lx p (l + 1) (l - 1) 1 (1 / ((l : ℚ_[p]) + 1)))

lemma PsiLin_mem_image {l : ℕ} {v : V p (l + 1) (l - 1)}
    (hv : v ∈ Lx p (l + 1) (l - 1) 1 (1 / ((l : ℚ_[p]) + 1))) : PsiLin p l v ∈ PsiImage p l :=
  Submodule.mem_map_of_mem (f := (PsiLin p l).restrictScalars ℤ_[p]) hv

lemma bvec1_mem_image {l : ℕ} (hl : 1 ≤ l) (k : ℕ) (hk : k ≤ l) :
    bvec 1 (eN p l k) ∈ PsiImage p l := by
  rcases Nat.lt_or_ge k l with h | h
  · rw [← PsiLin_stilde hl k (by omega)]
    exact PsiLin_mem_image (stilde_mem_Lx _ _ _)
  · have hkl : k = l := by omega
    subst hkl
    have := PsiLin_mem_image (p := p) (ell_mem_Lx (L := k + 1) (M := k - 1) 1
      (1 / ((k : ℚ_[p]) + 1)) (k + 1))
    rw [PsiLin_ell] at this
    unfold PsiL at this
    rw [eN_of_gt (by omega), map_zero, zero_add, if_pos (by omega), Nat.add_sub_cancel] at this
    exact this

lemma single_mem_image {l : ℕ} (hl : 1 ≤ l) (q : Fin 2 × Fin (l + 1)) :
    (Pi.single q 1 : Fin 2 × Fin (l + 1) → ℚ_[p]) ∈ PsiImage p l := by
  obtain ⟨e, k⟩ := q
  rw [single_eq_bvec, ← eN_fin]
  have hk := Nat.le_of_lt_succ k.2
  fin_cases e
  · have h1 := PsiLin_mem_image (p := p) (ell_mem_Lx (L := l + 1) (M := l - 1) 1
      (1 / ((l : ℚ_[p]) + 1)) k)
    rw [PsiLin_ell] at h1
    unfold PsiL at h1
    split_ifs at h1 with hk1
    · have h2 := bvec1_mem_image (p := p) hl (k - 1) (by omega)
      have := Submodule.sub_mem _ h1 h2
      simpa using this
    · simpa using h1
  · exact bvec1_mem_image hl k hk

lemma coeL_eq_sum {κ : Type*} [Fintype κ] [DecidableEq κ] (z : κ → ℤ_[p]) :
    coeL ℤ_[p] ℚ_[p] κ z = ∑ k, z k • (Pi.single k 1 : κ → ℚ_[p]) := by
  have hz : z = ∑ k, z k • (Pi.single k (1 : ℤ_[p]) : κ → ℤ_[p]) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  conv_lhs => rw [hz]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, coeL_single]

/-- **(G2)** `Ψ` maps `Lx p (l + 1) (l − 1) 1 (1/(l + 1))` onto the standard lattice of `W`, the
image of `Fin 2 × Fin (l + 1) → ℤ_[p]` (the `ℤ_[p]`-span of the `b_ε ⊗ e_r`). -/
theorem G2_PsiLin {l : ℕ} (hl : 1 ≤ l) :
    PsiImage p l = LinearMap.range (coeL ℤ_[p] ℚ_[p] (Fin 2 × Fin (l + 1))) := by
  apply le_antisymm
  · rw [PsiImage, Lx, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    rcases hv with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · show PsiLin p l (ell p (l + 1) (l - 1) i) ∈ _
      rw [PsiLin_ell]; exact PsiL_mem l i
    · show PsiLin p l (stilde p (l + 1) (l - 1) 1 _ j) ∈ _
      rw [PsiLin_stilde hl j (Nat.le_of_lt_succ j.2)]; exact bvec_eN_mem l 1 j
  · rintro w ⟨z, rfl⟩
    rw [coeL_eq_sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (single_mem_image hl k)

lemma PsiLin_surjective {l : ℕ} (hl : 1 ≤ l) : Function.Surjective (PsiLin p l) := by
  intro w
  have hmem : ∀ q, (Pi.single q 1 : Fin 2 × Fin (l + 1) → ℚ_[p]) ∈ LinearMap.range (PsiLin p l) := by
    intro q
    obtain ⟨v, -, hv⟩ := single_mem_image (p := p) hl q
    exact ⟨v, hv⟩
  have : w ∈ LinearMap.range (PsiLin p l) := by
    have hw : w = ∑ q, w q • (Pi.single q 1 : Fin 2 × Fin (l + 1) → ℚ_[p]) := by
      conv_lhs => rw [← Finset.univ_sum_single w]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hw]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hmem q)
  exact this

lemma PsiLin_bijective {l : ℕ} (hl : 1 ≤ l) : Function.Bijective (PsiLin p l) := by
  have hrank : Module.finrank ℚ_[p] (V p (l + 1) (l - 1)) =
      Module.finrank ℚ_[p] (Fin 2 × Fin (l + 1) → ℚ_[p]) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).2
    (PsiLin_surjective hl), PsiLin_surjective hl⟩

variable (p) in
/-- **(G1) The intertwiner** `Ψ` as a linear isomorphism `V p (l + 1) (l − 1) ≃ W`. -/
def PsiCG (l : ℕ) (hl : 1 ≤ l) : V p (l + 1) (l - 1) ≃ₗ[ℚ_[p]] (Fin 2 × Fin (l + 1) → ℚ_[p]) :=
  LinearEquiv.ofBijective (PsiLin p l) (PsiLin_bijective hl)

@[simp] lemma PsiCG_apply {l : ℕ} (hl : 1 ≤ l) (v : V p (l + 1) (l - 1)) :
    PsiCG p l hl v = PsiLin p l v := rfl

/-- **(G1)** `Ψ` is a linear isomorphism with `Ψ(ℓ_i) = b_0 ⊗ e_i + b_1 ⊗ e_{i−1}`,
`Ψ(s_j) = ((l − j) • b_1 ⊗ e_j − (j + 1) • b_0 ⊗ e_{j+1})/(l + 1)`, commuting with every `F t`,
`E t`, and preserving weights. -/
theorem G1 {l : ℕ} (hl : 1 ≤ l) :
    (∀ i : ℕ, i ≤ l + 1 → PsiCG p l hl (ell p (l + 1) (l - 1) i) =
      bvec 0 (eN p l i) + if 1 ≤ i then bvec 1 (eN p l (i - 1)) else 0) ∧
    (∀ j : ℕ, j ≤ l - 1 → PsiCG p l hl (ess p (l + 1) (l - 1) j) =
      (1 / ((l : ℚ_[p]) + 1)) •
        (((l : ℚ_[p]) - j) • bvec 1 (eN p l j) - ((j : ℚ_[p]) + 1) • bvec 0 (eN p l (j + 1)))) ∧
    (∀ t, (PsiCG p l hl).toLinearMap ∘ₗ Fop p (l + 1) (l - 1) t =
      (tensorV (delta ℚ_[p] l)).Fd t ∘ₗ (PsiCG p l hl).toLinearMap) ∧
    (∀ t, (PsiCG p l hl).toLinearMap ∘ₗ Eop p (l + 1) (l - 1) t =
      (tensorV (delta ℚ_[p] l)).Ed t ∘ₗ (PsiCG p l hl).toLinearMap) ∧
    (∀ (y : Idx (l + 1) (l - 1)) (k : (tensorV (delta ℚ_[p] l)).ι),
      Glue.wt (l + 1) (l - 1) y ≠ (tensorV (delta ℚ_[p] l)).wt k →
        PsiCG p l hl (Pi.single y 1) k = 0) :=
  ⟨fun i _ => PsiLin_ell l i, fun j _ => PsiLin_ess hl j, fun t => PsiLin_F hl t,
    fun t => PsiLin_E hl t, fun y k hyk => PsiLin_wt hl y k hyk⟩

/-- **(G2)** `Ψ` maps `Lx p (l + 1) (l − 1) 1 (1/(l + 1))` onto the `ℤ_[p]`-span of the
`b_ε ⊗ e_r`, i.e. the image of `Fin 2 × Fin (l + 1) → ℤ_[p]` in `W`. -/
theorem G2 {l : ℕ} (hl : 1 ≤ l) :
    Submodule.map ((PsiCG p l hl).toLinearMap.restrictScalars ℤ_[p])
        (Lx p (l + 1) (l - 1) 1 (1 / ((l : ℚ_[p]) + 1))) =
      LinearMap.range (coeL ℤ_[p] ℚ_[p] (tensorV (delta ℚ_[p] l)).ι) :=
  G2_PsiLin hl

end ColouredSand.TiltP
