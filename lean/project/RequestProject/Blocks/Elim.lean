module

public import RequestProject.Blocks.Glued
public import RequestProject.Blocks.UChain

/-!
# The glue relation (CSG1, §3 "Elimination", the end of the `s̃`-chain)

After contracting the unit links, `Mblk` becomes a glued system with chains `g_0, …, g_{a+1}`
and `h_0, …` (`RequestProject/Blocks/Glued.lean`).  §3 of `CSG1_lemma_8_the_blocks.md` then
treats the end relation of the `s̃`-chain, `σ_end = p^σ h_last + u g_{a+1}`:

* if `r ≤ p − 1`, `u` is a unit and `g_{a+1}` is eliminated (`elimUnitEquiv`);
* if `r = p`, the glue is one more `p`-link `h_{a−1} → g_{a+1}`, and `g_{a+1}` is regarded as
  the last vertex of the second chain (`elimReindexEquiv`).

In both cases the result is the system `uRel` of `RequestProject/Blocks/UChain.lean`.
-/

@[expose] public section

open Submodule

namespace ColouredSand.Blocks

variable {R : Type*} [CommRing R]

section unit

variable {a : ℕ} {D S D' S' : ℕ → R} {u : R}

/-- First component of the elimination map: `g_i ↦ g_i` (`i ≤ a`), `g_{a+1} ↦ c h_a`. -/
noncomputable def elimPi₁ (a : ℕ) (c : R) :
    (Fin (a + 2) → R) →ₗ[R] (Fin (a + 1) → R) × (Fin (a + 1) → R) :=
  linOfFun (fun i => if i ≤ a then ((ev i : Fin (a + 1) → R), (0 : Fin (a + 1) → R))
    else (0, c • ev a))

lemma elimPi₁_ev (c : R) {i : ℕ} (hi : i ≤ a) :
    elimPi₁ a c (ev i) = ((ev i : Fin (a + 1) → R), (0 : Fin (a + 1) → R)) := by
  rw [elimPi₁, linOfFun_ev _ (by omega), if_pos hi]

lemma elimPi₁_ev_last (c : R) :
    elimPi₁ a c (ev (a + 1)) = ((0 : Fin (a + 1) → R), c • (ev a : Fin (a + 1) → R)) := by
  rw [elimPi₁, linOfFun_ev _ (by omega), if_neg (by omega)]

/-- **Eliminating `g_{a+1}` with the unit glue entry** (`r ≤ p − 1`). -/
noncomputable def elimUnitEquiv (hu : IsUnit u) :
    (((Fin (a + 1 + 1) → R) × (Fin (a + 1) → R)) ⧸ gluedRel (a + 1) a D S D' S' (a + 1) u)
      ≃ₗ[R] (((Fin (a + 1) → R) × (Fin (a + 1) → R)) ⧸
        uRel a D S (fun t => if t = a then D (a + 1) * (-Ring.inverse u * D' a) else D' t) S'
          (S a * (-Ring.inverse u * D' a))) := by
  set c : R := -Ring.inverse u * D' a with hc
  have hiu : Ring.inverse u * u = 1 := Ring.inverse_mul_cancel _ hu
  let ext0 : (Fin (a + 1) → R) →ₗ[R] (Fin (a + 2) → R) := linOfFun (fun i => ev i)
  have ext0_ev : ∀ i ≤ a, ext0 (ev i) = ev i := fun i hi => linOfFun_ev _ (by omega)
  refine quotEquivOfSection _ _ ((elimPi₁ a c).coprod (LinearMap.inr R _ _))
    (ext0.prodMap LinearMap.id) ?_ ?_ ?_
  · have : ((elimPi₁ a c).coprod (LinearMap.inr R _ _)).comp (ext0.prodMap LinearMap.id) =
        LinearMap.id := by
      apply LinearMap.prod_ext
      · apply ext_ev
        intro i hi
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
          LinearMap.prodMap_apply, LinearMap.coprod_apply, map_zero, add_zero,
          LinearMap.id_apply]
        rw [ext0_ev i (by omega), elimPi₁_ev c (by omega)]
      · ext x <;> simp
    intro w; exact congrArg (fun f => f w) this
  · rintro ⟨x, y⟩
    have h1 : ∀ x : Fin (a + 2) → R, ((x, 0) : (Fin (a + 2) → R) × (Fin (a + 1) → R)) -
        (ext0.prodMap LinearMap.id) (((elimPi₁ a c).coprod (LinearMap.inr R _ _)) (x, 0)) ∈
          gluedRel (a + 1) a D S D' S' (a + 1) u := by
      intro x
      have := mem_of_forall_ev ((LinearMap.inl R _ _) - (ext0.prodMap LinearMap.id) ∘ₗ
        ((elimPi₁ a c).coprod (LinearMap.inr R _ _)) ∘ₗ (LinearMap.inl R _ _))
        (gluedRel (a + 1) a D S D' S' (a + 1) u) ?_ x
      · simpa using this
      intro i hi
      simp only [LinearMap.sub_apply, LinearMap.inl_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.coprod_apply, map_zero, add_zero]
      by_cases hia : i ≤ a
      · rw [elimPi₁_ev c hia]
        simp [ext0_ev i hia]
      · have : i = a + 1 := by omega
        subst this
        rw [elimPi₁_ev_last]
        have hmem := gluedCol_last_mem (n₁ := a + 1) (n₂ := a) (d₁ := D) (s₁ := S) (d₂ := D')
          (s₂ := S') (g := a + 1) (u := u)
        have := Submodule.smul_mem _ (Ring.inverse u) hmem
        convert this using 1
        rw [chainCol, ev_eq_zero (m := a + 1) (show a + 1 ≤ a + 1 from le_rfl), smul_zero,
          add_zero]
        ext j
        · simp [smul_smul, hiu]
        · simp [hc]
    have := h1 x
    convert this using 1
    simp
  · set D₂ : ℕ → R := fun t => if t = a then D (a + 1) * c else D' t with hD₂
    set π := (elimPi₁ a c).coprod (LinearMap.inr R (Fin (a + 1) → R) (Fin (a + 1) → R))
    have hinl : ∀ i : Fin (a + 2), π (gluedCol (a + 1) a D S D' S' (a + 1) u (.inl i)) =
        if h : (i : ℕ) ≤ a then uCol a D S D₂ S' (S a * c) (.inl ⟨i, by omega⟩)
        else uCol a D S D₂ S' (S a * c) (.inr ⟨a, by omega⟩) := by
      rintro ⟨i, hi2⟩
      simp only [gluedCol, π, LinearMap.coprod_apply, map_zero, add_zero, chainCol, map_add,
        map_smul]
      by_cases hi : i < a
      · rw [dif_pos (by omega), elimPi₁_ev c (by omega), elimPi₁_ev c (by omega)]
        simp only [uCol, chainCol, if_neg (show i ≠ a by omega)]
        ext j <;> simp
      · by_cases hia : i = a
        · subst hia
          rw [dif_pos le_rfl, elimPi₁_ev c le_rfl, elimPi₁_ev_last]
          simp only [uCol, chainCol,
            ev_eq_zero (m := i + 1) (show i + 1 ≤ i + 1 from le_rfl)]
          ext j <;> simp [smul_smul]
        · have hi' : i = a + 1 := by omega
          subst hi'
          rw [dif_neg (by omega), elimPi₁_ev_last,
            ev_eq_zero (m := a + 2) (show a + 2 ≤ a + 1 + 1 from le_rfl)]
          simp only [uCol, chainCol, hD₂, if_pos rfl,
            ev_eq_zero (m := a + 1) (show a + 1 ≤ a + 1 from le_rfl)]
          ext j <;> simp [smul_smul]
    have hinr : ∀ j : Fin (a + 1), π (gluedCol (a + 1) a D S D' S' (a + 1) u (.inr j)) =
        if (j : ℕ) < a then uCol a D S D₂ S' (S a * c) (.inr j) else 0 := by
      intro j
      simp only [gluedCol, π, LinearMap.coprod_apply, LinearMap.inr_apply]
      by_cases hj : (j : ℕ) < a
      · rw [if_neg (by omega), if_pos hj, map_zero]
        simp only [uCol, chainCol, hD₂, if_neg (show (j : ℕ) ≠ a by omega)]
        ext k <;> simp
      · have hj' : (j : ℕ) = a := by omega
        rw [if_pos hj', if_neg hj, map_smul, elimPi₁_ev_last]
        simp only [chainCol, hj', ev_eq_zero (m := a + 1) (show a + 1 ≤ a + 1 from le_rfl)]
        ext k
        · simp
        · simp only [Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Prod.snd_add,
            Prod.snd_zero, Pi.zero_apply, smul_zero, add_zero]
          rw [hc]
          linear_combination (-(D' a) * (ev a : Fin (a + 1) → R) k) * hiu
    unfold gluedRel
    rw [map_span_range]
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨i | j, rfl⟩
      · rw [Function.comp_apply, hinl]
        split_ifs
        · exact subset_span ⟨_, rfl⟩
        · exact subset_span ⟨_, rfl⟩
      · rw [Function.comp_apply, hinr]
        split_ifs
        · exact subset_span ⟨_, rfl⟩
        · exact zero_mem _
    · rw [uRel, span_le]
      rintro _ ⟨t | t, rfl⟩
      · refine subset_span ⟨.inl ⟨t, by omega⟩, ?_⟩
        rw [Function.comp_apply, hinl, dif_pos (by simp; omega)]
      · by_cases ht : (t : ℕ) < a
        · refine subset_span ⟨.inr t, ?_⟩
          rw [Function.comp_apply, hinr, if_pos ht]
        · refine subset_span ⟨.inl ⟨a + 1, by omega⟩, ?_⟩
          rw [Function.comp_apply, hinl, dif_neg (by simp)]
          congr
          have := t.2; omega

end unit

section reindex

variable {b : ℕ} {D S D' S' : ℕ → R} {u : R}

/-- First component of the reindexing: `g_i ↦ g_i` (`i ≤ b+1`), `g_{b+2} ↦ h_{b+1}`. -/
noncomputable def reiPi₁ (b : ℕ) :
    (Fin (b + 3) → R) →ₗ[R] (Fin (b + 2) → R) × (Fin (b + 2) → R) :=
  linOfFun (fun i => if i ≤ b + 1 then ((ev i : Fin (b + 2) → R), (0 : Fin (b + 2) → R))
    else (0, ev (b + 1)))

lemma reiPi₁_ev {i : ℕ} (hi : i ≤ b + 1) :
    reiPi₁ (R := R) b (ev i) = ((ev i : Fin (b + 2) → R), (0 : Fin (b + 2) → R)) := by
  rw [reiPi₁, linOfFun_ev _ (by omega), if_pos hi]

lemma reiPi₁_ev_last :
    reiPi₁ (R := R) b (ev (b + 2)) = ((0 : Fin (b + 2) → R), (ev (b + 1) : Fin (b + 2) → R)) := by
  rw [reiPi₁, linOfFun_ev _ (by omega), if_neg (by omega)]

/-- Second component of the reindexing: `h_j ↦ h_j`. -/
noncomputable def reiPi₂ (b : ℕ) :
    (Fin (b + 1) → R) →ₗ[R] (Fin (b + 2) → R) × (Fin (b + 2) → R) :=
  linOfFun (fun j => ((0 : Fin (b + 2) → R), (ev j : Fin (b + 2) → R)))

lemma reiPi₂_ev {j : ℕ} (hj : j ≤ b) :
    reiPi₂ (R := R) b (ev j) = ((0 : Fin (b + 2) → R), (ev j : Fin (b + 2) → R)) := by
  rw [reiPi₂, linOfFun_ev _ (by omega)]

/-- Inverse of the reindexing. -/
noncomputable def reiSig (b : ℕ) :
    (Fin (b + 2) → R) × (Fin (b + 2) → R) →ₗ[R] (Fin (b + 3) → R) × (Fin (b + 1) → R) :=
  (linOfFun (fun i => ((ev i : Fin (b + 3) → R), (0 : Fin (b + 1) → R)))).coprod
    (linOfFun (fun j => if j ≤ b then ((0 : Fin (b + 3) → R), (ev j : Fin (b + 1) → R))
      else (ev (b + 2), 0)))

/-- **The glue as a `p`-link** (`r = p`): `g_{b+2}` (`= g_{a+1}`, `a = b + 1`) becomes the last
vertex of the second chain, the glue entry `u` its last link. -/
noncomputable def elimReindexEquiv :
    (((Fin (b + 2 + 1) → R) × (Fin (b + 1) → R)) ⧸ gluedRel (b + 2) b D S D' S' (b + 2) u)
      ≃ₗ[R] (((Fin (b + 1 + 1) → R) × (Fin (b + 1 + 1) → R)) ⧸
        uRel (b + 1) D S (fun t => if t = b + 1 then D (b + 2) else D' t)
          (fun t => if t = b then u else S' t) (S (b + 1))) := by
  set D₂ : ℕ → R := fun t => if t = b + 1 then D (b + 2) else D' t with hD₂
  set S₂ : ℕ → R := fun t => if t = b then u else S' t with hS₂
  set π := (reiPi₁ (R := R) b).coprod (reiPi₂ b)
  have hσ1 : ∀ i ≤ b + 1, reiSig (R := R) b ((ev i : Fin (b + 2) → R), 0) = (ev i, 0) := by
    intro i hi
    simp [reiSig, linOfFun_ev _ (show i < b + 2 by omega)]
  have hσ2 : ∀ j ≤ b, reiSig (R := R) b (0, (ev j : Fin (b + 2) → R)) = (0, ev j) := by
    intro j hj
    simp [reiSig, linOfFun_ev _ (show j < b + 2 by omega), if_pos hj]
  have hσ3 : reiSig (R := R) b (0, (ev (b + 1) : Fin (b + 2) → R)) = (ev (b + 2), 0) := by
    simp [reiSig, linOfFun_ev _ (show b + 1 < b + 2 by omega)]
  refine quotEquivOfSection _ _ π (reiSig b) ?_ ?_ ?_
  · have : π.comp (reiSig b) = LinearMap.id := by
      apply LinearMap.prod_ext
      · apply ext_ev
        intro i hi
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
          LinearMap.id_apply]
        rw [hσ1 i (by omega)]
        simp [π, reiPi₁_ev (show i ≤ b + 1 by omega)]
      · apply ext_ev
        intro j hj
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply,
          LinearMap.id_apply]
        by_cases hjb : j ≤ b
        · rw [hσ2 j hjb]
          simp [π, reiPi₂_ev hjb]
        · have : j = b + 1 := by omega
          subst this
          rw [hσ3]
          simp [π, reiPi₁_ev_last]
    intro w; exact congrArg (fun f => f w) this
  · have : (reiSig b).comp π = LinearMap.id := by
      apply LinearMap.prod_ext
      · apply ext_ev
        intro i hi
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
          LinearMap.id_apply, π, LinearMap.coprod_apply, map_zero, add_zero]
        by_cases hib : i ≤ b + 1
        · rw [reiPi₁_ev hib, hσ1 i hib]
        · have : i = b + 2 := by omega
          subst this
          rw [reiPi₁_ev_last, hσ3]
      · apply ext_ev
        intro j hj
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply,
          LinearMap.id_apply, π, LinearMap.coprod_apply, map_zero, zero_add]
        rw [reiPi₂_ev (by omega), hσ2 j (by omega)]
    intro v
    rw [show (reiSig b) (π v) = v from congrArg (fun f => f v) this, sub_self]
    exact zero_mem _
  · have hinl : ∀ i : Fin (b + 3), π (gluedCol (b + 2) b D S D' S' (b + 2) u (.inl i)) =
        if h : (i : ℕ) ≤ b + 1 then uCol (b + 1) D S D₂ S₂ (S (b + 1)) (.inl ⟨i, by omega⟩)
        else uCol (b + 1) D S D₂ S₂ (S (b + 1)) (.inr ⟨b + 1, by omega⟩) := by
      rintro ⟨i, hi2⟩
      simp only [gluedCol, π, LinearMap.coprod_apply, map_zero, add_zero, chainCol, map_add,
        map_smul]
      by_cases hi : i < b + 1
      · rw [dif_pos (by omega), reiPi₁_ev (by omega), reiPi₁_ev (by omega)]
        simp only [uCol, chainCol, if_neg (show i ≠ b + 1 by omega)]
        ext j <;> simp
      · by_cases hia : i = b + 1
        · subst hia
          rw [dif_pos le_rfl, reiPi₁_ev le_rfl, reiPi₁_ev_last]
          simp only [uCol, chainCol, ev_eq_zero (m := b + 2) (show b + 2 ≤ b + 1 + 1 from le_rfl)]
          ext j <;> simp
        · have hi' : i = b + 2 := by omega
          subst hi'
          rw [dif_neg (by omega), reiPi₁_ev_last,
            ev_eq_zero (m := b + 3) (show b + 3 ≤ b + 2 + 1 from le_rfl)]
          simp only [uCol, chainCol, hD₂, if_pos rfl,
            ev_eq_zero (m := b + 2) (show b + 2 ≤ b + 1 + 1 from le_rfl)]
          ext j <;> simp
    have hinr : ∀ j : Fin (b + 1), π (gluedCol (b + 2) b D S D' S' (b + 2) u (.inr j)) =
        uCol (b + 1) D S D₂ S₂ (S (b + 1)) (.inr ⟨j, by omega⟩) := by
      rintro ⟨j, hj⟩
      simp only [gluedCol, π, LinearMap.coprod_apply, chainCol, map_add, map_smul]
      by_cases hjb : j < b
      · rw [if_neg (by omega), map_zero, zero_add, reiPi₂_ev (by omega), reiPi₂_ev (by omega)]
        simp only [uCol, chainCol, hD₂, hS₂, if_neg (show j ≠ b + 1 by omega),
          if_neg (show j ≠ b by omega)]
        ext k <;> simp
      · have : j = b := by omega
        subst this
        rw [if_pos rfl, map_smul, reiPi₁_ev_last, reiPi₂_ev le_rfl,
          ev_eq_zero (m := j + 1) (show j + 1 ≤ j + 1 from le_rfl)]
        simp only [uCol, chainCol, hD₂, hS₂, if_neg (show j ≠ j + 1 by omega), if_pos rfl]
        ext k <;> simp [add_comm]
    unfold gluedRel
    rw [map_span_range]
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨i | j, rfl⟩
      · rw [Function.comp_apply, hinl]
        split_ifs
        · exact subset_span ⟨_, rfl⟩
        · exact subset_span ⟨_, rfl⟩
      · rw [Function.comp_apply, hinr]
        exact subset_span ⟨_, rfl⟩
    · rw [uRel, span_le]
      rintro _ ⟨t | t, rfl⟩
      · refine subset_span ⟨.inl ⟨t, by omega⟩, ?_⟩
        rw [Function.comp_apply, hinl, dif_pos (by simp; omega)]
      · by_cases ht : (t : ℕ) ≤ b
        · refine subset_span ⟨.inr ⟨t, by omega⟩, ?_⟩
          rw [Function.comp_apply, hinr]
        · refine subset_span ⟨.inl ⟨b + 2, by omega⟩, ?_⟩
          rw [Function.comp_apply, hinl, dif_neg (by simp)]
          congr
          have := t.2; omega

end reindex

end ColouredSand.Blocks
