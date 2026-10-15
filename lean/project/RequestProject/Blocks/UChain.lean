module

public import RequestProject.Blocks.PChain

/-!
# Two `ϖ`-chains with two end relations (CSG1, §3 "Elimination", the `p I_{2a}` step for `Mblk`)

After contracting the unit links of `Mblk` and eliminating the glue
(`RequestProject/Blocks/Elim.lean`), §3 of `CSG1_lemma_8_the_blocks.md` arrives at two chains
`g_0, …, g_a` and `h_0, …, h_a` whose links are `p · unit`, together with two end relations
`D₁ g_a + β h_a` and `D₂ h_a`.  Clearing the `2a` unit links of `M' = M/p` splits off
`p I_{2a}`, and a `2 × 2` block remains.  This file proves that statement.

## Encoding

* Ambient module `R^{a+1} × R^{a+1}`; the columns `uCol` are
  `inl t ↦ (chainCol₁ t, [t = a] β e_a)` and `inr t ↦ (0, chainCol₂ t)`, and `uRel` is their
  span.  (So `inl a` is the relation `D₁(a) g_a + β h_a` and `inr a` is `D₂(a) h_a`.)
* The result is `((R ⧸ ϖ)^a × (R ⧸ ϖ)^a) × (R² ⧸ span {(D₁ κ₁, β κ₂), (0, D₂ κ₂)})`.
-/

@[expose] public section

open Submodule

namespace ColouredSand.Blocks

variable {R : Type*} [CommRing R]

/-- Columns of the system of two `ϖ`-chains with the end relations `D₁ g_a + β h_a`,
`D₂ h_a`. -/
def uCol (a : ℕ) (D₁ S₁ D₂ S₂ : ℕ → R) (β : R) :
    Fin (a + 1) ⊕ Fin (a + 1) → (Fin (a + 1) → R) × (Fin (a + 1) → R)
  | .inl t => (chainCol a D₁ S₁ t, if (t : ℕ) = a then β • ev a else 0)
  | .inr t => (0, chainCol a D₂ S₂ t)

/-- The relation module of `uCol`. -/
def uRel (a : ℕ) (D₁ S₁ D₂ S₂ : ℕ → R) (β : R) :
    Submodule R ((Fin (a + 1) → R) × (Fin (a + 1) → R)) :=
  Submodule.span R (Set.range (uCol a D₁ S₁ D₂ S₂ β))

variable {a : ℕ}

lemma prod_piSpan_mem (ϖ : R) (K : Submodule R (((Fin a → R) × (Fin a → R)) × (R × R)))
    (h₁ : ∀ t < a, (((ϖ • (ev t : Fin a → R), (0 : Fin a → R)), (0 : R × R))) ∈ K)
    (h₂ : ∀ t < a, (((0 : Fin a → R), ϖ • (ev t : Fin a → R)), (0 : R × R)) ∈ K)
    {z : (Fin a → R) × (Fin a → R)} (hz : z ∈ (piSpan a ϖ).prod (piSpan a ϖ)) :
    ((z, 0) : ((Fin a → R) × (Fin a → R)) × (R × R)) ∈ K := by
  obtain ⟨z₁, z₂⟩ := z
  obtain ⟨hz₁, hz₂⟩ := hz
  let f₁ : (Fin a → R) →ₗ[R] ((Fin a → R) × (Fin a → R)) × (R × R) :=
    LinearMap.inl R _ _ ∘ₗ LinearMap.inl R _ _
  let f₂ : (Fin a → R) →ₗ[R] ((Fin a → R) × (Fin a → R)) × (R × R) :=
    LinearMap.inl R _ _ ∘ₗ LinearMap.inr R _ _
  have k₁ : span R (Set.range fun t : Fin a => ϖ • (ev t : Fin a → R)) ≤ K.comap f₁ := by
    rw [span_le]; rintro _ ⟨t, rfl⟩; exact h₁ t t.2
  have k₂ : span R (Set.range fun t : Fin a => ϖ • (ev t : Fin a → R)) ≤ K.comap f₂ := by
    rw [span_le]; rintro _ ⟨t, rfl⟩; exact h₂ t t.2
  have m₁ : f₁ z₁ ∈ K := k₁ (piSpan_le_span ϖ (show z₁ ∈ piSpan a ϖ from hz₁))
  have m₂ : f₂ z₂ ∈ K := k₂ (piSpan_le_span ϖ (show z₂ ∈ piSpan a ϖ from hz₂))
  have := add_mem m₁ m₂
  convert this using 1
  simp [f₁, f₂]

variable {P₁ w₁ P₂ w₂ : ℕ → R}

/-- The change of generators for the two chains at once. -/
noncomputable def uPi (a : ℕ) (P₁ w₁ P₂ w₂ : ℕ → R) :
    (Fin (a + 1) → R) × (Fin (a + 1) → R) →ₗ[R] ((Fin a → R) × (Fin a → R)) × (R × R) :=
  ((LinearMap.fst R _ _ ∘ₗ pcPi a P₁ w₁).prodMap (LinearMap.fst R _ _ ∘ₗ pcPi a P₂ w₂)).prod
    ((LinearMap.snd R _ _ ∘ₗ pcPi a P₁ w₁).prodMap (LinearMap.snd R _ _ ∘ₗ pcPi a P₂ w₂))

/-- Its inverse. -/
noncomputable def uSig (a : ℕ) (P₁ w₁ P₂ w₂ : ℕ → R) :
    ((Fin a → R) × (Fin a → R)) × (R × R) →ₗ[R] (Fin (a + 1) → R) × (Fin (a + 1) → R) :=
  (pcSig a P₁ w₁ ∘ₗ ((LinearMap.fst R _ _ ∘ₗ LinearMap.fst R _ _).prod
      (LinearMap.fst R _ _ ∘ₗ LinearMap.snd R _ _))).prod
    (pcSig a P₂ w₂ ∘ₗ ((LinearMap.snd R _ _ ∘ₗ LinearMap.fst R _ _).prod
      (LinearMap.snd R _ _ ∘ₗ LinearMap.snd R _ _)))

lemma uPi_apply (x y : Fin (a + 1) → R) :
    uPi a P₁ w₁ P₂ w₂ (x, y) = (((pcPi a P₁ w₁ x).1, (pcPi a P₂ w₂ y).1),
      ((pcPi a P₁ w₁ x).2, (pcPi a P₂ w₂ y).2)) := rfl

lemma uSig_apply (y₁ y₂ : Fin a → R) (r₁ r₂ : R) :
    uSig a P₁ w₁ P₂ w₂ ((y₁, y₂), (r₁, r₂)) = (pcSig a P₁ w₁ (y₁, r₁), pcSig a P₂ w₂ (y₂, r₂)) :=
  rfl

/-- **The `ϖ`-chain lemma for two chains with two end relations.** -/
noncomputable def uPchainEquiv (ϖ : R) (D₁ S₁ D₂ S₂ : ℕ → R) (β : R)
    (hD₁ : ∀ t < a, D₁ t = ϖ * P₁ t) (hS₁ : ∀ t < a, S₁ t = ϖ * w₁ t)
    (hw₁ : ∀ t < a, IsUnit (w₁ t))
    (hD₂ : ∀ t < a, D₂ t = ϖ * P₂ t) (hS₂ : ∀ t < a, S₂ t = ϖ * w₂ t)
    (hw₂ : ∀ t < a, IsUnit (w₂ t))
    (hDa₁ : ϖ ∣ D₁ a) (hβ : ϖ ∣ β) (hDa₂ : ϖ ∣ D₂ a) :
    (((Fin (a + 1) → R) × (Fin (a + 1) → R)) ⧸ uRel a D₁ S₁ D₂ S₂ β) ≃ₗ[R]
      (((Fin a → R) ⧸ piSpan a ϖ) × ((Fin a → R) ⧸ piSpan a ϖ)) ×
        ((R × R) ⧸ span R {((D₁ a * pcCoef P₁ w₁ a, β * pcCoef P₂ w₂ a) : R × R),
          (0, D₂ a * pcCoef P₂ w₂ a)}) := by
  set X : R × R := (D₁ a * pcCoef P₁ w₁ a, β * pcCoef P₂ w₂ a)
  set Y : R × R := (0, D₂ a * pcCoef P₂ w₂ a)
  refine (quotEquivOfSection _ (((piSpan a ϖ).prod (piSpan a ϖ)).prod (span R {X, Y}))
    (uPi a P₁ w₁ P₂ w₂) (uSig a P₁ w₁ P₂ w₂) ?_ ?_ ?_).trans
    ((quotProdEquiv _ _).trans (LinearEquiv.prodCongr (quotProdEquiv _ _) (LinearEquiv.refl _ _)))
  · rintro ⟨⟨y₁, y₂⟩, ⟨r₁, r₂⟩⟩
    rw [uSig_apply, uPi_apply, pcPi_pcSig hw₁, pcPi_pcSig hw₂]
  · rintro ⟨x, y⟩
    rw [uPi_apply, uSig_apply]
    simp [pcSig_pcPi hw₁, pcSig_pcPi hw₂]
  · have himg : ∀ c : Fin (a + 1) ⊕ Fin (a + 1), uPi a P₁ w₁ P₂ w₂ (uCol a D₁ S₁ D₂ S₂ β c) =
        match c with
        | .inl t => if (t : ℕ) < a then ((ϖ • (ev t : Fin a → R), 0), 0)
            else ((D₁ a • (pcImg a P₁ w₁ a).1, β • (pcImg a P₂ w₂ a).1), X)
        | .inr t => if (t : ℕ) < a then ((0, ϖ • (ev t : Fin a → R)), 0)
            else ((0, D₂ a • (pcImg a P₂ w₂ a).1), Y) := by
      rintro (t | t)
      · by_cases h2 : (t : ℕ) < a
        · simp only [uCol, uPi_apply, if_pos h2, if_neg (show (t : ℕ) ≠ a by omega)]
          rw [chainCol, hD₁ t h2, hS₁ t h2, pcPi_link hw₁ ϖ h2]
          simp
        · have : (t : ℕ) = a := by omega
          simp only [uCol, uPi_apply, if_neg h2, if_pos this]
          rw [chainCol, this, ev_eq_zero (show a + 1 ≤ a + 1 from le_rfl), smul_zero, add_zero]
          simp only [map_smul, pcPi_ev le_rfl, Prod.smul_fst, Prod.smul_snd, pcImg_snd,
            smul_eq_mul, X]
      · simp only [uCol, uPi_apply]
        split_ifs with h2
        · rw [chainCol, hD₂ t h2, hS₂ t h2, pcPi_link hw₂ ϖ h2]
          simp
        · have : (t : ℕ) = a := by omega
          rw [chainCol, this, ev_eq_zero (show a + 1 ≤ a + 1 from le_rfl), smul_zero, add_zero]
          simp only [map_smul, pcPi_ev le_rfl, Prod.smul_fst, Prod.smul_snd, pcImg_snd,
            smul_eq_mul, map_zero, Prod.fst_zero, Prod.snd_zero, Y]
    rw [uRel, map_span_range]
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨c, rfl⟩
      rw [Function.comp_apply, himg c]
      rcases c with t | t
      · simp only
        split_ifs
        · exact ⟨⟨smul_ev_mem_piSpan ϖ _, zero_mem _⟩, zero_mem _⟩
        · exact ⟨⟨smul_mem_piSpan hDa₁ _, smul_mem_piSpan hβ _⟩, subset_span (by simp [X])⟩
      · simp only
        split_ifs
        · exact ⟨⟨zero_mem _, smul_ev_mem_piSpan ϖ _⟩, zero_mem _⟩
        · exact ⟨⟨zero_mem _, smul_mem_piSpan hDa₂ _⟩, subset_span (by simp [Y])⟩
    · set K := span R (Set.range (uPi a P₁ w₁ P₂ w₂ ∘ uCol a D₁ S₁ D₂ S₂ β))
      have hK₁ : ∀ t < a, (((ϖ • (ev t : Fin a → R), (0 : Fin a → R)), (0 : R × R))) ∈ K := by
        intro t ht
        refine subset_span ⟨.inl ⟨t, by omega⟩, ?_⟩
        rw [Function.comp_apply, himg]
        simp [ht]
      have hK₂ : ∀ t < a, (((0 : Fin a → R), ϖ • (ev t : Fin a → R)), (0 : R × R)) ∈ K := by
        intro t ht
        refine subset_span ⟨.inr ⟨t, by omega⟩, ?_⟩
        rw [Function.comp_apply, himg]
        simp [ht]
      have hX : ((D₁ a • (pcImg a P₁ w₁ a).1, β • (pcImg a P₂ w₂ a).1), X) ∈ K := by
        refine subset_span ⟨.inl ⟨a, by omega⟩, ?_⟩
        rw [Function.comp_apply, himg]
        simp
      have hY : (((0 : Fin a → R), D₂ a • (pcImg a P₂ w₂ a).1), Y) ∈ K := by
        refine subset_span ⟨.inr ⟨a, by omega⟩, ?_⟩
        rw [Function.comp_apply, himg]
        simp
      rintro ⟨yy, ww⟩ ⟨hyy, hww⟩
      obtain ⟨c₁, c₂, hc⟩ := Submodule.mem_span_pair.mp hww
      have hz : yy - c₁ • (D₁ a • (pcImg a P₁ w₁ a).1, β • (pcImg a P₂ w₂ a).1) -
          c₂ • ((0 : Fin a → R), D₂ a • (pcImg a P₂ w₂ a).1) ∈
            (piSpan a ϖ).prod (piSpan a ϖ) := by
        refine sub_mem (sub_mem hyy (Submodule.smul_mem _ _ ⟨?_, ?_⟩))
          (Submodule.smul_mem _ _ ⟨zero_mem _, ?_⟩)
        · exact smul_mem_piSpan hDa₁ _
        · exact smul_mem_piSpan hβ _
        · exact smul_mem_piSpan hDa₂ _
      have := add_mem (prod_piSpan_mem ϖ K hK₁ hK₂ hz)
        (add_mem (K.smul_mem c₁ hX) (K.smul_mem c₂ hY))
      convert this using 1
      subst hc
      ext <;> simp

end ColouredSand.Blocks
