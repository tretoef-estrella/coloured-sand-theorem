module

public import RequestProject.Blocks.Segment

/-!
# Two glued chains: segment reduction (CSG1, §3 "Elimination", first step for `Mblk`)

The matrix `Mblk` of §1 of `CSG1_lemma_8_the_blocks.md` consists of two lower bidiagonal
chains (the `ℓ`-chain and the `s̃`-chain) and one glue entry `u` (row `ℓ_g`, column `s̃_μ`).
This file encodes such systems and contracts the unit links of both chains at once
(the first step of the elimination in §3).

## Encoding

* The ambient module is `R^{n₁+1} × R^{n₂+1} = (Fin (n₁+1) → R) × (Fin (n₂+1) → R)`.
* `gluedCol` lists the columns: `inl i ↦ (chainCol₁ i, 0)`, and
  `inr j ↦ ([j = n₂] u e_g, chainCol₂ j)`; `gluedRel` is their span (the range of the matrix).
-/

@[expose] public section

open Submodule

namespace ColouredSand.Blocks

variable {R : Type*} [CommRing R]

/-- The columns of the two-chain system glued by the entry `u` in row `g` of the first chain
and the last column of the second chain. -/
def gluedCol (n₁ n₂ : ℕ) (d₁ s₁ d₂ s₂ : ℕ → R) (g : ℕ) (u : R) :
    Fin (n₁ + 1) ⊕ Fin (n₂ + 1) → (Fin (n₁ + 1) → R) × (Fin (n₂ + 1) → R)
  | .inl i => (chainCol n₁ d₁ s₁ i, 0)
  | .inr j => (if (j : ℕ) = n₂ then u • ev g else 0, chainCol n₂ d₂ s₂ j)

/-- The relation module (range) of the glued two-chain system. -/
def gluedRel (n₁ n₂ : ℕ) (d₁ s₁ d₂ s₂ : ℕ → R) (g : ℕ) (u : R) :
    Submodule R ((Fin (n₁ + 1) → R) × (Fin (n₂ + 1) → R)) :=
  Submodule.span R (Set.range (gluedCol n₁ n₂ d₁ s₁ d₂ s₂ g u))

variable {n₁ n₂ L : ℕ} {d₁ s₁ d₂ s₂ : ℕ → R} {g : ℕ} {u : R}

lemma gluedCol_inl_mem {i : ℕ} (hi : i ≤ n₁) :
    ((chainCol n₁ d₁ s₁ i, 0) : (Fin (n₁ + 1) → R) × (Fin (n₂ + 1) → R)) ∈
      gluedRel n₁ n₂ d₁ s₁ d₂ s₂ g u :=
  subset_span ⟨.inl ⟨i, by omega⟩, rfl⟩

lemma gluedCol_inr_mem {j : ℕ} (hj : j < n₂) :
    ((0, chainCol n₂ d₂ s₂ j) : (Fin (n₁ + 1) → R) × (Fin (n₂ + 1) → R)) ∈
      gluedRel n₁ n₂ d₁ s₁ d₂ s₂ g u := by
  refine subset_span ⟨.inr ⟨j, by omega⟩, ?_⟩
  show (if (j : ℕ) = n₂ then u • ev g else 0, chainCol n₂ d₂ s₂ j) = _
  rw [if_neg (by omega)]

lemma gluedCol_last_mem :
    ((u • ev g, chainCol n₂ d₂ s₂ n₂) : (Fin (n₁ + 1) → R) × (Fin (n₂ + 1) → R)) ∈
      gluedRel n₁ n₂ d₁ s₁ d₂ s₂ g u := by
  refine subset_span ⟨.inr ⟨n₂, by omega⟩, ?_⟩
  show (if (n₂ : ℕ) = n₂ then u • ev g else 0, chainCol n₂ d₂ s₂ n₂) = _
  rw [if_pos rfl]

/-- **Segment reduction for two glued chains**: contracting all unit links of both chains.
The glue row `g` must be the start of a segment. -/
noncomputable def gluedSegRedEquiv (hL : 0 < L) (hs₁ : ∀ i < n₁, (i + 1) % L ≠ 0 → IsUnit (s₁ i))
    (hs₂ : ∀ i < n₂, (i + 1) % L ≠ 0 → IsUnit (s₂ i)) (hg : g ≤ n₁) (hgL : g % L = 0) :
    (((Fin (n₁ + 1) → R) × (Fin (n₂ + 1) → R)) ⧸ gluedRel n₁ n₂ d₁ s₁ d₂ s₂ g u) ≃ₗ[R]
      (((Fin (n₁ / L + 1) → R) × (Fin (n₂ / L + 1) → R)) ⧸
        gluedRel (n₁ / L) (n₂ / L) (segD n₁ L d₁ s₁) (segS L s₁) (segD n₂ L d₂ s₂) (segS L s₂)
          (g / L) u) := by
  have hgg : g / L * L = g := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hgL)
  have hevg : segPi n₁ L d₁ s₁ (ev g) = ev (g / L) := by
    rw [segPi_ev hg, ← hgg, segCoef_mul hL, one_smul, hgg]
  refine quotEquivOfSection _ _ ((segPi n₁ L d₁ s₁).prodMap (segPi n₂ L d₂ s₂))
    ((segSig n₁ L).prodMap (segSig n₂ L)) ?_ ?_ ?_
  · rintro ⟨x, y⟩
    simp [segPi_segSig hL]
  · rintro ⟨x, y⟩
    have h1 := segSig_segPi_sub_mem hs₁
      ((gluedRel n₁ n₂ d₁ s₁ d₂ s₂ g u).comap (LinearMap.inl R _ _))
      (fun i hi _ => gluedCol_inl_mem (by omega)) x
    have h2 := segSig_segPi_sub_mem hs₂
      ((gluedRel n₁ n₂ d₁ s₁ d₂ s₂ g u).comap (LinearMap.inr R _ _))
      (fun i hi _ => gluedCol_inr_mem hi) y
    have := add_mem (show LinearMap.inl R _ _ _ ∈ gluedRel n₁ n₂ d₁ s₁ d₂ s₂ g u from h1)
      (show LinearMap.inr R _ _ _ ∈ gluedRel n₁ n₂ d₁ s₁ d₂ s₂ g u from h2)
    convert this using 1
    ext <;> simp
  · rw [gluedRel, map_span_range]
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨i | j, rfl⟩
      · simp only [Function.comp_apply, gluedCol, LinearMap.prodMap_apply, map_zero]
        rw [segPi_chainCol hL hs₁ (by omega)]
        split_ifs
        · exact zero_mem _
        · exact gluedCol_inl_mem (Nat.div_le_div_right (by omega))
      · simp only [Function.comp_apply, gluedCol, LinearMap.prodMap_apply]
        rw [segPi_chainCol hL hs₂ (by omega)]
        by_cases hw : (j : ℕ) < n₂ ∧ ((j : ℕ) + 1) % L ≠ 0
        · rw [if_pos hw, if_neg (by omega), map_zero]
          exact zero_mem _
        · rw [if_neg hw]
          by_cases hj : (j : ℕ) = n₂
          · rw [if_pos hj, map_smul, hevg, hj]
            exact gluedCol_last_mem
          · rw [if_neg hj, map_zero]
            have hlt : (j : ℕ) / L < n₂ / L := by
              have := (not_within_iff hL (by omega) hw).not.mp hj
              have := Nat.div_le_div_right (c := L) (show (j : ℕ) ≤ n₂ by omega)
              omega
            exact gluedCol_inr_mem hlt
    · rw [gluedRel, span_le]
      rintro _ ⟨t | t, rfl⟩
      · obtain ⟨i, hi, hni, hit⟩ := exists_chainCol_eq hL (show (t : ℕ) ≤ n₁ / L by omega)
        refine subset_span ⟨.inl ⟨i, by omega⟩, ?_⟩
        simp only [Function.comp_apply, gluedCol, LinearMap.prodMap_apply, map_zero]
        rw [segPi_chainCol hL hs₁ hi, if_neg hni, hit]
      · obtain ⟨j, hj, hnj, hjt⟩ := exists_chainCol_eq hL (show (t : ℕ) ≤ n₂ / L by omega)
        refine subset_span ⟨.inr ⟨j, by omega⟩, ?_⟩
        simp only [Function.comp_apply, gluedCol, LinearMap.prodMap_apply]
        rw [segPi_chainCol hL hs₂ hj, if_neg hnj, hjt]
        have hiff := not_within_iff hL hj hnj
        rw [hjt] at hiff
        by_cases ht : (t : ℕ) = n₂ / L
        · rw [if_pos (hiff.mpr ht), if_pos ht, map_smul, hevg]
        · rw [if_neg (fun h => ht (hiff.mp h)), if_neg ht, map_zero]

end ColouredSand.Blocks
