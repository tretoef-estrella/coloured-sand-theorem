module

public import RequestProject.Windows.TheoremW

/-!
# Part D of `C14_windows_and_theorem_D.md`: Theorem D

* `finalMatrix A ds α i : Matrix (Fin (2^m)) (Fin (2^m)) A` is the final matrix
  `Mfin (dance ds 1 (pσ α i) κσ)` over `A`, read on `Fin (2^m)` through the cast
  `Fin (2^m) ≃ Fin (1 · 2^m)` exactly as in `Dance.proposition_4_3`.
* **Theorem D**: `theorem_D_i`, `theorem_D_ii`, `theorem_D_iii`, `theorem_D_iv`, assembled in
  `theorem_D`.
-/

@[expose] public section

universe u

namespace Windows

open Finset Deficit Payment Split Dance
open scoped Pointwise

/-- The final matrix `M` over a commutative ring `A`: `Mfin (dance ds 1 (pσ α i) κσ)`, read on
`Fin (2^m)` through the cast `Fin (2^m) ≃ Fin (1 · 2^m)` (`Matrix.submatrix` along `Fin.cast`), as
in `Dance.proposition_4_3` (*Part D*, Theorem D, of `C14_windows_and_theorem_D.md`). -/
noncomputable def finalMatrix (A : Type u) [CommRing A] (ds : List Bool) (α i : ℕ) :
    Matrix (Fin (2 ^ mCount ds)) (Fin (2 ^ mCount ds)) A :=
  (Mfin (dance ds 1 (pσ (A := A) α i) κσ).1 (dance ds 1 (pσ (A := A) α i) κσ).2).submatrix
    (Fin.cast (one_mul (2 ^ mCount ds)).symm) (Fin.cast (one_mul (2 ^ mCount ds)).symm)

/-- The final matrix over `A` is the image of the one over `ℤ` (*Part H*, (H3), read on
`Fin (2^m)`; used for Theorem D of `C14_windows_and_theorem_D.md`). -/
lemma finalMatrix_eq_map (A : Type u) [CommRing A] (ds : List Bool) (α i : ℕ) :
    finalMatrix A ds α i = (finalMatrix ℤ ds α i).map (Int.castRingHom A) := by
  unfold finalMatrix
  rw [H3_final_matrix, Matrix.submatrix_map]

/-- **Theorem D, (D-i)** (*Part D* of `C14_windows_and_theorem_D.md`):
`Sys(T(ds), Fin 1) ⧸ range(σ^{(α)}_i) ≅ Π_{a<k} ((Fin (2^{k+m−1−a}) → ℤ) ⧸ 2^a·⊤)
  × (Fin (2^m) → ℤ) ⧸ range(2^k · Matrix.toLin' M)` over `ℤ` (this is `Dance.proposition_4_3`
at `A = ℤ`).  The hypothesis `1 ≤ k` of Theorem D is not needed for this part; `1 ≤ α` is
passed on to `Dance.proposition_4_3`, whose proof does not use it. -/
theorem theorem_D_i (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) :
    Nonempty ((SysT ℤ ds (Fin 1) ⧸ LinearMap.range (sigma ℤ ds α i)) ≃ₗ[ℤ]
      (((a : Fin ds.length) → (Fin (2 ^ (ds.length + mCount ds - 1 - a)) → ℤ) ⧸
          (2 : ℤ) ^ (a : ℕ) • (⊤ : Submodule ℤ (Fin (2 ^ (ds.length + mCount ds - 1 - a)) → ℤ))) ×
        ((Fin (2 ^ mCount ds) → ℤ) ⧸ LinearMap.range ((2 : ℤ) ^ ds.length •
          Matrix.toLin' (finalMatrix ℤ ds α i))))) :=
  proposition_4_3 ds α i hα

/-- **Theorem D, (D-ii)** (*Part D* of `C14_windows_and_theorem_D.md`): for all `s, s'`,
`(M s s' : ℚ) = Mc I k α i (D(ds,s)) (D(ds,s'))` if `D(ds,s') ⊆ D(ds,s)`, and `M s s' = 0`
otherwise (`M` the final matrix over `ℤ`).  The hypothesis `1 ≤ k` is not needed for this
part. -/
theorem theorem_D_ii (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (s s' : Fin (2 ^ mCount ds)) :
    (Dset ds s' ⊆ Dset ds s →
      ((finalMatrix ℤ ds α i s s' : ℤ) : ℚ) =
        Mc (Ids ds) ds.length (α : ℤ) i (Dset ds s) (Dset ds s')) ∧
    (¬ Dset ds s' ⊆ Dset ds s → finalMatrix ℤ ds α i s s' = 0) := by
  have h44 := theorem_4_4 ds α i hα s s'
  have hmap : ((finalMatrix ℤ ds α i s s' : ℤ) : ℚ) = finalMatrix ℚ ds α i s s' := by
    rw [finalMatrix_eq_map ℚ]; rfl
  rw [← finalMatrix.eq_def ℚ ds α i] at h44
  refine ⟨fun hD => ?_, fun hD => ?_⟩
  · rw [hmap, h44, if_pos hD]
  · rw [if_neg hD, ← hmap] at h44
    exact_mod_cast h44

/-- **Theorem D, (D-iii)** (*Part D* of `C14_windows_and_theorem_D.md`): for `k ≥ 1`, if
`D(ds,s') ⊆ D(ds,s)` and `0 < i + o(D(ds,s))`, then `M s s' ≠ 0` and
`v_2(M s s') = 1 − 2^k + o(Δ) + δ(Δ) + Σ_{d ∈ [o(D(ds,s)), o(D(ds,s')) + 2^k)} (α + v_2(i + d))`
(as integers, the valuation being `padicValInt 2`), with `Δ := D(ds,s) ∖ D(ds,s')`. -/
theorem theorem_D_iii (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α)
    (s s' : Fin (2 ^ mCount ds)) (hD : Dset ds s' ⊆ Dset ds s)
    (hi : 0 < i + Rulers.oE (Dset ds s)) :
    finalMatrix ℤ ds α i s s' ≠ 0 ∧
      (padicValInt 2 (finalMatrix ℤ ds α i s s') : ℤ) =
        1 - (2 : ℤ) ^ ds.length + Rulers.oE (Dset ds s \ Dset ds s') +
          Rulers.delta ds.length (Dset ds s \ Dset ds s') +
          ∑ d ∈ Ico (Rulers.oE (Dset ds s)) (Rulers.oE (Dset ds s') + 2 ^ ds.length),
            ((α : ℤ) + (Rulers.v2 (i + d) : ℤ)) := by
  obtain ⟨⟨z, hz0, hMz⟩, hval⟩ := C2_integrality_valuation hk (I := Ids ds)
    (fun t ht => lt_of_mem_Ids ht) (α := (α : ℤ)) (by exact_mod_cast hα) i hD
    (filter_subset _ _) hi
  have hM := (theorem_D_ii ds α i hα s s').1 hD
  rw [hMz] at hM
  have hMz' : finalMatrix ℤ ds α i s s' = z := by exact_mod_cast hM
  refine ⟨hMz' ▸ hz0, ?_⟩
  rw [← (theorem_D_ii ds α i hα s s').1 hD, padicValRat.of_int] at hval
  exact hval

/-- **Theorem D, (D-iv)** (*Part D* of `C14_windows_and_theorem_D.md`): for every commutative ring
`A`, the final matrix over `A` is `M.map (Int.castRingHom A)`.  The hypotheses `1 ≤ k` and
`1 ≤ α` of Theorem D are not needed for this part. -/
theorem theorem_D_iv (A : Type u) [CommRing A] (ds : List Bool) (α i : ℕ) :
    finalMatrix A ds α i = (finalMatrix ℤ ds α i).map (Int.castRingHom A) :=
  finalMatrix_eq_map A ds α i

/-- **Theorem D (assembly)** (*Part D* of `C14_windows_and_theorem_D.md`).  Let `ds : List Bool`
with `k := length ds ≥ 1`, `m := mCount ds`, `I := I(ds)`, `α ≥ 1`, `i ∈ ℕ`, and let
`M := finalMatrix ℤ ds α i` be the final matrix over `ℤ`.  Then (D-i), (D-ii), (D-iii) and
(D-iv) hold (see `theorem_D_i`, …, `theorem_D_iv`; (D-iv) is stated for rings `A` in the
universe `0` here, and for all universes in `theorem_D_iv`). -/
theorem theorem_D (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) :
    Nonempty ((SysT ℤ ds (Fin 1) ⧸ LinearMap.range (sigma ℤ ds α i)) ≃ₗ[ℤ]
      (((a : Fin ds.length) → (Fin (2 ^ (ds.length + mCount ds - 1 - a)) → ℤ) ⧸
          (2 : ℤ) ^ (a : ℕ) • (⊤ : Submodule ℤ (Fin (2 ^ (ds.length + mCount ds - 1 - a)) → ℤ))) ×
        ((Fin (2 ^ mCount ds) → ℤ) ⧸ LinearMap.range ((2 : ℤ) ^ ds.length •
          Matrix.toLin' (finalMatrix ℤ ds α i))))) ∧
    (∀ s s' : Fin (2 ^ mCount ds),
      (Dset ds s' ⊆ Dset ds s →
        ((finalMatrix ℤ ds α i s s' : ℤ) : ℚ) =
          Mc (Ids ds) ds.length (α : ℤ) i (Dset ds s) (Dset ds s')) ∧
      (¬ Dset ds s' ⊆ Dset ds s → finalMatrix ℤ ds α i s s' = 0)) ∧
    (∀ s s' : Fin (2 ^ mCount ds), Dset ds s' ⊆ Dset ds s → 0 < i + Rulers.oE (Dset ds s) →
      finalMatrix ℤ ds α i s s' ≠ 0 ∧
        (padicValInt 2 (finalMatrix ℤ ds α i s s') : ℤ) =
          1 - (2 : ℤ) ^ ds.length + Rulers.oE (Dset ds s \ Dset ds s') +
            Rulers.delta ds.length (Dset ds s \ Dset ds s') +
            ∑ d ∈ Ico (Rulers.oE (Dset ds s)) (Rulers.oE (Dset ds s') + 2 ^ ds.length),
              ((α : ℤ) + (Rulers.v2 (i + d) : ℤ))) ∧
    (∀ (A : Type) [CommRing A],
      finalMatrix A ds α i = (finalMatrix ℤ ds α i).map (Int.castRingHom A)) :=
  ⟨theorem_D_i ds α i hα, theorem_D_ii ds α i hα,
    fun s s' hD hi => theorem_D_iii ds hk α i hα s s' hD hi,
    fun A _ => theorem_D_iv A ds α i⟩

end Windows
