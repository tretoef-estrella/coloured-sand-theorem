module

public import RequestProject.Dance.D1
public import RequestProject.Dance.D2
public import RequestProject.Dance.D3

/-!
# Part D of `C13_the_dance.md`: Proposition 4.3 (the dance) and (D4)

* `Mfin_relab`: relabelling the data by an order isomorphism of `Fin`'s reindexes `Mfin`.
* **Proposition 4.3** `proposition_4_3`: for every digit list `ds` (`k = n(ds)`, `|I| = m(ds)`),
  `α ≥ 1` and `i ∈ ℕ`, with `M` the final matrix of `dance ds 1 pσ κσ` (read on `Fin (2^{|I|})`
  through the cast `Fin (2^{|I|}) ≃ Fin (1 · 2^{|I|})`),
  `Sys(T(ds), Fin 1) ⧸ range(σ^{(α)}_i) ≅ Π_{a < k} ((Fin (2^{k+|I|−1−a}) → A) ⧸ 2^a·⊤)
    × (Fin (2^{|I|}) → A) ⧸ range(2^k · Matrix.toLin' M)`.
* **(D4)** `D4_lower_triangular_even`: `Mfin (dance ds r p κ)` is lower triangular with entries
  on and below the diagonal in `2A`.
-/

@[expose] public section

universe u

namespace Dance

open DirectSum Payment
open scoped Pointwise

variable {A : Type u} [CommRing A]

/-- Relabelling the data along an order isomorphism `e : Fin R ≃o Fin R'` reindexes the final
matrix: `Mfin (p ∘ e) (κ ∘ (e × e)) = (Mfin p κ).submatrix e e` (used for Proposition 4.3 of
`C13_the_dance.md`). -/
lemma Mfin_relab {R R' : ℕ} (e : Fin R ≃o Fin R') (p : Fin R' → ℕ → A)
    (κ : Fin R' → Fin R' → ℕ → A) :
    Mfin (relabP e p) (relabK e κ) = (Mfin p κ).submatrix e e := by
  ext s s'
  simp only [Mfin, relabP, relabK, Matrix.submatrix_apply, e.injective.eq_iff, e.lt_iff_lt]

/-- **Proposition 4.3 (the dance)** of `C13_the_dance.md`.  Let `ds` be a digit list
(`k := n(ds)`, `|I| := m(ds)`), `α ≥ 1`, `i ∈ ℕ`, `(p_k, κ_k) := dance ds 1 pσ κσ` (data on
`Fin (1 · 2^{|I|})`) and `M := Mfin(p_k, κ_k)`, read on `Fin (2^{|I|})` through the cast
`Fin (2^{|I|}) ≃ Fin (1 · 2^{|I|})` (`Matrix.submatrix` along `Fin.cast`).  Then
`X^{(α)}(λ, i) := Sys(T(ds), Fin 1) ⧸ range(σ^{(α)}_i)
  ≅ Π_{a < k} ((Fin (2^{k + |I| − 1 − a}) → A) ⧸ 2^a·⊤) × (Fin (2^{|I|}) → A) ⧸ range(2^k · M)`.

The statement is proved for every digit list `ds` (each `ds` is the digit list of exactly one
`λ`, see the Setting).  The hypothesis `1 ≤ α` of the file is kept but is not used by the proof
(for `α = 0` the halved payment `2^{α−1}(i + f)` is computed with truncated subtraction). -/
theorem proposition_4_3 (ds : List Bool) (α i : ℕ) (_hα : 1 ≤ α) :
    Nonempty ((SysT A ds (Fin 1) ⧸ LinearMap.range (sigma A ds α i)) ≃ₗ[A]
      (((a : Fin (nLen ds)) → (Fin (2 ^ (nLen ds + mCount ds - 1 - a)) → A) ⧸
          (2 : A) ^ (a : ℕ) • (⊤ : Submodule A (Fin (2 ^ (nLen ds + mCount ds - 1 - a)) → A))) ×
        ((Fin (2 ^ mCount ds) → A) ⧸ LinearMap.range ((2 : A) ^ nLen ds •
          Matrix.toLin' ((Mfin (dance ds 1 (pσ (A := A) α i) κσ).1 (dance ds 1 (pσ α i) κσ).2).submatrix
            (Fin.cast (one_mul (2 ^ mCount ds)).symm)
            (Fin.cast (one_mul (2 ^ mCount ds)).symm)))))) := by
  have hσ : sigma A ds α i = (2 : A) ^ 0 • G (fl ds) (F A ds) (pσ α i) κσ := by
    rw [pow_zero, one_smul]; rfl
  rw [hσ]
  obtain ⟨e1⟩ := D1_scaled_dance ds 1 (pσ (A := A) α i) κσ 0
  obtain ⟨e2⟩ := D2_clocks (A := A) ds 1 0
  let eC := e2.trans (LinearEquiv.piCongrRight fun a =>
    pqCast (A := A) (one_mul _) (zero_add (a : ℕ)))
  let eo : Fin (2 ^ mCount ds) ≃o Fin (1 * 2 ^ mCount ds) :=
    Fin.castOrderIso (one_mul (2 ^ mCount ds)).symm
  obtain ⟨e3⟩ := R1_coker (N := fun _ : Idx [] => A) (fl []) (F A []) eo
    (dance ds 1 (pσ (A := A) α i) κσ).1 (dance ds 1 (pσ α i) κσ).2 ((2 : A) ^ (0 + nLen ds))
  obtain ⟨e4⟩ := D3_final_matrix (2 ^ mCount ds) (relabP eo (dance ds 1 (pσ (A := A) α i) κσ).1)
    (relabK eo (dance ds 1 (pσ α i) κσ).2) ((2 : A) ^ (0 + nLen ds))
  rw [Mfin_relab] at e4
  rw [show (2 : A) ^ nLen ds = (2 : A) ^ (0 + nLen ds) by rw [zero_add]]
  exact ⟨e1.trans (LinearEquiv.prodCongr eC (e3.symm.trans e4))⟩

/-- The final matrix of any data is lower triangular, and its entries on and below the diagonal
are `2 ×` an element of `A` (used for (D4) of `C13_the_dance.md`). -/
lemma Mfin_lower_triangular_even {R : ℕ} (p : Fin R → ℕ → A) (κ : Fin R → Fin R → ℕ → A) :
    (∀ s s' : Fin R, s < s' → Mfin p κ s s' = 0) ∧
      (∀ s s' : Fin R, s' ≤ s → ∃ a : A, Mfin p κ s s' = 2 * a) := by
  refine ⟨fun s s' h => ?_, fun s s' h => ?_⟩
  · simp [Mfin, h.ne, not_lt.2 h.le]
  · by_cases hss : s = s'
    · exact ⟨p s 0, by simp [Mfin, hss]⟩
    · exact ⟨κ s s' 0, by simp [Mfin, hss, lt_of_le_of_ne h (Ne.symm hss)]⟩

/-- **(D4) The final matrix is lower triangular, with an even diagonal** of `C13_the_dance.md`:
for every `ds`, `r`, `(p, κ)`, `Mfin (dance ds r p κ)` has `Mfin s s' = 0` for `s < s'`, and every
diagonal entry and every entry below the diagonal lies in `2A` (it is `2 ×` an element of `A`). -/
theorem D4_lower_triangular_even (ds : List Bool) (r : ℕ) (p : Fin r → ℕ → A)
    (κ : Fin r → Fin r → ℕ → A) :
    (∀ s s' : Fin (r * 2 ^ mCount ds), s < s' →
        Mfin (dance ds r p κ).1 (dance ds r p κ).2 s s' = 0) ∧
      (∀ s s' : Fin (r * 2 ^ mCount ds), s' ≤ s →
        ∃ a : A, Mfin (dance ds r p κ).1 (dance ds r p κ).2 s s' = 2 * a) :=
  Mfin_lower_triangular_even _ _

end Dance
