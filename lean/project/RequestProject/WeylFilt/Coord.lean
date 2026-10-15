module

public import RequestProject.WeylFilt.Maps

/-!
# `C19_weyl_filtrations_of_V_tensor.md`: coordinate formulas (auxiliary, for Part M and Part S)

Coordinates `ext0 (slice e w) n` of the maps of "The four maps", of `F^{(t)}`, `E^{(s)}`, `H` on
`Δ_A(λ)`, `∇_A(λ)` and on `V ⊗ M`.
-/

@[expose] public section

noncomputable section

namespace WeylFilt

open DPLattice Finset

variable {A : Type*} [CommRing A]

lemma ext0_slice0_fDelta (m : ℕ) (x : Fin (m + 1 + 1) → A) (n : ℕ) :
    ext0 (slice 0 (fDeltaCoord m x)) n = if n ≤ m then ext0 x n else 0 := by
  unfold ext0; split_ifs <;> first | rfl | (exfalso; omega) | simp_all [fDeltaCoord, ext0]

lemma ext0_slice1_fDelta (m : ℕ) (x : Fin (m + 1 + 1) → A) (n : ℕ) :
    ext0 (slice 1 (fDeltaCoord m x)) n = if n ≤ m then ext0 x (n + 1) else 0 := by
  unfold ext0; split_ifs <;> first | rfl | (exfalso; omega) | simp_all [fDeltaCoord, ext0]

lemma ext0_gDelta (m : ℕ) (y : Fin 2 × Fin (m + 1) → A) (n : ℕ) :
    ext0 (gDeltaCoord m y) n =
      if n ≤ m - 1 then ext0 (slice 1 y) n - ext0 (slice 0 y) (n + 1) else 0 := by
  rw [ext0]; split_ifs <;> first | rfl | (exfalso; omega)

lemma ext0_slice0_fNabla (m : ℕ) (x : Fin (m - 1 + 1) → A) (n : ℕ) :
    ext0 (slice 0 (fNablaCoord m x)) n = if n ≤ m ∧ 1 ≤ n then ext0 x (n - 1) else 0 := by
  rw [ext0]; split_ifs with h1 h2 h2
  · simp [fNablaCoord, h2.2]
  · simp only [slice_apply, fNablaCoord, LinearMap.coe_mk, AddHom.coe_mk, if_true]
    rw [if_neg (by omega)]
  · exfalso; omega
  · rfl

lemma ext0_slice1_fNabla (m : ℕ) (x : Fin (m - 1 + 1) → A) (n : ℕ) :
    ext0 (slice 1 (fNablaCoord m x)) n = if n ≤ m then -ext0 x n else 0 := by
  rw [ext0]; split_ifs <;> first | rfl | (exfalso; omega)

lemma ext0_gNabla (m : ℕ) (y : Fin 2 × Fin (m + 1) → A) (n : ℕ) :
    ext0 (gNablaCoord m y) n = if n ≤ m + 1 then
      ext0 (slice 0 y) n + (if 1 ≤ n then ext0 (slice 1 y) (n - 1) else 0) else 0 := by
  rw [ext0]; split_ifs <;> first | rfl | (exfalso; omega) | simp_all [gNablaCoord]

section tensor

variable {ι : Type*} (F : ℕ → Module.End A (ι → A)) (t : ℕ) (w : Fin 2 × ι → A)

lemma slice0_tensorFd : slice 0 (tensorFd F t w) = F t (slice 0 w) := by
  funext i; simp [tensorFd]

lemma slice1_tensorFd : slice 1 (tensorFd F t w) = F t (slice 1 w) + pred F t (slice 0 w) := by
  funext i; simp [tensorFd]

lemma slice0_tensorEd : slice 0 (tensorEd F t w) = F t (slice 0 w) + pred F t (slice 1 w) := by
  funext i; simp [tensorEd]

lemma slice1_tensorEd : slice 1 (tensorEd F t w) = F t (slice 1 w) := by
  funext i; simp [tensorEd]

end tensor

lemma ext0_H (l : ℕ) (u : Fin (l + 1) → A) (n : ℕ) :
    ext0 (Hop (A := A) (weylWt l) u) n = ((l : A) - 2 * n) * ext0 u n := by
  unfold ext0; split_ifs <;> simp [weylWt]

lemma ext0_slice0_H (l : ℕ) (w : Fin 2 × Fin (l + 1) → A) (n : ℕ) :
    ext0 (slice 0 (Hop (A := A) (tensorWt (weylWt l)) w)) n =
      (1 + (l : A) - 2 * n) * ext0 (slice 0 w) n := by
  unfold ext0; split_ifs <;> simp [weylWt, tensorWt]; ring

lemma ext0_slice1_H (l : ℕ) (w : Fin 2 × Fin (l + 1) → A) (n : ℕ) :
    ext0 (slice 1 (Hop (A := A) (tensorWt (weylWt l)) w)) n =
      (-1 + (l : A) - 2 * n) * ext0 (slice 1 w) n := by
  unfold ext0; split_ifs <;> simp [weylWt, tensorWt]; ring

lemma ext_tensor {l : ℕ} {w w' : Fin 2 × Fin (l + 1) → A}
    (h0 : ∀ n, n ≤ l → ext0 (slice 0 w) n = ext0 (slice 0 w') n)
    (h1 : ∀ n, n ≤ l → ext0 (slice 1 w) n = ext0 (slice 1 w') n) : w = w' :=
  ext_slice (ext_ext0 fun n hn => h0 n (by omega)) (ext_ext0 fun n hn => h1 n (by omega))

end WeylFilt
