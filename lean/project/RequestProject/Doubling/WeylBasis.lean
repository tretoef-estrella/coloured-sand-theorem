module

public import RequestProject.Doubling.Functor

/-!
# `C20_the_doubling_functor.md`: Part D — the single operators on `Δ_A(λ)`, `∇_A(λ)`

Auxiliary formulas: `F e_s`, `E e_s`, `FE e_s` on C18's `Δ_A(λ)` and `∇_A(λ)` (basis
`Fin (λ + 1)`, `e_s = Pi.single s 1`), in the form used in the proofs of (D1), (D2):
on `Δ(λ)`: `F e_s = (s+1) e_{s+1}`, `E e_s = (λ−s+1) e_{s−1}`;
on `∇(λ)`: `F w_s = (λ−s) w_{s+1}`, `E w_s = s w_{s−1}`; on both, `FE e_s = s(λ−s+1) e_s`.
-/

@[expose] public section

noncomputable section

namespace Doubling

open DPLattice Finset

variable {A : Type*} [CommRing A]

section weyl

variable (l : ℕ)

lemma dF1_lt (s t : Fin (l + 1)) (h : (t : ℕ) = s + 1) :
    (delta A l).Fd 1 (Pi.single s 1) = (((s : ℕ) + 1 : ℕ) : A) • (Pi.single t (1 : A) : Fin (l + 1) → A) := by
  rw [delta_Fd_single, dif_pos (by omega)]
  congr 1
  · simp
  · congr 1; exact Fin.ext h.symm

lemma dF1_last (s : Fin (l + 1)) (h : (s : ℕ) = l) : (delta A l).Fd 1 (Pi.single s 1) = 0 := by
  rw [delta_Fd_single, dif_neg (by omega)]

lemma dE1_pos (s t : Fin (l + 1)) (h : (s : ℕ) = t + 1) :
    (delta A l).Ed 1 (Pi.single s 1) = ((l - s + 1 : ℕ) : A) • (Pi.single t (1 : A) : Fin (l + 1) → A) := by
  rw [delta_Ed_single, dif_pos (by omega)]
  congr 1
  · simp
  · congr 1; exact Fin.ext (by simp; omega)

lemma dE1_zero (s : Fin (l + 1)) (h : (s : ℕ) = 0) : (delta A l).Ed 1 (Pi.single s 1) = 0 := by
  rw [delta_Ed_single, dif_neg (by omega)]

lemma nF1_lt (s t : Fin (l + 1)) (h : (t : ℕ) = s + 1) :
    (nabla A l).Fd 1 (Pi.single s 1) = ((l - s : ℕ) : A) • (Pi.single t (1 : A) : Fin (l + 1) → A) := by
  rw [nabla_Fd_single, dif_pos (by omega)]
  congr 1
  · simp
  · congr 1; exact Fin.ext h.symm

lemma nF1_last (s : Fin (l + 1)) (h : (s : ℕ) = l) : (nabla A l).Fd 1 (Pi.single s 1) = 0 := by
  rw [nabla_Fd_single, dif_neg (by omega)]

lemma nE1_pos (s t : Fin (l + 1)) (h : (s : ℕ) = t + 1) :
    (nabla A l).Ed 1 (Pi.single s 1) = ((s : ℕ) : A) • (Pi.single t (1 : A) : Fin (l + 1) → A) := by
  rw [nabla_Ed_single, dif_pos (by omega)]
  congr 1
  · simp
  · congr 1; exact Fin.ext (by simp; omega)

lemma nE1_zero (s : Fin (l + 1)) (h : (s : ℕ) = 0) : (nabla A l).Ed 1 (Pi.single s 1) = 0 := by
  rw [nabla_Ed_single, dif_neg (by omega)]

lemma dFE (s : Fin (l + 1)) : (delta A l).Fd 1 ((delta A l).Ed 1 (Pi.single s 1)) =
    (((s : ℕ) * (l - s + 1) : ℕ) : A) • (Pi.single s (1 : A) : Fin (l + 1) → A) := by
  rcases Nat.eq_zero_or_pos (s : ℕ) with h | h
  · rw [dE1_zero l s h, map_zero, h]; simp
  · have hs := s.isLt
    rw [dE1_pos l s ⟨s - 1, by omega⟩ (by simp; omega), map_smul,
      dF1_lt l ⟨s - 1, by omega⟩ s (by simp; omega), smul_smul]
    congr 1
    have : (s : ℕ) - 1 + 1 = s := by omega
    rw [this]; push_cast; ring

lemma nFE (s : Fin (l + 1)) : (nabla A l).Fd 1 ((nabla A l).Ed 1 (Pi.single s 1)) =
    (((s : ℕ) * (l - s + 1) : ℕ) : A) • (Pi.single s (1 : A) : Fin (l + 1) → A) := by
  rcases Nat.eq_zero_or_pos (s : ℕ) with h | h
  · rw [nE1_zero l s h, map_zero, h]; simp
  · have hs := s.isLt
    rw [nE1_pos l s ⟨s - 1, by omega⟩ (by simp; omega), map_smul,
      nF1_lt l ⟨s - 1, by omega⟩ s (by simp; omega), smul_smul]
    congr 1
    have : l - (s - 1) = l - s + 1 := by omega
    simp only [this]; push_cast; ring

end weyl

end Doubling
