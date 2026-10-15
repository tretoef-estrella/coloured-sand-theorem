module

public import RequestProject.Doubling.WeylBasis

/-!
# `C20_the_doubling_functor.md`: Part D — `Φ` on Weyl lattices (Prop. 3.1 (d))

Encodings:
* The basis of `Φ(Δ_A(μ))` (and of `Φ(∇_A(μ))`) is `Fin 2 × Fin (μ + 1)`; the `R`-th vector
  `x_R` (`0 ≤ R ≤ 2μ + 1`, `R : Fin (2μ + 1 + 1)`) is `xR μ R = b_{R mod 2} e_{R / 2}`, i.e.
  `b_0 e_s` for `R = 2s` and `b_1 e_s` for `R = 2s + 1`.
* `cD R` is `c_R` (`c_{2s} = ⅟(2s−1)!!`, `c_{2s+1} = ⅟(2s+1)!!`) and `cDinv R` is `c_R^{-1}`
  (`(2s−1)!!`, resp. `(2s+1)!!`).
* `deltaMap μ` is `δ_μ : Δ_A(2μ+1) → Φ(Δ_A(μ))`, `e'_R ↦ c_R x_R`, and `deltaInv μ` is
  `x_R ↦ c_R^{-1} e'_R`; both are defined on basis vectors (`Basis.constr`).
* `dN μ R` is `d_R` (a product of inverses of odd integers, satisfying the recursion of the file,
  `dN_zero`, `dN_odd`, `dN_even`), `dNinv μ R` is `d_R^{-1}`; `nablaMap μ` is
  `ν_μ : ∇_A(2μ+1) → Φ(∇_A(μ))`, `w'_R ↦ d_R x_R`, and `nablaInv μ` is `x_R ↦ d_R^{-1} w'_R`.

The commutation of `δ_μ`, `ν_μ` with `F^{(1)}`, `E^{(1)}` and `H` is checked directly on basis
vectors; the commutation with all divided powers then follows from (B2)-type recursions and
cancellation in a domain of characteristic zero (`homOfOne`). No complete reducibility is used.
-/

@[expose] public section

noncomputable section

namespace Doubling

open DPLattice Finset WeylFilt

open scoped Nat

variable {A : Type*} [CommRing A]

/-! ### Basis vectors of the Weyl lattices -/

/-- the basis vector `e_s` of `Δ_A(l)`. -/
def eD (l : ℕ) (s : Fin (l + 1)) : (delta A l).ι → A := Pi.single s 1

/-- the basis vector `w_s` of `∇_A(l)`. -/
def eN (l : ℕ) (s : Fin (l + 1)) : (nabla A l).ι → A := Pi.single s 1

section basis

variable (l : ℕ)

lemma eD_F_lt (s t : Fin (l + 1)) (h : (t : ℕ) = s + 1) :
    (delta A l).Fd 1 (eD l s) = (((s : ℕ) + 1 : ℕ) : A) • eD l t := dF1_lt l s t h
lemma eD_F_last (s : Fin (l + 1)) (h : (s : ℕ) = l) : (delta A l).Fd 1 (eD l s) = 0 :=
  dF1_last l s h
lemma eD_E_pos (s t : Fin (l + 1)) (h : (s : ℕ) = t + 1) :
    (delta A l).Ed 1 (eD l s) = ((l - s + 1 : ℕ) : A) • eD l t := dE1_pos l s t h
lemma eD_E_zero (s : Fin (l + 1)) (h : (s : ℕ) = 0) : (delta A l).Ed 1 (eD l s) = 0 :=
  dE1_zero l s h
lemma eD_FE (s : Fin (l + 1)) : (delta A l).Fd 1 ((delta A l).Ed 1 (eD l s)) =
    (((s : ℕ) * (l - s + 1) : ℕ) : A) • eD l s := dFE l s
lemma eN_F_lt (s t : Fin (l + 1)) (h : (t : ℕ) = s + 1) :
    (nabla A l).Fd 1 (eN l s) = ((l - s : ℕ) : A) • eN l t := nF1_lt l s t h
lemma eN_F_last (s : Fin (l + 1)) (h : (s : ℕ) = l) : (nabla A l).Fd 1 (eN l s) = 0 :=
  nF1_last l s h
lemma eN_E_pos (s t : Fin (l + 1)) (h : (s : ℕ) = t + 1) :
    (nabla A l).Ed 1 (eN l s) = ((s : ℕ) : A) • eN l t := nE1_pos l s t h
lemma eN_E_zero (s : Fin (l + 1)) (h : (s : ℕ) = 0) : (nabla A l).Ed 1 (eN l s) = 0 :=
  nE1_zero l s h
lemma eN_FE (s : Fin (l + 1)) : (nabla A l).Fd 1 ((nabla A l).Ed 1 (eN l s)) =
    (((s : ℕ) * (l - s + 1) : ℕ) : A) • eN l s := nFE l s

lemma wt_eD (s : Fin (l + 1)) : InWt (delta A l).wt ((l : ℤ) - 2 * (s : ℕ)) (eD (A := A) l s) :=
  inWt_single _ (s : (delta A l).ι)
lemma wt_eN (s : Fin (l + 1)) : InWt (nabla A l).wt ((l : ℤ) - 2 * (s : ℕ)) (eN (A := A) l s) :=
  inWt_single _ (s : (nabla A l).ι)

end basis

/-! ### The vectors `x_R` -/

/-- (D1), (D2) the slot `R mod 2` of `x_R`. -/
def parR (R : ℕ) : Fin 2 := ⟨R % 2, Nat.mod_lt _ two_pos⟩

/-- (D1) the `R`-th basis vector `x_R` of `Φ(Δ_A(μ))`, ordered by weight:
`x_{2s} = b_0 e_s`, `x_{2s+1} = b_1 e_s`. -/
def xD (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) : Fin 2 × (delta A μ).ι → A :=
  bvec (parR R) (eD μ ⟨R / 2, by omega⟩)

/-- (D2) the `R`-th basis vector `x_R` of `Φ(∇_A(μ))`, ordered by weight:
`x_{2s} = b_0 w_s`, `x_{2s+1} = b_1 w_s`. -/
def xN (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) : Fin 2 × (nabla A μ).ι → A :=
  bvec (parR R) (eN μ ⟨R / 2, by omega⟩)

lemma parR_even (R k : ℕ) (h : R = 2 * k) : parR R = 0 := Fin.ext (by simp [parR]; omega)
lemma parR_odd (R k : ℕ) (h : R = 2 * k + 1) : parR R = 1 := Fin.ext (by simp [parR]; omega)

lemma xD_even (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) (s : Fin (μ + 1)) (h : (R : ℕ) = 2 * s) :
    xD (A := A) μ R = bvec 0 (eD μ s) := by
  have h2 : (⟨R / 2, by omega⟩ : Fin (μ + 1)) = s := Fin.ext (by simp; omega)
  rw [xD, parR_even _ _ h, h2]

lemma xD_odd (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) (s : Fin (μ + 1)) (h : (R : ℕ) = 2 * s + 1) :
    xD (A := A) μ R = bvec 1 (eD μ s) := by
  have h2 : (⟨R / 2, by omega⟩ : Fin (μ + 1)) = s := Fin.ext (by simp; omega)
  rw [xD, parR_odd _ _ h, h2]

lemma xN_even (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) (s : Fin (μ + 1)) (h : (R : ℕ) = 2 * s) :
    xN (A := A) μ R = bvec 0 (eN μ s) := by
  have h2 : (⟨R / 2, by omega⟩ : Fin (μ + 1)) = s := Fin.ext (by simp; omega)
  rw [xN, parR_even _ _ h, h2]

lemma xN_odd (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) (s : Fin (μ + 1)) (h : (R : ℕ) = 2 * s + 1) :
    xN (A := A) μ R = bvec 1 (eN μ s) := by
  have h2 : (⟨R / 2, by omega⟩ : Fin (μ + 1)) = s := Fin.ext (by simp; omega)
  rw [xN, parR_odd _ _ h, h2]

/-- (D1) the index `R = 2s + e` of the basis vector `b_e e_s = x_R`. -/
def xIdx (μ : ℕ) (p : Fin 2 × Fin (μ + 1)) : Fin (2 * μ + 1 + 1) :=
  ⟨2 * (p.2 : ℕ) + p.1, by have := p.1.isLt; have := p.2.isLt; omega⟩

lemma xD_xIdx (μ : ℕ) (p : Fin 2 × Fin (μ + 1)) :
    xD (A := A) μ (xIdx μ p) = Pi.single (p : Fin 2 × (delta A μ).ι) 1 := by
  obtain ⟨e, s⟩ := p
  rw [single_eq_bvec]
  rcases fin_two_cases e with rfl | rfl
  · exact xD_even μ _ s (by simp [xIdx])
  · exact xD_odd μ _ s (by simp [xIdx])

lemma xN_xIdx (μ : ℕ) (p : Fin 2 × Fin (μ + 1)) :
    xN (A := A) μ (xIdx μ p) = Pi.single (p : Fin 2 × (nabla A μ).ι) 1 := by
  obtain ⟨e, s⟩ := p
  rw [single_eq_bvec]
  rcases fin_two_cases e with rfl | rfl
  · exact xN_even μ _ s (by simp [xIdx])
  · exact xN_odd μ _ s (by simp [xIdx])

lemma xIdx_parR (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    xIdx μ (parR R, ⟨R / 2, by omega⟩) = R := Fin.ext (by simp [xIdx, parR]; omega)

lemma xD_eq_single (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    xD (A := A) μ R = Pi.single ((parR R, ⟨R / 2, by omega⟩) : Fin 2 × (delta A μ).ι) 1 := by
  rw [xD, eD, single_eq_bvec]

lemma xN_eq_single (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    xN (A := A) μ R = Pi.single ((parR R, ⟨R / 2, by omega⟩) : Fin 2 × (nabla A μ).ι) 1 := by
  rw [xN, eN, single_eq_bvec]

/-! ### The weights of `x_R` -/

lemma H_xD (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    Hop (phiWt (delta A μ)) (xD μ R) =
      ((((2 * μ + 1 : ℕ) : ℤ) - 2 * (R : ℕ) : ℤ) : A) • xD (A := A) μ R := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (R : ℕ)
  · have hs : k < μ + 1 := by omega
    rw [xD_even μ R ⟨k, hs⟩ hk, Hop_of_inWt (inWt_bvec _ 0 (wt_eD μ _))]
    congr 2; simp [hk]; ring
  · have hs : k < μ + 1 := by omega
    rw [xD_odd μ R ⟨k, hs⟩ hk, Hop_of_inWt (inWt_bvec _ 1 (wt_eD μ _))]
    congr 2; simp [hk]; ring

lemma H_xN (μ : ℕ) (R : Fin (2 * μ + 1 + 1)) :
    Hop (phiWt (nabla A μ)) (xN μ R) =
      ((((2 * μ + 1 : ℕ) : ℤ) - 2 * (R : ℕ) : ℤ) : A) • xN (A := A) μ R := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (R : ℕ)
  · have hs : k < μ + 1 := by omega
    rw [xN_even μ R ⟨k, hs⟩ hk, Hop_of_inWt (inWt_bvec _ 0 (wt_eN μ _))]
    congr 2; simp [hk]; ring
  · have hs : k < μ + 1 := by omega
    rw [xN_odd μ R ⟨k, hs⟩ hk, Hop_of_inWt (inWt_bvec _ 1 (wt_eN μ _))]
    congr 2; simp [hk]; ring

lemma H_eD (l : ℕ) (R : Fin (l + 1)) :
    Hop (delta A l).wt (eD l R) = (((l : ℤ) - 2 * (R : ℕ) : ℤ) : A) • eD (A := A) l R :=
  Hop_of_inWt (wt_eD l R)

lemma H_eN (l : ℕ) (R : Fin (l + 1)) :
    Hop (nabla A l).wt (eN l R) = (((l : ℤ) - 2 * (R : ℕ) : ℤ) : A) • eN (A := A) l R :=
  Hop_of_inWt (wt_eN l R)

end Doubling
