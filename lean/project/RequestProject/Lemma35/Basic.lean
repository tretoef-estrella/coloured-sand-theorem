module

public import RequestProject.Lemma35.Sum

/-!
# `C22_lemma_35_over_F2.md`: Part L — tools

Encodings (namespace `Lemma35`):

* `ofImg v` is the linear map `(ι → A) → (κ → A)` defined on basis vectors by
  `δ_i ↦ v i` (its matrix has columns `v i`), so `ofImg v (Pi.single i 1) = v i`
  (`ofImg_single`). The maps `g`, `h`, `u`, `u⁻¹` of Part L are of this form.
* `homOfSmall` builds a `Hom` from a linear map that commutes with `F^{(r)}`, `E^{(r)}` on basis
  vectors for `1 ≤ r ≤ m` and sends basis vectors to vectors of the same weight, when all weights
  lie in `[−m, m]` (for `r = 0` use (P0), for `r > m` both sides vanish by (W)); this is the
  argument of the proof sketch of (L1), (L2).
-/

@[expose] public section

noncomputable section

namespace Lemma35

open DPLattice Finset WeylFilt

variable {A : Type*} [CommRing A]

/-- Part L: the linear map defined on basis vectors by `δ_i ↦ v i`. -/
def ofImg {ι κ : Type*} [Fintype ι] [DecidableEq ι] (v : ι → κ → A) :
    (ι → A) →ₗ[A] (κ → A) :=
  Matrix.toLin' (Matrix.of fun j i => v i j)

lemma ofImg_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] (v : ι → κ → A) (x : ι → A)
    (j : κ) : ofImg v x j = ∑ i, x i * v i j := by
  simp [ofImg, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- Part L: `ofImg v` sends the basis vector `δ_i` to `v i`. -/
@[simp] lemma ofImg_single {ι κ : Type*} [Fintype ι] [DecidableEq ι] (v : ι → κ → A) (i : ι) :
    ofImg v (Pi.single i 1) = v i := by
  funext j; simp [ofImg_apply, Pi.single_apply]

/-- Part L (proof sketch): if every weight lies in `[−m, m]`, then `F^{(r)} = 0` for `r > m`. -/
lemma Fd_eq_zero_of_bound (M : DPLattice A) (m : ℤ) (hw : ∀ i, -m ≤ M.wt i ∧ M.wt i ≤ m)
    (r : ℕ) (hr : m < r) : M.Fd r = 0 :=
  ext_single fun i => by
    funext j
    rw [M.isDP.W_F i r j (by have := hw i; have := hw j; omega)]
    rfl

/-- Part L (proof sketch): if every weight lies in `[−m, m]`, then `E^{(r)} = 0` for `r > m`. -/
lemma Ed_eq_zero_of_bound (M : DPLattice A) (m : ℤ) (hw : ∀ i, -m ≤ M.wt i ∧ M.wt i ≤ m)
    (r : ℕ) (hr : m < r) : M.Ed r = 0 :=
  ext_single fun i => by
    funext j
    rw [M.isDP.W_E i r j (by have := hw i; have := hw j; omega)]
    rfl

/-- Part L (proof sketch): a linear map between DP-lattices with all weights in `[−m, m]`, which
commutes with `F^{(r)}`, `E^{(r)}` on basis vectors for `1 ≤ r ≤ m` and sends every basis vector
to a vector of the same weight, is a `Hom`. -/
def homOfSmall (M N : DPLattice A) (φ : (M.ι → A) →ₗ[A] (N.ι → A)) (m : ℕ)
    (hM : ∀ i, -(m : ℤ) ≤ M.wt i ∧ M.wt i ≤ m) (hN : ∀ j, -(m : ℤ) ≤ N.wt j ∧ N.wt j ≤ m)
    (hF : ∀ r, 1 ≤ r → r ≤ m → ∀ i, φ (M.Fd r (Pi.single i 1)) = N.Fd r (φ (Pi.single i 1)))
    (hE : ∀ r, 1 ≤ r → r ≤ m → ∀ i, φ (M.Ed r (Pi.single i 1)) = N.Ed r (φ (Pi.single i 1)))
    (hH : ∀ i j, N.wt j ≠ M.wt i → φ (Pi.single i 1) j = 0) : Hom M N where
  toLin := φ
  comm_F r := ext_single fun i => by
    simp only [LinearMap.comp_apply]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [M.isDP.P0_F, N.isDP.P0_F]; rfl
    · by_cases hrm : r ≤ m
      · exact hF r hr hrm i
      · rw [Fd_eq_zero_of_bound M m hM r (by omega), Fd_eq_zero_of_bound N m hN r (by omega)]
        simp
  comm_E r := ext_single fun i => by
    simp only [LinearMap.comp_apply]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [M.isDP.P0_E, N.isDP.P0_E]; rfl
    · by_cases hrm : r ≤ m
      · exact hE r hr hrm i
      · rw [Ed_eq_zero_of_bound M m hM r (by omega), Ed_eq_zero_of_bound N m hN r (by omega)]
        simp
  comm_H := ext_single fun i => by
    simp only [LinearMap.comp_apply]
    rw [Doubling.Hop_of_inWt (inWt_single M.wt i), map_smul,
      Doubling.Hop_of_inWt (μ := M.wt i) (fun j hj => hH i j hj)]

@[simp] lemma homOfSmall_toLin (M N : DPLattice A) (φ : (M.ι → A) →ₗ[A] (N.ι → A)) (m : ℕ) hM hN
    hF hE hH : (homOfSmall M N φ m hM hN hF hE hH).toLin = φ := rfl

end Lemma35
