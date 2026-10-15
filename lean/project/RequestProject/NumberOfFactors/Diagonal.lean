module

public import RequestProject.NumberOfFactors.Wilson

/-!
# (D1) Wilson's diagonal form: the matrix statement

This file corresponds to **(D1) Wilson's diagonal form, the case `k = t + 1`** of
`CS5_theorem_D_number_of_factors.md`; the encodings are explained in
`RequestProject/NumberOfFactors/Wilson.lean` (rows/columns of `inclMat m t` are the `t`- and
`(t+1)`-subsets of `Fin m`; "equivalent over `ℤ`" means `P * W * Q = diagonal` with `P`, `Q`
integer matrices of unit determinant).
-/

@[expose] public section

open Finset Module

namespace ColouredSand.NumberOfFactors

open ColouredSand.Strings

/-- The inclusion matrix acts as the up operator: `Wᵀ (f|_{t-sets}) = (U f)|_{(t+1)-sets}`. -/
lemma toLin'_inclMat_transpose {m t : ℕ} (f : level m ℤ t) :
    Matrix.toLin' (inclMat m t).transpose (levelEquivFun m ℤ t f) =
      levelEquivFun m ℤ (t + 1) ⟨U m ℤ f, U_mem_level f.2⟩ := by
  funext T
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, inclMat,
    Matrix.of_apply, levelEquivFun, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    ite_mul, one_mul, zero_mul]
  rw [U_eq_zeta f.2, zeta_apply, if_pos ⟨subset_univ _, T.2⟩]
  rw [← Finset.sum_subtype (univ.filter fun S : Finset (Fin m) => S.card = t)
    (by simp) (fun S => if S ⊆ (T : Finset (Fin m)) then (f : B m ℤ) S else 0), sum_filter]
  have hT : (T : Finset (Fin m)).powerset = univ.filter (fun S => S ⊆ (T : Finset (Fin m))) := by
    ext S; simp
  rw [hT, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  by_cases hS : S.card = t
  · simp [hS]
  · simp only [hS, if_false]
    split_ifs
    · exact (f.2 S hS).symm
    · rfl

/-- **(D1) Wilson's diagonal form, `k = t + 1`.**  Let `W = W_{t,t+1}` be the inclusion matrix of
the `t`-subsets (rows) versus the `(t+1)`-subsets (columns) of `Fin m`, and suppose
`t ≤ m − t − 1`, i.e. `2t + 1 ≤ m`.  Then there are integer matrices `P`, `Q`, invertible over `ℤ`
(unit determinant), an injection `φ` of the rows into the columns and labels `lab a ≤ t` such that
`P W Q` is the rectangular diagonal matrix with entry `t + 1 − lab a` at `(a, φ a)` and `0`
elsewhere, and each value `t + 1 − i` (`0 ≤ i ≤ t`) occurs with multiplicity
`C(m,i) − C(m,i−1)` (`strMult m i`, with `C(m,−1) = 0`). -/
theorem wilson_diagonal_form (m t : ℕ) (ht : 2 * t + 1 ≤ m) :
    ∃ (P : Matrix {S : Finset (Fin m) // S.card = t} {S : Finset (Fin m) // S.card = t} ℤ)
      (Q : Matrix {T : Finset (Fin m) // T.card = t + 1} {T : Finset (Fin m) // T.card = t + 1} ℤ)
      (φ : {S : Finset (Fin m) // S.card = t} ↪ {T : Finset (Fin m) // T.card = t + 1})
      (lab : {S : Finset (Fin m) // S.card = t} → ℕ),
      IsUnit P.det ∧ IsUnit Q.det ∧ (∀ a, lab a ≤ t) ∧
      P * inclMat m t * Q =
        Matrix.of (fun a b => if b = φ a then (t : ℤ) + 1 - lab a else 0) ∧
      ∀ i ≤ t, Fintype.card {a // lab a = i} = strMult m i := by
  classical
  obtain ⟨ι, κ, hι, hκ, b, b', φ, lab, hlab, hrel, hcard⟩ := wilson_bases m t ht
  set rows := {S : Finset (Fin m) // S.card = t}
  set cols := {T : Finset (Fin m) // T.card = t + 1}
  let V := Matrix.toLin' (inclMat m t).transpose
  let x := b.map (levelEquivFun m ℤ t)
  let y := b'.map (levelEquivFun m ℤ (t + 1))
  have hxy : ∀ a, V (x a) = ((t : ℤ) + 1 - lab a) • y (φ a) := by
    intro a
    simp only [V, x, y, Basis.map_apply]
    rw [toLin'_inclMat_transpose, ← map_zsmul]
    congr 1
    exact Subtype.ext (hrel a)
  have hcι : Fintype.card ι = Fintype.card rows := by
    rw [← finrank_eq_card_basis x, Module.finrank_fintype_fun_eq_card]
  have hcκ : Fintype.card κ = Fintype.card cols := by
    rw [← finrank_eq_card_basis y, Module.finrank_fintype_fun_eq_card]
  let eι : ι ≃ rows := Fintype.equivOfCardEq hcι
  let eκ : κ ≃ cols := Fintype.equivOfCardEq hcκ
  let x' := x.reindex eι
  let y' := y.reindex eκ
  let φ' : rows ↪ cols := eι.symm.toEmbedding.trans (φ.trans eκ.toEmbedding)
  let lab' : rows → ℕ := fun r => lab (eι.symm r)
  have hφ' : ∀ r, φ' r = eκ (φ (eι.symm r)) := fun r => rfl
  have hxy' : ∀ r, V (x' r) = ((t : ℤ) + 1 - lab' r) • y' (φ' r) := by
    intro r
    simp only [x', y', Basis.reindex_apply, hφ', Equiv.symm_apply_apply]
    exact hxy _
  have hmat : LinearMap.toMatrix x' y' V =
      Matrix.of (fun c r => if c = φ' r then (t : ℤ) + 1 - lab' r else 0) := by
    ext c r
    rw [LinearMap.toMatrix_apply, hxy', map_zsmul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, Matrix.of_apply]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  have key := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix x' (Pi.basisFun ℤ rows)
    y' (Pi.basisFun ℤ cols) V
  have hstd : LinearMap.toMatrix (Pi.basisFun ℤ rows) (Pi.basisFun ℤ cols) V =
      (inclMat m t).transpose := by
    ext c r
    rw [LinearMap.toMatrix_apply]
    simp only [Pi.basisFun_repr, Pi.basisFun_apply, V]
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]; rfl
  rw [hstd, hmat] at key
  set A := y'.toMatrix ⇑(Pi.basisFun ℤ cols)
  set B := (Pi.basisFun ℤ rows).toMatrix ⇑x'
  refine ⟨B.transpose, A.transpose, φ', lab', ?_, ?_, fun a => hlab _, ?_, fun i hi => ?_⟩
  · rw [Matrix.det_transpose]
    exact Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip _ _)
  · rw [Matrix.det_transpose]
    exact Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip _ _)
  · have := congrArg Matrix.transpose key
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at this
    rw [this]
    ext a c
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    exact if_congr Iff.rfl rfl rfl
  · rw [← hcard i hi]
    exact Fintype.card_congr (eι.symm.subtypeEquiv fun r => Iff.rfl)

end ColouredSand.NumberOfFactors
