module

public import Mathlib

/-!
# Cokernels from a Smith form (generic linear algebra for Part Y of
`CSI18_theorem_4_4_smith_form_of_Mp.md`)

Over a commutative ring `R`, with matrices acting on column vectors (`Matrix.mulVecLin`, the
convention of CSI10's `Cmod`):

* `oddSmithDiagQuot d` — `(ι → R) ⧸ range (diagonal d) ≃ Π i, R ⧸ (d i)` (`Submodule.quotientPi`);
* `oddSmithUnitQuot` — multiplying a matrix on both sides by matrices with unit determinant does
  not change the cokernel;
* `oddSmithReindexQuot` — reindexing rows and columns simultaneously along `e : ι ≃ κ` does not
  change the cokernel;
* `oddSmithSnocEquiv` — `Π_{i : Fin (n+1)} M i ≃ M (last n) × Π_{i : Fin n} M i.castSucc`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Matrix

variable {R : Type*} [CommRing R]

/-- The range of a diagonal matrix (Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
lemma oddSmith_range_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → R) :
    LinearMap.range (diagonal d).mulVecLin =
      Submodule.pi Set.univ (fun i => (Ideal.span {d i} : Submodule R R)) := by
  ext v
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi,
    Set.mem_univ, true_implies, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨w, rfl⟩ i
    rw [mulVec_diagonal]
    exact Dvd.intro _ rfl
  · intro h
    choose w hw using h
    exact ⟨w, funext fun i => by rw [mulVec_diagonal]; exact (hw i).symm⟩

/-- `(ι → R) ⧸ range (diagonal d) ≃ Π i, R ⧸ (d i)` (Part Y of
`CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
def oddSmithDiagQuot {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → R) :
    ((ι → R) ⧸ LinearMap.range (diagonal d).mulVecLin) ≃ₗ[R]
      ((i : ι) → R ⧸ Ideal.span {d i}) :=
  (Submodule.quotEquivOfEq _ _ (oddSmith_range_diagonal d)).trans (Submodule.quotientPi _)

/-- Multiplying by matrices of unit determinant does not change the cokernel (Part Y of
`CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
def oddSmithUnitQuot {ι : Type*} [Fintype ι] [DecidableEq ι] (A P Q : Matrix ι ι R)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    ((ι → R) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[R]
      ((ι → R) ⧸ LinearMap.range (P * A * Q).mulVecLin) :=
  Submodule.Quotient.equiv _ _ (P.toLinearEquiv' (P.invertibleOfIsUnitDet hP)) (by
    have hQs : LinearMap.range Q.mulVecLin = ⊤ := by
      have h := (Q.toLinearEquiv' (Q.invertibleOfIsUnitDet hQ)).range
      rw [Matrix.toLinearEquiv'_apply] at h
      exact h
    rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hQs,
      LinearMap.range_comp]
    rfl)

/-- Simultaneous reindexing does not change the cokernel (Part Y of
`CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
def oddSmithReindexQuot {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (M : Matrix κ κ R) :
    ((κ → R) ⧸ LinearMap.range M.mulVecLin) ≃ₗ[R]
      ((ι → R) ⧸ LinearMap.range (M.submatrix e e).mulVecLin) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.funCongrLeft R R e) (by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨w ∘ e, ?_⟩
      rw [submatrix_mulVec_equiv]
      ext i
      have : (w ∘ e) ∘ e.symm = w := by ext; simp
      simp [LinearEquiv.funCongrLeft_apply, this]
    · rintro ⟨w, rfl⟩
      refine ⟨_, ⟨w ∘ e.symm, rfl⟩, ?_⟩
      rw [submatrix_mulVec_equiv]
      ext i
      simp [LinearEquiv.funCongrLeft_apply])

/-- `Π_{i : Fin (n+1)} M i ≃ M (last n) × Π_{i : Fin n} M i.castSucc` (Part Y of
`CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
def oddSmithSnocEquiv {n : ℕ} (M : Fin (n + 1) → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] :
    ((i : Fin (n + 1)) → M i) ≃ₗ[R] (M (Fin.last n) × ((i : Fin n) → M i.castSucc)) where
  toFun f := (f (Fin.last n), fun i => f i.castSucc)
  invFun g := Fin.snoc g.2 g.1
  map_add' f g := rfl
  map_smul' c f := rfl
  left_inv f := Fin.snoc_init_self f
  right_inv g := by
    ext
    · simp
    · simp

end ColouredSand.OddTwist
