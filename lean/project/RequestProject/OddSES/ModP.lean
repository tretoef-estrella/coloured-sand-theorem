module

public import RequestProject.OddSES.Casimir

/-!
# `CSI4_the_short_exact_sequences.md`: congruences modulo `p` (used in Parts C and S)

Encodings:

* `pSub X` is the submodule `p • X` of a `ℤ_[p]`-module `X` (the range of `x ↦ p • x`); for
  `X = ι → ℤ_[p]` this is the `p • (ι → ℤ_[p])` of the file. CSI3's `ModP p x y` ("`x ≡ y`
  modulo `p`") is `x − y ∈ pSub X` (`modP_iff`).
* "`T = p • R` for some endomorphism `R`" is `∃ R, T = (p : ℤ_[p]) • R`; on a lattice with a
  finite basis it is equivalent to "`T δ_i ∈ p • (ι → ℤ_[p])` for every basis vector `δ_i`"
  (`exists_eq_p_smul`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- The submodule `p • X` of a `ℤ_[p]`-module `X`. -/
def pSub (X : Type*) [AddCommGroup X] [Module ℤ_[p] X] : Submodule ℤ_[p] X :=
  LinearMap.range ((p : ℤ_[p]) • LinearMap.id : X →ₗ[ℤ_[p]] X)

variable {X : Type*} [AddCommGroup X] [Module ℤ_[p] X]

lemma mem_pSub {x : X} : x ∈ pSub p X ↔ ∃ z, x = (p : ℤ_[p]) • z := by
  constructor
  · rintro ⟨z, rfl⟩; exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩; exact ⟨z, rfl⟩

lemma p_smul_mem_pSub (z : X) : (p : ℤ_[p]) • z ∈ pSub p X := mem_pSub.2 ⟨z, rfl⟩

lemma modP_iff {x y : X} : ModP p x y ↔ x - y ∈ pSub p X := by
  rw [mem_pSub]; rfl

lemma ModP.mem_pSub {x : X} (h : ModP p x 0) : x ∈ pSub p X := by
  have := modP_iff.1 h; rwa [sub_zero] at this

/-- If `x ≡ y` modulo `p` and `y ∈ W ⊔ p • X`, then `x ∈ W ⊔ p • X`. -/
lemma ModP.mem_sup {W : Submodule ℤ_[p] X} {x y : X} (h : ModP p x y)
    (hy : y ∈ W ⊔ pSub p X) : x ∈ W ⊔ pSub p X := by
  have hx : x = y + (x - y) := by abel
  rw [hx]
  exact Submodule.add_mem _ hy (Submodule.mem_sup_right (modP_iff.1 h))

/-- A linear map out of `ι → ℤ_[p]` all of whose values on basis vectors lie in `p • X` is
`p • R` for some linear map `R`. -/
lemma exists_eq_p_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (T : (ι → ℤ_[p]) →ₗ[ℤ_[p]] X)
    (h : ∀ i, T (Pi.single i 1) ∈ pSub p X) : ∃ R : (ι → ℤ_[p]) →ₗ[ℤ_[p]] X,
      T = (p : ℤ_[p]) • R := by
  choose z hz using fun i => mem_pSub.1 (h i)
  refine ⟨(Pi.basisFun ℤ_[p] ι).constr ℤ_[p] z, ext_single fun i => ?_⟩
  rw [LinearMap.smul_apply, ← Pi.basisFun_apply ℤ_[p], Module.Basis.constr_basis,
    Pi.basisFun_apply, hz i]

/-- Conversely, `p • R` maps everything into `p • X`. -/
lemma p_smul_apply_mem {Y : Type*} [AddCommGroup Y] [Module ℤ_[p] Y] (R : Y →ₗ[ℤ_[p]] X) (y : Y) :
    ((p : ℤ_[p]) • R) y ∈ pSub p X := p_smul_mem_pSub _

end ColouredSand.OddTwist
