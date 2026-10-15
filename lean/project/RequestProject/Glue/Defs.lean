module

public import RequestProject.Blocks.Defs

/-!
# The glued lattice: definitions (CSG2, §0 "Setting")

This file contains the definitions of §0 of `CSG2_lemma_7_the_glue.md`.  They are stated for
arbitrary natural numbers `L` (for `λ`) and `M` (for `μ`) and a shift `r`; the statements of §1
use `L = lam p r a`, `M = mu p r a` (from `RequestProject/Blocks/Defs.lean`).

## Encoding

* `Idx L M = Fin (L + 1) ⊕ Fin (M + 1)` and `V p L M = Idx L M → ℚ_[p]`; `inl i` is the
  coordinate of `ℓ_i` and `inr j` that of `s_j`.
* `ell p L M i = ℓ_i = Pi.single (inl i) 1` and `ess p L M j = s_j = Pi.single (inr j) 1`.
  They are indexed by natural numbers, and are `0` when the index is out of range (`i > L`,
  resp. `j > M`).  This is the convention "`… • ℓ (i + t)` if `i + t ≤ λ`, else `0`" of §0.
* The divided powers `Fop p L M t = F t`, `Eop p L M t = E t` and the weight projections
  `Pop p L M w = P w` are `Matrix.mulVecLin` of the matrices `Fmat`, `Emat`, `Pmat`, whose entries
  are written out: the column of `ℓ_i` (resp. `s_j`) is the image of `ℓ_i` (resp. `s_j`):
  - `Fmat t (inl i') (inl i) = C(i + t, t)` if `i' = i + t`, `Fmat t (inr j') (inr j) = C(j + t, t)`
    if `j' = j + t`, all other entries `0`;
  - `Emat t (inl i') (inl i) = C(λ − i + t, t)` if `i' + t = i`,
    `Emat t (inr j') (inr j) = C(μ − j + t, t)` if `j' + t = j`, all other entries `0`;
  - `Pmat w` is the diagonal matrix with entry `1` at the indices of weight `w`, where
    `wt (inl i) = λ − 2i` and `wt (inr j) = μ − 2j` (in `ℤ`).
* `V` is a `ℤ_[p]`-module by restriction of scalars (Mathlib's `Algebra ℤ_[p] ℚ_[p]`), and
  lattices are `Submodule ℤ_[p] (V p L M)`.  `IsStable Λ` says that `F t`, `E t` (`t ≥ 1`) and
  `P w` (all `w : ℤ`) map `Λ` into `Λ`.
* `stilde p L M r x j = s̃ x j = s_j + (x C(j + r, j)) • ℓ_{j + r}` for `j ≤ M`
  (and `0` for `j > M`).
* `Lx p L M r x = span ℤ_[p] ({ℓ_i} ∪ {s̃ x j})`, `Dlam = span ℤ_[p] {ℓ_i}`,
  `Dmu = span ℤ_[p] {s_j}`.
* For (G5): `Hop p q c k L M r = Hq` (diagonal, `Hq ℓ_i = N_i ℓ_i`, `Hq s_j = N_{j+r} s_j` with
  `N = Nt p q c k` from `Blocks`), `Oop = Hq + F 1`, and `xzero p r a = x₀ = p^(−ν)`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Glue

open ColouredSand.Blocks

variable (p : ℕ) [Fact p.Prime] (L M : ℕ)

/-- The index set `Fin (λ + 1) ⊕ Fin (μ + 1)` (`inl i ↔ ℓ_i`, `inr j ↔ s_j`). -/
abbrev Idx : Type := Fin (L + 1) ⊕ Fin (M + 1)

/-- The space `V = (Fin (λ + 1) ⊕ Fin (μ + 1)) → ℚ_[p]` (§0). -/
abbrev V : Type := Idx L M → ℚ_[p]

/-- `ℓ_i = Pi.single (inl i) 1` (and `0` if `i > λ`). -/
noncomputable def ell (i : ℕ) : V p L M :=
  if h : i ≤ L then Pi.single (Sum.inl ⟨i, Nat.lt_succ_of_le h⟩) 1 else 0

/-- `s_j = Pi.single (inr j) 1` (and `0` if `j > μ`). -/
noncomputable def ess (j : ℕ) : V p L M :=
  if h : j ≤ M then Pi.single (Sum.inr ⟨j, Nat.lt_succ_of_le h⟩) 1 else 0

/-- The weight of a basis vector: `wt ℓ_i = λ − 2i`, `wt s_j = μ − 2j`. -/
def wt : Idx L M → ℤ
  | .inl i => (L : ℤ) - 2 * (i : ℤ)
  | .inr j => (M : ℤ) - 2 * (j : ℤ)

/-- The matrix of the divided power `F t = f^{(t)}`. -/
noncomputable def Fmat (t : ℕ) : Matrix (Idx L M) (Idx L M) ℚ_[p] :=
  Matrix.of fun y z => match y, z with
    | .inl i', .inl i => if (i' : ℕ) = i + t then (((i : ℕ) + t).choose t : ℚ_[p]) else 0
    | .inr j', .inr j => if (j' : ℕ) = j + t then (((j : ℕ) + t).choose t : ℚ_[p]) else 0
    | _, _ => 0

/-- The matrix of the divided power `E t = e^{(t)}`. -/
noncomputable def Emat (t : ℕ) : Matrix (Idx L M) (Idx L M) ℚ_[p] :=
  Matrix.of fun y z => match y, z with
    | .inl i', .inl i => if (i' : ℕ) + t = i then ((L - i + t).choose t : ℚ_[p]) else 0
    | .inr j', .inr j => if (j' : ℕ) + t = j then ((M - j + t).choose t : ℚ_[p]) else 0
    | _, _ => 0

/-- The matrix of the weight projection `P w`. -/
noncomputable def Pmat (w : ℤ) : Matrix (Idx L M) (Idx L M) ℚ_[p] :=
  Matrix.of fun y z => if y = z ∧ wt L M z = w then 1 else 0

/-- The divided power `F t : V → V`. -/
noncomputable def Fop (t : ℕ) : V p L M →ₗ[ℚ_[p]] V p L M := Matrix.mulVecLin (Fmat p L M t)

/-- The divided power `E t : V → V`. -/
noncomputable def Eop (t : ℕ) : V p L M →ₗ[ℚ_[p]] V p L M := Matrix.mulVecLin (Emat p L M t)

/-- The weight projection `P w : V → V`. -/
noncomputable def Pop (w : ℤ) : V p L M →ₗ[ℚ_[p]] V p L M := Matrix.mulVecLin (Pmat p L M w)

/-- A `ℤ_[p]`-submodule of `V` is **stable** if `F t`, `E t` (`t ≥ 1`) and `P w` (all `w`)
map it into itself. -/
def IsStable (Λ : Submodule ℤ_[p] (V p L M)) : Prop :=
  (∀ t : ℕ, 1 ≤ t → ∀ v ∈ Λ, Fop p L M t v ∈ Λ ∧ Eop p L M t v ∈ Λ) ∧
    ∀ w : ℤ, ∀ v ∈ Λ, Pop p L M w v ∈ Λ

/-- `s̃ x j = s_j + (x C(j + r, j)) • ℓ_{j + r}` (for `j ≤ μ`; `0` for `j > μ`). -/
noncomputable def stilde (r : ℕ) (x : ℚ_[p]) (j : ℕ) : V p L M :=
  if j ≤ M then ess p L M j + (x * ((j + r).choose j : ℚ_[p])) • ell p L M (j + r) else 0

/-- **The glued lattice** `Lx x = span ℤ_[p] ({ℓ_i} ∪ {s̃ x j})`. -/
noncomputable def Lx (r : ℕ) (x : ℚ_[p]) : Submodule ℤ_[p] (V p L M) :=
  Submodule.span ℤ_[p]
    (Set.range (fun i : Fin (L + 1) => ell p L M i) ∪
      Set.range (fun j : Fin (M + 1) => stilde p L M r x j))

/-- The Weyl lattice `Dλ = span ℤ_[p] {ℓ_i}`. -/
noncomputable def Dlam : Submodule ℤ_[p] (V p L M) :=
  Submodule.span ℤ_[p] (Set.range (fun i : Fin (L + 1) => ell p L M i))

/-- The Weyl lattice `Dμ = span ℤ_[p] {s_j}`. -/
noncomputable def Dmu : Submodule ℤ_[p] (V p L M) :=
  Submodule.span ℤ_[p] (Set.range (fun j : Fin (M + 1) => ess p L M j))

/-- `x₀ = p^(−ν)` (G5). -/
noncomputable def xzero (r a : ℕ) : ℚ_[p] := (p : ℚ_[p]) ^ (-(nu p r a : ℤ))

variable (q c k : ℕ)

/-- The diagonal matrix of `Hq`: `Hq ℓ_i = N_i ℓ_i`, `Hq s_j = N_{j+r} s_j` (G5). -/
noncomputable def Hmat (r : ℕ) : Matrix (Idx L M) (Idx L M) ℚ_[p] :=
  Matrix.diagonal fun y => match y with
    | .inl i => ((Nt p q c k i : ℤ_[p]) : ℚ_[p])
    | .inr j => ((Nt p q c k ((j : ℕ) + r) : ℤ_[p]) : ℚ_[p])

/-- `Hq : V → V` (the operator `q (c + H)` on the block at levels `k, …, k + λ`). -/
noncomputable def Hop (r : ℕ) : V p L M →ₗ[ℚ_[p]] V p L M := Matrix.mulVecLin (Hmat p L M q c k r)

/-- `O = Hq + F 1` (the operator `q (c + H) + U` on the block) (G5). -/
noncomputable def Oop (r : ℕ) : V p L M →ₗ[ℚ_[p]] V p L M := Hop p L M q c k r + Fop p L M 1

end ColouredSand.Glue
