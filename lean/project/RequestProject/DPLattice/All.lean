module

public import RequestProject.DPLattice.Basic
public import RequestProject.DPLattice.Tensor
public import RequestProject.DPLattice.Weyl
public import RequestProject.DPLattice.PartT
public import RequestProject.DPLattice.Dictionary
public import RequestProject.DPLattice.Corollary

/-!
# `C18_divided_power_lattices_and_the_dictionary.md`: divided-power lattices and the dictionary

Index of the formalization (namespace `DPLattice`). From C17 it reuses `CubeLaplacian.G`,
`CubeLaplacian.e`, `CubeLaplacian.lap`, `CubeLaplacian.K`, `CubeLaplacian.Syl2` and
`CubeLaplacian.D2`; nothing else of C1–C17 is used.

## Encodings

* **DP-lattice** (`Basic.lean`): `M : DPLattice A` has a basis `M.ι : Type` with `Fintype` and
  `DecidableEq`, a weight `M.wt : M.ι → ℤ`, and `M.Fd M.Ed : ℕ → Module.End A (M.ι → A)`
  (`F^{(r)}`, `E^{(s)}`); basis vectors are `δ_i = Pi.single i 1`. The field `M.isDP : IsDP …`
  bundles (W) (`W_F`, `W_E`: coordinates of `F^{(r)} δ_i` outside weight `wt i − 2r` vanish, resp.
  of `E^{(r)} δ_i` outside `wt i + 2r`), (P0) (`P0_F`, `P0_E`), (P1) (`P1_F`, `P1_E`, with
  `C(a + b, a) = Ring.choose (a + b) a` cast to `A`) and (K) (`K`, with `C(wt i + s − r, j)` the
  generalized binomial `Ring.choose` on `ℤ`, cast to `A`). `H M` is the diagonal operator
  `(H f) i = wt i * f i`. Morphisms are `Hom M N`; "equal data under a bijection" is `DataEquiv`.
* **`𝟙`** (`one A`, `Tensor.lean`): `ι = Unit`, weight `0`, `F^{(r)} = E^{(r)} = if r = 0 then 1
  else 0`.
* **`V`** (`V A`, `PartT.lean`): `ι = Fin 2`, `wt = wtV` (`1, −1`), `F^{(1)}`, `E^{(1)}` given by
  their matrices, `F^{(0)} = E^{(0)} = 1`, `F^{(r)} = E^{(r)} = 0` for `r ≥ 2`.
* **`V ⊗ M`** (`tensorV M`, `Tensor.lean`): basis `Fin 2 × M.ι`, `wt (e, i) = wtV e + wt i`;
  `bvec e m` is `b_e m` (the vector with `m` in slot `e`), `slice e` reads slot `e`; the divided
  powers are the coproduct formulas (`tensorV_Fd_b0`, `tensorV_Fd_b1`, `tensorV_Ed_b1`,
  `tensorV_Ed_b0`, and the `r = 0` cases).
* **`V^{⊗n}`** (`tensorPow A n`): `V^{⊗0} = 𝟙`, `V^{⊗(n+1)} = V ⊗ V^{⊗n}`; the pure tensor with
  letters `b_1` on `S : Finset (Fin n)` is `Pi.single (pt A n S) 1` (`Dictionary.lean`); position
  `0` is the first factor.
* **Weyl lattices** (`Weyl.lean`): `delta A l = Δ_A(λ)`, `nabla A l = ∇_A(λ)` (`l = λ`), with
  `ι = Fin (λ + 1)`, `wt r = λ − 2r` and operators given by their matrices; the formulas of the
  file are `delta_Fd_single`, `delta_Ed_single`, `nabla_Fd_single`, `nabla_Ed_single`
  (`PartT.lean`). In these formulas `λ − r ≥ 0`, so the binomials are `Nat.choose`.
* **Dictionary** (`Dictionary.lean`): `Tn A n = F^{(1)} + n • id − H` on `V^{⊗n}`;
  `psi A n : (G n → A) ≃ₗ[A] V^{⊗n}` is `Ψ`.

## Where each statement is

* **Part T**: (T1) `T1` (+ the formulas `V_wt`, `V_Fd_one_b0`, …); (T2) `T2` (structure
  `tensorV`); (T3) `T3` (`tensorPow`); (T4) `T4` (+ `weyl_wt`, `delta_Fd_single`, …);
  (T5) `T5_delta_zero`, `T5_nabla_zero` (`DataEquiv … finOneEquivUnit`), `T5_delta_one`,
  `T5_nabla_one` (equalities `delta A 1 = V A`, `nabla A 1 = V A` of DP-lattices).
* **Part L**: (L1) `L1_F`, `L1_H`, and `pt_bijective`; (L2) `L2` (explicitly `psi_comm`).
* **Part C**: (C1) `C1` (explicit equivalence `C1equiv`); (C2) `C2`.

## Remarks

* All hypotheses are used. In (C1)/(C2) only `F^{(1)}` and `H` of the `M_j` enter the statement,
  as in the file; `[Fintype J]` and `[DecidableEq J]` are used to identify the quotient of the
  product with the product of the quotients.
* (T4) for `∇` is proved by induction on `λ` through the surjective intertwiner
  `V ⊗ ∇_A(λ) → ∇_A(λ+1)` (and (T2)); `Δ_A(λ)` is the transpose of `∇_A(λ)` with `F`, `E`
  exchanged (`IsDP.dual`).
-/
