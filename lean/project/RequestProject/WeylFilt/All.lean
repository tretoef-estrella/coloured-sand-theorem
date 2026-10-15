module

public import RequestProject.WeylFilt.Basic
public import RequestProject.WeylFilt.Maps
public import RequestProject.WeylFilt.Coord
public import RequestProject.WeylFilt.Comm
public import RequestProject.WeylFilt.PartM
public import RequestProject.WeylFilt.PartS

/-!
# `C19_weyl_filtrations_of_V_tensor.md`: the Weyl filtrations of `V ⊗ Δ_A(m)` and `V ⊗ ∇_A(m)`

Index of the formalization (namespace `WeylFilt`). From C18 (namespace `DPLattice`) it reuses
`DPLattice`, `IsDP`, `H`, `Hom`, `one`, `V`, `tensorV`, `bvec`, `delta`, `nabla`, `T5_delta_one`,
`T5_nabla_one` (and C18's auxiliary `slice`, `tensorFd`, `tensorEd`, `pred`, `deltaF`, `deltaE`,
`nablaF`, `nablaE`, `weylWt`, `Hop`, `delta_Fd_single`); nothing is redefined. Everything is over an
arbitrary commutative ring `A`.

## Encodings

* **Lattices** (C18): `delta A l = Δ_A(l)` and `nabla A l = ∇_A(l)` have basis `Fin (l + 1)`; the
  basis vector `e_r` (resp. `w_r`) is `Pi.single r 1`. `V ⊗ M` is C18's `tensorV M` (the factor
  `V` first), with basis `Fin 2 × M.ι`; `b_e m` is `bvec e m`. The parameters `m + 1` and `m − 1`
  of the file are `m + 1` and the truncated `m - 1 : ℕ` (all statements involving `m − 1` assume
  `m ≥ 1`).
* **Out-of-range basis vectors** (Setting): `ev l k` (`k : ℤ`) is `e_k` / `w_k` if `0 ≤ k ≤ l` and
  `0` otherwise.
* **Morphisms** (Setting): C18's `Hom M N`; `Hom.id M`, `Hom.comp g f` (`Basic.lean`).
* **Short exact sequence** (Setting): `ShortExact f g` — `f.toLin` injective, `g.toLin` surjective,
  `LinearMap.range f.toLin = LinearMap.ker g.toLin` (`Basic.lean`).
* **The four maps** (`Maps.lean`), defined on basis vectors by `Basis.constr` exactly as in the file:
  `fDeltaLin m : Δ_A(m+1) → V ⊗ Δ_A(m)` (`e'_R ↦ b_0 e_R + b_1 e_{R−1}`),
  `gDeltaLin m : V ⊗ Δ_A(m) → Δ_A(m−1)` (`b_1 e_s ↦ e''_s`, `b_0 e_R ↦ −e''_{R−1}`; the file's case
  list is `gDeltaLin_cases`), `fNablaLin m : ∇_A(m−1) → V ⊗ ∇_A(m)` (`w''_r ↦ b_0 w_{r+1} − b_1 w_r`),
  `gNablaLin m : V ⊗ ∇_A(m) → ∇_A(m+1)` (`b_0 w_r ↦ w'_r`, `b_1 w_r ↦ w'_{r+1}`). The basis formulas
  are the theorems `fDeltaLin_single`, `gDeltaLin_single`, `fNablaLin_single`, `gNablaLin_single`.
  The corresponding morphisms are `fDelta A m`, `gDelta A m hm`, `fNabla A m hm`, `gNabla A m`
  (`PartM.lean`).
* **Isomorphism** (S4): morphisms both ways whose composites are `Hom.id`.

## Results

* **Part M** (`PartM.lean`): (M1) `M1_fDelta`, `M1_gDelta`, `M1_fNabla`, `M1_gNabla`; (M2) `M2`.
* **Part S** (`PartS.lean`): (S1) `S1`; (S2) `S2`; (S3) `S3`; (S4) `S4_delta`, `S4_nabla`, `S4`.

## Generality and hypotheses

* (M1) for `fΔ`, `g∇` and (S3) hold for every `m` (the file states them for `m ≥ 1`); (M1) for `gΔ`,
  `f∇` and (S1), (S2) assume `m ≥ 1`, which is needed there (`m − 1` is the parameter of a lattice).
  No hypothesis is unused.
* (S4) is realised by `fΔ` and `g∇` for `m = 0` (both bijective) composed with C18 (T5)
  `Δ_A(1) = V = ∇_A(1)`.
-/
