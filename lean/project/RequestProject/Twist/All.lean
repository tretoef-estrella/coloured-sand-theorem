module

public import RequestProject.Twist.Basic
public import RequestProject.Twist.PartR
public import RequestProject.Twist.PartT
public import RequestProject.Twist.PartC
public import RequestProject.Twist.Prop31

/-!
# `C21_reduction_mod_2_and_the_twist.md`: index (namespace `Twist`)

Reused, not redefined: from C18 (`DPLattice`) `DPLattice`, `IsDP`, `H`, `Hom`, `V`, `tensorV`,
`bvec`, `slice` and `InWt` (with `Hop`, `tensorFd`, `tensorEd`, `tensorWt`, `pred`, `VFd`,
`VEd`); from C19 (`WeylFilt`) `Hom.id`, `Hom.comp`; from C20 (`Doubling`) `OddUnits`, `dfi`,
`piOp`, `phi`, `Iso` and the closed formulas `phiFd_even`, …, `phiEd_odd_b0`.

Encodings:
* **Vectors** over `B` are functions `ι → B`; `δ_i = Pi.single i 1`; the reduction of a vector
  `x : ι → A` is `⇑φ ∘ x`.
* **Base change of a linear map** (Part R): `bc φ f = Matrix.toLin' ((LinearMap.toMatrix' f).map φ)`
  for `f : (ι → A) →ₗ[A] (κ → A)`, so `f^φ (δ_i) j = φ (f (δ_i) j)` (`bc_single_apply`).
* **Base change of a DP-lattice** (Part R): `baseChange φ M` (basis `M.ι`, weights `M.wt`,
  `F^{(r)} = bc φ (M.Fd r)`, `E^{(r)} = bc φ (M.Ed r)`); of a morphism: `bcHom φ f`.
* **Frobenius twist** (Part T): `frob h2 M` for `h2 : (2 : B) = 0` (basis `M.ι`, weights
  `2 · M.wt`, `F^{(r)} = frobOp M.Fd r`, `E^{(r)} = frobOp M.Ed r`, where `frobOp F r` is
  `F (r/2)` for `r` even and `0` for `r` odd); of a morphism: `frobHom h2 f` (same linear map).
* **Isomorphism**: C20's `Doubling.Iso` (morphisms both ways whose `Hom.comp`s are `Hom.id`).
  The statements (R3) and (C2) also assert that both underlying linear maps are `LinearMap.id`.
* `Φ(N)` is `Doubling.phi N` (basis `Fin 2 × N.ι`, `b_e n = bvec e n`).

Results:
* Part R: `R0`, `R1` (and `baseChange`), `R2` (and `bcHom`), `R3`.
* Part T: `T0`, `T1` (and `frob`, `frob_data`, `H_frob`), `T2` (and `frobHom`).
* Part C: `C0`, `C1` (and the six `C1_…` lemmas), `C2` (and `prop31Iso`), `C3_hyp`, `C3`.

Hypotheses: Part R needs only commutative rings and a ring homomorphism. Part T needs only
`(2 : B) = 0` (used in (T0) and (T1); in (T2) it is only needed to form the twists). Part C:
`[IsDomain A] [CharZero A]` are needed to form `Doubling.phi N` (C20) and `[OddUnits A]` for
`φ(⅟(2s−1)!!) = 1`; the parts of (C0) not mentioning `dfi` hold without `OddUnits`. In (C0) the
oddness of `c_j` is proved for every `j`, not only `0 ≤ j ≤ s` (resp. `0 ≤ j ≤ s − 1`).
-/
