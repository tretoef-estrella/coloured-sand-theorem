module

public import RequestProject.OddTwistModP.PartT
public import RequestProject.OddTwistModP.PartS
public import RequestProject.OddTwistModP.PartC1
public import RequestProject.OddTwistModP.PartC2

/-!
# `CSI2_reduction_mod_p.md`: index (namespace `ColouredSand.OddTwist`)

Reduction modulo `p` of the odd twist, `Φ_p(N) ⊗ 𝔽_p ≅ St ⊗ (N ⊗ 𝔽_p)^{[1]}` (Proposition 1.2 (c)
of «the odd dance»), following C21 (`RequestProject/Twist/`) with `2` replaced by a prime `p`.

Reused without redefinition: C18 `DPLattice`, `IsDP`, `H`, `Hom`, `delta` (with
`delta_Fd_single`, `delta_Ed_single`); C19 `WeylFilt.Hom.id`, `WeylFilt.Hom.comp`; C20
`Doubling.Iso`, `Doubling.Iso.ofInverse`; C21 `Twist.bc`, `Twist.baseChange`, `Twist.bc_aeval`,
`Twist.bc_apply_comp`, …; C23 `Tensor2.tensor`, `Tensor2.tprod`, `Tensor2.tensor_Fd_tprod`,
`Tensor2.tensor_Ed_tprod`; CSI1 `qc`, `bv`, `twWt`, `twist`, `twFd`, `twEd`, `Sset`, `PP`,
`pFactor`, `twFd_single`, `twEd_single`, `isUnit_ordCompl_factorial`.

## Encodings

* **Setting**: `p : ℕ` with `[Fact p.Prime]`; `B` a commutative ring with `hp : (p : B) = 0`;
  `φ : ℤ_[p] →+* B` any ring homomorphism. The hypothesis `p ≠ 2` is never used (all results hold
  for every prime `p`, more general than the file). Integers prime to `p` are units of `B`:
  `isUnit_intCast_of_coprime`, `isUnit_natCast_of_coprime'`, `isUnit_factorial`.
* **Binomials** with integer top: `Ring.choose x k : ℤ`, cast to `B`.
* **Part T** (`PartT.lean`): `frobOpP p F r = F (r / p)` if `p ∣ r`, else `0`;
  `frobP hp M = M^{[1]}` (basis `M.ι`, weights `p · M.wt`); `frobPHom hp f` (same linear map).
* **Part S** (`PartS.lean`): `St φ = Twist.baseChange φ (delta ℤ_[p] (p − 1))`, basis
  `Fin (p − 1 + 1)`, `e_s = Pi.single s 1`. `n!'` is `ordCompl[p] n!`.
* **Part C** (`PartC1.lean`, `PartC2.lean`): `Φ_p(N) ⊗ B` is `Twist.baseChange φ (twist p N)`
  (basis `Fin p × N.ι`), `b_j n = bv p j n`, `N̄ = Twist.baseChange φ N`.
  `T = Tensor2.tensor (St φ) (frobP hp (Twist.baseChange φ N))` (basis `Fin (p − 1 + 1) × N.ι`,
  `e_j ⊗ n = Tensor2.tprod (Pi.single j 1) n`), `Fin (p − 1 + 1)` identified with `Fin p` by
  `Fin.cast`. `D = Dmap B p N.ι`, `D⁻¹ = Dinv B p N.ι`. Divisions by the units `t!`, `(j − t)!`
  are stated multiplicatively.

## Main results

* (T0) `T0` (with `choose_mul_of_not_dvd`); (T1) `T1`, `frobP`, `frobP_data`, `H_frobP`;
  (T2) `T2`, `frobPHom`.
* (S1) `oddModP_S1`, `St`.
* (C0) `C0`; (C1) `oddModP_C1` (= `C1_F` and `C1_E`); (C2) `oddModP_C2`, `prop12Iso`, `Dmap_bv`;
  (C3) `oddModP_C3`, `C3_hyp`.
-/
