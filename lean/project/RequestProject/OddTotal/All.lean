module

public import RequestProject.OddTotal.Unit
public import RequestProject.OddTotal.Block
public import RequestProject.OddTotal.Tensor
public import RequestProject.OddTotal.Uniqueness
public import RequestProject.OddTotal.Exponents
public import RequestProject.OddTotal.Sylow

/-!
# `CSI19_theorem_TOTAL.md` — Theorem TOTAL: `Syl_p K(H(d, q))` for every odd prime `p ∣ q` and
# every `d` (namespace `ColouredSand.OddTwist`, every new name prefixed `oddTotal`)

CSG7 Part S without the bound on `d`: CSG5's tilting lattices, `LP p m` and Lemma 8 are replaced
by CSI6's dance lattices `danceL p λ`, the list `LL p m` and CSI18's closed form (Y2) of `Y_p`.

Reused, not redefined: CSG6 `BlockOp.opT`, `cokT`, `K2`, `K3a`, `K3b`, `dsumTheta`, `two_mul_half`;
CSG7 `ThmG.T2`, `gTorList`, `ExpGrp`, `expCons`, `expAppend`, `expReplicate`, `expSingle`,
`expOfFn`, `expFlatMap`, `expPerm`, `expCast`, `cancelFree`, `L2_pos` (and, as in CSG7 `S1`, `S2`:
`TheoremB.sandpile`, `Corollaries.corollary1_whole`, `sylTorsXq_equiv`, `ThmH.freeTorsionEquiv`,
`ThmH.Psi`, `ThmH.piProdAddEquiv`, `ThmH.card_sigma_free`); CSI6 `danceL`, `VdotL`, `LL`,
`tpow_danceL` (R3), `le_of_mem_LL`; CSI9 `flL`, `Dop`, `wtForm_danceL` (the floors behind (G3));
CSI10 `sigmaOp`, `Yp`, `Zq`, `Sp`, `digitL`, `kTop`, `Iset`; CSI18 `oddSmithK`, `oddSmithC`,
`oddSmithYhat`, `oddSmithYhatSharp`, `oddSmith_Y2_pos`, `oddSmith_Y2_zero`,
`oddSmith_Y2_zero_empty`; `Blocks.padicQuotEquiv` (`ℤ_[p] ⧸ p^a ≃+ ℤ/p^a`).

## Encodings

* `p` is a prime (`[Fact p.Prime]`) with `hp2 : p ≠ 2`; `e = v_p(q)` is `padicValNat p q`;
  `p ∣ q` is `1 ≤ padicValNat p q`.
* The cokernel of an endomorphism `f` of `N` is `N ⧸ LinearMap.range f`; `cokT p M m q c` is that
  of CSG6's `opT p M m q c = F^{(1)} + q (c + (m − H)/2)`, and `Y_p(λ, i, e)` is CSI10's
  `Yp p λ i e` (cokernel of `σ = sigmaOp p λ e i`).
* `K(H(d,q)) = TheoremB.sandpile d q`, `Syl_p G = AddCommGroup.primaryComponent G p`, "`≅`" of
  abelian groups is `≃+`, of `ℤ_[p]`-modules `≃ₗ[ℤ_[p]]`.  Direct sums with multiplicities are
  products over `σ : Σ j : Fin (d+1), Fin (C(d,j)(q−2)^j)` and over the positions `t` of
  `LL p (d − j)` (`λ_t = (LL p (d − j)).get t`), as in CSG7.
* A list `L` of exponents encodes `⊕_{a ∈ L} ℤ/p^a` (`ExpGrp p L`).  `oddTotalTotList p q c m` is
  the file's `totList`: the flatMap over `λ ∈ LL p m` of the exponent list of
  `Y_p(λ, c + (m − λ)/2, e)` (the `S_p(λ)` exponents, then `k + C + ŷ` for `i ≥ 1` or
  `k + eK + ŷ^♯` for `i = 0`), with the entries `0` (trivial factors `ℤ/p^0`) removed.

## Contents (main theorems)

* **Part U** (`Unit.lean`): **(U1)** `oddTotal_U1` (convention: the diagonal map
  `oddTotalDiag`, `δ_i ↦ u^{−(wt i / 2)} δ_i`).
* **Part B** (`Block.lean`): `oddTotal_opT_eq_sigmaOp` (the operators are equal) and **(B1)**
  `oddTotal_B1`.
* **Part T** (`Tensor.lean`): **(T1)** `oddTotal_T1`; with `oddTotal_mem_LL` (`λ ∈ LL p m` gives
  `λ ≤ m`, `λ ≡ m (mod 2)`) and `oddTotal_cokT_tpow`.
* **Part S** (`Sylow.lean`): **(S1)** `oddTotal_S1`; **(S2)** `oddTotal_S2` with
  `oddTotalTotList`; **(S3)** `oddTotal_S3` and its consequence `oddTotal_S3_S2`; the factor forms
  `oddTotal_factor` (as CSG7 `T1`) and `oddTotal_factor_tors` (as CSG7 `T2`), with no bound on `m`.
* Auxiliary: `Exponents.lean` (`oddTotalSpList`, `oddTotalCList`, `oddTotalYList`,
  `oddTotal_Yp_split`), `Uniqueness.lean` (`oddTotal_perm_of_expGrp`: uniqueness of the
  exponents of a finite abelian `p`-group).
-/
