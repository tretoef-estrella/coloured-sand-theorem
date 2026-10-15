module

public import RequestProject.OddDance.Additive
public import RequestProject.OddDance.Rule
public import RequestProject.OddDance.Lattice
public import RequestProject.OddDance.Tensor
public import RequestProject.OddDance.Agree
public import RequestProject.OddDance.K3

/-!
# `CSI6_the_dance_lattices.md` — the dance lattices `L(λ)` and
# `V^{⊗m} ⊗ ℤ_p ≅ ⊕ L(λ)^{n_λ(m)}` for every `m` (all parts)

Namespace `ColouredSand.OddTwist`. No existing file is modified; no citation is used: every
isomorphism is built from the DP-lattice framework (C18–C31), CSG3–CSG5 (`TiltP`, `TiltRules`,
`TiltDec`) and the odd-dance files CSI1–CSI5.

Setting: `p` is a prime (`[Fact p.Prime]`), odd where needed (`p ≠ 2`, or `3 ≤ p` for the purely
combinatorial statements); the ring is `ℤ_[p]`; «`X ≅ Y`» is `Nonempty (Doubling.Iso X Y)`;
`dsum` is C22's `Lemma35.dsum`, `dsumList` is C30's `Step36.dsumList`, `V ⊗ X` is
`Tensor2.tensor (V ℤ_[p]) X`, `V^{⊗m}` is C29's `Filt.tpow ℤ_[p] m`; `psi p N r h1 h2` is CSI3's
`Ψ_r(N)` (the file's `psi p r N`).

Main results (exact Lean names):
* **Part A** (`Additive.lean`): (A1) `A1_additive` (with `twistDsumIso`, `psiDsumIso`),
  (A2) `A2_iso` (with CSI1's `Iso.twist` and the new `Iso.psi`), (A3) `A3_dsumList` (with
  `twistDsumListIso`, `psiDsumListIso`).
* **Part L** (`Lattice.lean`, `Rule.lean`): (L1) `danceL` with the defining equations
  `danceL_lt`, `danceL_d0_zero`, `danceL_d0_pos`; (L2) `card_danceL` (recursive form, `rankL`)
  and `card_danceL_digits` (digit formula; also `rankL_digits`, `leading_digit_ne_zero`).
* **Part R** (`Rule.lean`, `Tensor.lean`): (R1) `VdotL` with `VdotL_zero`, `VdotL_small`,
  `VdotL_d0_zero`, `VdotL_d0_one`, `VdotL_d0_mid`, `VdotL_d0_top`; (R2) `tensor_danceL`;
  (R3) `LL`, `nL`, `tpow_danceL` and the multiplicity form `tpow_danceL_mult`.
* **Part K** (`Agree.lean`, `K3.lean`): (K1) `K1_perm`; (K2) `K2_perm`, `K2_count`;
  (K3, optional) only for simple weights: `K3_simple`.
-/
