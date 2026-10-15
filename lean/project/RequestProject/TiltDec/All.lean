module

public import RequestProject.TiltDec.Rule
public import RequestProject.TiltDec.Weyl
public import RequestProject.TiltDec.Decomp

/-!
# `CSG5_the_induction.md` — the decomposition `V^{⊗n} ⊗ ℤ_p ≅ ⊕ T(λ)^{m_λ(n)}` for
# `n ≤ p² + p − 1`, and the multiplicities (T3) (namespace `ColouredSand.TiltDec`)

This is the odd-`p` analogue of the cube's C31 (`FamDec`) and follows it closely.

Reused, not redefined: `Filt.tpow`, `tpow_zero`, `tpow_succ` (C29); `Step36.dsumList`,
`dsumList_cons`, `dsumListSingletonIso`, `tensorVDsumListIso` (C30); `tensorVIso`, `dsumIso`
(C23); `Iso.refl` (C24); `Iso.trans`, `Iso.symm`, `Iso.ofDataEquiv` (C20); `T5_delta_zero`
(C18); `FamDec.P1`, `FamDec.P2`, `FamDec.perm_flatMap_replicate` (C31); `TiltP.Ttilt`,
`Ttilt_of_simple`, `Ttilt_of_not_simple`, `IsSimpleWt`, `rT`, `aT`, `T3`, `GlueHyp` (CSG3); the
CSG4 rules `S0`, `S1`, `S2`, `R1`, `R2`, `R3_pos`, `R3_zero`, `R4`; `lam`, `mu` (CSG0).

## Encodings

* A formal sum `Σ_λ c_λ [λ]` is a `List ℕ` with `c_λ` copies of `λ`, compared up to `List.Perm`.
* "`X ≅ Y`" is `Nonempty (Doubling.Iso X Y)`; `V^{⊗n} ⊗ ℤ_p` is `Filt.tpow ℤ_[p] n`; finite
  direct sums are `Step36.dsumList`.
* `p` prime with `p ≠ 2` is `[Fact p.Prime]`, `hp2 : p ≠ 2` in Part D; the purely combinatorial
  Parts M and W only assume `2 ≤ p` or `3 ≤ p` (more general; `3 ≤ p` holds for odd primes).
* `β n l` is the integer-valued `betaCG n l` (with `C(n, −1) = 0`); `l⁺` is encoded by the
  `Finset` `plusSet p n l` (at most one element, by the injectivity `W4_inj`); the rank of
  `Ttilt p λ` is `rankT p λ`, which equals `Fintype.card (Ttilt p λ).ι` (`card_Ttilt`).

## Contents

* `Rule.lean`, Part M: **(M1)** `VdotP` with the case equations `VdotP_zero`,
  `VdotP_simple_small`, `VdotP_simple_large`, `VdotP_r_one`, `VdotP_r_mid`, `VdotP_r_top_pos`,
  `VdotP_r_top_ext`; **(M2)** `LP`, `LP_zero`, `LP_succ`, `mP`; **(M3)** `M3`; the (M4)-type
  permutation `LP_perm_replicate`; and the arithmetic of `rT`, `aT`, `IsSimpleWt` used in (D1).
* `Weyl.lean`, Part W: **(W1)** `weylP`, `cgRule`, `CG`; **(W2)** `W2_rule`, `W2`; **(W3)**
  `betaCG`, `W3`; **(W4)** `W4_inj`, `plusSet`, `plusSet_subsingleton`, `W4`, `W4_of_plus`,
  `W4_of_no_plus`; **(W5)** `rankT`, `W5`.
* `Decomp.lean`, Part D: **(D1)** `D1`, **(D2)** `D2`, **(D3)** `D3`; and `card_Ttilt`,
  `W5_card` (the rank form of (W5)).
-/
