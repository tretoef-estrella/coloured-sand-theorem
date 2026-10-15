module

public import RequestProject.FamilyGroup.Basic
public import RequestProject.FamilyGroup.Cokernel
public import RequestProject.FamilyGroup.Group
public import RequestProject.FamilyGroup.Raw
public import RequestProject.FamilyGroup.TheoremX

/-!
# `C16_the_family_group_over_Z2.md`: the group of a family over `ℤ_2`

Index of the formalization (namespace `FamilyGroup`).

## Encodings

* `A = ℤ_[2]` (Mathlib's `PadicInt 2`); every isomorphism is a `ℤ_[2]`-linear equivalence, stated
  as `Nonempty (… ≃ₗ[ℤ_[2]] …)`.
* `ds : List Bool`, `k = ds.length`, `I = Windows.Ids ds`, `m = Dance.mCount ds` (`= #I`,
  `Windows.card_Ids`), `N = 2 ^ Dance.mCount ds`, `K = 2 ^ ds.length`.
* `X ds α i = Dance.SysT ℤ_[2] ds (Fin 1) ⧸ LinearMap.range (Dance.sigma ℤ_[2] ds α i)`;
  `SC ds` is the first factor of `Dance.proposition_4_3` over `ℤ_[2]`;
  `Q e = ℤ_[2] ⧸ Ideal.span {2 ^ e}`.
* The clocks of C15 are `DanceSmith.Cst` (`C`), `DanceSmith.yHat` (`ŷ`), `DanceSmith.yHatS`
  (`ŷ^♯`) and `DanceSmith.xClk` (`x`); the pooled raw clocks of §1.2 are `yPool ds i` (`ŷ_i`)
  and `yPool0 ds` (`ŷ_0`), built from `Rulers.clock`, `TheoremF.dancer` and `AntitonicFit.ifit`.
* A matrix `B : Matrix (Fin n) (Fin n) R` acts through `Matrix.toLin' B`; its cokernel is
  `(Fin n → R) ⧸ LinearMap.range (Matrix.toLin' B)`; `R ⧸ (d)` is `R ⧸ Ideal.span {d}`.
* Exponents that the file writes as integers are natural numbers `E p` with `(E p : ℤ) = …`;
  products over positions are products over `Fin N` (or `Fin (N − 1)`), read at `p.val`.

## Where each statement is

* **Part L** (`Cokernel.lean`): (L1) `L1`; (L2) `L2_range`, `L2`; (L3) `L3_unit`, `L3_zero`.
* **Part U** (`Cokernel.lean`): (U1) `U1`; (U2) `U2`.
* **Part X** (`Group.lean`): (X1) `X1`; (X2) `X2`; (X3) `X3`.
* **Part R** (`Raw.lean`): (R0) `R0`; (R1) `R1`; (R2) `R2`.
* **Part T** (`TheoremX.lean`): (T1) `T1`; (T2) `T2`, and `T2_empty` for `I = ∅`.

## Hypotheses

* (X1), (X2) use `1 ≤ k`, `1 ≤ α` (and `1 ≤ i`, resp. `I ≠ ∅`) through `DanceSmith.S3`,
  `DanceSmith.Z3`; (X3) uses `1 ≤ α` through `DanceSmith.Z1`.
* (R2) is stated without the hypothesis `I ≠ ∅` of the file, which is not needed (for `I = ∅`
  there is no position `q < N − 1 = 0`).  (R1) uses `1 ≤ i` (`Rulers.proposition_5_3`).
* (L1)–(L3) hold over any commutative ring, as in the file.
-/
