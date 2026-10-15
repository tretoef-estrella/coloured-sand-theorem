module

public import RequestProject.Splitting.Basic
public import RequestProject.Splitting.OneCoordinate
public import RequestProject.Splitting.Tensor
public import RequestProject.Splitting.Laplacian
public import RequestProject.Splitting.Conjugation
public import RequestProject.Splitting.Blocks
public import RequestProject.Splitting.TheoremA
public import RequestProject.Splitting.Rescaling

/-!
# Theorem A: the splitting of the Laplacian of the Hamming graph — index

Formalization of `CS2_theorem_A_splitting.md`, namespace `ColouredSand.Splitting`
(reusing `B_m`, `H`, `U` and `opM = q (c + H) + U` from `RequestProject/Strings/`):

* §0 (Objects): `RequestProject/Splitting/Basic.lean` (`hammingGraph`, `laplacian`, `Mq`, `Xq`)
  and `RequestProject/Splitting/Laplacian.lean` (`hammingGraph_degree`: `deg = d (q − 1)`).
* (A1): `RequestProject/Splitting/OneCoordinate.lean`
  (`basisVec_isBasis`, `K_ev_zero`, `K_sigma`, `K_fv`, `completeGraph_lapMatrix`).
* (A2): `RequestProject/Splitting/TheoremA.lean` (`theorem_A`), with the steps of the proof in
  `Tensor.lean`, `Laplacian.lean` (`laplacian_eq_sum_coordOp`), `Conjugation.lean`
  (`laplacian_conj`) and `Blocks.lean` (`Nop_block`, `card_blockJ`).
* (A3): `RequestProject/Splitting/Rescaling.lean` (`rescaling_padic`, `rescaling_padic_coker`,
  and the general-ring versions `rescaling`, `rescaling_coker`).
* (A4): `RequestProject/Splitting/Rescaling.lean` (`opM_coker_depends_only_on_valuations`,
  `opM_coker_equiv_valuations`).
-/
