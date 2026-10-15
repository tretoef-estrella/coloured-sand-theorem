module

public import RequestProject.OddSplitMove.Basic
public import RequestProject.OddSplitMove.Block
public import RequestProject.OddSplitMove.Layers
public import RequestProject.OddSplitMove.TheoremM

/-!
# `CSI8_the_split_move.md` — the odd split move (Proposition 2.2 of «the odd dance»;
# Parts S and M)

Namespace `ColouredSand.OddTwist`. No existing file is modified and no citation is used.
Reused: C11's `Payment.Sys` (module of a system) and `Payment.quotProdEquiv`; CSI7's generators
`oslot` / `oslotE` (C11's `slotLof` / `slotEmb` without the unused order), the system `Gp p fl F Q`,
`Gp_oslot`, `FSo`, `DSm`, `DSm_smul`, `DSmHom`, `layerD`, `chainOp`, `chainProd`, `chainRow`,
`chainCol` (with `chainRow_chainOp`, `chainRow_bijective`, `chainCol_surjective`), `smul_top_pi_eq`,
`list_prod_map_smul`, `QT`, `QTsign` and the scalar identity `smul_Gp_QTsign`. C12 serves as the
model for the block conventions (slots `S × Bool`, all `A` slots then all `C` slots).

Main definitions and results (exact Lean names):
* **Part S** (`Basic.lean`): the split `NS p N`, `flS p r fl`, `embS`, `FS p r hr F`; the products
  `prodQ Q a b = Π(a, b)`; the new data `QA p Q`, `QC p r Q`, `KS p r Q` (the file's `K`),
  `blockS`, `QS p r Q = [[QA, 0], [K, QC]]`; the sign variant `QSsign` (`QAsign`, `QCsign`) with
  `QSsign_of_odd`; the links to CSI7 `QA_eq_QT`, `QAsign_eq_QTsign`, `QCsign_eq_QTsign`.
* **Proof steps**: `layer_comp_GpS` (step 1, `Layers.lean`), `coupledCokerEquiv` (steps 1–3,
  `Block.lean`), `chainProd_layerD_gen`, `smul_DSm_KS`, `smul_blockGp`, `slot_comp_Gp_blockS`
  (`TheoremM.lean`, `Layers.lean`).
* **(M1)** `theorem_M1` (odd `p`, the file's `QS`) and `theorem_M1_sign` (every `p`, `QSsign`).
* **(M2)** `corollary_M2` (`c = p^h`).
-/
