module

public import RequestProject.OddPayment.Basic
public import RequestProject.OddPayment.Chain
public import RequestProject.OddPayment.Layers
public import RequestProject.OddPayment.TheoremA

/-!
# `CSI7_the_twist_move.md` — payment systems and the odd twist move
# (Proposition 2.1 of «the odd dance»; Parts T and A)

Namespace `ColouredSand.OddTwist`. No existing file is modified and no citation is used. C11's
setting is reused: the module of a system is `Payment.Sys N S`, the generators are C11's
`Payment.slotLof` / `Payment.slotEmb` (written `oslot` / `oslotE` because no order on the slot type
is wanted here; `oslot_eq_slotLof`, `oslotE_eq_slotEmb` show they are C11's maps), the quotient
lemma `Payment.quotProdEquiv` is used in the reduction, and the statements have C11's form
«a cokernel is isomorphic to a product of cokernels».

Main definitions and results (exact Lean names):
* **Setting** (`Basic.lean`): `oslot`, `oslotE`, the system with matrix data `Gp p fl F Q`.
* **Part T** (`Basic.lean`): `NT`, `flT`, `embT`, `FT`, the twisted data `QT` (and the signed
  variant `QTsign`, with `QTsign_of_odd`).
* **Part A** (`TheoremA.lean`):
  - (A1) `theorem_Ap` (odd `p`, data `QT` exactly as in the file), and `theorem_Ap_sign`
    (every `p ≥ 1`, sign `(−1)^p` built into the data); also `corollary_Ap_one` (`c = 1`);
  - (A2) `corollary_Ap2` (`c = p^h`);
  - (A3) `evenness_A3` (with the shape `QT_shape`).
* The proof: `layerProj_comp_Gp` (step 1: `G_T` in the layers is a chain operator, `Layers.lean`),
  `chainCokerEquiv` (steps 2–3: the row/column reduction, `Chain.lean`), `chainProd_layerD` and
  `smul_Gp_QTsign` (step 3: the product of the layers and the scalar `−c p`).
-/
