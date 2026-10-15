module

public import RequestProject.Glue.Defs
public import RequestProject.Glue.Coords
public import RequestProject.Glue.Lattice
public import RequestProject.Glue.Stability
public import RequestProject.Glue.Forced
public import RequestProject.Glue.ModP
public import RequestProject.Glue.Rescale
public import RequestProject.Glue.Operator

/-!
# Lemma 7 («the glue is forced») — index

Formalization of `CSG2_lemma_7_the_glue.md`, namespace `ColouredSand.Glue`.  It reuses
`lam`, `mu`, `nu`, `uGlue`, `Nt`, `Mblk`, `blkX`, `blkY`, `E12`, `E22`, `glue_exponent_N`, `B1`,
`B2` from `RequestProject/Blocks/` (namespace `ColouredSand.Blocks`).

* §0, the setting: `RequestProject/Glue/Defs.lean` (`V`, `ell`, `ess`, `wt`, `Fmat`, `Emat`,
  `Pmat`, `Fop`, `Eop`, `Pop`, `IsStable`, `stilde`, `Lx`, `Dlam`, `Dmu`, `xzero`, `Hmat`, `Hop`,
  `Oop`); the action on the basis exactly as in §0: `RequestProject/Glue/Coords.lean`
  (`F_ell`, `F_ess`, `E_ell`, `E_ess`, `P_ell`, `P_ess`).
* (G1) the stability threshold: `RequestProject/Glue/Stability.lean`
  (`G1_stability_threshold`).
* (G2) the glue is forced: `RequestProject/Glue/Forced.lean` (`G2_glue_forced`, and the
  general form `glue_forced`).
* (G3) split versus non-split modulo `p`: `RequestProject/Glue/ModP.lean`
  (`G3a_split`, `G3b_nonsplit`).
* (G4) rescaling: `RequestProject/Glue/Rescale.lean` (`G4_rescaling`).
* (G5) the basis and the operator, (G6) Lemma 8 on the lattice:
  `RequestProject/Glue/Operator.lean` (`G5a_basis`, `G5b_maps`, `Orestr`, `G5b_matrix`,
  `G6_B1`, `G6_B2`).
* Proof infrastructure: `Binomial.lean` (the commutation identity for divided powers and the
  Kummer computations), `Lattice.lean` (membership in `Lx x` and the basis `glueBasis`),
  `Identities.lean` (`E t`, `F t`, `P w` on the vectors `s̃ x j`).
-/
