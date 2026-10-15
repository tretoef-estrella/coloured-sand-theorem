module

public import RequestProject.Blocks.Defs
public import RequestProject.Blocks.Numbers
public import RequestProject.Blocks.TwoByTwo
public import RequestProject.Blocks.Simple
public import RequestProject.Blocks.Block

/-!
# Lemma 8 («the blocks») — index

Formalization of `CSG1_lemma_8_the_blocks.md`, namespace `ColouredSand.Blocks`
(pure linear algebra over `ℤ_[p]`; no other part of the project is used).

* Preamble, §1 and §2 definitions: `RequestProject/Blocks/Defs.lean`
  (`Nt`, `vt`, `lam`, `mu`, `nu`, `uGlue`, `Mblk`, `blkA`, `blkA'`, `blkAlpha`, `blkTau`,
  `E11`, `E12`, `E22`, `blkX`, `blkY`, `Mch`, `chA`).
* (P) positivity and (N) the glue exponent: `RequestProject/Blocks/Numbers.lean`
  (`positivity_P`, `glue_exponent_N`).
* (L) the 2×2 lemma: `RequestProject/Blocks/TwoByTwo.lean` (`lemma_L`, and the general
  `twoByTwo_nonempty`).
* (B1), (B2): `RequestProject/Blocks/Block.lean` (`B1`, `B2`).
* (S1), (S2): `RequestProject/Blocks/Simple.lean` (`S1`, `S2`, and the separate cases
  `S1_pos`, `S1_zero`, `S2_pos`, `S2_zero`).
* §3, the proof: `Tools.lean`, `Segment.lean` (contracting unit links), `Glued.lean`,
  `PChain.lean`, `UChain.lean` (the `p I_{2a}` step), `Elim.lean` (the glue relation),
  `Valuation.lean` (valuations of the coefficients), `BlockCore.lean` (assembly for `Mblk`).
-/
