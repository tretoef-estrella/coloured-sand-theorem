module

public import RequestProject.OddSplitting.PartT

/-!
# `CSI5_the_splitting.md` — the Casimir splitting over `ℤ_[p]`, and the three tensor
decompositions of the odd dance (all parts)

Namespace `ColouredSand.OddTwist`. Reuses C18 `DPLattice`, C19 `WeylFilt` (`ShortExact`,
`Hom.comp`), C20 `Doubling.Iso`, C22 `Lemma35.dsum`, C23 `Tensor2`, CSI1 `twist`, CSI3 `psi`,
`iotaHom`, `B4_iso`, and CSI4 `casimir`, `Dcas`, `C2`, `C3`, `S5_one`, `S5_mid`, `S5_last`,
`pairHom`. No existing file is modified.

Files:
* `Tools` — Cayley–Hamilton in the form `N² = p R ⇒ N^{2k} + p h(N) = 0`
  (`exists_annihilating_poly`), reduction modulo `p` detecting units (`modP`,
  `isUnit_of_isUnit_modP`), polynomials in intertwined operators (`intertwine_aeval`);
* `PartH` — **Part H**: `exists_retraction`, **(H1)** `splitting_H1`, **(H2)** `splitting_H2`;
* `DsumCasimir` — `Ω` on a direct sum (`casimir_dsum`, `Dcas_dsum`, `Dcas_sq_dsum`), and
  `Dcas_sq_zero_of_casimir` (from (C3) to the hypothesis of Part H with `b = 0`);
* `PartT` — **Part T**: **(T0)** `tensor_T0`, **(T1)** `tensor_T1`, **(T2)** `tensor_T2`,
  **(T3)** `tensor_T3`.
-/
