module

public import RequestProject.TheoremB.Basic
public import RequestProject.TheoremB.Ballot
public import RequestProject.TheoremB.Completion
public import RequestProject.TheoremB.TorsionTensor
public import RequestProject.TheoremB.Count
public import RequestProject.TheoremB.TheoremB
public import RequestProject.TheoremB.SmallCases
public import RequestProject.TheoremB.Structure

/-!
# Theorem B: the Sylow `p`-subgroup of `K(H(d,q))` for every prime `p > d` — index

Formalization of `CS3_theorem_B.md`, namespace `ColouredSand.TheoremB`, reusing Theorem E
(`RequestProject/Strings/`, CS1) and Theorem A (`RequestProject/Splitting/`, CS2):

* §0 (Objects): `RequestProject/TheoremB/Basic.lean` (`cokerL`, `sandpile`; `Syl_p` is
  `AddCommGroup.primaryComponent`, `mem_primaryComponent_iff`) and
  `RequestProject/TheoremB/Structure.lean` (`hammingGraph_connected`,
  `cokerL_equiv_int_prod_sandpile`: `coker L ≅ ℤ ⊕ K` and `K` finite).
* (B1): `RequestProject/TheoremB/Completion.lean` (`sylow_tensor_padic`, `coker_tensor_padic`,
  `coker_tensor_padic_matrix`; general `cokerBaseChange`).
* (B2): `RequestProject/TheoremB/Ballot.lean` (`ballot`, `ballot_identity`, `ballot_cast`).
* (B3): `RequestProject/TheoremB/TheoremB.lean` (`theorem_B`), using
  `RequestProject/TheoremB/TorsionTensor.lean` (`torsion_tensor_equiv_syl`) and
  `RequestProject/TheoremB/Count.lean` (`nCount`, `card_fiber_gIdx`, `bigIdxEquiv`).
* (B4): `RequestProject/TheoremB/SmallCases.lean` (`nCount_two`, `nCount_three`, `nCount_four`,
  and the explicit isomorphisms `theorem_B_two`, `theorem_B_three`, `theorem_B_four`).
-/
