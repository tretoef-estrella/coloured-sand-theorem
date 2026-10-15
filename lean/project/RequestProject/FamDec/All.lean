module

public import RequestProject.FamDec.Mult
public import RequestProject.FamDec.Perm
public import RequestProject.FamDec.Decomp

/-!
# `C31_theorem_36_the_family_decomposition.md` — Theorem 3.6 (the family decomposition) and
# Lemma 3.7 (namespace `FamDec`)

Nothing of the Setting is redefined: `DPLattice`, `one`, `V`, `tensorV` (C18); `Hom.id`,
`Hom.comp` (C19, through the isomorphisms); `phi`, `Iso`, `Iso.trans`, `Iso.symm`, `Iso.phi`,
`OddUnits` (C20); `C3_hyp` (C21); `dsum` (C22); `dsumIso`, `tensorVIso` (C23); `Iso.refl`,
`dsumComm`, `dsumAssoc` (C24); `zeroL` (C27); `H1`, `H2`, `H3`, `OneAddTwoUnit`, `Z1` (C28);
`T`, `tpow`, `T_zero`, `T_odd`, `T_even`, `tpow_zero`, `tpow_succ`, `T1` (C29); `A1`, `K1`,
`dsumList`, `dsumList_cons`, `dsumListAppendIso` (K4a), `tensorVDsumListIso` (K4c),
`phiDsumListIso` (K4d), `dsumListSingletonIso` (K4e) (C30).

Encodings:
* Formal sums `Σ_λ c_λ [λ]` (§1.2) are `List ℕ`: `c` copies of `λ`, order irrelevant (compared up
  to `List.Perm`). The paper's `λ` is written `lam`.
* `Vdot` is defined by well-founded recursion (`Vdot 0 = [1]`, `Vdot (n+1) = [n+2]` for even `n`,
  `[n, n] ++ (Vdot (n/2)).map (2·+1)` for odd `n`); the equations of (M1) are theorems.
  `L 0 = [0]`, `L (n+1) = (L n).flatMap Vdot`, `m lam n = (L n).count lam`.
* "`X ≅ Y`" is `Nonempty (Doubling.Iso X Y)`; explicit isomorphisms are `def`s.
* The hypotheses of C30 (A1) are explicit arguments `H1 φ`, `H2 φ`, `H3 A`, `OneAddTwoUnit A`,
  `h2 : (2 : B) = 0`. `ℤ_[2]` is `PadicInt 2`.

Contents:
* `Mult.lean`: Part M — `Vdot`, `Vdot_zero`, `Vdot_odd`, `Vdot_even` (M1); `L`, `L_zero`,
  `L_succ`, `m` (M2); `mem_L_zero`, `M3` (M3); `M4` (M4). Part L — `L1`, `L2`, `L3`, `L4`.
* `Perm.lean`: Part P — `P1`, `P2`.
* `Decomp.lean`: Part D — `D1`, `D2`, `D3`; Part Z — `Z1_D1`, `Z1_D2`, `Z1_D3`, `Z1`.

Hypotheses: in (L2) the hypothesis `1 ≤ n` is unused (`m_self` proves `m n n = 1` for all `n`),
and in (L3) it is unused (it follows from oddness); they are kept as in the file. Part P holds
over any commutative ring. In Part D every hypothesis of (A1) is used (through C30 `A1`).
-/
