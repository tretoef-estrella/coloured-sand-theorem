module

public import RequestProject.ThmG.ExpGroups
public import RequestProject.ThmG.GroupList
public import RequestProject.ThmG.TheoremG
public import RequestProject.ThmG.Glue
public import RequestProject.ThmG.Sylow
public import RequestProject.ThmG.Example

/-!
# `CSG7_theorem_G.md` — Theorem G, the Glue Theorem, the Example and `Syl_p K(H(d,q))`

Folder `RequestProject/ThmG/`, namespace `ColouredSand.ThmG`.  The odd-`p` analogue of
`RequestProject/ThmH` (Theorem H); no existing file is modified, and the objects of the earlier
pieces (`Splitting.Xq`, `Strings.opM`, `Corollaries.sylTorsXq_equiv`, `corollary1_whole`,
`TheoremB.sandpile`, `ThmH.freeTorsionEquiv`, `piProdAddEquiv`, `card_sigma_free`,
`BlockOp.opT`, `cokT`, `K4`, `G1a`, `G1b`, `G1c`, `TiltDec.LP`, `mP`, `M3`, `betaCG`, `W4`,
`TiltP.IsSimpleWt`, `rT`, `aT`, `Ttilt`, `Blocks.chA`, `vt`, `blkX`, `blkY`, `E12`, `E22`) are
reused, not redefined.

Throughout, `p` is a prime (`[Fact p.Prime]`) with `hp2 : p ≠ 2`, and `1 ≤ padicValNat p q`.

## Encodings

* A list of exponents `L : List ℕ` stands for `⊕_{e ∈ L} ℤ/p^e`, the type
  `(i : Fin L.length) → ZMod (p ^ L.get i)` (abbreviated `ExpGrp p L`); lists of exponents are
  compared up to `List.Perm`.
* `Syl_p G` is `AddCommGroup.primaryComponent G p`, `tors X` is `Submodule.torsion ℤ X`,
  `ℤ_p^{[c=0]}` is `Fin (if c = 0 then 1 else 0) → ℤ_[p]`, "`≅`" is `≃+`.
* Direct sums with multiplicities are products over positions in lists (`LP p m`) or over the
  index type `Σ j : Fin (d + 1), Fin (C(d,j)(q−2)^j)` of Corollary 1.

## Files

* `ExpGroups.lean` — auxiliary: `ExpGrp` and its isomorphisms (`expCons`, `expAppend`,
  `expReplicate`, `expOne`, `expPerm`, `expFlatMap`, `expSum`), and `cancelFree` (cancelling
  torsion-free parts).
* `GroupList.lean` — Part L: (L0) `blkList`, `freeBlk`, `GBlk`; (L1) `L1`; (L2) `L2_val`,
  `L2_pos`.
* `TheoremG.lean` — Part T: (T1) `T1` (Theorem G as printed); (T2) `gTorList`, `T2`.
* `Glue.lean` — Part F: `betaN`, `Ac`, `FPiece`, `FList`; (F1) `F1`; (F2) `F2` (Theorem F).
* `Sylow.lean` — Part S: (S1) `S1`, (S2) `S2`.
* `Example.lean` — Part X: `X1_multiset`, (X1) `X1`.

## Deviations from the file (generalisations only)

* (L2) `L2_val` needs no hypothesis, and `L2_pos` holds for every `l` (not only
  `l ≤ p² + p − 1`).
-/
