module

public import RequestProject.Step36.PartW
public import RequestProject.Step36.PartA
public import RequestProject.Step36.PartK

/-!
# `C30_the_step_of_theorem_36.md` — the step of Theorem 3.6 (namespace `Step36`)

Nothing of the Setting is redefined: `DPLattice`, `Hom`, `one`, `V`, `tensorV`, `tensorWt` (C18);
`Hom.id`, `Hom.comp`, `Hom.ext'` (C19); `phi`, `phiWt`, `phiHom`, `Iso`, `Iso.trans`, `Iso.symm`,
`D3`, `OddUnits` (C20); `bc`, `baseChange`, `C3_hyp` (C21); `dsum`, `hL`, `himg` (C22);
`isoOfReindex`, `dsumIso`, `tensorVIsoTensor`, `unitRightIso` (C23); `Iso.refl`, `dsumAssoc`,
`lemma35Iso`, `lemma35Iso_single`, `L5img`, `uIdx` (C24); `IsWtPres` (C25); `zeroL`,
`HasDeltaFilt`, `HasNablaFilt` (C27); `H1`, `H2`, `H3`, `OneAddTwoUnit`, `C3`,
`isWtPres_inverse`, `Z1` (C28); `T3` (C29). C23's `distribLeftIso` and `P8` are also used.

Encodings:
* A vector of `M` is `M.ι → A`, `δ_i = Pi.single i 1`. All isomorphisms are `Doubling.Iso`;
  "`X ≅ Y`" is an explicit `Iso X Y` (a `def`) or `Nonempty (Iso X Y)`.
* "Weight-preserving" is C25's `IsWtPres`; over `B` it refers to the lattices `baseChange φ _`,
  which carry the weights of the lattices over `A`.
* (A1) "reduces to `lemma35Iso`" means `bc φ e.hom.toLin = (lemma35Iso φ h2 N).hom.toLin` and
  `bc φ e.inv.toLin = (lemma35Iso φ h2 N).inv.toLin`.
* (K2) reindexes along `Equiv.prodSumDistrib : Fin 2 × (M.ι ⊕ N.ι) ≃ (Fin 2 × M.ι) ⊕ (Fin 2 × N.ι)`.
* (K4) `dsumList` is defined by recursion on the list; pointwise isomorphisms are a
  `List.Forall₂` of `Nonempty (Iso _ _)` (`K4b`), or the same length together with
  `Nonempty (Iso (L.get k) (L'.get k))` for every `k` (`K4b_get`).
* (Z1) `ℤ_[2]` is `PadicInt 2`, `B = ZMod 2`, `φ = PadicInt.toZMod`.

Contents:
* `PartW.lean`: Part W — `qWt`, `himg_wt` (the finite check on `himg`), `W1`, `W2`.
* `PartA.lean`: Part A — `A1`; Part Z — `Z1_W1`, `Z1_W2`, `Z1_A1`, `Z1`.
* `PartK.lean`: Part K — `tensorVOneIso`, `K1`; `phiDsumIso`, `K2`; `dsumZeroIso`, `zeroDsumIso`,
  `tensorVZeroIso`, `phiZeroIso`, `K3`; `dsumList`, `dsumList_nil`, `dsumList_cons`,
  `dsumListAppendIso`/`K4a`, `K4b`, `K4b_get`, `tensorVDsumListIso`/`K4c`,
  `phiDsumListIso`/`K4d`, `dsumListSingletonIso`/`K4e`.

Hypotheses: every hypothesis of `A1` is used (`H1`, `H2`, `H3`, `OneAddTwoUnit` by C28 (C3),
`h2` to form `lemma35Iso`); `h2` could be derived from `H2 φ`, but is kept as in the file.
(W1), (W2) need no hypothesis beyond the Setting. In Part K, the statements not involving `phi`
hold over any commutative ring; `K1` and `K3` carry `[IsDomain A] [CharZero A] [OddUnits A]`
because they mention `phi`. The weight-preservation of the maps in Part K (C25 (P1)) is not
restated.
-/
