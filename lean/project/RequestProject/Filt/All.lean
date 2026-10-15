module

public import RequestProject.Filt.PartT

/-!
# `C29_filtrations_and_dance_lattices.md`: index

Filtrations of `V ⊗ −`, `Φ`, `⊕` and of the dance lattices `T(λ)`; namespace `Filt`.

Reused, not redefined: from C18 (`DPLattice`) `DPLattice`, `IsDP`, `Hom`, `H`, `delta`, `nabla`,
`one`, `V`, `tensorV`, `T5_delta_zero`, `T5_nabla_zero`, `T5_delta_one`, `T5_nabla_one`; from
C19 (`WeylFilt`) `Hom.id`, `Hom.comp`, `ShortExact`, `fDelta`, `gDelta`, `fNabla`, `gNabla`
(through `S1`, `S2`), `S1`, `S2`, `S4`; from C20 (`Doubling`) `phi`, `phiHom`, `A3`, `Iso`,
`Iso.ofInverse`, `Iso.symm`, `Iso.ofDataEquiv`, `deltaIso`, `nablaIso`, `OddUnits` (and
`phiLin` with its exactness lemmas); from C22 (`Lemma35`) `dsum`, `inlHom`, `sndHom` (with
`inlL`, `sndL`); from C23 (`Tensor2`) `tensorVHom`, `tensorVHom_bvec`; from C25 (`LemmaW`)
`IsWtPres`, `P1`, `K_vec`; from C27 (`Cocycle`) `HasDeltaFilt`, `HasNablaFilt`, `G7`, `zeroL`,
`F2_delta`, `F2_nabla`, `isDP_transport`, `thetaL`, `thetaInvL` and weight lemmas; from C28
(`Lift2`) `isWtPres_inverse`.

Encodings:
* a vector of a DP-lattice `M` is a function `M.ι → A`, `δ_i = Pi.single i 1`;
* (S1), (S2): the new lattice has basis a finite type `κ : Type` with decidable equality and
  weights `wK : κ → ℤ`; weight preservation of `j, p, q, s` is the raw form of C25's
  `IsWtPres`; stability of `range j` is `∀ r x, X.Fd r (j x) ∈ LinearMap.range j` (same for
  `Ed`), stability of `ker q` is `∀ r x, x ∈ ker q → X.Fd r x ∈ ker q` (same for `Ed`);
  `sub X wK j p …`, `quot X wK q s …` are the lattices, `subHom`, `quotHom` the morphisms `j`,
  `q`;
* isomorphisms are C20's `Iso`; "weight-preserving" is C25's `IsWtPres` on underlying maps;
* **[char 0]** is `[IsDomain A] [CharZero A]`, **[Φ]** is `[IsDomain A] [CharZero A]
  [OddUnits A]`;
* `T A : ℕ → DPLattice A` (dance lattices, well-founded recursion) and `tpow A : ℕ → DPLattice A`
  (`V^{⊗n} ⊗ A`); `ℤ_[2]` is `PadicInt 2`.

Files:
* `Sub.lean`: Part S: `sub_isDP`, `sub`, `subHom`, `S1`; `quot_isDP`, `quot`, `quotHom`, `S2`.
* `PartI.lean`: Part I: `I1_delta`, `I1_nabla`, `I1`; `I2_delta_one`, `I2_nabla_one`,
  `I2_delta_V`, `I2_nabla_V`, `I2` (with the auxiliary `Hom.liftInj`, `Hom.descSurj`,
  `ShortExact.isoComp`).
* `PartE.lean`: Part E: `E1` (induction on the filtration of the quotient, with the sub-lattice
  of (S1) built from the sections of C27 (G7)), `E2` (dually, with the quotient lattice of (S2)),
  `E3_delta`, `E3_nabla`, `E3`.
* `PartV.lean`: Part V: `V1_delta`, `V1_nabla`, `V1`; `V2_delta`, `V2_nabla`, `V2`.
* `PartT.lean`: Part T: `T`, `tpow`, `T_zero`, `T_odd`, `T_even`, `tpow_zero`, `tpow_succ`,
  `T0`, `T1`, `T2`, `T3`, `T3_T`; Part Z: `Z1`.
-/
