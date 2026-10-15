module

public import RequestProject.Cocycle.PartFV

/-!
# `C27_cocycles_and_filtrations.md`: index

Lemma 3.3, second sentence (`Ext^1(M, N) = 0` for `Δ`-filtered `M` and `∇`-filtered `N`),
through explicit cocycles; namespace `Cocycle`.

Reused, not redefined: from C18 (`DPLattice`) `DPLattice`, `IsDP`, `Hom`, `Hop`/`H`, `delta`,
`nabla`, `InWt`, `inWt_single`; from C19 (`WeylFilt`) `Hom.id`, `Hom.comp`, `Hom.ext'`,
`ShortExact`; from C20 (`Doubling`) `Iso`, `Iso.ofInverse`; from C25 (`LemmaW`) `IsWtPres`,
`pr`, `HasWt`, `P1`, `P2_wtPres`, `P2_F`, `P2_E`, `E1`, `E2`, `K_vec`, `comm_prW_of_shift`,
`exists_section`, `exists_retraction_of_section`.

Encodings:
* a vector of a DP-lattice `M` is a function `M.ι → A`, `δ_i = Pi.single i 1`;
  `Lin M N = (M.ι → A) →ₗ[A] (N.ι → A)`;
* a pair `c = (cF, cE)` is `c : Pair M N = (ℕ → Lin M N) × (ℕ → Lin M N)`, `cF = c.1`,
  `cE = c.2`;
* a vector `z = (u, v)` on `N.ι ⊕ M.ι` is `Sum.elim u v` (`u = z ∘ Sum.inl`,
  `v = z ∘ Sum.inr`); `blk a b d` is the block operator `(u, v) ↦ (a u + b v, d v)`;
* `zeroL A`: basis `Empty`; glued data: weights `gwt M N = Sum.elim N.wt M.wt`, operators
  `gF c r = blk (N.Fd r) (c.1 r) (M.Fd r)`, `gE c r = blk (N.Ed r) (c.2 r) (M.Ed r)`;
  `IsCocycle c := IsDP (gwt M N) (gF c) (gE c)`; `glue M N c hc` the glued DP-lattice;
* `incl` (`u ↦ (u, 0)`), `proj` (`(u, v) ↦ v`); `d ψ`; `IsCoboundary c := ∃ ψ, IsWtPres ψ ∧ d ψ = c`;
* `pcomp c i = c ∘ i`, `qcomp j c = j ∘ c`;
* isomorphisms are `Doubling.Iso` with their underlying maps `.hom.toLin`, `.inv.toLin` stated;
* `HasDeltaFilt`, `HasNablaFilt`: inductive predicates; `ℤ_[2] = PadicInt 2`.

Contents:
* `Basic.lean`: Setting, (G0) `zeroL`, (G1) `blk`, `gwt`, `gF`, `gE`, `IsCocycle`, `glue`,
  (G2) `CocycleEqs`, `G2`.
* `Weights.lean`: auxiliary weight lemmas: `wd` (weight-diagonal part, `wd_eq_sum`),
  `exists_wtPres_lift`, `exists_wtPres_section`, `isDP_transport`, cocycle equations at
  weight vectors (`cF_inWt`, `cE_inWt`, `K_cocycle_vec`).
* `PartG.lean`: (G2) `cocycles` (submodule), (G3) `incl`, `proj`, `G3`, (G4) `d`,
  `IsCoboundary`, `G4`.
* `PartG56.lean`: (G5) `secHom`, `G5`; (G6) `pcomp`, `qcomp`, `G6a` (`G6a_pcomp`, `G6a_qcomp`,
  `G6a_d_pcomp`, `G6a_d_qcomp`), `G6b`, `G6c`.
* `PartG7.lean`: (G7) `extCocycle`, `G7`, `G7_split`.
* `PartFV.lean`: (F1) `HasDeltaFilt`, `HasNablaFilt`; (F2) `F2_delta`, `F2_nabla`, `F2`;
  (V1) `V1`, (V2) `V2`, (V3) `V3`, (V4) `V4_nabla`, `V4_cocycle`, `V4`, (V5) `V5`, (V6) `V6`.
-/
