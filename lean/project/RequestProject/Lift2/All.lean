module

public import RequestProject.Lift2.PartZ

/-!
# `C28_lifting_mod_2_and_corollary_34.md`: index

Lifting modulo 2 (end of the proof of Lemma 3.3) and Corollary 3.4; namespace `Lift2`.

Reused, not redefined: from C18 (`DPLattice`) `DPLattice`, `IsDP`, `Hom`, `H`, `Hop`,
`ext_single`; from C19 (`WeylFilt`) `Hom.id`, `Hom.comp`, `Hom.ext'`; from C20 (`Doubling`)
`Iso`, `Hom.ofInverse`, `Iso.ofInverse`; from C21 (`Twist`) `bc`, `bc_comp`, `bc_id`, `bc_one`,
`bc_add`, `bc_smul`, `bc_single_apply`, `baseChange`, `bcHom`; from C25 (`LemmaW`) `IsWtPres`,
`pr`; from C27 (`Cocycle`) `Lin`, `Pair`, `IsCocycle`, `CocycleEqs`, `G2`, `d`, `d_add`, `G4`,
`HasDeltaFilt`, `HasNablaFilt`, `V4`, `isWtPres_iff`, `isWtPres_sub`, `comm_H_of_isWtPres`.
(The C27 objects `cocycles`, `IsCoboundary` and the definitions of `ShortExact`, `delta`,
`nabla` enter through `V4`, `HasDeltaFilt` and `HasNablaFilt`.)

Encodings:
* a vector of a DP-lattice `M` is a function `M.ι → A`, `δ_i = Pi.single i 1`;
  `Lin M N = (M.ι → A) →ₗ[A] (N.ι → A)`; a pair is `c : Pair M N`, `cF = c.1`, `cE = c.2`;
* `φ : A →+* B`; the base change of a linear map is `bc φ f` (entrywise `φ` on the matrix),
  of a DP-lattice `baseChange φ M`, of a morphism `bcHom φ f`;
* hypotheses, as explicit propositions passed as arguments: `H1 φ` (surjective), `H2 φ`
  (`φ a = 0 ↔ ∃ b, a = 2 * b`), `H3 A` (`2 * a = 0 → a = 0`), `OneAddTwoUnit A`
  (`∀ a, IsUnit (1 + 2 * a)`, the hypothesis of (C1));
* `2 • U`, `2 • c` are scalar multiples by `(2 : A)`;
* "weight-preserving" is C25's `IsWtPres` (for maps over `B` between reductions, with respect
  to `baseChange φ M`, `baseChange φ N`, which carry the weights of `M`, `N`);
* "`u` invertible" is `IsUnit u` in `Module.End A (ι → A)`, equivalently `Function.Bijective u`;
* isomorphisms are `Doubling.Iso`, with both underlying maps `.hom.toLin`, `.inv.toLin` stated;
* `ℤ_[2] = PadicInt 2`, `φ = PadicInt.toZMod : ℤ_[2] →+* ZMod 2`.

Hypotheses used by each statement:
* (D1) `D1`: (H2), (H3) (`D1_exists`, the existence part: (H2) only);
* (D2) `D2`: (H3); (D3) `D3`: (H2), (H3);
* (L0) `L0`: (H1); (L1) `L1`: none; (L2) `L2`: (H1), (H2), (H3);
* (C1) `C1`: `OneAddTwoUnit A` only;
* (C2) `C2`: (H2) and `OneAddTwoUnit A`; (H3), listed in the file, is **not needed** and is
  omitted (a more general statement);
* (C3) `C3`: (H1), (H2), (H3), `OneAddTwoUnit A`;
* (Z1) `Z1`, (Z2) `Z2_L2`, `Z2_C3`: no hypotheses (they are proved for `PadicInt.toZMod`).

Contents:
* `Basic.lean`: Setting (`H1`, `H2`, `H3`, `OneAddTwoUnit`), auxiliary `two_smul_cancel`,
  `two_smul_cancel_lin`, `bc_sub`, `d_smul`, `d_sub`; Part D: `D1_exists`, `D1`, `D2`, `D3`.
* `PartL.lean`: Part L: `L0`, `L1`, `L2`.
* `PartC.lean`: Part C: `det_one_add_two_smul`, `C1`, `C2`, `isWtPres_inverse`, `C3`.
* `PartZ.lean`: Part Z: `Z1`, `Z2_L2`, `Z2_C3`.
-/
