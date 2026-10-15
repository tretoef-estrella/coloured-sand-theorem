module

public import RequestProject.LemmaW.PartE

/-!
# `C25_lemma_W_and_ext.md`: index

Lemma 3.2 (Lemma W) and the first sentence of Lemma 3.3 (every extension of `Δ_A(λ)` by
`∇_A(μ)` splits), namespace `LemmaW`.

Reused, not redefined: from C18 (`DPLattice`) `DPLattice`, `IsDP`, `Hop`, `H`, `Hom`, `delta`,
`nabla`, `weylWt`, `deltaF`, `deltaE`, `nablaF`, `nablaE` (and the lemmas `IsDP.dual`,
`deltaF_eq`, `deltaE_eq`); from C19 (`WeylFilt`) `Hom.id`, `Hom.comp`, `Hom.ext'`,
`ShortExact`; from C20 (`Doubling`) `Iso`, `Iso.ofInverse`.

Encodings:
* vectors of a DP-lattice `M` are functions `M.ι → A`; `δ_i = Pi.single i 1`;
* weight-preserving: `IsWtPres φ`; weight projection: `pr M w`; "has weight `w`": `HasWt M w z`
  (`pr M w z = z`); transpose: `trM φ = Matrix.toLin' (LinearMap.toMatrix' φ)ᵀ`;
* an extension is a short exact sequence `N —f→ X —g→ Z` of DP-lattices (`ShortExact f g`); it
  splits when `g` has a section / `f` has a retraction in `Hom`;
* `dual M`: same basis and weights, `F^{(r)} = trM (M.Ed r)`, `E^{(r)} = trM (M.Fd r)`;
  `dualHom f` has underlying map `trM f.toLin`;
* an isomorphism is a `Doubling.Iso` (underlying maps `u.hom.toLin`, `u.inv.toLin`);
* `sW x` is the linear map `δ_r ↦ F^{(r)} x` (`z ↦ Σ_r z_r • F^{(r)} x`).

Contents:
* `Basic.lean`: Setting, Part P — `P1_H`, `P1`, `P2` (`P2_wtPres`, `P2_F`, `P2_E`), `P3`.
* `Dual.lean`: Part D — `dual`, `D1`, `dualHom`, `D2` (`dualHom_id`, `dualHom_comp`,
  `dualHom_wtPres`), `isoDualDual`, `D3`, `D4_delta`, `D4_nabla`, `isoDualDelta`,
  `isoDualNabla`, `D4`, `D5`.
* `PartW.lean`: Part W — `W1`, `W2`, `sW`, `sW_single`, `sWHom`, `W3`, `W4` (Lemma 3.2), `W5`.
* `PartE.lean`: Part E — `E1`, `E2_le`, `E2_gt`, `E2` (Lemma 3.3, first sentence), `E3`, `E4`.
-/
