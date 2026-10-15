module

public import RequestProject.Tensor2.Kron
public import RequestProject.Tensor2.Comb
public import RequestProject.Tensor2.Basic
public import RequestProject.Tensor2.Morph
public import RequestProject.Tensor2.VTensor
public import RequestProject.Tensor2.Iso

/-!
# `C23_the_tensor_product.md`: index (namespace `Tensor2`)

Reused, not redefined: from C18 (`DPLattice`) `DPLattice`, `IsDP`, `H`, `Hom`, `V`, `tensorV`,
`bvec`, `one` (with `Hop`, `tensorFd`, `tensorEd`, `oneFd`, `ext_single`, `ext_bvec`); from C19
(`WeylFilt`) `Hom.id`, `Hom.comp`; from C20 (`Doubling`) `Iso`, `Iso.ofInverse`,
`Iso.ofDataEquiv`; from C22 (`Lemma35`) `dsum`, `dsumHom` (with `blk`, `inlL`, `inrL`).
(`slice`, `delta` and `nabla` are not needed by any statement of the file.)

Encodings:
* **Vectors** of a DP-lattice `M` are functions `M.ι → A` (`A` any commutative ring); the basis
  vector `δ_i` is `Pi.single i 1`.
* **Pure tensors**: `tprod m n : ι × κ → A`, `(i, j) ↦ m i * n j`, so `δ_{(i,j)} = δ_i ⊗ δ_j`.
* **Kronecker product** `f ⊠ g` (Setting): `kron f g`, the linear map whose matrix is the Kronecker
  product of the matrices of `f` and `g`; `(f ⊠ g)(δ_{(i,j)}) (i', j') = f(δ_i)(i') · g(δ_j)(j')`
  (`kron_single_apply`) and `(f ⊠ g)(m ⊗ n) = f m ⊗ g n` (`kron_tprod`).
* **Tensor product** (P1): `tensor M N`, basis `M.ι × N.ι`, weights `M.wt i + N.wt j`,
  `F^{(r)} = coFd M.Fd N.Fd r = Σ_{a=0}^{r} M.Fd a ⊠ N.Fd (r − a)` and likewise `E^{(r)}`.
* **Morphisms** (P2): `kronHom f g` (underlying map `f ⊠ g`), `tensorIso u v`.
* **Isomorphisms** are C20's `Iso` (morphisms both ways with identity composites). Each
  isomorphism theorem states its underlying linear maps:
  - (P3) `tensorVIsoTensor M : tensorV M ≅ V A ⊗ M`: `LinearMap.id` both ways;
  - (P4) `assocIso`, (P5) `distribRightIso`, `distribLeftIso`, (P8) `unitLeftIso`,
    `unitRightIso`: reindexing along a bijection `e` of bases, `f ↦ f ∘ e⁻¹` (sending `δ_x` to
    `δ_{e x}`) and its inverse `g ↦ g ∘ e`, where `e` is `Equiv.prodAssoc`
    (`((i, j), k) ↦ (i, (j, k))`), `Equiv.sumProdDistrib` (`(inl i, k) ↦ inl (i, k)`,
    `(inr j, k) ↦ inr (j, k)`), `Equiv.prodSumDistrib` (`(i, inl j) ↦ inl (i, j)`,
    `(i, inr k) ↦ inr (i, k)`), `Equiv.uniqueProd` (`((), i) ↦ i`), `Equiv.prodUnique`
    (`(i, ()) ↦ i`);
  - (P6) `tensorVHom f` (underlying map `id ⊠ f`, i.e. `bvec e m ↦ bvec e (f m)`),
    `tensorVIso u`;
  - (P7) `dsumIso u v` (underlying maps `dsumHom u.hom v.hom`, `dsumHom u.inv v.inv`).

Results: `P1` (with `tensor_isDP`, `tensor_Fd_tprod`, `tensor_Ed_tprod`), `P2`
(`kronHom_id`, `kronHom_comp`, `tensorIso`), `P3` (`tensorV_Fd_eq`, `tensorV_Ed_eq`), `P4`,
`P5`, `P6` (`tensorVHom_bvec`, `tensorVHom_id`, `tensorVHom_comp`, `tensorVIso`), `P7`
(`dsumIso`), `P8`.
-/
