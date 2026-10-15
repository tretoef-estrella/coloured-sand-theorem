module

public import RequestProject.Lemma35.Sum
public import RequestProject.Lemma35.Basic
public import RequestProject.Lemma35.L1Defs
public import RequestProject.Lemma35.L1Comm
public import RequestProject.Lemma35.PartL1
public import RequestProject.Lemma35.PartL2
public import RequestProject.Lemma35.PartL3

/-!
# `C22_lemma_35_over_F2.md`: index (namespace `Lemma35`)

Reused, not redefined: from C18 (`DPLattice`) `DPLattice`, `IsDP`, `H`, `Hom`, `V`, `tensorV`,
`delta`, `bvec` (with `Hop`, `tensorFd`, `tensorEd`, `tensorWt`, `wtV`, `weylWt`); from C19
(`WeylFilt`) `Hom.id`, `Hom.comp`; from C20 (`Doubling`) `Iso` (and `Hom.ofInverse`); from C21
(`Twist`) `frob` (the Frobenius twist `M^{[1]}`).

Encodings:
* **Vectors** of a DP-lattice `M` are functions `M.ι → B`; the basis vector `δ_i` is
  `Pi.single i 1`.
* **Direct sum** (Part S, `Sum.lean`): `dsum M N` has basis `M.ι ⊕ N.ι`, weights
  `Sum.elim M.wt N.wt`, and `F^{(r)} = blk (M.Fd r) (N.Fd r)`, `E^{(r)} = blk (M.Ed r) (N.Ed r)`
  where `blk f g z = Sum.elim (f (z ∘ inl)) (g (z ∘ inr))` is the blockwise map. The inclusions
  are `x ↦ Sum.elim x 0`, `y ↦ Sum.elim 0 y` (`inlHom`, `inrHom`), the projections `z ↦ z ∘ inl`,
  `z ↦ z ∘ inr` (`fstHom`, `sndHom`), and `f ⊕ g` is `dsumHom f g` (underlying map `blk`).
* **Maps given on basis vectors** (Part L): `ofImg v` is the linear map with `δ_i ↦ v i`.
* **`V^{⊗3}`** is `T3 B = tensorV (tensorV (V B))`, basis `Fin 2 × (Fin 2 × Fin 2)`; the word
  `e_1e_2e_3` is `w e_1 e_2 e_3 = δ_{(e_1, (e_2, e_3))}`.
* **`D = Δ(3) ⊕ (V ⊕ V)`** is `D3 B = dsum (delta B 3) (dsum (V B) (V B))`, basis
  `Fin 4 ⊕ (Fin 2 ⊕ Fin 2)`; `e_r = eD r = δ_{inl r}`, `b_e = bD e = δ_{inr (inl e)}`,
  `c_e = cD e = δ_{inr (inr e)}`.
* **`g`, `h`** of (L1) are `gL = ofImg gimg`, `hL = ofImg himg` (tables: `g_basis`, `h_basis`);
  their `Hom`s are `gHom h2`, `hHom h2`, and `isoL1 h2 : Doubling.Iso (T3 B) (D3 B)`.
* **`V ⊗ V^{[1]}`** is `VV1 h2 = tensorV (Twist.frob h2 (V B))`, basis `Fin 2 × Fin 2`;
  `b_e b'_{e'}` is `bb e e' = δ_{(e, e')}`; in `Δ(3)`, `e_r` is `eW r = δ_r`.
* **`u`, `u⁻¹`** of (L2) are `uL = ofImg uimg`, `uinvL = ofImg uinvimg` (tables: `u_basis`,
  `uinv_basis`); their `Hom`s are `uHom h2`, `uinvHom h2`, and
  `isoL2 h2 : Doubling.Iso (delta B 3) (VV1 h2)`.
* **Isomorphism** means `Doubling.Iso`.

Results:
* **Part S** (any commutative ring): (S1) `S1` (and `dsum`, `dsum_Fd`, `dsum_Ed`); (S2) `S2`
  (and `inlHom`, `inrHom`, `fstHom`, `sndHom`, `dsumHom`, `dsumHom_id`, `dsumHom_comp`).
* **Part L** (commutative ring `B` with `h2 : (2 : B) = 0`): (L1) `L1` (and `g_basis`,
  `h_basis`, `gHom`, `hHom`, `hg_id`, `gh_id`, `isoL1`, `g_eD_eq_Fd`); (L2) `L2` (and `u_basis`,
  `uinv_basis`, `uHom`, `uinvHom`, `uinv_u_id`, `u_uinv_id`, `isoL2`, `u_eW_eq_Fd`);
  (L3) `L3` (`B = ZMod 2`).
* Remark of the proof sketch: `g_not_hom_int` (over `ℤ`, `g` is not a `Hom`).

Hypotheses: `h2` is used in (L1), (L2) only for the `Hom` and inverse statements (and to form
`V^{[1]}`); the formulas `g (e_r) = F^{(r)}(000)` (`g_eD_eq_Fd`) and the tables hold without it;
`u (e_r) = F^{(r)}(b_0 b'_0)` needs `h2` only because `V^{[1]}` is formed with it.
-/
