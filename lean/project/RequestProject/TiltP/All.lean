module

public import RequestProject.TiltP.Descent
public import RequestProject.TiltP.GlueDP
public import RequestProject.TiltP.Tglue
public import RequestProject.TiltP.Tilt
public import RequestProject.TiltP.WeylDual
public import RequestProject.TiltP.CG
public import RequestProject.TiltP.CGLattice
public import RequestProject.TiltP.Cor

/-!
# CSG3 — the tilting lattices as DP-lattices, and the Clebsch–Gordan lattice — index

Namespace `ColouredSand.TiltP`.  Reused, not redefined: `DPLattice`, `IsDP`, `Hom`, `delta`,
`nabla`, `weylWt`, `deltaF`, `deltaE`, `tensorV` (C18); `Hom.id`, `Hom.comp`, `ShortExact`
(C19); `Doubling.Iso` (C20); `Lemma35.dsum`; `LemmaW.IsWtPres` (C25); and from the attached
files `lam`, `mu`, `nu` (Blocks) and `V`, `Idx`, `ell`, `ess`, `Fop`, `Eop`, `Lx`, `glueBasis`,
`xzero`, `stilde`, `G1_stability_threshold` (Glue).

## Part T
* (T1) `Tglue p r a : DPLattice ℤ_[p]` — `RequestProject/TiltP/Tglue.lean` (`Tglue`, `Tglue_ι`,
  `Tglue_wt_inl`, `Tglue_wt_inr`, `T1_stable`, `T1_Fd`, `T1_Ed`, `T1_isDP`); the general
  construction `glueDP` and the proof of (W), (P0), (P1), (K) by conjugation and descent are in
  `RequestProject/TiltP/GlueDP.lean` and `RequestProject/TiltP/Descent.lean`.
* (T2) `Tf`, `Tg`, `Tf_single`, `Tg_single_inl`, `Tg_single_inr`, `T2` —
  `RequestProject/TiltP/Tglue.lean`.
* (T3) `IsSimpleWt`, `rT`, `aT`, `Ttilt`, `Ttilt_of_simple`, `Ttilt_of_not_simple`, `T3`,
  `T3_simple_iff` — `RequestProject/TiltP/Tilt.lean`.

## Part C
* (C1) `deltaToNabla`, `C1`; (C2) `C2_not_dvd`, `C2_units`, `C2` —
  `RequestProject/TiltP/WeylDual.lean`.

## Part G
* (G1) `PsiLin`, `PsiCG`, `G1`, `G1_hw` — `RequestProject/TiltP/CGLattice.lean` (with the
  computations in `W` in `RequestProject/TiltP/CG.lean`).
* (G2) `PsiLin_stilde`, `G2` — `RequestProject/TiltP/CGLattice.lean`.
* (G3) `G3`; (G4) `G4` (and the general form `iso_tensor_glueDP`) —
  `RequestProject/TiltP/Cor.lean`.
-/
