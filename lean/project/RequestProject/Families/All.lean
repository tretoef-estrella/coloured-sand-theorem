module

public import RequestProject.Families.Digits
public import RequestProject.Families.Tower
public import RequestProject.Families.Group
public import RequestProject.Families.Quot
public import RequestProject.Families.Theorem

/-!
# `C32_theorem_38_the_groups_of_the_families.md` — Theorem 3.8 (the groups of the families)

Folder `RequestProject/Families/`, namespace `Families`.  Nothing listed in the Setting of the
file is redefined: C11 `Payment` (`Sys`, `slotLof`, `slotEmb`, `G`, `NΦ`, `flΦ`, `embΦ`, `FΦ`),
C12 `Split` (`NVΦ`, `flVΦ`, `embVΦ`, `FVΦ`, `NΨ`, `flΨ`, `embΨ`, `FΨ`, `theta`, `thetaInv`,
`thetaEquiv`, `A2_theta_comp_F`), C13 `Dance` (`Idx`, `fl`, `F`, `SysT`, `pσ`, `κσ`, `sigma`),
C14 `Windows.Ids`, C16 `FamilyGroup.X`, C17 `CubeLaplacian` (`G`, `lap`, `K`, `Syl2`, `D2`),
C18 `DPLattice` (`DPLattice`, `Hom`, `H`, `one`, `tensorV`, `tensorPow`, `C1equiv`), C20
`Doubling` (`phi`, `B1`, `Iso`, `OddUnits`), C21 `Twist.C3_hyp`, C22 `Lemma35.dsum`, C28 `Lift2`
(`H1`, `H2`, `H3`, `OneAddTwoUnit`, `Z1`), C29 `Filt` (`T`, `T_zero`, `T_odd`, `T_even`, `tpow`,
`tpow_succ`), C30 `Step36.dsumList`, C31 `FamDec` (`L`, `m`, `M3`, `le_of_mem_L`, `D2`) are used
directly.

## Encodings

* **Digits** (`Digits.lean`): `ds : ℕ → List Bool` by well-founded recursion, with
  `ds_zero`, `ds_odd`, `ds_even` the three equations of (B0); the family `I` is `Windows.Ids`.
* **Vectors**: a vector of a DP-lattice `M` is `M.ι → A` (basis `Pi.single j 1`); a vector of the
  tower `T(ds)` is an element of `⨁ _ : Dance.Idx ds, A`, with coordinates `v q`.
* **(B1)** (`Tower.lean`): `B1` is the existence statement; `Theta A λ` is a chosen equivalence,
  with properties `B1a` and `B1b`.  The odd step sends `b_e n` to `embΦ e (Θ n)`; the even step
  sends `b_a ⊗ b_e n` to `embVΦ a e (Θ n)` and is followed by C12's `thetaEquiv` (= `theta`).
* **(B2)** (`Group.lean`): `sigL A λ α i` is the operator of the file; cokernels are quotients by
  `LinearMap.range`; the identification `M ≃ M^{Fin 1}` is `slotE` (`m ↦ m ι_0`); `sigEquiv` is
  the explicit equivalence, and `B2`, `B2Z` are the statements (the hypothesis `1 ≤ α` is not
  needed).
* **(Q)** (`Quot.lean`): `Q0`; `Q1` (and its general form `dsumMap_exists` for `l.map f`), with
  products as dependent functions over `Fin Ls.length` and the componentwise form of C18 `C1`;
  `Q2` with the explicit `isoEquiv`.
* **(T)** (`Theorem.lean`): the hypotheses of C30 (A1) are explicit arguments; `T1` (with the
  explicit `T1equiv`), `T2` and `T3` (with the reindexing `famReindex` of `L n` by entries and
  multiplicities); `ℤ_[2]` is `PadicInt 2`.  "`X ≅ Y`" is `Nonempty (X ≃ₗ[A] Y)` or
  `Nonempty (X ≃+ Y)`, as written in the file.
-/
