module

public import RequestProject.Windows.Basic
public import RequestProject.Windows.Labels
public import RequestProject.Windows.Hom
public import RequestProject.Windows.Step
public import RequestProject.Windows.Moves
public import RequestProject.Windows.TheoremW
public import RequestProject.Windows.TheoremD

/-!
# The windows and Theorem D (`C14_windows_and_theorem_D.md`)

Index of the formalization (namespace `Windows`).  Reused unchanged: from C10 (`Deficit`)
`starMul`, `a`, `c`, `pi0`, `Mc`, `B1_rescaling`, `C2_integrality_valuation` (and (A1)
`A1_support`, used through `B1_rescaling` for the support of `c_h`); from C3 (`Rulers`) `oE`,
`delta`, `v2`; from C11 (`Payment`) `pT`, `κT`; from C12 (`Split`) `pSp`, `κSp`; from C13 (`Dance`)
`mCount`, `dance`, `danceAux`, `slots_eq`, `splitIso`, `relabP`, `relabK`, `Mfin`, `pσ`, `κσ`,
`sigma`, `SysT`, `proposition_4_3`.

## Encodings (`Basic.lean`, the *Setting*)

* Digit lists `ds : List Bool` (lowest digit first), `ds[t]?` the `t`-th entry,
  `k = ds.length`, `m = Dance.mCount ds`.
* `Ids ds = {t < length ds : ds[t] = true}` (`I(ds)`, a `Finset ℕ`); `rank I t = #{u ∈ I : u < t}`.
* `Dset ds s = {t ∈ I(ds) : Nat.testBit s (m − 1 − rank t)}` (`D(ds, s)`, for `s : ℕ`; slots
  `s : Fin _` are read through `s.val`); `Dlab P s` is the same formula for any finite set `P`.
* Prefixes are `ds.take h`; `π_0 = Deficit.pi0 α i` with `α` cast to `ℤ`, `c_h = Deficit.c (Ids ds) h`,
  `o = Rulers.oE`, windows are `Finset.Ico`.
* Ring homomorphisms act pointwise on data (`fun s f => φ (p s f)`), and by `Matrix.map` on
  matrices.
* `finalMatrix A ds α i` (`TheoremD.lean`) is `Mfin (dance ds 1 (pσ α i) κσ)` over `A`, read on
  `Fin (2^m)` through `Fin.cast` as in `Dance.proposition_4_3`.

## Results

* **Part H** (`Hom.lean`): (H1) `H1_pT`, `H1_κT`, `H1_pSp`, `H1_κSp`, `H1_relabP`, `H1_relabK`,
  `H1_danceAux`, `H1_dance`; (H2) `H2_Mfin`, `H2_pσ`; (H3) `H3_final_matrix`.
* **Part W**: (W) `W_windows` and Theorem 4.4 `theorem_4_4` (`TheoremW.lean`); the induction is
  `windows_gen`, with the moves `twist_step`, `split_step` (`Moves.lean`), the coefficient and
  window identities `core_pay`, `core_coupling` (`Step.lean`) and the label lemmas `Dlab_split`,
  `Dlab_mono`, `Dlab_inj`, `Dlab_surj` (`Labels.lean`).
* **Part D** (`TheoremD.lean`): Theorem D, `theorem_D_i`, `theorem_D_ii`, `theorem_D_iii`,
  `theorem_D_iv`, assembled in `theorem_D`.
-/
