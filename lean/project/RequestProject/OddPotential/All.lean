module

public import RequestProject.OddPotential.Sequences
public import RequestProject.OddPotential.Walk
public import RequestProject.OddPotential.TheoremF1
public import RequestProject.OddPotential.LemmaP
public import RequestProject.OddPotential.Flat
public import RequestProject.OddPotential.TheoremT

/-!
# `CSI16_theorem_F_at_p.md` — Theorem F at a prime `p` (Theorem 7.8_p)

Namespace `ColouredSand.OddTwist`.  Encodings: see `RequestProject/OddPotential/Sequences.lean`
(houses, dancers, sequences, the walk) and `RequestProject/OddPotential/LemmaP.lean` (`ŷ_H`,
`ĉ_H`, potentials, `X_1`, `v'`).  Reused, not redefined: C1 (`AntitonicFit`), C3 (`Rulers`),
C4 (`GoldenMatching.rank`), C7 (`TheoremF.dancer`, Lemma 0), C8 (`Potential.IsArrow`), CSI14
(`A1_same_order`) and CSI15 (`xHP`, `JHP`, `RHP`, `cHatHP`, `typP`, `kapP`, `satP`, `tauP`, `d1P`
and Lemmas A0, C1–C7).

* *Setting*: `xHseqP`, `JHseqP`, `dWalkP` (`dWalkP_eq`), `oddF_xH_antisymm`, `oddF_J0`,
  `oW_dancer_mono`, `JHseqP_mono`; `yhatP`, `cHatSeqP`, `IsPotentialP`, `X1P`, `vPrimeP`.
* **Part F1** (Theorem F1_p): `oddF_theorem_F1`, `oddF_F1_Lambda` (`(Λ_p)`),
  `oddF_F1_Lambda_pow` (`o_I ≤ p^k − 1`), `oddF_F1_Cut` ((Cut)).
* **Part F0** (Theorem F0_p): `oddF_theorem_F0`, and separately `oddF_W0`, `oddF_W1_antitone`,
  `oddF_W1_change`, `oddF_W2`, `oddF_W3`.
* **Part P**: Lemma P `oddF_lemma_P` (`oddF_P1_low`, `oddF_P1_high`, `oddF_P1_cross`, `oddF_P2`,
  `oddF_P3`, `oddF_P4` with the sharp form of (P4)); Lemma X `oddF_lemma_X`; Lemma N
  `oddF_lemma_N`; Lemma F `oddF_lemma_F` (`oddF_F1_flat`, `oddF_F2_flat`, `oddF_F3_flat`,
  `oddF_F4_flat`, with `loFP`, `hiFP`, `flatVP`; `oddF_exists_flat_start`,
  `oddF_X1_last_nonpos_of_flat`).
* **Part T**: Theorem F_p `oddF_theorem_F`, Corollary F′_p `oddF_corollary_F'`.
* **Part Δ**, step 1: `oddF_delta_step1`; step 3 is (P4) (`oddF_P4`); steps 2 and 4 are inside
  the proofs of `oddF_F1_step` and `oddF_F4_flat`.
-/
