module

public import RequestProject.OddSES.PartC4

/-!
# `CSI4_the_short_exact_sequences.md` — the Casimir and the short exact sequences
`0 → Ψ_{r+1}(N) → V ⊗ Ψ_r(N) → Q_{r−1}(N) → 0` (all parts)

Namespace `ColouredSand.OddTwist`; `p` is an odd prime (`[Fact p.Prime]`, with `3 ≤ p` or
`p ≠ 2` where needed), the ring is `ℤ_[p]`, `N : DPLattice ℤ_[p]`.

Files: `Casimir` ((C1)), `ModP` (congruences mod `p`), `CasimirPsi` ((C2)), `CasimirTwist`
((C3)), `PartP1` ((P1)), `PartP2`, `PartP3` ((P2), (P3)), `PartS1`, `PartS1b` ((S1), the
contraction and action maps), `PartS2` ((S2), (S3)), `SESTools` (Nakayama, rank argument),
`PartS4`, `PartS4b` ((S4)), `PartS5a`, `PartS5b`, `PartS5` ((S5)), `PartC4` ((C4)).

Main results:
* (C1) `C1`, `casimir_hom`; (C2) `C2`; (C3) `C3`; (C4) `C4`;
* (P1) `P1`; (P2) `P2`; (P3) `P3`, `iotaPHom`;
* (S1) `S1`, `omegaHom`; (S2) `piHom`, `S2`; (S3) `pi1Hom`, `S3`;
* (S4) `S4_pi`, `S4_pi1` (and `surj_of_modP`);
* (S5) `S5_one`, `S5_mid`, `S5_last` (and `shortExact_of_rank`).
-/
