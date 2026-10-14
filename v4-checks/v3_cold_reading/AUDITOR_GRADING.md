# Grading of the cold reading COLOURED_SAND_1 («Grepy el Tamiz») — Grepy Altair, Tue Oct 13 09:30:59 CEST 2026

Report: `~/Desktop/LECTORES_EN_FRIO/COLOURED_SAND_1/REPORT_COLOURED_SAND_1.md` (md5 482dc343…, 401 lines), copied with its checks to `VIVOS/ATAQUES_Y_REPORTES/COLOURED_SAND_1/` (manifest there). First line: **HOLDS WITH CORRECTIONS**.

## Grade: HIGH MARK
Every proof of the paper (A–H, Lemmas 2–5, 7, 8, Corollaries 1, 6, Conjecture I) re-derived in writing, not stamped. Own engine (C, local Smith over Z_(p), tested 300 + 136 + 200 random matrices against exact arithmetic and Sage). 115/115 sealed groups reproduced; 18 + 14 new predictions written before computing (timestamps, md5), all hit, with controls that differ. Literature read in originals (JNR03 from Reiner's page, CSX15, DGW, TW, STWZ, HW). Found a real priority omission. One procedural slip declared by itself (an md5 check run outside the watchdog).

## Checked by the auditor (not taken on trust)
- **d = 2 already known — CONFIRMED in the original:** Ducey–Gerhard–Watson arXiv:1507.06583, Theorem 1.1 (1.1): K(R_n) ≅ (Z/2n)^{(n−2)²+1} ⊕ (Z/2n²)^{2(n−2)}, R_n = K_n × K_n = H(2,n) (pdftotext of the reader's download, md5 c655bdd2…). Our §Provenance (line 513) claims B, C, D, F, G, H «new» without excluding d = 2. **Real correction.**
- **Wilson's range — CONFIRMED:** CSX15 p. 4: «We shall state his result for t ≤ k ≤ n/2». The paper says it uses the statement «as given in [CSX15, (2)]» and needs 2s = m−1. Citation gap; statement true. **Already machine-closed by us:** Lean CS5 proves W_{t,t+1} for 2t+1 ≤ m (middle rank included) from scratch.
- **Remark after Theorem G — CONFIRMED wrong example:** the reader's scripts re-run by me give the same output (Thm G form at e = 0 = computed {1:108}; Thm F form differs); my own Sage computation of Syl_3 K(H(4,4)) = (Z/3)^108.
- Other corrections accepted as stated (not re-derived by me): Lemma 8 sentence placement; «63» counts two groups twice (61 distinct, 105 in all); «384»/«112» subsets not described; Theorem B's (j,k) ≠ (0,0) vacuous; precise (T1) reference (Jantzen II.E.19–E.22); for p = 2, Conjecture I «holds» needs a proof that every big clock exceeds θ (only machine-checked, 9000/9000, least margin 1); Theorem H is conditional on [DST] (same author, unrefereed).

## Consequences
- No theorem falls. Nothing is FATAL.
- Corrections go into paper v4 (with the Lean). The public v3 overstates novelty for d = 2: Rafa decides whether to fix it before v4.
- Lean plan: Theorem H's dependence on [DST] becomes machine-checked through the cube's Lean (stage 2) — this answers the reader's caveat. The p = 2 Conjecture-I inequality is not in the Lean plan (it is about a conjecture).
