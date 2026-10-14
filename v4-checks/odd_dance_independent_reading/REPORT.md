HOLDS WITH CORRECTIONS

# REPORT — COLOURED_SAND_2 («the odd dance») — cold reading by Grepy el Jurado
Reader: Grepy el Jurado, Tue 13 Oct 2026, 21:34–23:04 CEST (times from `date` in the step log at the end). Under review: `material/REPORT_ODD_DANCE.md` (md5 d9c2f1ab…). All work done by me in this session (no agents, no workflows); every computation under `vigia.sh` with the log path first; estimates written before runs (the few exceptions are listed as slips in the step log).

**In one paragraph.** Every proof of the report was re-derived by hand and every one holds: the odd-p lattices `Φ_p`, `Ψ_r` (all `[E,F] = H` cases by hand, the embedding `ι`, the Casimir argument, the filtrations), Theorem 1.6, the moves and Theorem D_p, Theorem I (= Conjecture I of [CS3], every prime), the windows / deficit law / cost form, and Theorem 4.4. The report's riskiest step, the odd-p floor (Theorem F), was only a list of changes to [DST] §7: I wrote it out as a full proof (`checks/THEOREM_F_ODD_P.md`) and every change on the list is right; the list missed one small fact (the o-order of `o_D = Σ d_t p^t` is the binary order of the digit sets), which I supply. My own engines confirm everything with live controls: 569 lattices (K1), 62 identifications `L(λ)⊗𝔽_p ≅ T(λ)` without Donkin (K2), **31/31 sealed direct Smith forms on B_12, B_13 beyond the published range, 0 disagreements (K3)**, the closed formula against Theorem G, DST, all 10710 sealed cells and the exact Smith form of `M_p` (K4, ~34000 cells), 12 whole Hamming groups up to d = 60 against Kirchhoff and the 𝔽_p-rank (K5), 47310 houses for Theorem F_p (K6). No error and no counterexample. **Corrections** are of presentation, citation and priority: write Theorem F_p in full (done here) with fact (O1); write the closed `E^{(r)}`; name Weyl's theorem in Lemma 1.0; cite Donkin's tensor product theorem and the tilting classification precisely (STWZ Prop. 3.4(a); Andersen 1997 Remark 1.1(ii); Jantzen E.6, E.19–E.22); state that the **existence** of the ℤ_p tilting lattices and the lifting of `V^{⊗m}` decompositions is classical (Andersen 1997 §1.2; Jantzen E) — what is new is their explicit form; and that **d = 2 of Theorem TOTAL is Ducey–Gerhard–Watson (2016)**. The grade of claim #15 («PROVED (pencil)») was stronger than what was written at the time.

## Summary table (R1–R11, K1–K7, L1–L4)
| item | verdict | one-line reason | where checked |
|---|---|---|---|
| R1 Lemma 1.0 | CORRECT (PRESENTATION) | `D = φE − Eφ` commutes with `F`, raises weight; injectivity of `F^{h+1}` on `Y_{h+2}` holds for every finite-dim `Y` by Weyl's complete reducibility — the proof says only «on Δ(c)»: name Weyl's theorem | by hand (JOB 1 R1); `E` from `(F,H)` = printed `E` in 71/71 (`checks/k1_controls.log`) |
| R2 Def 1.1, Prop 1.2 | CORRECT (PRESENTATION) | all `[E,F]` cases; closed **`E^{(r)}(b_jn) = (p/u)^c (c!/r!) b_{j''} E^{(c)} ∏_{(a,i)∈S(j,r)}[p²X + (i−pa)(p(w+1+a)−i)] n`** (the report gives only «`P(X,H)`»), integral for all `r`; reductions mod p incl. `(ps+t)!/(p^s s!) ≡ (−1)^s t!`, `∏(−i²) ≡ 1`, `E^{(t)}` on St; Δ/∇ isomorphisms | by hand; `checks/k1b.log` (273812 pairs, control 1242 failures) |
| R3 Def 1.3, Prop 1.4 | CORRECT (PRESENTATION) | `[E,F] = H` re-checked by hand on every case of the definition (the 10 index ranges `A_0`, `A_{1..r−1}`, `A_r`, `A_{r+1..p−2}`, `A_{p−1}`, `C_0`, `C_{1..p−r−1}`, `C_{p−r}`, `C_{p−r+1..p−2}`, `C_{p−1}`, with their `r = 1` and `r = p−1` variants); the two `F`-identities of `ι`; `ῑ` injective with saturated image (`r−1` unit); Casimir argument and Lucas; Δ-filtration by path counting. Small point: Lemma 1.0(ii) is applied to `Ψ_1(N)` before it is known to be a lattice (harmless) | by hand; K1 (569 lattices); `checks/k1b.log` (ι: 98, filtrations: 33, Casimir: 98) |
| R4 Lemma 1.5 | CORRECT | [DST] Lemma 3.2 (Kostant (K), weights), 3.3 (Weyl, forward differences, duality, `×p`), Cor. 3.4 (completeness), Lemma 2.4 use nothing of `p = 2`; Lift′ correct as stated | [DST] md §2.3–3.2 |
| R5 Theorem 1.6 | CORRECT (citations) | (i)–(iii) re-derived; Donkin's theorem read in originals: STWZ arXiv:2105.07724 **Prop. 3.4(a)** (ℓ = p for SL_2 over 𝔽̄_p) and Andersen 1997 **Remark 1.1(ii)** (`p ≥ 2h−2`, i.e. every `p` for SL_2): covers `r = 0` with any `b`, and `λ = p−1`; Krull–Schmidt: Jantzen E.6 (= Heidersdorf–Wenzl Prop. 5.1); passage to `Y_p` via [CS3] Lemma 2 correct | `material/sources…/STWZ`, `C_1912.09457`; `checks/downloads/Andersen1997` |
| R6 Props 2.1–2.3, Thm D_p | CORRECT | every pivot exactly 1 (units `s+1 ≤ p−2` at the last level); signs `(−1)^{p−1}`, `(−1)^{p−r}`; unit `u`; `Q_A, Q_C, K` shapes; no `C → A` coupling; last level on `Δ(d_k−1)`; summand count | by hand; K4 (moves code = windows code; SEALED_1 1520/1520); K3 |
| R7 Theorem I | CORRECT | from D_p (`M ∈ p^{d_k}M`); `p = 2` from [DST] Thm D, stated for every `α ≥ 1`, `M` even; count `= dim T(λ)/p` (`k ≥ 1`) | by hand |
| R8 PASO 4 (a1)–(a3) | CORRECT | windows/adjacency, `c^{(h)}` recursion and normalization to `q_{t+1} = q_t^p − [t∈I]y_tq_t^{p−d_t}`; deficit law `k − |Δ| − min Δ`; cost form via Legendre/Kummer, `i = 0` case, non-vanishing on the support | by hand; `checks/k4_windows.log` (4836 cells, 73632 entries) |
| R9 Theorem 4.4 | CORRECT (PRESENTATION) | ceiling ([DST] §6) verbatim given fact (O1) (o-order = binary order of digit sets; not stated in the report) and the proved non-vanishing; floor: **full written proof `checks/THEOREM_F_ODD_P.md`** — every item of the report's list of changes is right, incl. «DIG sat=1 → 3(b); DIG sat=0, NEV → 3(d)» | by hand; `checks/k6_p3.log`, `k6_p5.log` (47310 houses) |
| R10 Theorem TOTAL | CORRECT | Theorem A ([JNR03] Thm 13) ⊗ ℤ_p, multiplicities `C(d,j)(q−2)^j n_λ(d−j)`, `i = j + (d−j−λ)/2`, `e = v_p(q)` ([CS3] Lemma 2), one free summand (`j = 0, λ = d, i = 0`) | by hand; `checks/k5.log` (12/12) |
| R11 grades | PRESENTATION | grades are honest overall (provisos stated); but #15 «PROVED (pencil)» rested on a list of changes nobody had expanded; #5/#6 re-prove classical facts without saying so; #20 (literature) was one search | report table of claims |
| K1 | CORRECT | 569 lattices (p = 3, 5, 7; dim ≤ 600): relations, character = Donkin product, rank, integrality of `E^{(r)}, F^{(r)}` for every `r` (min excess 0). Controls: coupling `p²` 84/84 and `0` 84/84 fail; twist without `p` 18/23 (5 vacuous) | `checks/k1_p3.log`, `k1_p5.log`, `k1_p7.log`, `k1_controls.log`, `k1b.log` |
| K2 | CORRECT | 62/62 `L(λ)⊗𝔽_p` (λ = 12…50 for p = 3, 30…45 for p = 5, 56…62 for p = 7) tilting (Δ- and ∇-filtrations) and indecomposable (End local, dim `2^{|I|}`), hence `T(λ)` by the classification — **no use of Donkin's theorem**; controls fire | `checks/k2_*.log` |
| K3 | CORRECT | **31/31 sealed cells agree, 0 disagree** — direct p-adic Smith forms of `q(c+H)+U` on B_12 (19 cells, e = 1…4, c ≤ 13, q ∈ {3,6,9,12,15,27,54,81}), B_13 (4 cells, q ∈ {3,6,27}) and p = 2 (8 cells, m ≤ 13, e ∈ {2,3}); predictions sealed 22:12:35, md5 `fb7cf75162e4f9dadfa0224f4180b862`; engine validated on 97 proved-range cells | `checks/K3_PREDICTIONS.txt`, `checks/k3_*.log` |
| K4 | CORRECT | my closed formula (from the printed notation) = Theorem G (18540 cells), = DST (7236 cells; raw-clock rule too), = SEALED_2 (300 random and all 10710), = Smith form of `M_p` (≈ 34000 cells, p = 3, 5, 7, λ ≤ 400), windows = moves; controls (no pooling, `K = p^k`, `κ(i,K)`, no `d_k`-term) fire | `checks/k4_*.log` |
| K5 | CORRECT | 12/12 whole groups `Syl_p K(H(d,q))` with `d ≥ p²+p` (up to (7, 60, 14)) have exactly Kirchhoff's length and the 𝔽_p-rank count of cyclic factors; the formula with `e+1` fails 12/12; also the report's `Syl_3 K(H(12,3))` and [CS3] §10 reproduced | `checks/k5.log`, `k5b.log`, `k5c.log` |
| K6 | CORRECT | 47310 houses (p = 3, k ≤ 4; p = 5, k ≤ 3; e ∈ {1,2}): Lemma 7.6_p/7.7_p, gluing, (Λ_p), strict cuts, integrality, the potential V of my proof with (E),(M),(G); `T(r) ≥ Y(r)` by brute force on 14906 houses × 3; all four types occur (OR, AND, DIG, NEV); controls fire | `checks/k6_p3.log`, `k6_p5.log`, `k6_control_*.log` |
| K7 | CORRECT | md5 of SEALED_1, SEALED_2 = report; 1520 and 10710 cells | `checks/k7_md5.log` |
| L1 | PARTLY KNOWN | existence/uniqueness/lifting of ℤ_p tilting lattices classical (Andersen 1997 §1.2; Jantzen E.19–E.22); explicit SL_2 lattices for all λ and integral functors `Φ_p, Ψ_r`: not found | JOB 3 L1 |
| L2 | PARTLY KNOWN | d = 2: Ducey–Gerhard–Watson (2016); d ≥ 3 at p ∣ q: nothing outside the author's [CS3], [DST] | JOB 3 L2 |
| L3 | NOT FOUND | no Smith form of `f + p^e(D+i)` (or similar) on tilting modules; nearest: Andersen's tilting filtrations (a different pairing) | JOB 3 L3 |
| L4 | — | priority table below; nothing CONTRADICTED | JOB 3 |

## Priority table (L4) — rows of the report's table of claims
| # | claim | status | where |
|---|---|---|---|
| 1 | Lemma 1.0 (`E` determined by `F, H`) | NOT FOUND as a stated lemma; routine `sl_2` linear algebra (Weyl's theorem) | not searched as a priority item |
| 2 | `Φ_p` lattice / functor; reduction `St ⊗ N̄^{[1]}`; `Φ_p(Δ(μ)) ≅ Δ(pμ+p−1)` | PARTLY KNOWN: over fields `St ⊗ H^0(μ)^{[1]} ≅ H^0(p(μ+1)−1)` (Jantzen II.3.19, recalled in Andersen 1997 Remark 1.1(ii)); the integral functor for odd p NOT FOUND (p = 2: author's [DST] §3.1) | arXiv, zbMATH, OpenAlex, MO (S-L1, S-ENG1, S-OA1) |
| 3 | `Ψ_r` lattice / functor; reduction `T(p−1+r) ⊗ N̄^{[1]}`; Δ-filtration | PARTLY KNOWN (field-level module: Donkin [Don93]; STWZ Prop. 3.4); the integral functor NOT FOUND | same |
| 4 | ∇-filtration of `Ψ_r(∇)` | not claimed | — |
| 5 | ℤ_p versions of [DST] 3.2–3.4, Lift′ | ALREADY KNOWN in general form: Jantzen RAGS B.9–B.10, E.19–E.22 (Heidersdorf–Wenzl arXiv:1912.09457 §5.4); Andersen 1997 §1.2 (Ext vanishing (1), lifts) | material C_1912.09457; D1 |
| 6 | Theorem 1.6 (`L(λ) ≅ T_{ℤ_p}(λ)`, decomposition of `V^{⊗m}⊗ℤ_p`) | PARTLY KNOWN: existence/uniqueness/decomposition of ℤ_p tilting modules ALREADY KNOWN (Andersen 1997 §1.2; Jantzen E); the explicit lattices `L(λ)` NOT FOUND | D1; S-L1, S-OA1 |
| 7 | Gate A | measurement — reproduced independently (K1) | — |
| 8 | twist / split / last-level moves (odd p) | NOT FOUND (p = 2: author's [DST] Props 4.1–4.3) | S-L2, S-OA1, S-ENG1 |
| 9 | Theorem D_p | NOT FOUND | same |
| 10 | Theorem I = Conjecture I ([CS3] §8), every prime | NOT FOUND (the conjecture itself is the author's [CS3] §8) | same |
| 11 | number of cyclic summands `= dim T(λ)/p` | ALREADY KNOWN in substance: it is the number of Jordan blocks of `f` on the `G_1`-projective `T(λ)` (Jantzen II.11.11 as recalled in Andersen 1997 Remark 1.1(ii); [CS3] §8) | D1 |
| 12 | Theorem 4.1 (windows; `q_{t+1} = q_t^p − [t∈I]y_tq_t^{p−d_t}`) | NOT FOUND (p = 2: [DST] Thm 4.4) | S-L2 … |
| 13 | Lemma 4.2 (deficit law) | NOT FOUND (p = 2: [DST] Lemma 4.5) | same |
| 14 | Prop. 4.3 (cost form, base-p carries) | NOT FOUND (p = 2: [DST] Prop. 5.2) | same |
| 15 | Lemmas 7.5–7.7_p, Theorem F_p | NOT FOUND (p = 2: [DST] §7) | same |
| 16 | Theorem 4.4 | NOT FOUND | same |
| 17 | Theorem TOTAL / whole `Syl_p K(H(d,q))` | PARTLY KNOWN: **d = 2 ALREADY KNOWN** — Ducey–Gerhard–Watson, arXiv:1507.06583 = EJC 23(4) #P4.9, Thm 1.1 (also JNR03 Thm 13 + Ex. 11); `p > d`, `d ≤ p²+p−1`, `p = 2`: the author's own [CS3] Thms B, G, H and [DST]; the rest NOT FOUND | S-OA1, C-trees |
| 18 | contains Theorem G, DST, [CS3] §10, Theorem B | measurement — reproduced independently (K4, K5) | — |
| 19 | provenance of the `E`-formulas | — | — |
| 20 | «no published Smith form of `f + p^e(D+i)` on tilting modules; no integral odd-p twist functor» | CONFIRMED by a wide sweep (L1, L3), with the precision that integral tilting lattices themselves are classical | JOB 3 |
**CONTRADICTED: none.** Side notes for the author (not about this report): D. Betzer, Zenodo 10.5281/zenodo.22065778 (23 Aug 2026) claims GMMY Conj. 4.14 for the hypercube (relevant to [DST] §1.8); OpenAlex conflates [CS3]'s title with CSX15's DOI.

## Theorem F for odd p (R9) — `checks/THEOREM_F_ODD_P.md`
The full written proof is in `checks/THEOREM_F_ODD_P.md` (ceiling §1, sequence lemmas §2, houses / Lemma 7.5_p / Lemma 7.6_p (four types) / Lemma 7.7_p §3, Theorem F_p statement §4, the induction steps 1–8 written out §5, Lemma 7.9_p §6, Theorem 7.10_p and the house `ℓ = p^k − 1` for `i = 0` §7, assessment of the report's list of changes §8). It was completed; there is no place where I could not complete it.

## JOB 1 — proofs line by line (R1–R11)

### R1. Lemma 1.0 — CORRECT (one sentence to add)
Re-derived. `D := φE − Eφ` raises weights by 2 and `DF − FD = φ[E,F] − [E,F]φ = φH − Hφ = 0` (using `φF = Fφ`). `X` is spanned by `F^k x` with `x` primitive of weight `h ≥ 0`, `F^{h+1}x = 0`; then `F^{h+1}(Dx) = D F^{h+1}x = 0`. **Injectivity of `F^{h+1}` on `Y_{h+2}` for every finite-dimensional `Y`:** by Weyl's theorem `Y_ℚ ≅ ⊕ Δ_ℚ(c)`, `F` acts summand by summand, and on `Δ_ℚ(c)` the weight-`μ` vector `e_s` (`μ = c − 2s`, `μ ≤ c`) satisfies `F^k e_s = (s+1)⋯(s+k) e_{s+k}`, zero iff `k > c − s = (c+μ)/2`; with `μ = h+2`, `(c+μ)/2 ≥ μ = h+2 > h+1`, so `F^{h+1}` is injective on each summand's weight space, hence on `Y_{h+2}`. The proof as printed says only «on `Δ(c)`»: the reduction to `Δ(c)` is Weyl's complete reducibility (also needed for «`X` is spanned by `F^k x`»). **Verdict: CORRECT; PRESENTATION: name Weyl's theorem.** (ii) is right: commuting with `E, F, H` over `ℚ` gives commuting with `Dist_A ⊂ U_ℚ`, and the inverse of an `A`-isomorphism commuting with them also commutes. Every later use of Lemma 1.0 (Props 1.2(d), 1.4(b), base case of 1.4(b)) applies it to `U_ℚ`-modules already established in (a) — consistent. Machine: `E` recovered from `(F,H)` equals the printed `E` on 71/71 lattices (`checks/k1_controls.log`).

### R2. Definition 1.1, Proposition 1.2 — CORRECT
*Relations.* Weights: `b_{p−1}n` has weight `pw−p+1`, `b_0(Fn)` weight `pw−p−1`; `b_{p−1}(En)` weight `pw+p+1 = wt(b_0n)+2`. `[E,F]` on `b_j n` (`1≤j≤p−2`): `g_{j+1} − g_j = (j+1)(pw+p−j−1) − j(pw+p−j) = pw+p−1−2j`. On `b_0 n`: `EF = b_0 g_1`, `FE = (p/u)(pu) b_0 X = p² b_0 X`, difference `pw+p−1`. On `b_{p−1}n`: `EF = pu·(p/u) b_{p−1}EF n = p²(X+w)`, `FE = g_{p−1} = p²X + (p−1)(pw+1)`, difference `pw−p+1`. All are the weights. (b) `F^r(b_j n) = (pu)^c b_{j+r−pc}F^c n`, `c = ⌊(j+r)/p⌋`; `v_p(p^c c!/r!) = c + v_p(c!) − ⌊r/p⌋ − v_p(⌊r/p⌋!) ≥ 0` (Legendre; `x ↦ x + v_p(x!)` increasing, `c ≥ ⌊r/p⌋`).
**The closed formula for `E^{(r)}` (asked by the mission; the report gives only «`P(X,H)`»).** Write `Ω = 4FE + (H+1)²` (central; `= 4X + (w+1)²` on `n` of weight `w`). Then `g_j = (p²Ω − (p(w+1) − 2j)²)/4`, i.e. `g_j` is `(p²Ω_N − (H+1)²)/4` evaluated at the weight `pw+p−1−2j` of `b_j n`; equivalently the Casimir of `Φ_p(N)` is `p²·Ω_N` on every `b_j n`. Since `Ω` commutes with `E`, walking `E` from `b_j n` (indices `j, j−1, …, 1`, wrap to `p−1` with one `E` on `N` and a factor `p/u`, then `p−1, …, 1`, wrap, …) gives, for `r ≥ 0`,
  **`E^{(r)}(b_j n) = (p/u)^c (c!/r!) · b_{j''} E^{(c)} ∏_{(a,i)∈S(j,r)} [ p²X + (i − pa)(p(w+1+a) − i) ] n`,**
with `X = FE` and `w` taken on `n`, `c = ⌊(r+p−1−j)/p⌋` the number of wraps, `j'' = j − r + pc`, and `S(j,r)` the set of pairs (number `a` of wraps already made, current index `i ≥ 1`) met in the first `r` steps: `a = 0, i = j, …, 1`, then `a = 1, i = p−1, …, 1`, etc. (the factor of `(a,i)` is `(p²Ω − (p(w+2a+1) − 2i)²)/4` rewritten with `Ω = 4X+(w+1)²`). The polynomial is `∏ [p²X + (i−pa)(p(w+1+a)−i)]`, with integer coefficients; `v_p(p^c c!/r!) ≥ 0` because `c ≥ ⌊r/p⌋`; `E^{(c)}` of an integral vector is integral. **Integral for every `r`.** Checked by machine against the matrix powers of `Φ_p(L(b))`: 273812 (vector, `r`) pairs, `p = 3,5,7`, 0 failures; the control «`i` instead of `i−pa`» fails 1242/3456 (`checks/k1b.log`, `k1b_control.log`).
(c) `F^{(r)} ≡ [j+t≤p−1](1/t!) b_{j+t}F^{(s)}n` (`r = ps+t`): only `c = s` survives (`c = s+1` costs a factor `p`), and `(ps+t)!/(p^s s!) = ((p−1)!)^s t! ≡ (−1)^s t!` (the factors prime to `p` of `[1,ps+t]`; Wilson), with `u ≡ −1`. `E^{(r)}`: `c = s + [t ≥ j+1]`; for `t > j` the factor `p^{s+1}(s+1)!/r!` has positive valuation; for `t ≤ j` the `g`-factors are `≡ (i)(−i) = −i²`, a full cycle gives `∏_{i=1}^{p−1}(−i²) = (−1)^{p−1}((p−1)!)² ≡ 1`, the first partial run `∏_{i=1}^{j}(−i²)` and the last `∏_{i=j−t+1}^{p−1}(−i²)` multiply to `(−1)^t (j!/(j−t)!)²` (p odd), and the scalar is `≡ (−1)^s/(u^s(−1)^s t!) ≡ 1/t!`. So `E^{(r)}(b_j n) ≡ [t≤j](−1)^t (j!/(j−t)!)²/t! · b_{j−t}E^{(s)}n` — as printed. In `St = Δ(p−1)` with `b'_j = F^j b'_0 = j! e_j`: `F^{(t)}b'_j = b'_{j+t}/t!`, `E^{(t)}b'_j = j!·C(p−1−j+t,t)/(j−t)!·b'_{j−t}` and `C(p−1−j+t,t) ≡ C(−(j−t)−1,t) = (−1)^t C(j,t)` — the printed coefficient (the report's route via `i!(p−1−i)! ≡ (−1)^{i+1}` gives the same). With the coproduct, `F^{(r)}(b'_j⊗n) = Σ_β F^{(p(s−β)+t)}b'_j ⊗ F^{(β)}n`, and only `β = s` survives in `Δ(p−1)`; same for `E`. Weights agree (`p−1−2j + pw`). Machine: 273812 pairs, 0 failures; control (sign dropped) 344 failures.
(d) Basis `x_R = b_j e_s` (`R = ps+j`): `F x_R = x_{R+1}` (`j≤p−2`, and `R+1 ≢ 0`), `F x_{ps+p−1} = pu(s+1)x_{p(s+1)}` against `F e_R = p(s+1)e_{R+1}` in `Δ(pμ+p−1)`: ratios units; `x_L` is killed by `F` as `e_L`. The diagonal unit map commutes with `F, H`; Lemma 1.0(ii). `∇`: `λ−R = p(μ−s) + (p−1−j)`, same argument. Exactness: `Φ_p(f) = 1⊗f` commutes with `g_j` (a polynomial in `X` and the weight), hence with `E`. Machine: 33 filtration cases, 0 failures. **Verdict R2: CORRECT** (PRESENTATION: the closed `E^{(r)}` above should replace «`P(X,H)`»).

### R3. Definition 1.3, Proposition 1.4 — CORRECT
**(a) `[E,F] = H` on every case, by hand** (`w` = weight of `n`, `X = FE` on `N`, `EF n = (X+w)n`). Weight rules: the indices `p+j−1−r ∈ [p−r, p−1]`, `j−1−r ∈ [0,p−2−r]`, `j+r−1 ∈ [r,p−1]`, `j+r−1−p ∈ [0,r−2]` are in range, and every term has weight `+2` (checked term by term).
- `A_0`: `EF = A_0 g^A_1 n + r(p/u)C_{p−r}(En)`; `FE = (p/u)[pu A_0 Xn + p C_{p−r}En] − (p−r)(p/u)C_{p−r}En` (`F C_{p−1−r} = C_{p−r}` as `r ≥ 1`); the `C`-terms cancel (`p − (p−r) = r`), `g^A_1 − p²X = pw+p−1+r`. ✓
- `A_j`, `1 ≤ j ≤ r−1`: `C`-terms `r(p/u)C_{p+j−r}(En)` on both sides; `g^A_{j+1} − g^A_j = pw+p−1+r−2j`. ✓
- `A_r` (`r ≤ p−2`): `EF = A_r g^A_{r+1} + rp² C_0(Xn)`, `FE = A_r g^A_r + r(p/u)·pu C_0(FEn)`: same `C`-term. ✓
- `A_j`, `r+1 ≤ j ≤ p−2`: `rp²C_{j−r}(Xn)` on both sides. ✓
- `A_{p−1}` (both `r ≤ p−2` and `r = p−1`): `EF = A_{p−1}[p²(X+w) + pr] + C_{p−1−r}[−(p−r)p²(X+w) + p g^C_{p−r}]`, `FE = A_{p−1}g^A_{p−1} + rp²C_{p−1−r}(Xn)` (for `r = p−1` via the wrap `C_{p−1} → pu C_0`); `A`-bracket `p²w + pr − (p−1)(pw+r+1) = pw−p+1+r` ✓, `C`-bracket `p³X − (p−r)p²X − rp²X + p²(p−r)w − (p−r)p²w = 0` ✓.
- `C_0`: `EF = C_0 g^C_1 + rA_r`, `FE = rA_r + p²C_0 X`: `g^C_1 − p²X = pw+p−1−r`. ✓
- `C_j`, `1 ≤ j ≤ p−r−1`: `rA_{j+r}` on both sides. ✓
- `C_{p−r}` (`r ≥ 2`): `EF = C_{p−r}(g^C_{p−r+1}+rp) + rpu A_0(Fn)`, `FE = C_{p−r}g^C_{p−r} + r[pu A_0(Fn) + pC_{p−r}n]`: the `rp` and `A_0(Fn)` terms cancel. ✓
- `C_j`, `p−r+1 ≤ j ≤ p−2` (`r ≥ 3`): `(g+rp)` and `rpuA_{j+r−p}(Fn)` on both sides. ✓
- `C_{p−1}`: `EF = rpuA_{r−1}(Fn) + p²C_{p−1}(X+w)`; for `r ≥ 2`, `FE = C_{p−1}(g^C_{p−1}+rp) + rpuA_{r−1}(Fn)`; for `r = 1` (`p−1 = p−r`), `FE = C_{p−1}g^C_{p−1} + [puA_0Fn + pC_{p−1}n]` — the same; bracket `p²w − (p−1)(pw−r+1) − rp = pw−p+1−r`. ✓
`r = 1` and `r = p−1` are covered by the case list (for `r = 1` the cases `A_1…A_{r−1}`, `C_{p−r+1}…` are empty; for `r = p−1`, `A_r = A_{p−1}`). Machine: 569 lattices, 0 failures (`checks/k1_p*.log`).
**(b)** The two identities re-derived: `F^p γ(n) = pu[b̂_0⊗C'_1Fn + b̂_1⊗A'_{r−1}Fn + (p+r−pw) b̂_1⊗C'_0Fn] = pu γ(Fn)` (using `F^{p−1}C'_1n = puC'_0Fn`, `F^pA'_{r−1}n = puA'_{r−1}Fn + p²uC'_0Fn`); `F^pα(n) = pu b̂_0⊗A'_0Fn + p b̂_0⊗C'_{p−r+1}n + p b̂_1⊗A'_{p−1}n + p² b̂_1⊗C'_{p−r}Xn = puα(Fn) + pF^{p−r}γ(n)`. Lemma 1.0 then gives `E`-equivariance over `ℚ`. **Reduction:** `ῑ(A_jn) = b̂_0⊗A'_jn + j b̂_1⊗A'_{j−1}n`; `ῑ(C_jn)` has `b̂_0`-part `C'_{j+1}n` (`j ≤ p−2`) and `b̂_1`-parts on `C'_j, C'_{≤p−2}` only (the wraps of `F^jA'_{r−1}` carry a factor `p`); `ῑ(C_{p−1}n) = (p−1+r) b̂_1⊗C'_{p−1}n = (r−1)·(unit)` since `F^{p−1}A'_{r−1}n ≡ 0` exactly when `r ≥ 2`. On the `2p` coordinates per `n` named in the report the reduction is the identity except the entry `r−1`, a unit for `2 ≤ r ≤ p−1`: **`ῑ` is injective and the image is a direct summand (saturated)** — correct. A saturated `U_ℚ`-stable sublattice is `Dist_A`-stable, and injectivity over `ℚ` pulls stability back to `Ψ_r(N)`. Base `r = 1`: the map is unitriangular, commutes with `F` (including `F(b̂_0⊗b_{p−1}n + (p−1)b̂_1⊗b_{p−2}n) = pu b̂_0⊗b_0Fn + p b̂_1⊗b_{p−1}n = image of F(A_{p−1}n)`) and `H`. So **«`Ψ_r(N)` is a lattice for every lattice `N`» is correctly concluded** by induction on `r` (each step needs only that `V⊗Ψ_{r−1}(N)` is a lattice). Machine: 98 cases, exact equivariance, full rank mod p, unit determinant for `r = 1`: 0 failures (`checks/k1b.log`). Small remark: Lemma 1.0(ii) is stated for lattices; in the base case it is applied before `Ψ_1(N)` is known to be a lattice — harmless (pull `Dist`-stability back along the `A`-isomorphism), PRESENTATION.
**(c)** Correct. `V⊗T(p−2+r)` has Δ-factors `p−1+r, p−3+r, p+1−r, p−1−r`; `Ω` acts on `Δ(ν)` by `(ν+1)²`: `r²` on the first and last, `(r−2)²` on the middle two, and `(r−2)² ≡ r²` iff `r ≡ 1` (p odd). The generalized eigenspaces of the central `Ω` are summands; the generalized-eigenspace functor is exact, so `M_{r²}` has Δ-factors `p−1±r` and contains `T(p−1+r)`. If `T(p−1+r) ≠ M_{r²}`, then `T(p−1+r) = Δ(p−1+r)` would be tilting, hence `= ∇ = L` simple (a tilting Weyl module is simple: the non-zero map `Δ(λ) → ∇(λ)` has image `L(λ)`); but `F^{(r)}v` is primitive in `Δ(p−1+r)`: `E^{(s)}F^{(r)}v = C(p−1+s,s)F^{(r−s)}v` and `C(p−1+s,s) ≡ C(1,0)C(s−1,s) = 0` (Lucas, `1 ≤ s ≤ r ≤ p−1`). On `M⊗N̄^{[1]}`, `F, E` act as `0` on the twisted factor and `H ≡ H_M (mod p)`, so `Ω = Ω_M⊗1`. On `Ψ_r(N)`, `∏(Ω − (p(b+1)±r)²) = 0` over `ℚ` (character), hence `(Ω − r²)` is nilpotent mod `p`, and `ῑ(Ψ̄_r(N))` lies in the generalized `r²`-eigenspace `T(p−1+r)⊗N̄^{[1]}`; dimensions `2p·rank N`. Machine: `(Ω − r²)` nilpotent mod p in 98/98 cases. (Base `V⊗St = T(p)`: `V⊗St` is tilting with character `χ(p)+χ(p−2)`, and `Δ(p)` is not simple, so the summand `T(p)` is all of it.)
**(d)** Correct. `F^{(k)}(A_0n_0)` for `k < p(μ+1)` has the single `A`-coordinate `(pu)^s s!/k!·A_{k mod p}n_s` (a unit; Legendre), plus `C`-terms; for `k = p(μ+1)+t`, `0 ≤ t ≤ r−1`, every path branched once at some `A_{p−1}n_s` and then wrapped `μ−s` times in the `C`-string: each branch contributes `(pu)^s s!·p·(pu)^{μ−s}μ!/s! = p^{μ+1}u^μ μ!`, independent of `s`, so the sum is `p^{μ+1}u^μ(μ+1)!` and `F^{(k)}(A_0n_0) = (unit)·C_{p−r+t}n_μ`. The change of basis is block unitriangular; `A_0n_0` is a top-weight vector, so `Dist·A_0n_0 ≅ Δ_A(L+r)` (Lemma W) is saturated; the quotient has weights `≤ L−r`, `C̄_0n_0` is primitive there (`E(C_0n_0) = rA_{r−1}n_0 ∈` sub) and `F^{(k)}C_0n_0 = (unit)C_{k mod p}n_{⌊k/p⌋}` (no branching in the `C`-string). Machine: 33/33. **Verdict R3: CORRECT** (one PRESENTATION point in (b)).

### R4. Lemma 1.5 — CORRECT
Opened [DST] at each place. **Lemma 3.2 (W)** uses only (K) (Kostant's formula, char-free in `U_ℚ`) and the weight bounds `E^{(s)}x = 0`, `F^{(r)}x = 0` for `r > λ`: no `p`. **Lemma 3.3**: Weyl's theorem over `ℚ`; the weight projector `P(H) = Σ_r (Δ^rP)(w_0)C(H−w_0,r)` with integer forward differences (any `p`; `C(H−w_0,r) ∈ Dist_ℤ`); the duality `ι` (`Ext¹(Δ(λ),∇(μ)) ≅ Ext¹(Δ(μ),∇(λ))`); and `0 → N →(×2) N → N̄ → 0` — with `p` in place of `2` verbatim. **Corollary 3.4**: `gf ≡ 1 (mod p)` in the finite free `ℤ_p`-module `End(X)`, so `gf = 1 + ph` is invertible (geometric series; completeness). **Lemma 2.4**: the primitive vectors `F^{(r)}(v⊗b_0) = F^{(r)}v⊗b_0 + F^{(r−1)}v⊗b_1` and `E(v⊗b_1) = v⊗b_0`: no `p`. **Lift′** (one side Δ-filtered, the other a direct summand of a ∇-filtered lattice `Z = Y ⊕ Y'`): lift `X̄ → Ȳ ↪ Z̄` to `X → Z` by (Ext) (`Ext¹(X, Z) = 0`), compose with the projection `Z → Y` (it reduces to the projection), `det f̄ ≠ 0` ⇒ `det f` a unit ⇒ `f` an `A`-isomorphism commuting with `Dist_A`. Correct as stated. In Theorem 1.6(iii) it is used with `Y = Z = V^{⊗m}⊗ℤ_p` (∇-filtered by Lemma 2.4 and exactness of `V⊗−`), so the summand generality is not even needed.

### R5. Theorem 1.6 — CORRECT (citations to be made precise)
(i) Induction: `rank` multiplies by `p` (`Φ_p`) or `2p` (`Ψ_r`) from `rank Δ(d_k−1) = d_k`: `d_k p^k 2^{|I|}`; Δ-filtration by exactness and saturation (Props 1.2(a,d), 1.4(b,d)) — Weyl factors `b ↦ pb+p−1` or `pb+p−1±d_0`. Machine: rank and character on 569 lattices.
(ii) `L̄(λ) ≅ T(p−1+d_0)⊗L̄(b)^{[1]}` (Props 1.2(c), 1.4(c), `T(p−1) = St`), then Donkin. **Exact statement found and read** (`material/sources_from_previous_reading/STWZ_2105.07724.pdf`, Sutton–Tubbenhauer–Wedrich–Zhu, «SL2 tilting modules in the mixed case», §3A, **Proposition 3.4(a), formula (3-1)**): for `v = [a_j, …, a_0]_{p,ℓ}`, `T(v−1) ≅ T(a_j−1)^{(j)} ⊗ ⊗_{i<j} T(a_i + p∨ℓ − 1)^{(i)}`, the product over all non-leading digits (zero digits included), with `ℓ = p` when `q = ±1` (their §2, «ℓ = p for q = ±1»), i.e. for `SL_2` over a field of characteristic `p`; they cite [And19, Prop. 5.2], [TW20, Prop. 4.7]; the original is [Don93, Prop. 2.1] (cited so in Tubbenhauer–Wedrich arXiv:1907.11560, §1, p. 3). With `v = λ+1` this is `T(λ) ≅ ⊗_{t<k} T(p−1+d_t)^{[t]} ⊗ T(d_k−1)^{[k]}`, whose one-step form is `T(p−1+r+pb) ≅ T(p−1+r)⊗T(b)^{[1]}` for **every** `0 ≤ r ≤ p−1` and every `b ≥ 0`: **`r = 0` with arbitrary `b` is covered** (a zero digit gives the factor `T(p−1) = St`), and **`λ = p−1` is handled** (`v = [1,0]`: `T(p−1) = T(0)^{(1)}⊗T(p−1)`; in the report `L(p−1) = Φ_p(Δ(0)) ≅ Δ(p−1) = St` by Prop. 1.2(d)). Hypotheses fit. (Donkin's general statement needs `p ≥ 2h−2`, which for `SL_2` (`h = 2`) is every `p`. [Don93] itself is closed access (OpenAlex: no open copy) and I could not open it; but **H. H. Andersen, «Filtrations and tilting modules», Ann. Sci. ÉNS 30 (1997), Remark 1.1(ii)** (downloaded, `checks/downloads/Andersen1997/`, D1) restates it — for `p ≥ 2h−2` and `λ` restricted, `T_k((p−1)ρ+λ) ⊗ T_k(μ)^{[1]} ≅ T_k(p(μ+ρ)−ρ+λ)`, «compare [Do]» — with a proof sketch (`T_k((p−1)ρ+λ)` is the `G_1T`-projective cover of `L((p−1)ρ+λ)`, Jantzen II.11.11). For `SL_2` this is exactly `T(p−1+r) ⊗ T(b)^{[1]} ≅ T(p−1+r+pb)`, `0 ≤ r ≤ p−1`, every `b`.) The **Krull–Schmidt / classification** used in (iii): Heidersdorf–Wenzl arXiv:1912.09457, §5.3 **Proposition 5.1 (= [Jantzen, RAGS, Lemma E.6])**: for each `λ` a unique indecomposable tilting `T(λ)` with `T(λ)_λ` of rank one and weights `≤ λ`; every tilting module is uniquely a direct sum of these. `V^{⊗m}` is tilting (tensor products of tilting modules are tilting, ibid. §5.3). The report admits it did not open these references; the statements it uses are the right ones.
(iii) `X = ⊕L(λ)^{n_λ(m)}` (Δ-filtered), `Y = V^{⊗m}⊗ℤ_p` (∇-filtered), `X̄ ≅ Ȳ` by (ii) and the definition of `n_λ(m)`; Lift′. Correct. **Passage to `Y_p`:** the iso is one of `Dist_A`-lattices, so it carries `f = U` and `H`; on a summand `L(λ)` sitting at levels `k_0..k_0+λ` (`m = λ + 2k_0`), `q(c+H)+U = f + q(c+k_0+D_λ)`; [CS3] Lemma 2 (unit rescaling of floors; its proof uses only that `f` raises the floor by one, as [CS3] says in the proof of Theorem H) replaces `q(c+k_0+s)` by `p^{e}(c+k_0+s)` — both have the valuations `e + v_p(c+k_0+s)`. With `i = c + k_0` this is [CS3] §8. **Correct**, and it does not even need the abstract `T_{ℤ_p}(λ)`: (iii) gives the decomposition of `B_m⊗ℤ_p` with the explicit `L(λ)` directly.


### R6. Propositions 2.1, 2.2, 2.3 and Theorem D_p — CORRECT
Conventions checked: the relation of `x ι_{s'}` is `[g(Fx) + g(x)P(φ)]_{s'}` with `P_{ss'}` = coefficient of generator slot `s` in relation slot `s'` (lower triangular); for `p = 2`, `[P(2f)P(2f+1)]_{us'} = π_u(2f)K_{us'}(2f+1) + K_{us'}(2f)π_{s'}(2f+1) + Σ K_{us}(2f)K_{ss'}(2f+1)` is exactly [DST] Prop. 4.1's coupling (sign `−½` included).
- **Floors.** In `Φ_p(N')` (top weight `pb+p−1`) `b_jn` has floor `(pb+p−1−pw−p+1+2j)/2 = pf+j`; in `Ψ_r(N')` (top `pb+p−1+r`) `A_jn` is on `pf+j`, `C_jn` on `pf+r+j`; `C_{p−r}n` and `A_0(Fn)` both sit on `p(f+1)`, one floor above `A_{p−1}n`, as they must.
- **Pivots.** For `j ≤ p−2`, `F(b_jn) = b_{j+1}n`, `F(A_jn) = A_{j+1}n`, `F(C_jn) = C_{j+1}n` *exactly*: each such relation has coefficient `1` on one new generator and its other terms on the current index; the pivot block is unitriangular. **All pivots are exactly 1**; at the last level the pivots are `s+1 ≤ d_k−1 ≤ p−2`, units. (Machine: no pivot is ever chosen in my moves code; equality with the direct Smith form is checked in K4/K3.)
- **Signs.** `g_{j+1} = −g_jP(pf+j)` iterated `p−1` times: `(−1)^{p−1} = +1`; in the split, `c_{p−r} = (−1)^{p−r}c_0P(pf+r)⋯P(pf+p−1)` (`p−r` eliminations in the `C`-string), which is the sign of `K`. The last relations are `pu[·]`; dividing by the unit `u` is harmless. With `u = −1`: `a = (−1)^{p−1}/(up) = −1/p`, `b_r = (−1)^{p−r}/u = (−1)^r`.
- **Shapes.** `pu·a_0(Fn) + p·c_{p−r}(n) + a_{p−1}(n)P(pf+p−1) = pu[a_0(Fn) + a_0(n)Q_A(f) + c_0(n)K(f)]` and `pu[c_0(Fn) + c_0(n)Q_C(f)]` with `Q_A = a∏_{j=0}^{p−1}P(pf+j)`, `Q_C = a∏_{j=0}^{p−1}P(pf+r+j)`, `K = b_r∏_{j=r}^{p−1}P(pf+j)` (`p−r` factors). **No `C → A` coupling**: the `C`-string relations contain only `C`-generators (`F(C_jn)` has no `A`-component). Valuations `Q ∈ p^{p−1}M`, `K ∈ p^{p−r}M ⊂ pM`: even.
- **Last level** (Prop. 2.3) on `Δ_A(d−1)`: `g(e_{s+1}) = −g(e_s)P(s)/(s+1)`; the last relation is `g(e_{d−1})P(d−1) = 0` because `F e_{d−1} = d e_d = 0`; `M = (−1)^{d−1}((d−1)!)^{−1}∏_{s<d}P(s) ∈ p^dM`.
- **Count.** Move `t` eliminates `(p−1)·R_t·(1+[t∈I])·rank L(λ_{t+1}) = (p−1)d_kp^{k−t−1}2^{|I|}` pivots (independent of `t`'s digit), and the system after move `t` is multiplied by `p^{t+1}`: `(ℤ/p^h)^{(p−1)d_kp^{k−h−1}2^{|I|}}` for `1 ≤ h ≤ k−1` (move 0 gives trivial summands), `(ℤ/p^k)^{(d_k−1)2^{|I|}}` and `coker(p^kM)`. Matches the statement.
- Machine: the recursion of my moves code (`checks/k4_mp.py`, written from Props 2.1–2.3) equals my windows code entry by entry (K4) and, with the Smith form, reproduces SEALED_1 (K4) and the direct Smith form on `B_m` (K3).
**Verdict R6: CORRECT.**

### R7. Theorem I — CORRECT
Given Theorem D_p: `coker(p^kM)` has exactly `2^{|I|}` cyclic summands, each `ℤ_p` or of order `≥ p^{k+1}` (all Smith exponents of `M` are `≥ 1` since `M ∈ p^{d_k}M_{2^{|I|}}(ℤ_p)`, in particular in `pM`), and `S_p(λ)` has orders `≤ p^k`; uniqueness of elementary divisors. **p = 2:** [DST] Theorem D is stated «for every family λ, every α ≥ 1 and every shift i ≥ 0» (DST v10, §4.5, md line 426–430) and its `M` is the final matrix of an even payment system (Prop. 4.3: «an even payment system on `T(0)^{⊕2^{|I|}}`»), so `M ∈ 2M` and the same argument applies, for every `α ≥ 1`. (This closes the small gap the previous reader found in [CS3] §8 for `p = 2` — «every big clock exceeds `2^θ`» — by a one-line argument instead of a check.) **Count** `= d_kp^{k−1}2^{|I|} = dim T(λ)/p` for `k ≥ 1`: arithmetic re-done; for `k = 0` the count is `1` (one Jordan block on `Δ(λ)`, `λ ≤ p−2`), consistent with [CS3] §8. Hypotheses: `e ≥ 1`; odd `p` rests on Theorem 1.6 (Donkin, Jantzen E.6), `p = 2` on [DST] (unrefereed, same author, Lean-checked per its §12.3 — not re-checked by me).

### R8. PASO 4 (a1)–(a3) — CORRECT
**(a1)** Induction on `h`. In a product of consecutive payment matrices every entry is a sum over chains `D = T_0 ⊇ ⋯ ⊇ T_s = D'`; the window of `P_h(pf+j)_{T_jT_{j+1}}` ends at `p^{h+1}f+p^hj+o_{T_{j+1}}+p^h−1` and the next starts at `p^{h+1}f+p^h(j+1)+o_{T_{j+1}}`: adjacent, so every chain gives the same monomial in `π_0` and the coefficients sum to `[(c^{(h)})^s]_{D∖D'}` (`x_t² = 0`). Twist and `Q_A` (`s = p` from `pf`), `Q_C` (`s = p` from `pf+r`, slot `D∪{h}`, `o_{D∪{h}} = o_D + d_hp^h`), `K` (`s = p−r` from `pf+r`, pair `(D∪{h}, D')`, coefficient of `x_hx^{D∖D'}`), last level (`s = d_k` from floor 0, window `[o_D, o_{D'}+K−1]`, `K = d_kp^k`). Hence `c^{(h+1)} = a(c^{(h)})^p + [h∈I]b_hx_h(c^{(h)})^{p−d_h}`. Normalization: `a·a^{p(p^h−1)/(p−1)} = a^{(p^{h+1}−1)/(p−1)}` and the `x_h`-term carries `a^{(p−d_h)(p^h−1)/(p−1) − (p^{h+1}−1)/(p−1)} = a^{−1−d_h(p^h−1)/(p−1)} = (−p)^{1+d_h(p^h−1)/(p−1)}` (`a = −1/p`), which is absorbed by `y_h = −b_h(−p)^{1+d_h(p^h−1)/(p−1)}x_h`: `q_{t+1} = q_t^p − [t∈I]y_tq_t^{p−d_t}`, integer coefficients. Machine (K4 `windows`): windows = moves entry by entry and `c^{(h)} = a^{(p^h−1)/(p−1)}q_h(y)` coefficient by coefficient.
**(a2)** Re-derived. `[q_{m+1}]_Δ = −[q_m^{p−d_m}]_{Δ∖{m}}` (`m = max Δ`; `q_m` has no `y_m`). `[q^N]_Γ = Σ_{partitions of Γ into j blocks}(N)_j∏_B[q]_B`. For `N = p−d_m ∈ [1,p−1]` the one-block term has the unit `N`; for `N = p` (all later moves; the `y_t`-term, `t > max Δ`, does not touch `y^Δ`) `(p)_j` has `v_p = 1` for `1 ≤ j ≤ p` and vanishes for `j > p`. A `j`-block term has valuation `≥ jt − |Δ| − Σ_B min B ≥ (t − |Δ| − min Δ) + (j−1)(t − max Δ)`, strictly more than the one-block term. So `v_p = m − (|Δ|−1) − min Δ` at `t = m+1`, `+1` per move, and the final power `d_k` (a unit) changes nothing: `v_p([q_k^{d_k}]_Δ) = k − |Δ| − min Δ`. **Correct, independent of the digits.** Machine: K4 `windows`, every family.
**(a3)** Re-derived (Legendre `v_p(n!) = (n − s_p(n))/(p−1)`, Kummer `κ_p(a,b) = (s_p(a)+s_p(b)−s_p(a+b))/(p−1)`, `s_p(o_E) = Σ_{t∈E}d_t`, `s_p(K) = d_k`, and [DST] Lemma 5.1(a) `δ(Δ) = Σ_{t∈Δ}(h_t−1) + γ(Δ)`, which uses only `I`): the `s_p`-terms collapse to `κ_p(m,K) − κ_p(m,o_a) + κ_p(m+K,o_b)`, the `h`-terms to `Σ_{t∈Δ}h_t + γ`, giving `eK + κ_p(m,K) + R_m(a) − R_{m+K}(b) + γ(a∖b)`. For `i = 0`: the window contains `d = 0` iff `a = ∅`; `s_p(o_a−1) = Σ_{t∈a}d_t − 1 + (p−1)min a`, `κ_p(K−1, o_E) = k − min E` (positions `min E, …, k−1` carry, position `k` holds `d_k−1+1 < p`), giving `eK + R^♯(a) − R^♯(b) + γ`. **Non-vanishing in the support:** `[q_k^{d_k}]_Δ ≠ 0` (finite valuation by (a2)) and the window product vanishes only for `i = 0, a = ∅`. Machine: every entry of every cell of K4 `windows`.

### R9. Theorem 4.4 — CORRECT (PRESENTATION: the floor was only a list of changes; now written in full)
**Ceiling ([DST] §6).** Lemma 6.1, Theorem 6.2 (Theorem O), Corollary 6.3, Lemma 6.4, Theorem 6.5 are usable verbatim **given two facts**: (i) the cost form with non-vanishing of every entry in the support — **proved for odd p** in the report (Prop. 4.3, last sentence; I re-derived it in R8: the coefficient `[q_k^{d_k}]_Δ` has finite valuation by the deficit law and no window factor vanishes for `i ≥ 1`, or for `a ≠ ∅` when `i = 0`); (ii) **(O1): the o-order of `o_D = Σ_{t∈D} d_t p^t` is the binary order of the digit sets** (because `d_tp^t > Σ_{u<t}(p−1)p^u`), on which Theorem O's bit-clearing proof rests — true, but not stated in the report. Theorem O itself is a statement about `I` and `γ` only (tails = blocks of top bits).
**Floor ([DST] §7).** Written line by line in `checks/THEOREM_F_ODD_P.md`: houses; Lemma 7.5_p (penalties: the carry out of digit `k−1` runs through the digits `p−1` of `m` from digit `k`); Lemma 7.6_p (the **four types OR, DIG, AND, NEV** by `θ_t = p − ℓ_t` against `d·d_t + c_t ∈ {0,1,d_t,d_t+1}`; `κ_t = 1 + min(r_{t+1}(ℓ), h_t−1)` for every type; carry leaves iff saturated); Lemma 7.7_p (top digit, `τ = h − e d_cp^c − [OR∨DIG]κ`, the `J`'s, `d_1, d_2`); Theorem F_p by induction, steps 1–8, with `(Λ_p) |ŷ_H| ≤ e·o_I`; Lemma 7.9_p (integrality); Theorem 7.10_p (with `i = 0` through the house `ℓ = p^k − 1`: all windows OR and saturated, `J = [D ≠ ∅]`). **The report's list is enough in substance:** each listed change is right, including the claim to check most carefully — **DIG with sat = 1 falls into case 3(b)** (that case uses only `d_1 ≡ e d_cp^c` on the first half and `J_H = (0,1)`), and **DIG with sat = 0 and NEV fall into 3(d)** (`J_H ≡ 0`); also AND with `J' ≡ 0` lands in 3(d), as for p = 2. Where the list was not enough: only (O1) for the ceiling, and the fact that the list was never expanded into a proof (now done). K6 checks every step (47310 houses, the potential of my proof included; controls fire).

### R10. Theorem TOTAL and `Syl_p K(H(d,q))` — CORRECT
`coker L(H(d,q)) ≅ ⊕_j X_q(d−j, j)^{C(d,j)(q−2)^j}` ([CS3] Thm A = [JNR03] Thm 13); `⊗ℤ_p`; `X_q(m,c)⊗ℤ_p = ℤ_p^{[c=0]} ⊕ Syl_p X_q(m,c) ≅ ⊕_λ Y_p(λ, c + (m−λ)/2, v_p(q))^{n_λ(m)}` (Theorem 1.6(iii) + [CS3] Lemma 2, which needs only the valuations `e + v_p(c+k+s)` of the floor payments, so `q = p^eu` may be replaced by `p^e`); the only `c = 0` piece is `j = 0`, multiplicity `C(d,0)(q−2)^0 = 1`, giving the single free `ℤ_p` (`λ = d`, `i = 0`); `n_λ(m)` by peeling the Donkin characters from the top (they are unitriangular). For `q = 2` only `j = 0` survives. K5: 12 whole groups with `d ≥ p²+p` match Kirchhoff and the 𝔽_p-rank count exactly; the `e+1` control fails.

### R11. Grades — PRESENTATION
- #1–#3, #5, #8, #9, #10, #12–#14, #16: «PROVED (pencil)» — confirmed by my re-derivations.
- #6 (Theorem 1.6): «PROVED (pencil), citing [Don93], [Jan03] … I did not open these references» — honest; the cited statements are the right ones (R5); but the abstract part (existence/uniqueness of `T_{ℤ_p}(λ)`, lifting of decompositions) is classical (Andersen 1997 §1.2; Jantzen E.19–E.22) and should be credited, the novelty being the explicit lattices.
- #11 («PROVED (pencil; arithmetic)»): right; the count itself is known (Jordan blocks of `f` on a `G_1`-projective module).
- **#15 «PROVED (pencil, adaptation of DST §7, changes written out)»: stronger than what existed** — the report itself says the floor was «not rewritten line by line, and nobody has read it cold». It is now proved (R9), so the claim stands, but the grade was premature.
- #17 («PROVED (pencil), with the provisos of #6 and #15»): right with those provisos, which are now discharged (#6 by citations, #15 by `checks/THEOREM_F_ODD_P.md`).
- MEASURED items (#7, #9, #16, #18): all reproduced by my own code (K1, K4, K5); SEALED files: md5 verified (K7); «blind» cannot be verified from outside.
- #20 («one search»): honest; my sweep (JOB 3) confirms the absence of a prior Smith form or integral twist functor.
- No statement of the report is contradicted; the only mathematical omission I found is (O1) in R9.

## JOB 2 — computations (K1–K7)

Summary of my computations (every engine is my own, written from the printed definitions; logs end with `VIGIA-FIN-OK` unless stated; details, estimates and slips are in the step log below):
- **K1** — `checks/lat.py`, `k1.py`, `k1_controls.py`, `k1b.py`: 569 lattices, all checks 0 failures; controls fire (coupling p² / 0: 84/84 each; twist without p: 18/23, 5 vacuous). Closed `E^{(r)}` and reductions: 273812 pairs.
- **K2** — `checks/k2.py`: 62/62 identified as `T(λ)` by tilting + local End (no Donkin); controls fire.
- **K3** — `checks/psmith.c`, `psmith128.c`, `k3.py`: predictions sealed in `checks/K3_PREDICTIONS.txt` (22:12:35, md5 `fb7cf75162e4f9dadfa0224f4180b862`) then computed: **31/31 agree, 0 disagree**; engine validated on 41 + 16 + 40 proved-range cells.
- **K4** — `checks/k4_formula.py`, `k4_mp.py`, `k4_run.py`, `k4_fast.py`, `k4_control.py`: formula = Theorem G (18540), = DST (7236), = SEALED_2 (all 10710; random 300), SEALED_1 = my moves (1520/1520), windows = moves (4836 cells), Smith(`M_p`) + small part = formula on ≈ 34000 cells (p = 3: λ ≤ 360 and 381–390 plus the parts of 361–400 listed in STEP 6c; p = 5, 7: λ ≤ 400); 0 mismatches; controls fire.
- **K5** — `checks/k5.py`: 12/12 Hamming groups (d ≥ p²+p) match Kirchhoff + 𝔽_p-rank; control fires; `k5b`, `k5c`: report's H(12,3), [CS3] §10, previous reader's 14 blocks reproduced.
- **K6** — `checks/k6.py`: 47310 houses, 0 failures, four types occur, controls fire.
- **K7** — `checks/k7_md5.py`: md5 match.


## JOB 3 — literature (L1–L4)

Sweep done 22:21–22:49 (all searches in `checks/SEARCHES.md`, raw answers in `checks/lit/`, downloads in `checks/DOWNLOADS.md`). Engines reached: arXiv API (40 subject queries + 18 author queries), Hexagon (complete listing of all 139 deposits through its API + 7 queries), zbMATH Open API, OpenAlex (keyword search, dissertations filter, forward citations of 11 seed works, author work lists of 10 people), Zenodo API, HAL API, CORE API (word queries; its phrase syntax is rejected), StackExchange API (MathOverflow, Math.SE), GitHub repository search, general web search (as a stand-in for Google Scholar, which cannot be queried by tool), FPSAC (DMTCS proceedings) by web search, home pages (Reiner's publication page; Sin's research page; Ducey's page — DNS failure, replaced by his arXiv/OpenAlex lists; Tubbenhauer — page 404, replaced by his 69 arXiv items; Donkin, Andersen, Jantzen, S. Martin, Levine, Perkinson — through OpenAlex/arXiv author lists). **Not reachable:** Semantic Scholar (HTTP 429 rate limit without a key, even with 15–30 s pacing), BASE (Anubis bot check), OATD (Cloudflare/403) — not bypassed; their coverage is replaced by OpenAlex. Forward citations: JNR03 (45 citers), Ducey–Gerhard–Watson (8), Ducey–Jalil (13), Chandler–Sin–Xiang (9), Bai 2003 (35), STWZ (12), Tubbenhauer–Wedrich (5), S. Martin I (2) and II (0), Donkin 1993 (319, filtered by keywords), GMMY (1 + 1) — all titles read, abstracts opened where relevant.

### L1. Integral tilting lattices — PARTLY KNOWN (existence classical; explicit lattices and integral twist functors NOT FOUND)
- **Existence, uniqueness and Krull–Schmidt of tilting lattices over ℤ_p (and over complete DVRs) are classical:** H. H. Andersen, «Filtrations and tilting modules», Ann. Sci. ÉNS 30 (1997), **§1.2** (downloaded, D1): «The tilting modules T_k(λ) also lift to G_{ℤ_p}. In fact, the Ringel construction (which even works over ℤ, see [Do]) gives an indecomposable tilting G_{ℤ_p}-module T_{ℤ_p}(λ)», with T_{ℤ_p}(λ) ⊗ k ≅ T_k(λ), uniqueness, and unique decomposition of every tilting G_{ℤ_p}-module; also Jantzen RAGS II.E.19–E.22, B.9–B.10 (as quoted in Heidersdorf–Wenzl arXiv:1912.09457, §5.3–5.5: Prop. 5.1, Lemmas 5.2–5.3, Cor. 5.5). For quantum groups: Andersen–Papadopoulo, «Liftings of quantum tilting modules» (2000, Zbl 1007.17009); P. Fiebig, «Quantum tilting modules over local rings» (arXiv:2207.14516, JLMS 2023) and «Tilting modules and torsion phenomena» (arXiv:2009.08677). **So the report's Lemma 1.5 / Theorem 1.6(iii) (`L(λ) ≅ T_{ℤ_p}(λ)`, `V^{⊗m}⊗ℤ_p ≅ ⊕ T_{ℤ_p}(λ)^{n_λ}`) re-proves known facts for SL_2** (by an elementary route, as [DST] did for p = 2).
- **Explicit ℤ_p-forms (explicit bases and E, F, H) of every SL_2 tilting module for odd p, and integral Frobenius-twist / split functors like Φ_p, Ψ_r: NOT FOUND** — searched: arXiv (`all:"integral tilting"`, `"tilting modules" AND "p-adic"`, `"tilting modules" AND SL2 AND (integral OR lattice)`, `"Frobenius twist" AND (lattice OR "integral form")`, `"Weyl filtration" AND lattice`, `"tilting" AND "Kostant form"`, `"hyperalgebra" AND "tilting"`, p-JW / mixed case), zbMATH, OpenAlex, Zenodo, HAL, CORE, MathOverflow; the closest are the p-JW projectors of Burrull–Libedinsky–Sentinelli (arXiv:1902.00305, over 𝔽_p, idempotents in TL_n, not lattices), STWZ (fields), Tubbenhauer–Wedrich (𝔽_p), S. Martin I/II (fields), Doty 0909.2239 (fields), McNinch, «Faithful representations of SL2 over truncated Witt vectors» (J. Algebra 2003; abstract not indexed — by its title a different question). The p = 2 analogue (Φ, V ⊗ Φ) is the author's own [DST] §3.1, §3.3.

### L2. The critical group of the Hamming graph at p | q — PARTLY KNOWN only for d = 2 (and for the author's own earlier preprints)
- **d = 2 (rook's graph K_q × K_q): ALREADY KNOWN** — Ducey–Gerhard–Watson, arXiv:1507.06583 = EJC 23(4) (2016) #P4.9, Thm 1.1 (whole K(R_n)); also derivable from JNR03 Thm 13 + Ex. 11 (as the previous reader found).
- **p ∤ q: JNR03 Theorem 2** (not claimed by the report).
- Everything else (d ≥ 3 at p | q; the whole Syl_p for every d; Theorem D_p; Theorem I; the deficit law; the cost form; Theorem TOTAL): **NOT FOUND** outside the author's own [CS3] (Zenodo 10.5281/zenodo.23329314; Theorems B, G, H, Conjecture I) and [DST] (hexagon:2610.00205; Zenodo 23298437). Searched: arXiv (Hamming graph(s) × critical/sandpile/Smith/Jacobian; rook's graph; critical group × complete graphs / Cartesian product / distance-regular / Cayley graph; Smith normal form × Boolean lattice / up operator / Hamming scheme / tensor power; inclusion matrices × Smith; Jordan type × tensor power), Hexagon (all 139 deposits), zbMATH, OpenAlex (+ dissertations), Zenodo, HAL, CORE, MathOverflow/Math.SE, GitHub, FPSAC (DMTCS: only Duval–Klivans–Martin, simplicial complexes), all citers of JNR03, DGW, DJ14, CSX15, Bai03. Nearest work: Ducey–Jalil (p ∤ |G|), GMMY and Betzer (Cayley graphs of 𝔽_2^r, p = 2), Ducey et al. (strongly regular graphs: d = 2), Agarwal–Gaetz (differential posets).
- Side notes for the author: (i) D. Betzer, Zenodo 10.5281/zenodo.22065778 (23 Aug 2026) claims to close GMMY Conjecture 4.14 for the hypercube — relevant to [DST]'s priority list (claim 3 of DST §1.8), not to this report; (ii) OpenAlex attaches the title of [CS3] to the DOI of CSX15 (arXiv:1511.00272, year 2015) — a metadata conflation worth reporting to OpenAlex, not a prior publication.

### L3. Smith forms on tilting modules — NOT FOUND
No computation of the Smith form of `f + p^e(D+i)` (or of `q(c+H)+U`-type operators) on tilting modules or on `V^{⊗m}` over ℤ_p, other than the author's [CS3]/[DST]. The nearest objects in the literature are **elementary divisors attached to integral tilting modules of a different map**: Andersen's filtration of `Hom(V_{ℤ_p}(λ), Q)` by the elementary divisors of the pairing with `Hom(Q, H^0_{ℤ_p}(λ))` (Andersen 1997 §1.3–1.4; sum formula: Andersen, «A sum formula for tilting filtrations» (2000); Andersen–Kulkarni, Adv. Math. 2008), and the Smith forms of inclusion matrices (Wilson 1990; Ghorbani et al. 2007; Ducey et al. arXiv:2310.09227). Searched: arXiv (`"Smith normal form" AND "tilting"` → 0; `"Smith normal form" AND "tensor power"` → 0), zbMATH («Smith normal form tilting module» → none), OpenAlex (7 hits, none relevant), CORE (noise), MathOverflow (none).

### L4. Priority table — see the summary «Priority table (L4)» at the top of this report.


## Log of steps

## STEP 0 — STATE: DONE (Tue Oct 13 21:34 CEST 2026)
Read CLAUDE.md, MISSION.md, vigia.sh; md5 of every file in material/ matches MANIFEST_md5.txt (checks/md5_material_at_start.txt). Read material/REPORT_ODD_DANCE.md in full (328 lines). Decision: no agents/subagents/workflows (MISSION §0, CLAUDE.md), even though the environment announces «ultracode».

Error of my own (disclosed at once): at 21:34 a shell command of mine created an empty file `REPORT_COLOURED_SAND_2.md.tmp` by accident (a stray `cat >>` with an empty heredoc) and the same command removed it with `rm`. It was an empty file I had just created, never part of the material; but the rule says «never delete files», and I broke it once. No other file has been or will be removed.

## STEP 1 — STATE: DONE (Tue Oct 13 21:34–21:49 CEST 2026, end time from `date`)
Read in full: `material/MISSION_GIVEN_TO_THE_CONSTRUCTOR.md`; [CS3] `THE_COLOURED_SAND_THEOREM_v3.md` (all 527 lines); [DST] `THE_DANCING_SAND_THEOREM_v10.md` §1–§8 (lines 1–692: notation, §2 dictionary, §3 doubling functor and lifting lemmas, §4 dance and Theorem D, §5 cost form, §6 ceiling, §7 floor, §8 assembly). Skimmed (context only, not authority) `PREVIOUS_COLD_READING_OF_v3.md`: it already found (i) Donkin's theorem at [Don93, Prop. 2.1] and STWZ arXiv:2105.07724 Prop. 3.4(a); (ii) the lifting over complete DVRs at Jantzen RAGS II.E.19–E.22 via Heidersdorf–Wenzl arXiv:1912.09457 §5.4; (iii) `d = 2` (rook's graph) is Ducey–Gerhard–Watson arXiv:1507.06583; (iv) it computed the blocks `λ = 12` (`q = 9, 27`, `c = 0..6`) and `λ = 13` (`q = 3, 9`) for `p = 3` directly — I will use these only as extra comparison data, after my own computations.
Plan (all by me, no agents): JOB 1 by hand (R1–R11) with symbolic/numeric confirmation; K1 lattices engine; K4 closed-formula engine (+ Theorem G, DST rule, windows and moves for `M_p`); K6 houses and the potential of Theorem F_p; K3 sealed predictions, then a C engine for the Smith form of `q(c+H)+U` on `B_m`; K5 Hamming groups (Kirchhoff + `𝔽_p`-ranks); K2 (tilting + local endomorphism ring); K7 md5; JOB 3 literature; `checks/THEOREM_F_ODD_P.md`.

## STEP 2 — K7 md5 — estimate (written before running, Tue Oct 13 21:50 CEST 2026)
`checks/k7_md5.py`: md5 of `material/SEALED_1.txt`, `material/SEALED_2.txt` vs the md5 printed in the report; cell counts per prime. Expected: both MATCH; 1520 cells (p=3: 552, p=5: 968) and 10710 cells (p=3: 2560, p=5: 3300, p=7: 3270, p=11: 1176, p=13: 404). Estimate < 20 MB, < 2 s.
Second stray file of mine (disclosed): at 21:50 another empty heredoc created an empty `REPORT_COLOURED_SAND_2.md.new`; not deleted — moved to `checks/_old/EMPTY_stray_file_REPORT_COLOURED_SAND_2.md.new`. I stop using `cat >>` heredocs for the report.

## STEP 2 — STATE: DONE (Tue Oct 13 21:50 CEST 2026)
K7: `checks/k7_md5.log` — SEALED_1 md5 `0a9c3442e54c54c8cc880d9b2bc070b0`, SEALED_2 md5 `2f931de9eb3933c51a4ff3efb03274ab`: both MATCH the report (each md5 is printed 4 times in it); 1520 cells (3: 552, 5: 968) and 10710 cells (3: 2560, 5: 3300, 7: 3270, 11: 1176, 13: 404), no duplicate cells; the headers carry the times 20:08:00 and 20:17:05. Caveat: the md5 only proves that the files did not change after the report was written; that they were written before the computations cannot be checked from outside.

## STEP 3 — STATE: DONE — K1 engine, smoke test and full runs — estimate (Tue Oct 13 21:52 CEST 2026, written before running)
`checks/lat.py` (my implementation of Defs 1.1, 1.3 and of L(λ), exact integers, u = −1) and `checks/k1.py 3 60` (p = 3, every λ with dim T(λ) ≤ 60). Expected: 0 relation, character and integrality failures. Estimate < 100 MB, < 60 s.

Result `checks/k1_smoke.log`: p = 3, 30 lattices (λ ≤ 53): 0 failures, min v_p(X^r) − v_p(r!) = 0 for E and F; 0.1 s, 7 MB.
Estimate for the full K1 runs (Tue Oct 13 21:53 CEST 2026): `k1.py P 600` for P = 3, 5, 7 separately (every λ with dim T(λ) ≤ 600, twice the mission's 300). Expected: 0 failures each. Estimate each < 300 MB, < 400 s (split by p; if killed, lower the cap).

Results (Tue Oct 13 21:57 CEST 2026): `checks/k1_p3.log`, `k1_p5.log`, `k1_p7.log`, all `VIGIA-FIN-OK`: **p = 3: 134 lattices (λ ≤ 485), p = 5: 200 (λ ≤ 499), p = 7: 235 (λ ≤ 342), every λ with dim T(λ) ≤ 600: sl_2 relations (including that E raises and F lowers weights by 2) 0 failures; character = Donkin product, rank = d_k p^k 2^{|I|}, top weight λ: 0 failures; integrality of X^r/r! for X = E, F and EVERY r (exact integer weight-block products): 0 failures; the minimum of v_p(X^r) − v_p(r!) is exactly 0 for E and for F (so the divided powers are integral and not all divisible by p).** 66 s, 88 s, 106 s; peak 9–12 MB.

## STEP 4 — K1 controls and proposition checks — estimate (Tue Oct 13 21:58 CEST 2026)
(a) `checks/k1_controls.py 40`: for every λ with dim T(λ) ≤ 40 (p = 3, 5, 7): the printed lattice and the controls «coupling p → p²», «coupling p → 0» (all split moves, and outermost only), «twist without p»; for each, the printed-E relation failures and the E recovered from (F, H) alone over ℚ (exact rref; unique by Lemma 1.0 if it exists) with the p-integrality of all its divided powers. Expected: printed lattice: 0 failures, E_rec = printed E, min v_p = 0; controls: relation failures > 0 with the printed E, and either no sl_2-structure or a non-integral E_rec. Estimate < 200 MB, < 300 s.
(b) `checks/k1b.py`: R2(b) my closed formula for E^r, F^r on Φ_p(N); R2(c) reductions mod p; R3(b) ι and the r = 1 map (exact E, F, H-equivariance, rank mod p, unit determinant); R2(d)/R3(d) the Δ-filtrations; R3(c) (Ω − r²) nilpotent mod p. Expected: 0 failures. Estimate < 200 MB, < 300 s.

Results (Tue Oct 13 22:00 CEST 2026):
(a) `checks/k1_controls.log` (a first run, which checked only E^(r) and not F^(r) of the controls, is kept in `checks/_old/k1_controls_first_run_without_F_check.log`): 71 printed lattices (dim ≤ 40, p = 3, 5, 7): 0 relation failures, E recovered from (F, H) unique and **equal to the printed E in 71/71**, all divided powers integral. Controls: **coupling p → p²: 44/44 (all moves) and 40/40 (outer move only) fail** (printed-E relations fail; E from (F,H) exists, unique, and is NOT p-integral); **coupling p → 0: 44/44 and 40/40 fail** (printed-E relations fail; (F, H) admit NO sl_2-structure at all); **twist without p: 18/23 not Dist-stable** (F^(p) non-integral; E_rec itself is integral there); the 5 survivors are exactly the vacuous cases where the twist acts on Δ(0) (F_N = 0): λ = p−1 for p = 3, 5, 7 and λ = 9, 10 for p = 3. Peak 50 MB, 1 s.
(b) `checks/k1b.log`: **E-closed formula (R2(b)) and F^r formula: 273812 (basis vector, r) pairs on Φ_p(L(b)), p = 3, 5, 7: 0 failures; reductions mod p (R2(c)): 273812 pairs, 0 failures; ι and the r = 1 map (R3(b)): 98 cases (p = 3, 5, 7, every r, N = L(b)): exact E, F, H-equivariance, ῑ of full rank 2p·rank N, det of the r = 1 map a unit: 0 failures; Δ-filtrations (R2(d), R3(d)): 33 cases (μ ≤ 2p, every r): 0 failures; Casimir (R3(c)): (Ω − r²) nilpotent mod p on Ψ_r(N), 98 cases: 0 failures.** 79 s, 49 MB. Control `checks/k1b_control.log` (K1B_CONTROL=1: the factor (i − pa) replaced by i in the E-formula, and the sign (−1)^t dropped in the reduction): **1242/3456 and 344/3456 failures** (p = 3) — the checks can fail.

## STEP 4 — STATE: DONE (Tue Oct 13 22:00 CEST 2026)

## STEP 5 — STATE: DONE (JOB 1 R1–R5 written into the JOB 1 section, Tue Oct 13 22:02 CEST 2026)

## STEP 6 — K4 engine smoke test — estimate (Tue Oct 13 22:05 CEST 2026)
`checks/k4_formula.py` (Theorem TOTAL from the printed notation of PASO 4 only; Theorem G of [CS3] §6 from its text; [DST] §1.2 raw-clock rule and the R-form of [DST] Thm 7.10; n_λ(m) by peeling Donkin characters), `checks/k4_mp.py` (M_p by the moves of Props 2.1–2.3 and by the windows of Theorem 4.1, exact rationals; q-polynomial; exact p-adic Smith form), `checks/k4_run.py smoke` (p = 3, 5, λ ≤ 40, small e, i). Expected: 0 failures everywhere. Estimate < 100 MB, < 60 s.

Result `checks/k4_smoke.log` (22:06): windows = moves entrywise, deficit law, normalization `c^(h) = a^{(p^h−1)/(p−1)} q_h(y)`, cost form: 0 failures (p = 3, 5, λ ≤ 40); Smith(M_p) + small part = my closed formula in 738/738 cells; closed formula = Theorem G in 432/432; at p = 2 = DST (R-form and raw-clock rule) in 248/248. 0.5 s.
Controls `checks/k4_control.py` → `checks/k4_control.log` (**slip of mine: this 21 s, 13 MB run was started at 22:06:18 before its estimate was written here**): against Smith(M_p) + small part, p = 3 (λ < 120), p = 5 (λ < 160), e ∈ {1,2}, i ∈ {0,1,2,4,9}, 2800 cells: (a) no pooling: 117 differ; (b) K := p^k: 1304 differ; (c) κ_p(i, K) instead of κ_p(i−1, K): 48 differ; (d) no (ℤ/p^k)^{(d_k−1)2^{|I|}} term: 1290 differ. The comparison can fail.
Estimates for the full K4 runs (Tue Oct 13 22:07 CEST 2026), each alone under the watchdog:
- `k4_run.py G` (closed formula vs my Theorem G, p ∈ {3,5,7,11,13}, every λ ≤ p²+p−1, e ≤ 3, i ≤ 14): < 50 MB, < 60 s; expected 0 mismatches.
- `k4_run.py dst` (p = 2, λ ≤ 200, α ≤ 4, i ≤ 8, vs DST R-form and raw-clock rule): < 50 MB, < 60 s; expected 0.
- `k4_run.py sealed2 300 20261013` (300 random SEALED_2 cells, seed 20261013) and `sealed2 99999 1` (all 10710): < 100 MB, < 120 s; expected 0 mismatches.
- `k4_run.py sealed1` (all 1520 SEALED_1 cells by my moves + Smith): < 300 MB, < 500 s; expected 0.
- `k4_run.py windows` (p = 3 λ ≤ 120, p = 5 λ ≤ 160, p = 7 λ ≤ 120; e ∈ {1,2}; i ∈ {0,1,2,3,5,9}): < 300 MB, < 500 s (split if killed); expected 0 failures.
- `k4_run.py fit P LO HI` (Smith of M_p by the moves + small part vs closed formula; e ∈ {1,2,3}; 15 values of i up to 243, to exercise the carry penalties r_k(m)): p = 3 in ranges of λ up to 400, p = 5 up to 300, p = 7 up to 200; each < 300 MB, < 550 s; expected 0 mismatches.

Results so far (22:07–22:10): `checks/k4_G.log`: **closed formula = my Theorem G in 18540/18540 cells** (p ∈ {3,5,7,11,13}, every λ ≤ p²+p−1, e ≤ 3, i ≤ 14). `checks/k4_dst.log`: **p = 2, 7236 cells (λ ≤ 200, α ≤ 4, i ≤ 8): = DST R-form in all; = DST raw-clock rule (§1.2, α = 1) in all 1809 α = 1 cells.** `checks/k4_sealed2_300.log`: **300 random SEALED_2 cells (seed 20261013): my closed formula gives the sealed value in 300/300**; `k4_sealed2_all.log`: all 10710/10710. `checks/k4_sealed1.log`: **SEALED_1, 1520/1520 reproduced by my moves + exact Smith form**. `checks/k4_windows.log`: **windows = moves entry by entry, deficit law, normalization, cost form, non-vanishing on the support: 4836 cells, 73632 entries (p = 3 λ ≤ 120, p = 5 λ ≤ 160, p = 7 λ ≤ 120; e ∈ {1,2}; i ∈ {0,1,2,3,5,9}): 0 failures.**
Two more slips of mine: `checks/k4_timing.py` (14 s, 14 MB: the moves route needs ~7 s per cell when |I| = 5) and `checks/k4_fast.py crosscheck 12` (17 s, 14 MB) were run at 22:09 and 22:10 before their estimates were written. Results: the fast route (`checks/k4_fast.py`: M_p by the windows formula, integer scaling, Smith form modulo p^B with B > every finite exponent) equals the moves route on 36/36 large cells (`checks/k4_fast_cross.log`).
Estimate (Tue Oct 13 22:11 CEST 2026, before running): `k4_fast.py fit P LO HI ES IS` — Smith(M_p) + small part vs my closed formula: p = 3, λ ∈ [0, 400], e ∈ {1,2,3}, i ∈ {0,1,2,3,4,7,10,26,27,28,80,81,82,242,243} (18045 cells), split in λ-ranges [0,241], [242,320], [321,400]; p = 5, λ ∈ [0, 400] same e, i ∈ {0,1,4,5,24,25,26,124,125}; p = 7, λ ∈ [0, 400], i ∈ {0,1,6,7,48,49,50,342,343}. Expected 0 mismatches. Each < 200 MB, < 550 s (re-split if killed).

(next step, as planned at that time) STEP 6 — K4 fit runs (running).

## STEP 7 — K3 engine validation — estimate (Tue Oct 13 22:12 CEST 2026, written before running; runs while the p = 3 fit run is still going)
`checks/psmith.c` (compiled with clang -O3 under the watchdog, `checks/psmith_compile.log`): exact p-adic Smith form of `q(c+H)+U` on `B_m` built from its definition (bitmask subsets), modulo `p^M` (M = 39 for p = 3, 62 for p = 2), level-by-level unit-pivot elimination; for exponents ≥ M it also computes the Smith form of `p^E (q(c+H)+U)^{−1}` (closed form of [CS3] Lemma 4), whose exponents are `E − a_i`, and checks the overlap. Driver `checks/k3.py validate`: proved range only (p = 3, m ∈ {5,8,9,10,11}, (c,q) ∈ {(0,3),(1,3),(2,9),(5,6),(1,27)}; p = 2, m ∈ {4,6,8,9}, (c,q) ∈ {(0,2),(1,4),(3,8),(2,12)}): direct vs closed formula and (p = 3) vs Theorem G. Expected: 0 disagreements. Estimate < 150 MB (B_11: 2048² × 8 B = 34 MB), < 120 s.
Result `checks/k3_validate.log` (22:11): **41/41 proved-range cells: direct Smith form on B_m = closed formula (and = Theorem G for p = 3)**; B_11 in 0.5 s; reproduces [DST]'s example `Syl_2 K(Q_6) = {1:12, 2:4, 3:1, 5:4, 6:10}` (cell p=2 m=6 c=0 q=2). The inverse path was not exercised there.
Estimate (Tue Oct 13 22:13 CEST 2026): `k3.py validate_inv` — same comparison with the precision lowered to M = 20 (p = 3) / 24 (p = 2), which forces the inverse-matrix path for the large exponents; p = 3, m ∈ {9,10,11}, (c,q) ∈ {(1,27),(2,9),(4,54),(7,3)}; p = 2, m ∈ {8,9}, (c,q) ∈ {(3,8),(1,16)}. Expected 0 disagreements and no overlap inconsistency. < 100 MB, < 60 s.
Result `checks/k3_validate_inv.log` (22:12): **16/16 cells with the precision forced down (M = 20 / 24): the inverse path, combined with the normal run and with the overlap checked, gives the closed formula (and Theorem G) every time.**
Estimate (Tue Oct 13 22:14 CEST 2026): `k3.py predict checks/K3_PREDICTIONS.txt <cells>` — writes the closed-formula prediction for 30 new cells (no Smith form computed): p = 3, m = 12: (c,q) = (1,27), (3,27), (4,27), (2,54), (5,54), (7,3), (8,3), (9,3), (10,3), (12,3), (13,3), (0,9), (5,9), (8,9), (9,6), (11,12), (4,15), (1,81), (2,81); p = 3, m = 13: (2,3), (4,3), (1,27), (0,6); p = 2: (7,1,4), (7,2,8), (8,3,12), (10,0,4), (10,5,8), (12,1,4), (12,2,24), (13,1,8). < 50 MB, < 10 s.

**K3 SEALED PREDICTIONS** — `checks/K3_PREDICTIONS.txt`, written Tue Oct 13 22:12:35 CEST 2026 (time printed by `date` inside the writing command), **md5 `fb7cf75162e4f9dadfa0224f4180b862`**, before any direct computation of these 31 cells (`checks/k3_predict.log`). Contents (verbatim):
```
K3 PREDICTIONS — Grepy el Jurado — written Tue Oct 13 22:12:35 CEST 2026, before any direct computation of these cells.
Prediction = the report's closed formula (Theorem TOTAL, checks/k4_formula.py Y_total) assembled over n_lam(m): Syl_p X_q(m,c) as {exponent: count}.
p=3 m=12 c=1 q=27 : {1: 442, 3: 1, 4: 131, 10: 297, 17: 131, 18: 143, 19: 1, 22: 143, 23: 1, 24: 10, 29: 54, 34: 10, 35: 1, 39: 1}
p=3 m=12 c=3 q=27 : {1: 442, 5: 1, 6: 131, 11: 297, 16: 131, 17: 143, 18: 1, 23: 143, 24: 1, 25: 10, 29: 54, 33: 10, 34: 1, 40: 1}
p=3 m=12 c=4 q=27 : {1: 442, 3: 1, 4: 131, 11: 297, 17: 131, 18: 143, 19: 1, 22: 143, 23: 1, 24: 10, 29: 54, 34: 10, 35: 1, 39: 1}
p=3 m=12 c=2 q=54 : {1: 442, 3: 1, 4: 131, 11: 297, 17: 131, 18: 143, 19: 1, 22: 143, 23: 1, 24: 10, 29: 54, 34: 10, 35: 1, 39: 1}
p=3 m=12 c=5 q=54 : {1: 442, 3: 1, 4: 131, 10: 297, 17: 131, 18: 143, 19: 1, 22: 143, 23: 1, 24: 10, 29: 54, 34: 10, 35: 1, 39: 1}
p=3 m=12 c=7 q=3 : {1: 443, 2: 131, 4: 297, 6: 131, 7: 286, 8: 2, 9: 10, 11: 54, 13: 10, 14: 2}
p=3 m=12 c=8 q=3 : {1: 443, 2: 131, 4: 297, 6: 131, 7: 286, 8: 2, 9: 10, 11: 54, 13: 10, 14: 2}
p=3 m=12 c=9 q=3 : {1: 442, 2: 1, 3: 131, 4: 297, 5: 131, 6: 143, 7: 1, 9: 143, 10: 1, 11: 74, 12: 1, 15: 1}
p=3 m=12 c=10 q=3 : {1: 443, 2: 131, 4: 297, 7: 131, 8: 286, 9: 2, 10: 10, 11: 54, 12: 10, 13: 2}
p=3 m=12 c=12 q=3 : {1: 442, 3: 1, 4: 131, 5: 297, 6: 131, 7: 143, 8: 1, 9: 143, 10: 1, 11: 74, 12: 1, 14: 1}
p=3 m=12 c=13 q=3 : {1: 443, 2: 131, 5: 297, 7: 131, 8: 286, 9: 2, 10: 10, 11: 54, 12: 10, 13: 2}
p=3 m=12 c=0 q=9 : {1: 442, 3: 1, 4: 131, 7: 297, 10: 131, 11: 143, 12: 1, 16: 143, 17: 1, 18: 10, 20: 54, 22: 10, 23: 1}
p=3 m=12 c=5 q=9 : {1: 442, 2: 1, 3: 131, 7: 297, 12: 131, 13: 143, 14: 1, 15: 143, 16: 1, 17: 10, 20: 54, 23: 10, 24: 1, 26: 1}
p=3 m=12 c=8 q=9 : {1: 442, 2: 1, 3: 131, 7: 297, 11: 131, 12: 143, 13: 1, 14: 143, 15: 1, 16: 10, 20: 54, 24: 10, 25: 1, 27: 1}
p=3 m=12 c=9 q=6 : {1: 442, 2: 1, 3: 131, 4: 297, 5: 131, 6: 143, 7: 1, 9: 143, 10: 1, 11: 74, 12: 1, 15: 1}
p=3 m=12 c=11 q=12 : {1: 443, 2: 131, 5: 297, 7: 131, 8: 286, 9: 2, 10: 10, 11: 54, 12: 10, 13: 2}
p=3 m=12 c=4 q=15 : {1: 443, 2: 131, 5: 297, 7: 131, 8: 286, 9: 2, 10: 10, 11: 54, 12: 10, 13: 2}
p=3 m=12 c=1 q=81 : {1: 442, 4: 1, 5: 131, 13: 297, 22: 131, 23: 143, 24: 1, 29: 143, 30: 1, 31: 10, 38: 54, 45: 10, 46: 1, 52: 1}
p=3 m=12 c=2 q=81 : {1: 442, 4: 1, 5: 131, 14: 297, 22: 131, 23: 143, 24: 1, 29: 143, 30: 1, 31: 10, 38: 54, 45: 10, 46: 1, 52: 1}
p=3 m=13 c=2 q=3 : {1: 1015, 4: 1, 5: 856, 6: 143, 7: 1, 8: 417, 9: 12, 10: 143, 11: 130, 13: 12, 15: 1}
p=3 m=13 c=4 q=3 : {1: 1015, 2: 1, 3: 428, 6: 428, 7: 143, 8: 418, 9: 155, 10: 1, 11: 128, 12: 1, 13: 12, 14: 1}
p=3 m=13 c=1 q=27 : {1: 1015, 6: 1, 7: 428, 14: 428, 15: 143, 16: 1, 20: 417, 21: 12, 25: 143, 26: 1, 27: 64, 31: 64, 32: 1, 37: 12, 42: 1}
p=3 m=13 c=0 q=6 : {1: 1015, 3: 1, 4: 856, 5: 143, 6: 1, 8: 417, 9: 12, 10: 143, 11: 130, 13: 12}
p=2 m=7 c=1 q=4 : {1: 28, 2: 1, 6: 8, 7: 6, 10: 14, 13: 6, 19: 1}
p=2 m=7 c=2 q=8 : {1: 28, 2: 1, 7: 8, 8: 6, 14: 14, 21: 6, 27: 1}
p=2 m=8 c=3 q=12 : {1: 56, 2: 2, 3: 8, 4: 6, 9: 8, 10: 6, 11: 28, 12: 6, 17: 6, 19: 2}
p=2 m=10 c=0 q=4 : {1: 240, 2: 20, 3: 16, 4: 26, 8: 16, 9: 26, 10: 96, 11: 26, 13: 1, 17: 26, 19: 18}
p=2 m=10 c=5 q=8 : {1: 240, 2: 20, 5: 16, 6: 26, 9: 16, 10: 26, 11: 48, 18: 48, 19: 26, 21: 1, 23: 26, 25: 1, 26: 8, 28: 8, 29: 1, 33: 1}
p=2 m=12 c=1 q=4 : {1: 992, 2: 132, 3: 32, 4: 100, 9: 32, 10: 100, 11: 328, 12: 102, 14: 10, 17: 100, 19: 108, 24: 10, 26: 2}
p=2 m=12 c=2 q=24 : {1: 992, 2: 132, 7: 32, 8: 100, 11: 32, 12: 100, 13: 164, 14: 1, 17: 164, 18: 101, 20: 10, 22: 100, 24: 10, 25: 44, 29: 44, 30: 10, 34: 10, 36: 1, 40: 1}
p=2 m=13 c=1 q=8 : {1: 2016, 2: 364, 9: 64, 10: 364, 11: 1, 15: 560, 16: 12, 20: 364, 21: 1, 22: 64, 27: 208, 32: 64, 33: 1, 38: 12, 43: 1}
```
Estimate (Tue Oct 13 22:14 CEST 2026): `k3.py compute K3_PREDICTIONS.txt <selection>` in three runs: (i) the 19 cells p = 3, m = 12 (B_12: 4096², 134 MB dense; ~5 s per Smith form, plus an inverse run when an exponent ≥ 39): < 400 MB, < 550 s; (ii) the 4 cells p = 3, m = 13 (B_13: 8192², 537 MB; ~40 s per Smith form, the normal and inverse runs one after the other, never together): < 1.0 GB, < 550 s (split per cell if killed); (iii) the 8 cells p = 2 (m ≤ 13, M = 62): < 1.0 GB, < 300 s. Only one heavy run at a time.

Observation (22:15): in run (i) the first cell's normal run finished in seconds, but the inverse run (`p^39 (q(c+H)+U)^{−1}`, dense) on B_12 was still running after 3 minutes. I wrote `checks/psmith128.c` (same algorithm, 128-bit storage, Montgomery arithmetic modulo p^M < 2^126, M = 79 for p = 3, so exponents up to 78 come out directly; compiled under the watchdog, `checks/psmith128_compile.log`).
Estimate (Tue Oct 13 22:16 CEST 2026): `checks/k3_test128.py` — psmith128 vs psmith (+ inverse path) on the proved-range cells of `validate`/`validate_inv` for p = 3 (m ≤ 11) and the closed formula; expected identical; < 200 MB, < 120 s.

Result `checks/k3_test128.log` (22:16): **psmith128 = closed formula on 40/40 proved-range cells** (p = 3, m ≤ 11, including q = 27, 54, 81), B_11 in 0.3–0.4 s.
Run (i) with the inverse path: **stopped by me at 22:16** (pkill of its two processes; its log is kept as `checks/_old/k3_compute_p3m12_stopped_by_me_inverse_too_slow.log`). Before the stop it had finished one cell: **p=3 m=12 c=1 q=27: AGREES** (normal run 4.3 s, inverse run E = 39, 166.6 s). The second cell was interrupted by my kill (the «ERROR» line there is the kill).
Estimate (Tue Oct 13 22:17 CEST 2026): run (i) again with psmith128 (M = 79): two runs of 10 and 9 cells, each < 400 MB (4096² × 16 B = 268 MB), < 550 s; expected to agree with the sealed predictions (or a disagreement is reported with the same prominence).

(next step, as planned at that time) STEP 7 — K3 direct computations (i) with psmith128 (running), (ii), (iii).

## STEP 8 — K6 Theorem F_p numerically — estimate (Tue Oct 13 22:17 CEST 2026, written before running)
`checks/k6.py P:k ...` — every house H = (I, k, ℓ, e, (d_t)) with e ∈ {1,2}: p = 3, k = 1..4 (14760 houses) and p = 5, k = 1..3 (32550 houses). Checks: gates (Lemma 7.6_p, the four window types) against the direct carry count; Lemma 7.7_p (both halves of R_H and J_H, d_1 monotone and ≤ e d_c p^c, first half of x_H = x_{H'} + d_1); the gluing ŷ_H = [max(X_1,0), min(X_2,0)]; (Λ_p); (Cut) strict at the first dancer with J = 1 and at its mirror; integrality of the real fits (house and five penalty cells) and the penalty shift of the integer fit; the potential V built by my proof (steps 1–8: v', slack h, junction bound, central flat interval, (E), (M), (G)); and, on every third house with |I| ≤ 3, T(r) ≥ Y(r) by brute-force min-cost r-matchings (penalties (0,0), (1,0), (0,2)). Expected: 0 failures; all four types occur. Estimate < 300 MB, < 550 s per run; run p = 3 (k ≤ 4) and p = 5 (k ≤ 3) separately.

Result `checks/k6_p3.log` (22:17): **p = 3, k ≤ 4: 14760 houses (e ∈ {1,2}), 0 failures in every check** (gates, Lemma 7.7_p, d_1, gluing, (Λ_p), strict (Cut), integrality incl. penalty cells, the potential V by my proof with (E), (M), (G), junction bound and central interval; T(r) ≥ Y(r) by brute-force matchings on 4056 houses × 3 penalty settings); top-window types among the distinct houses with I ≠ ∅: **OR 4840, AND 4840, DIG 2420, NEV 2420**; central flats in 899 houses; a J-boundary (strict cut checked) in 7260. 22 s, 44 MB.
Estimate (22:18): `k6.py 5:1 5:2 5:3` (32550 houses): < 300 MB, < 550 s. Controls `K6_CONTROL=tau` (τ without the DIG term) and `K6_CONTROL=gate` (DIG treated as NEV in the gate rule) on p = 3, k ≤ 3: must produce failures; < 100 MB, < 60 s each.

Controls (22:17): `checks/k6_control_tau.log` (τ without the DIG term): **failures in Lemma 7.7_p (596), first half of x_H (596), gluing (590+590), (G) for v' (2120), (E) (2188), (G) (1355), junction (252), empty central interval (24)**; `checks/k6_control_gate.log` (DIG treated as NEV): **2014 gate failures**. The checks can fail.
K3 run (i) completed with psmith128: `checks/k3_compute_p3m12a.log` (10 cells, 25 s) and `checks/k3_compute_p3m12b.log` (9 cells, 21 s, 274 MB): **19/19 AGREE with the sealed predictions, 0 disagree** (p = 3, m = 12; e = 1, 2, 3, 4; q ∈ {3, 6, 9, 12, 15, 27, 54, 81}; c ∈ {0, …, 13}).
Estimate (22:18): run (ii), p = 3, m = 13 (B_13, 8192 subsets): cells (2,3), (4,3), (0,6) with the 64-bit engine at M = 39 (their predicted exponents are ≤ 15; 8192² × 8 B = 537 MB): `K3_M=39`, < 700 MB, < 550 s; then cell (1,27) alone with psmith128 (8192² × 16 B = 1.074 GB, below the 1.2 GB cap — the watchdog decides): < 1.15 GB, < 550 s.

K3 runs (ii) and (iii): `checks/k3_compute_p3m13a.log` (3 cells, 99 s, 535 MB), `checks/k3_compute_p3m13b.log` (cell (1,27) with psmith128: 18 s, **peak 1.06 GB**, under the cap), `checks/k3_compute_p2.log` (8 cells, 17 s, 535 MB): **all AGREE**. **K3 total: 31/31 sealed cells agree, 0 disagree** (one cell, p=3 m=12 c=1 q=27, was computed twice, by the inverse route and by psmith128: same group).
`checks/k6_p5.log` (22:19): **p = 5, k ≤ 3: 32550 houses, 0 failures; types OR 6448, AND 6448, DIG 9672, NEV 9672**; T(r) ≥ Y(r) by brute force on 10850 houses × 3; 41 s, 71 MB.
**Watchdog kill (reported):** `k4_fast.py fit 3 0 241 …` (started 22:10:33) was killed at 601 s (`VIGIA-MATADO-TIEMPO pico_kb=12640 t=601s`); its log printed nothing (output only at the end) and is kept as `checks/_old/k4_fit_p3a_KILLED_by_watchdog_601s.log`. Not a result. Re-split with progress lines every 10 values of λ.
Estimate (22:21): `k4_fast.py fit 3 LO HI 1,2,3 <15 values of i>` in six λ-ranges [0,90], [91,160], [161,210], [211,241], [242,300], [301,340], [341,400] (run up to four at once, each under its own watchdog), each < 100 MB, < 550 s; expected 0 mismatches.

(next step, as planned at that time) STEP 6b — K4 fit runs, split (running).

## STEP 9 — JOB 3 literature sweep — started (Tue Oct 13 22:21 CEST 2026)
Searches logged in `checks/SEARCHES.md`, downloads in `checks/DOWNLOADS.md`, raw result lists in `checks/lit/`. Estimate for `checks/arxiv_sweep.py` (arXiv API, 20 queries per run, 3.5 s apart, saves XML + list): < 50 MB, < 200 s per run.

Estimate (22:26): `checks/openalex_cites.py lit/seeds1.json C` — OpenAlex API: for 10 seed works (JNR03, DGW, DJ14, CSX, Bai03, STWZ, TW, Martin I, Donkin 1993, GMMY) all citing works; < 50 MB, < 300 s.

K4 fit, partial results (22:27): `checks/k4_fit_p3_0_90.log` (4095 cells), `k4_fit_p3_91_160.log` (3150), `k4_fit_p3_161_210.log` (2250): **9495 cells, Smith(M_p) + small part = closed formula in all, 0 mismatches**.
Estimate (22:27): because |I| = 5 cells are slow, λ ∈ [242, 400] for p = 3 is run on a reduced grid e ∈ {1,3}, i ∈ {0,1,80,243} (stated, not hidden): four ranges [242,280], [281,320], [321,360], [361,400]; and p = 5, λ ∈ [0,400], e ∈ {1,2,3}, i ∈ {0,1,4,5,24,25,26,124,125}; p = 7, λ ∈ [0,400], e ∈ {1,2,3}, i ∈ {0,1,6,7,48,49,50,342,343}; each < 100 MB, < 550 s.

K4 fit results (22:34–22:42): `k4_fit_p3_211_241.log` 1395 cells, `k4_fit_p3_242_280.log` 312, `k4_fit_p3_281_320.log` 320, `k4_fit_p3_321_360.log` 320, `k4_fit_p7.log` 10827 cells (p = 7, λ ≤ 400): **0 mismatches**.
**Two more watchdog kills (reported):** `k4_fit_p3_361_400` and `k4_fit_p5` (p = 5, λ ≤ 400) were killed at 601 s (`VIGIA-MATADO-TIEMPO`); logs kept in `checks/_old/…_KILLED_by_watchdog_601s.log` (their progress lines showed 0 mismatches up to the kill, but a killed run is not a result). Re-split (estimate 22:43): p = 3 [361,370], [371,385], [386,400] (e ∈ {1,3}, i ∈ {0,1,80,243}); p = 5 [0,200], [201,300], [301,350], [351,400]; each < 100 MB, < 550 s.

(next step, as planned at that time) STEP 9 — literature (continuing); fit re-runs in background.

## STEP 10 — K5 whole Hamming groups — estimate (Tue Oct 13 22:53 CEST 2026)
`checks/k5.py 15`: 12 cells (p,d,q) = (3,12,3), (3,13,3), (3,14,6), (3,15,9), (3,16,3), (3,20,3), (3,24,27), (5,30,5), (5,31,10), (5,35,25), (7,56,7), (7,60,14) — all with d ≥ p² + p (beyond Theorem G). Closed formula assembled (Theorem TOTAL) vs (I1) Kirchhoff's v_p|K| and (I2) the number of cyclic factors from rank_{F_p} of the Laplacian (reduction mod p: L ≡ −Σ J_i, J² = 0, so coker dimension = Σ_j C(d,j)(q−2)^j (2^m − rank U on B_m); rank of U by Wilson's diagonal form for every m and, for m ≤ 15, also by direct FLINT nmod_mat ranks of the inclusion matrices — the two must agree). Control: the formula with e+1 must contradict Kirchhoff. Expected: 12 AGREE, control fires. Estimate < 600 MB (largest inclusion matrix C(15,8)×C(15,7) = 6435² mod p), < 400 s.

**Watchdog kill (reported):** `k5.py 15` was killed for memory (`VIGIA-MATADO-MEMORIA mem_kb=1327104 t=13s`) while building the m = 15 inclusion matrices for the direct rank; before that it printed 3 AGREE lines (d = 12, 13, 14). Log kept in `checks/_old/k5_KILLED_by_watchdog_memory_at_m15.log`. Re-run (estimate 22:54): `k5.py 13` (direct ranks for m ≤ 13, Wilson beyond; < 400 MB, < 300 s).

Result `checks/k5.log` (22:52, 8 s, 135 MB): **12/12 cells AGREE with both invariants** — the assembled closed formula has exactly Kirchhoff's total length v_p|K| and exactly the number of cyclic factors given by the F_p-rank count, and exactly one free summand; d up to 60, e up to 3 (e.g. p=7, d=56, q=7: length 276905881008120163903327489627922975347274216200 both ways). Wilson's rank = direct FLINT rank for every m ≤ 13 used. **Control (formula with e+1): contradicts Kirchhoff in 12/12.**
Extra (run without a written estimate, < 1 s each — slip of mine): `checks/k5b.log`: my closed formula gives exactly the report's illustration `Syl_3 K(H(12,3)) = {1: 36952, …, 13: 12}` and reproduces all seven rows d = 5…11 of [CS3] §10. `checks/k5c.log`: the 14 blocks λ = 12, 13 (p = 3; q = 3, 6, 9, 27; c = 0…6) that the previous reader extracted from direct Smith forms on B_12, B_13 all equal my closed formula (14/14; their data, my formula).

## STEP 10 — STATE: DONE (Tue Oct 13 22:53 CEST 2026)

## STEP 6c — K4 fit, the last range — estimate (Tue Oct 13 22:54 CEST 2026)
**Three more watchdog kills (reported):** the re-split runs `k4_fit_p3_361_370`, `_371_385`, `_386_400` were all killed at 601 s (`VIGIA-MATADO-TIEMPO`; logs in `checks/_old/`). Cause: my Smith form worked modulo p^B with B = the sum of all diagonal valuations (~3·10⁴ digits). New route `group_fast2` in `checks/k4_fast.py`: B = 2·(largest diagonal valuation) + 20, **certified** by Σ(Smith exponents) = v_p(det M) = Σ(diagonal valuations) (M is triangular and non-singular for i ≥ 1), falling back to the old route otherwise. Slip: one 0.6 s timing call of it was run outside the watchdog (22:54).
Estimate: `k4_fast.py fit2 3 LO HI 1,2,3 1,2,3,4,7,10,26,27,28,80,81,82,242,243` for [361,370], [371,380], [381,390], [391,400] (i = 0 is not in this grid; i = 0 was covered for λ ≤ 360 and in the sealed files), four runs in parallel, each < 100 MB, < 400 s. Expected 0 mismatches.

## STEP 11 — K2 independent identification — estimate (Tue Oct 13 22:56 CEST 2026)
`checks/k2.py 220 P LO HI`: for M = L(λ) ⊗ 𝔽_p: (a) Δ-filtration by the greedy top-weight algorithm; (b) ∇-filtration (the same on the contravariant dual); (c) End_Dist(M) (block-diagonal maps commuting with E^(p^t), F^(p^t)) local, i.e. the kernel of the top-weight character nilpotent; plus dim End (Tubbenhauer–Wedrich: 2^{|I|}) and the Jordan type of f. Tilting + indecomposable + top weight λ of multiplicity one ⇒ M ≅ T(λ) by the classification of tilting modules (Ringel; Jantzen E.6), **without Donkin's tensor product theorem**. Smoke test first: p = 3, λ ∈ [12, 14]; < 300 MB, < 120 s. Controls: L(λ) ⊕ L(λ−2) must fail (c); Δ(λ) ⊗ 𝔽_p must fail (b).

Smoke test `checks/k2_smoke.log` (22:56, 9 s, 119 MB): λ = 12, 13, 14 (p = 3) identified (tilting, End local of dimension 2^{|I|}, Δ-factors {12,10,6,4}, {13,9,7,3}, {14,2}); **controls fire: L(λ) ⊕ L(λ−2) is tilting but End is not local (3/3); Δ(λ) ⊗ 𝔽_p has no ∇-filtration (3/3).**
Estimate (22:57): full K2 in four parallel runs — p = 3, λ ∈ [12,30] and [31,50]; p = 5, λ ∈ [30,45]; p = 7, λ ∈ [56,62]; dim ≤ 220; each < 600 MB, < 550 s.

Result (22:57): `checks/k2_p3_12_30.log` (19 lattices), `k2_p3_31_50.log` (20), `k2_p5_30_45.log` (16), `k2_p7_56_62.log` (7) — **62/62 lattices L(λ) ⊗ 𝔽_p identified as T(λ) without Donkin's theorem: every one has a Δ-filtration and a ∇-filtration (tilting), a local endomorphism ring (indecomposable) of dimension exactly 2^{|I|} (as Tubbenhauer–Wedrich predict), top weight λ of multiplicity one, and f acts with Jordan blocks all of size p (G_1-projectivity).** λ = 12…50 (p = 3), 30…45 (p = 5), 56…62 (p = 7): all beyond p² + p − 1, 62 ≥ 20 required. Peak 737 MB, ≤ 47 s per run. Controls in every run fire (direct sums: End not local; Weyl modules: no ∇-filtration). (The four logs were first written with spaces in their names by a quoting slip in my shell loop and then renamed with `mv`.)

## STEP 11 — STATE: DONE (Tue Oct 13 22:58 CEST 2026)

## STEP 6c — STATE: DONE (Tue Oct 13 23:03 CEST 2026)
`checks/k4_fit2_p3_361_370.log`, `_371_380.log`, `_381_390.log`, `_391_400.log`: 4 × 420 = **1680 cells (p = 3, λ ∈ [361, 400], e ∈ {1,2,3}, 14 values of i ≥ 1), 0 mismatches**, all `VIGIA-FIN-OK` (495, 463, 224, 578 s).
**K4 fit totals (Smith form of `M_p` by the windows/moves + small part, against my closed formula): p = 3: 13522 cells (λ ≤ 241 on the full grid e ∈ {1,2,3} × 15 values of i incl. i = 0; λ ∈ [242, 360] on the reduced grid e ∈ {1,3} × i ∈ {0,1,80,243}; λ ∈ [361, 400] on e ∈ {1,2,3} × 14 values of i ≥ 1); p = 5: 10827 (λ ≤ 400, e ∈ {1,2,3}, 9 values of i); p = 7: 10827 (same) — 35176 cells, 0 mismatches.** Not covered by this route: i = 0 for λ > 360 (p = 3) — covered for those λ only through SEALED_2 (my formula = sealed values) and K3/K5.
## STEP 6 — STATE: DONE · STEP 7 (K3) — STATE: DONE · STEP 8 (K6) — STATE: DONE · STEP 9 (JOB 3) — STATE: DONE (all as recorded above; closed Tue Oct 13 23:03 CEST 2026)

(next step, as planned at that time) STEP 12 — final checks of the files and of the material's md5; final line.

## STEP 12 — STATE: DONE (Tue Oct 13 23:04 CEST 2026)
Final checks: no process of mine is left running (0); **`material/` unchanged** (`checks/md5_material_at_end.txt` = `checks/md5_material_at_start.txt`); MISSION.md, CLAUDE.md, vigia.sh md5 unchanged (7a1be3b5…, 6ece31a6…, e5f8cf13…).

### Errors of my own and slips (all disclosed where they happened; collected here)
1. Two stray empty files from heredocs (21:34, 21:50): the first created and removed with `rm` in the same command (the only deletion of the session, of an empty file I had just made); the second moved to `checks/_old/`.
2. Time stamps: four headers were first written with guessed or approximate minutes («22:05», «21:5x», «22:1x», «22:1», «22:55», «22:57»); each was corrected from `date` within minutes. All times now in the log come from `date`.
3. Runs started before their estimate was written: `k4_control.py` (21 s), `k4_timing.py` (14 s), `k4_fast.py crosscheck` (17 s), `k5b.py`, `k5c.py` (< 1 s each); and one 0.6 s timing call of `group_fast2` outside the watchdog.
4. Watchdog kills (each reported, kept in `checks/_old/`, never a result, never the cap raised; the work was re-split): `k4_fit_p3a` (601 s), `k4_fit_p5` (601 s), `k4_fit_p3_361_400` (601 s), its three re-splits (601 s each), `k5.py 15` (memory, 1.33 GB at m = 15).
5. Runs I stopped myself: K3 run (i) with the dense inverse route (one cell had already finished and agreed); the Semantic Scholar/Zenodo redo (rate-limited / unquoted).
6. First version of `k1_controls` checked only `E^{(r)}` of the controls, not `F^{(r)}`, and so showed the «twist without p» lattices as stable; corrected (kept in `checks/_old/`).
7. K2 logs first written with spaces in their names (shell quoting), renamed with `mv`.
8. Literature: Semantic Scholar, BASE, OATD not reachable (rate limit / bot checks, not bypassed); Google Scholar not directly queryable by my tools; [Don93] closed access, not read (its statement read in two originals that restate it).

### What I did not do
- I did not re-prove [DST] (p = 2): Theorem I and TOTAL at p = 2 rest on it, as the report says.
- K4 did not cover i = 0 for λ > 360 at p = 3 by the Smith-form route (only through SEALED_2, K3, K5).
- K2 identifies `L(λ)⊗𝔽_p` with `T(λ)` for 62 values (dim ≤ 220), not for all λ; for all λ the identification rests on the report's proof (R5), which I checked.

### Files (scripts, logs, data in `checks/`, with md5; md5 list also in `checks/md5_checks_files.txt`)
| md5 | file |
|---|---|
| 9bd2e942517c37c81fb9881858c4a30c | `checks/DOWNLOADS.md` |
| fb7cf75162e4f9dadfa0224f4180b862 | `checks/K3_PREDICTIONS.txt` |
| 7ed8529eb3dc521e33868f3912f397f8 | `checks/SEARCHES.md` |
| 9ef0c04203217e82571ddc796576ca8a | `checks/THEOREM_F_ODD_P.md` |
| d41d8cd98f00b204e9800998ecf8427e | `checks/_arxiv_q1.xml` |
| b92180db86f50bdd830149f83109fd94 | `checks/_arxiv_test.xml` |
| 5139a399e13ac564fdcdac31536d7004 | `checks/_core_t.json` |
| ad8b977242c8ef989ddada3970e4ecad | `checks/_job1_R1_R5.md` |
| 40e46b6a4f1ab9a745c7705cf9ca90de | `checks/_job1_R6_R8.md` |
| be7a0106eac480e059aa2f394d5dec82 | `checks/_job1_R9_R11.md` |
| c3120c592164705def843b87f6f2ea7d | `checks/_job2.md` |
| 7d140e8bf422b1cbf111b476c104bdbe | `checks/_job3.md` |
| 246f06482c9c94c979590e1a3f678a5f | `checks/_top.md` |
| 593500d8dca13f754e5cc2dbb9b45051 | `checks/arxiv_sweep.py` |
| 0e337b14462d5936a1d16c6a878cb785 | `checks/hexagon_list.py` |
| 2d170dc2f9ffc0939c342831a5b59d32 | `checks/k1.py` |
| 93938f4538dd17db579e1da273754e4f | `checks/k1_controls.log` |
| 9f73851f86b6d8fa08d4dc9f668cdaf7 | `checks/k1_controls.py` |
| 4952c26bc996c0f3db1062bf7af15acc | `checks/k1_p3.log` |
| 53c811d902b7b61212c456197e3e0d6a | `checks/k1_p5.log` |
| 049aa0a835f7aaa5110ef2d7e603217b | `checks/k1_p7.log` |
| 0be0098cfea4863a4dae9595bda5523f | `checks/k1_smoke.log` |
| 2521303d6d7b515af81b608f1da90141 | `checks/k1b.log` |
| fb3e184f9080585f0791a401d3836ea7 | `checks/k1b.py` |
| 19d9a3b45d818161dec716260e82bc5c | `checks/k1b_control.log` |
| 377b2bacd553b70582fa965a13608faf | `checks/k2.py` |
| f70bbe2c488feea45a90fcd260fcc585 | `checks/k2_p3_12_30.log` |
| 53fcbf2619dcf5de5def4678145ed2da | `checks/k2_p3_31_50.log` |
| e4f46448f0ea755dd79d817712dc2522 | `checks/k2_p5_30_45.log` |
| 1f35a983fbf76cdc5d1d696b23647d10 | `checks/k2_p7_56_62.log` |
| 5e969a3530272b2cfa6b8584d2127da3 | `checks/k2_smoke.log` |
| a13c11bfca6ae6a47a24e66a014bf040 | `checks/k3.py` |
| e48aa1a957b7954c667797cedbadf21d | `checks/k3_compute_p2.log` |
| 276409b7558911236aac2e90be6ce93b | `checks/k3_compute_p3m12a.log` |
| d3036694d2273757e34fbcdeeb6bb6c8 | `checks/k3_compute_p3m12b.log` |
| 87d3d83cd8ff0ee4cf10df898b72d2e5 | `checks/k3_compute_p3m13a.log` |
| c702a82a2a348d662bf94b7fb2ae61f0 | `checks/k3_compute_p3m13b.log` |
| 296271047c6077de97c74018a2a3e073 | `checks/k3_predict.log` |
| 382e9b4af0cd25af8ab7518e1e2ee34d | `checks/k3_test128.log` |
| 66f7a3b4f584bb5fb05c18c3d606cced | `checks/k3_test128.py` |
| 093276feb41156725ca315f735bfc373 | `checks/k3_validate.log` |
| a7361daf596db59cc5302918966478c8 | `checks/k3_validate_inv.log` |
| 8eda6f15a1a126230f80707d5b16a3fc | `checks/k4_G.log` |
| 1e253ece3461da1052dd2aea212c72ca | `checks/k4_control.log` |
| 24fdf46fe0da968dd855128510c9ad95 | `checks/k4_control.py` |
| 3903c7659d42b804a1cf8f6cbfa38bf3 | `checks/k4_dst.log` |
| af8909911da70a07c083102486af396f | `checks/k4_fast.py` |
| 7f6689de763f9846c9d071667cfc4b0e | `checks/k4_fast_cross.log` |
| f2b7ee4ba4acae6e29e21360617543e6 | `checks/k4_fit2_p3_361_370.log` |
| f3c6f6e5e759ef609616e2cb5b9bb653 | `checks/k4_fit2_p3_371_380.log` |
| a6e42f01b358d815770022db33d08712 | `checks/k4_fit2_p3_381_390.log` |
| e1cbeb369d17f0382544fbf741c4d4b2 | `checks/k4_fit2_p3_391_400.log` |
| f430218c0d4d99196460b4a063d7147e | `checks/k4_fit_p3_0_90.log` |
| 7489aee02fb1848bdfab4847afe946d0 | `checks/k4_fit_p3_161_210.log` |
| 336611d85d97f3df7b7dc8bd010bfbb5 | `checks/k4_fit_p3_211_241.log` |
| d3d43d6fb80cddbdc7a283f39ad2f60f | `checks/k4_fit_p3_242_280.log` |
| 0af9cc80edb41f56885e2dc3e2f402d5 | `checks/k4_fit_p3_281_320.log` |
| 1725245abe2c08e93674255b7c449122 | `checks/k4_fit_p3_321_360.log` |
| 898ef8511e983124b2e12dd80386f0bc | `checks/k4_fit_p3_91_160.log` |
| 9bb083c0f878697d39cb6a0b0b5ce92c | `checks/k4_fit_p5_0_200.log` |
| 1029893e04c81aa1df50bca0f82964af | `checks/k4_fit_p5_201_300.log` |
| a4c030af01cd5fbffbcf8b907ff13ec4 | `checks/k4_fit_p5_301_350.log` |
| 3ef35f3138de283df4b3786e3c61fa1f | `checks/k4_fit_p5_351_400.log` |
| 55e02cea34225bd55c46269f55fa4fb7 | `checks/k4_fit_p7.log` |
| d75922137c9221e257e8e587b125fdcb | `checks/k4_formula.py` |
| ff673d1425689d185eb48d041d78516d | `checks/k4_mp.py` |
| 7295e05bc85b92b0c92a95ee607b31f8 | `checks/k4_run.py` |
| cd5b291ab5ca380725624becc7dbdbfb | `checks/k4_sealed1.log` |
| 31bfa43cd1e5e12d5c0bde563c99e990 | `checks/k4_sealed2_300.log` |
| 1bc84deff52cbb97ee6b0453e075a6dc | `checks/k4_sealed2_all.log` |
| 42ae05f789d4c0e8b7f10ece72779327 | `checks/k4_smoke.log` |
| bc69bd9d020c41677fe5629becca0e85 | `checks/k4_timing.log` |
| 9c420689f08601f8779c9cd6fca294b5 | `checks/k4_timing.py` |
| 61cf3f241c497456a184b41b1ec52fe5 | `checks/k4_windows.log` |
| 6a724edbf2de238520140b0edec21abc | `checks/k5.log` |
| b4b4b3ddbcef1526610f4fba148597dd | `checks/k5.py` |
| bd4e048d2b62ad0d668101f9f52a5c52 | `checks/k5b.log` |
| f572245cccecd46615e440a1ccbf2cb5 | `checks/k5b.py` |
| 0291a07454650b951038b4706d08a316 | `checks/k5c.log` |
| 296cd47e610117832103ff3c72a56220 | `checks/k5c.py` |
| a3f0fd7e22e0f53b83937d026b8806ef | `checks/k6.py` |
| 72aa2ae1695df786ff20a101e7bcd6d2 | `checks/k6_control_gate.log` |
| e9a04567b313af69e4e7e347103a8f6a | `checks/k6_control_tau.log` |
| 0ddd12629ca689e216d50e606326a1df | `checks/k6_p3.log` |
| 2128792f6fdf6097de5de7efdc36c472 | `checks/k6_p5.log` |
| 5f31bcdfc43ede2ed8a369f8fc82980e | `checks/k7_md5.log` |
| 0d83950f3f999339cca6b900b533d360 | `checks/k7_md5.py` |
| a0cf744c739338d93dffb66afb071f1a | `checks/lat.py` |
| f5e5fbdd171445a0e5f6cd6d8bc958e3 | `checks/lit_arxiv_L1.log` |
| 5fb22353772cc40b88d08dd58e14b174 | `checks/lit_arxiv_L2.log` |
| 0f39b566f220dda243dc1ecc5ad18bf2 | `checks/lit_arxiv_authors.log` |
| 32741d3a7a09bf1cad3a782459ddd4ae | `checks/lit_arxiv_authors2.log` |
| 791550d6c288aaeee19e2bea63ffb38a | `checks/lit_core.py` |
| 6d32a1fb144ccd0aad51a88520bbe3cd | `checks/lit_core2.log` |
| d4885165d55114308593c7fc1fc8c2c1 | `checks/lit_engines.py` |
| 9cb448776a6e99d3836bf9d95b6d2f4a | `checks/lit_engines1.log` |
| ee2e24a4a3d6b286f3de5b18110f5b44 | `checks/lit_hexagon.log` |
| 9206703b417ce6769813414d5bf202ff | `checks/lit_oa_authors.log` |
| 1fe8fe6c97d51d55e8e902650fb4b856 | `checks/lit_oa_authors.py` |
| b662b3ea9bdd5a4dd7798d66a9635af8 | `checks/lit_openalex_C.log` |
| d5c83c6d199761f96b9d0fdbc1f0089f | `checks/lit_openalex_search.py` |
| 4a8d8cd4a590c7e1b793c8e777257e40 | `checks/lit_openalex_search1.log` |
| 2964c18908d90613a852fadb862f7e74 | `checks/lit_s2_zenodo.py` |
| ddeb7c4e41612eb365f1543df12bb1a7 | `checks/lit_zenodo.py` |
| efa0827932eadc46802db24e41ab1877 | `checks/lit_zenodo1.log` |
| 702b44845f107ee1a13236fdc8ecf28c | `checks/md5_checks_files.txt` |
| 58577d06712ff1bd8eebbdab6b008bb8 | `checks/md5_material_at_end.txt` |
| 58577d06712ff1bd8eebbdab6b008bb8 | `checks/md5_material_at_start.txt` |
| 10952e4699513b420a5732d1785e3a11 | `checks/openalex_cites.py` |
| 58daedcc60f581aef2183f635e9d0651 | `checks/pdftotext_andersen.log` |
| 096124b14e9972b123de28ec4608b428 | `checks/pdftotext_material.log` |
| 8c9bd5e530fd0251a6ed790677bcd9c0 | `checks/psmith` |
| c6d2280603e083647f8fa9fe5bc0706a | `checks/psmith.c` |
| bb701fb0da7db7f400743b25bb5f0177 | `checks/psmith128` |
| 77aead798dd1ef4e33c5fa7e17e5e2bc | `checks/psmith128.c` |
| 4ec6a14593ed13c47cb452f5b5ab40c9 | `checks/psmith128_compile.log` |
| 7d046e10bf9c6cb31dc3985267e76e64 | `checks/psmith_compile.log` |
Raw search answers: `checks/lit/` (JSON/XML); text extracts: `checks/txt/`; download: `checks/downloads/Andersen1997/` (DOWNLOADS.md); superseded/killed logs: `checks/_old/`.

NEXT: nothing — mission complete (Tue Oct 13 23:04 CEST 2026). A future reader may extend K2 beyond dim 220 and K4 at i = 0 for λ > 360, p = 3.
