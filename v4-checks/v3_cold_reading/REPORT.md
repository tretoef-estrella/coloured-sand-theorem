HOLDS WITH CORRECTIONS

# REPORT — COLOURED_SAND_1 (cold reader: Grepy el Tamiz)

## Summary table

All theorems of the paper survive: every proof was re-derived by hand, and 300+ groups were recomputed with my own engine (none disagree). The corrections are a priority omission (d = 2 is known), a wrong citation range, a wrong counterexample in a remark, a misplaced sentence in Lemma 8's proof, one unproved step in §8, and over-counting of the predictions.

| item | verdict | one-line reason | where checked |
|---|---|---|---|
| P1 Thm A | CORRECT | basis, K_q = q on W, pieces q(c+H)+U re-derived; equals JNR Thm 13 after complementing subsets of S, multiplicities included; fair credit | §2; JNR03 pdf §4 (Thm 13, Def. 10) |
| P2 Lemma 2 | CORRECT | the unit recursion for λ_s, μ_s re-derived | §2 |
| P3 Lemma 3 | CORRECT | factors in [1,m] are units for p > m; idempotent splitting; bidiagonal blocks with unit subdiagonal, cyclic; C(m,k)−C(m,k−1) strings | §3 |
| P4 Thms E, B | CORRECT | E from Lemma 3; ballot identity, generating function, lists d = 2,3,4 re-derived; c+r ≤ d < p; condition (j,k) ≠ (0,0) is vacuous (PRESENTATION) | §3; K2 |
| P5 Lemmas 4, 5, Thm C | CORRECT | chain formula for M⁻¹; exponent = least valuation of M⁻¹ (Smith form); carry lemma induction; j = 0 quotient by M″; e = 0 also = JNR Thm 2 | §4; K3; JNR03 p. 2 |
| P6 Thm D | GAP | proof right, but Wilson's range t ≤ min(k,m−k) is attributed to CSX15 (2), which states only t ≤ k ≤ n/2; the middle rank of odd m needs Wilson's original | §5; CSX15 p. 4; arXiv:1302.4249 Thm 2.1; K4 (24 middle ranks) |
| P7 Cor 1 | CORRECT | Thm A + Lemma 2 | §2 |
| P8 Cor 6 | CORRECT | V^{⊗m} over F_3[e]/(e³), tensor rules, recursion, closed form re-derived | §5; K4 (9/9) |
| P9 (T1)–(T3) | CORRECT | (T2) characters and (T3) injectivity re-derived; (T1) is standard but cited vaguely; the precise place is Jantzen RAGS II.E.19–E.22 | §6; HW arXiv:1912.09457 §5.4; STWZ arXiv:2105.07724 Prop. 3.4 |
| P10 Lemma 7 | CORRECT | ν by Kummer; f / f^{(p)} recursion with unit binomials; splitting argument complete (universal property of Δ(μ) used without citation) | §6; K7 |
| P11 Lemma 8 | PRESENTATION | Smith form re-derived by Schur complements (r ≤ p−1 and r = p), c = k = 0, simple blocks; but «every entry has valuation ≥ 1» is false where placed (r ≤ p−1) | §6; K7 (2670/2670) |
| P12 Thms F, G | CORRECT (ERROR in a side remark) | both follow for all m ≤ p²+p−1 and every p (p = 2 too); F = case a = 0; four factors first at m = p²+p; but the «e ≥ 1 needed, fails at (4,3,4)» example is wrong for G's formula (it fails only for F's form) | §6; K5; e0_scan.log; e0_thmF.log |
| P13 Thm H | CORRECT (conditional on [DST]) | [DST] Thm D (p. 18), Prop. 5.2/5.4 (pp. 19–21) and Thm 7.10 (p. 28) are stated for every α ≥ 1; the reduction and the §7 formula are identical to them | DST pdf; K6 |
| P15 Conj. I | GAP | decomposition and both «known facts» right (references imprecise); holds for G by the inequalities; for p = 2, «follows from Thm H» lacks a proof that every big clock exceeds 2^θ (only checked by machine) | §8; K9; verify_paper_numbers.log |
| P14 grades, numbers | PRESENTATION | all numbers checked are right (115/115 sealed groups, §8 and §10 tables, N lists, ranges); «63» counts two groups twice (61 distinct); «new» must exclude d = 2 (DGW 2015); the 384/112 counts are not reproducible as described | §1, §9, §10; L2 |
| K1 | CORRECT | 20/20 cells (q^d ≤ 729, p ≤ d, composite q, p ∤ q): Laplacian = pieces; controls differ 20/20 | checks/k1_k4.log |
| K2 | CORRECT | 12/12, incl. (2,9,3) e=2, (2,25,5), (4,5,5), (4,7,7), (4,25,5) | checks/k1_k4.log |
| K3 | CORRECT | 21/21, incl. (10,3,3): E = 11 at s = 9 only; p = 2, q even; p ∤ q | checks/k1_k4.log |
| K4 | CORRECT | N: 17/17; Cor 6: 9/9 (q = 6, 9, 12, 15); rank formula 328/328 | checks/k1_k4.log |
| K5 | CORRECT | 18/18 predictions written first (07:55:35, 07:57:41): p=3 m = 9–11 (λ = 9, 10, 11), p=2 m = 4, 5, p=5 m = 11, 12, 13, e = 2, 3, 5 | checks/k5_compute3.log, k5b_compute.log |
| K6 | CORRECT | 14/14 predictions (08:07:40), e = 2, 3, 4, m = 6–12, plus 4 full Laplacians incl. H(6,4); α = 1 control differs 14/14 | checks/k6_compute.log |
| K7 | CORRECT | 71 lattices (p = 3, 5, 7; a = 1, a = p−1, r = p) stable; 2670/2670 cokernels = Lemma 8; x = p^{−ν−1} unstable, p^{1−ν} and 0 stable but wrong | checks/k7b.log |
| K8 | CORRECT | 6/6 md5 = §9; manifest 14/14; 115/115 sealed groups recomputed | checks/k8_md5.log, verify_paper_numbers.log |
| K9 | CORRECT (conjecture supported) | (i), (ii) hold in 14 cells: λ = 12 (8 cells not in §8: q = 9, 27; c = 4–6) and the new block λ = 13; §8 table reproduced | checks/k9.log |
| L1 JNR03 | CORRECT | quotation verbatim; Thm 13 gives A with multiplicities; Thm 2 gives C for e = 0 | JNR03 pdf from Reiner's page |
| L2 Priority | PRESENTATION | **d = 2 ALREADY KNOWN** (Ducey–Gerhard–Watson arXiv:1507.06583, Thm 1.1: all of K(H(2,q))); everything else NOT FOUND; nothing CONTRADICTED | OpenAlex (45 citers), arXiv, DJ14 |
| L3 Wilson | GAP | t ≤ min(k,n−k) is Wilson's range (arXiv:1302.4249 Thm 2.1); CSX15 (2) states t ≤ k ≤ n/2; cite [Wil90] directly | CSX15 p. 4; arXiv restatements |
| L4 Tilting | CORRECT | Donkin: [Don93, Prop. 2.1], explicit in STWZ Prop. 3.4(a); lifting over Z_p: HW §5.4, Lemma 5.3 / Cor. 5.5 (Jantzen E.19–E.22) | arXiv PDFs in checks/downloads |

### Corrections required (for the author)
1. Cite Ducey–Gerhard–Watson (arXiv:1507.06583, EJC 2016) and JNR03 Example 11 for d = 2. Restrict the «new» claims for B, C, D, G, H to d ≥ 3.
2. Theorem D: cite Wilson [Wil90, Thm 2] for the range t ≤ min(k, m−k). CSX15 (2) covers only k ≤ n/2, which misses 2s = m−1.
3. The remark after Theorem G: the (4,3,4) example does not make G's formula fail. Only F's simplified form fails there. G's formula agreed in 784/784 pieces with p ∤ q.
4. Lemma 8: move «every entry has valuation ≥ 1» after the elimination of g_{a+1} in the case r ≤ p−1.
5. §8: prove that every big clock exceeds θ for p = 2 (or say it is only checked). Give precise references for G₁-projectivity and for (T1) (Jantzen II.E.19–E.22).
6. Abstract and §9: «63» counts H(4,6) and H(5,4) twice (61 distinct groups; 105 in all). Describe the subsets behind «384» and «112». Note that the timing of the sealed predictions is not externally verifiable.
7. Theorem B: drop the vacuous condition (j,k) ≠ (0,0). Theorem H depends on the author's unrefereed [DST]; say so where it is claimed «proved».

## JOB 1 — proofs

### P1. Theorem A
**Hand check (§2).** K_q = qI−J. K_q e_0 = q e_0 − Σ_i e_i and Σ_i e_i = q e_0 + σ, so K_q e_0 = −σ; K_q f_i = q f_i (J kills differences), hence K_q σ = qσ. The basis (e_0, σ, f_1..f_{q−2}) is obtained from (e_0, f_1..f_{q−1}) by f_{q−1} ↦ σ (unimodular), which is unimodular from (e_0..e_{q−1}). So Z^q = A ⊕ W, both K_q-stable, K_q = q on W. On A^{⊗([d]∖T)} ⊗ W^{⊗T}, each factor i∈T contributes q, so L = (L_A + q|T|) ⊗ 1. On A^{⊗m} with S = positions of σ: K_q^{(i)} sends S to q S if i∈S and to −(S∪{i}) if i∉S, so L_A = qH − U; conjugating by diag((−1)^{|S|}) gives q(j+H)+U. Multiplicity C(d,j)(q−2)^j. **Proof in §2: CORRECT.**
**Comparison with JNR03 Thm 13 (original, see L1):** JNR prove L(K_{n_1}×…×K_{n_k}) ≈ ⊕_{S⊆[k]} M(N; n_S)^{⊕Π_{i∉S}(n_i−2)} (≈ = conjugation by GL(Z)), N = Σn_i, with M(m; m_1..m_r) = [[M(m; m_1..m_{r−1}), I],[0, M(m−m_r; m_1..m_{r−1})]]. Unwinding the recursion, M(N; n_S) is the operator e_T ↦ (N − Σ_{i∈T} n_i)e_T + Σ_{x∈T} e_{T∖x} on the subsets T ⊆ S (the identity block sends the coordinate T∪{s_r} to T). For n_i = q, |S| = r, the diagonal is q(d − |T|); complementation T ↦ S∖T (the order-reversing involution of the Boolean lattice of S) turns D into U and the diagonal into q((d−r) + |T'|): exactly q(c+H)+U on B_r with c = d − r. Multiplicity (q−2)^{d−r} for each of the C(d,r) sets S, i.e. C(d,j)(q−2)^j with j = d − r. So «after reversing the order of the subsets of S» is right, multiplicities included, and crediting A to JNR entirely is fair (the paper's own proof is a different, direct argument; both correct). **P1: CORRECT.**
### P2. Lemma 2
Need λ_s a_s μ_s = p^{w_s} and λ_{s+1} μ_s = 1 (block rank s → s+1 of PMQ is λ_{s+1} U μ_s since P, Q are scalar on each rank). With a_s = p^{w_s}u_s this is λ_s μ_s u_s = 1; the recursion μ_0 = 1, λ_0 = u_0^{−1}, λ_{s+1} = μ_s^{−1}, μ_{s+1} = (λ_{s+1}u_{s+1})^{−1} produces only units (products/inverses of units). Which entries are units: all λ_s, μ_s; the u_s are units by definition (u_s = 1 if a_s = 0, then λ_sμ_s = 1 and the diagonal stays 0). Over Z_(p) the diagonal entries q(c+s) are not units when p | q (that is why they are kept as p^{w}); the subdiagonal 1's stay 1. **CORRECT.** Corollary 1 follows (P7).
### P3. Lemma 3
- (1) D U^i v = i(m−2k−i+1) U^{i−1} v: from [D,U] = m − 2H, induction: D U^{i} v = U D U^{i−1}v + (m − 2(k+i−1)) U^{i−1}v = [(i−1)(m−2k−i+2) + m−2k−2i+2] U^{i−1} v = i(m−2k−i+1) U^{i−1}v. ✓
- Units: for r ≤ m/2, DU on U^{r−1−k}Λ_k is (r−k)(m−k−r+1) (take i = r−k in (1)); 1 ≤ r−k ≤ m and 1 ≤ m−k−r+1 ≤ m, so both are units when p > m. In the second part, factors i(m−2k−i+1) for 1 ≤ i ≤ r−k with k ≤ min(r, m−r): i ≤ m and m−2k−i+1 ≥ m−k−r+1 ≥ 1. ✓
- Splitting B_m(r) = U B_m(r−1) ⊕ Λ_r via the idempotent π = U(DU)^{−1}D: π² = U(DU)^{−1}(DU)(DU)^{−1}D = π, im π = U B_m(r−1) (since (DU)^{−1}D is onto B_m(r−1)), ker π = ker D because U(DU)^{−1} is injective (DU invertible ⇒ U injective on B_m(r−1)). ✓
- Triangularity of (ψ_{k'})∘Φ: correct; full rank by comparison over Q, and a split injection of free modules of equal rank is an isomorphism. ✓
- Each string is a bidiagonal block: in the basis v, Uv, …, U^{ℓ−1}v (v a basis vector of Λ_k), U sends U^i v to U^{i+1}v (subdiagonal 1) and U^{ℓ}v = 0; diagonal q(c+k+i). Deleting first row and last column leaves a unitriangular matrix, so the cokernel is cyclic, of order the determinant. ✓
- Count of strings of length m−2k+1: rank Λ_k = C(m,k) − C(m,k−1). ✓  **CORRECT.**
### P4. Theorems E and B
- E from Lemma 3: each of the C(m,k)−C(m,k−1) strings of Λ_k gives Z/p^{A_k}, A_k = Σ_{r=k}^{m−k}(e + v_p(c+r)); the zero diagonal entry occurs only at c = k = i = 0 and then the block is Z_(p) (free). ✓ (Theorem E needs only m < p; c is arbitrary, so v_p(c+r) can be > 0. ✓)
- Ballot identity: C(v+2k−1,k) − C(v+2k−1,k−1) = (v+2k−1)!/(k!(v+k)!)·[(v+k) − k] = v/(v+2k)·C(v+2k,k). ✓ and Σ_k b(k,v)x^k = C(x)^v (Lagrange inversion; standard). ✓
- Generating function: (yz c(z))^v = y^v Σ_k b(k,v) z^{v+2k}; coefficient of z^{d+1} in (1+uz)^d Σ_{v≥1}(yzc)^v is Σ_{j+v+2k=d+1} C(d,j)u^j b(k,v) y^v; the only term with v = d+1 is j = k = 0, removed by −y^{d+1}. ✓
- Lists d = 2,3,4 recomputed by hand from n_v: d=2: (u²+1, 2u); d=3: (u³+3u, 3u²+2, 3u); d=4: (u⁴+6u²+2, 4u³+8u, 6u²+3, 4u) using b(1,1)=1, b(2,1)=2, b(1,2)=2, b(1,3)=3. All ✓.
- p > d: every piece X(d−j, j) has m = d−j < p and c + r ≤ j + (d−j) = d < p, so v_p(c+r) = 0 whenever c + r ≥ 1; hence A_k = e(m−2k+1). ✓ The free part: the string k = 0 of the piece j = 0 has length d+1, i.e. v = d+1, which is outside 1 ≤ v ≤ d; so it is automatically excluded (the condition (j,k) ≠ (0,0) in n_v is vacuous, because j+2k = d+1−v ≥ 1). PRESENTATION only.  **CORRECT.**
### P5. Lemmas 4, 5 and Theorem C
- Lemma 4: M^{−1} = Σ_k (−Δ^{−1}U)^k Δ^{−1}; a term from S to T (|T∖S| = k) is a maximal chain S = S_0 ⊂ … ⊂ S_k = T (k! chains), each contributing Π_{i=0}^{k} 1/q(c+s+i). ✓
- «Exponent = largest denominator»: M = P D Q over the DVR ⇒ M^{−1} = Q^{−1}D^{−1}P^{−1}; min valuation of the entries is invariant under multiplication by invertible matrices, so it equals −(largest exponent of D). ✓ (Justified, one line.)
- Rewriting: with a = c+s, b = c+s+k, L = k+1: Σ_{i=0}^{k} v_p(c+s+i) − v_p(k!) = v_p(b!/((a−1)!(b−a)!)) and b!/((a−1)!(b−a)!) = L·C(b,L). ✓
- Lemma 5, re-derived: the carry bound v_p(L) + v_p C(b,L) ≤ ⌊log_p b⌋ is right (no carry below v_p(L), no carry out of the top digit). Induction: s* = leading digit·p^λ; case L ≤ s* bounded by e s* + λ ≤ e s* + v_p(s*); case L > s*: since r' + (r−r') = r < p^λ and s* has zero low digits, the carries of L + (b−L) are those of r' + (r−r'); v_p(s*+t) = v_p(t) because t < p^λ ≤ p^{v_p(s*)}. ✓ For e = 0 the max is ⌊log_p d⌋, attained at L = b = p^{⌊log_p d⌋}. ✓
- Proof of Theorem C: piece j = 1 occurs iff q ≥ 3 and its range a ∈ [1,d] contains the ranges of all j ≥ 2. The j = 0 piece: the row of ∅ in M_0 = qH + U is zero (∅ is never in the image of U and its diagonal entry is 0), so coker M_0 = Z∅ ⊕ B'/(M''B' + Zu); M'' (c = 0 on ranks ≥ 1, diagonal qs ≠ 0) is nonsingular and Lemma 4 applies to it verbatim with the same range 1 ≤ a ≤ b ≤ d; a quotient of coker M'' has exponent ≤ that of coker M''. ✓ The case e = 0 also follows the same lines (diagonal entries are units times p^{v_p(c+s)}). The JNR Theorem 2 claim is checked in L1.
- Example q = 3, d = 10: max_s (s + v_3(s)) = 9 + 2 = 11 at s = 9 (s = 10 gives 10). ✓ Q_2: bound e·2 + v_2(2) = 3, group Z/4. ✓  **CORRECT** (K3 checks by machine).
### P6. Theorem D
- coker L = Z ⊕ K, so coker L ⊗ F_p = F_p ⊕ K/pK and the number of cyclic factors of Syl_p K is dim_{F_p}(coker L ⊗ F_p) − 1. ✓ Right-exactness: coker(M) ⊗ F_p = coker(M mod p); since p | q, q(j+H)+U ≡ U. ✓
- U is block-subdiagonal (B(s) → B(s+1)), blocks in disjoint rows and columns, so rank U = Σ_s rank W_{s,s+1}. ✓
- Complementation: S ⊂ T (|S| = s, |T| = s+1) iff T^c ⊂ S^c, so W_{s,s+1} = (W_{m−s−1,m−s})^T up to the complement bijection. ✓ With (t,k) = (m−1−s, m−s) the entries C(k−i,t−i) = m−s−i. ✓
- **Range of Wilson's theorem.** The paper says «for t ≤ min(k, m−k) … (we use the statement as given in [CSX15, (2)])». CSX15 does **not** state that range: it says (material/CSX15, p. 4) «We shall state his result for t ≤ k ≤ n/2». The paper needs (t,k) = (s, s+1) with 2s ≤ m−1; when m is odd and 2s = m−1 one has k = (m+1)/2 > m/2, outside CSX15's stated range (and complementation sends this case to itself). That case is covered by Wilson's original statement (t ≤ min{k, n−k}), see L3. So the result stands but the citation is wrong for the middle rank of odd m: **GAP (citation), fixable by citing [Wil90] directly**. The middle-rank case is checked numerically in K4.
- N is correctly «number of cyclic factors of the p-part» = dim(coker ⊗ F_p) − 1. ✓
- **Verdict P6: CORRECT with a citation GAP** (statement used is Wilson's, not CSX15 (2)).
### P7. Corollary 1
By Theorem A, Syl_p K = ⊕_j Syl_p X_q(d−j,j)^{C(d,j)(q−2)^j} (minus the free Z); by Lemma 2 each Syl_p X_q(m,c) depends only on w_s = v_p(q(c+s)) = e + v_p(c+s), i.e. on e (and c, m). ✓ **CORRECT.**
### P8. Corollary 6
- B_m ⊗ F_3 = V^{⊗m}, S ↦ ⊗_i v_{[i∈S]}, and U = Σ_i e_i with e_i the Jordan block in factor i (v_0 ↦ v_1). ✓ The e_i commute; (Σe_i)^3 = Σ e_i^3 + 3(…) + 6(…) = 0 in char 3. ✓ F_3[e]/(e^3) with e primitive is a Hopf algebra (restricted enveloping algebra of a 1-dim p-Lie algebra with e^{[3]} = 0) and U is the action of e on the tensor product. ✓
- J_2⊗J_2: e²(v_0⊗v_0) = e²v_0⊗v_0 + 2ev_0⊗ev_0 + v_0⊗e²v_0 = 2v_1⊗v_1 ≠ 0 ⇒ a J_3, dimension 4 ⇒ J_3 ⊕ J_1. ✓ J_3 is the regular module; P⊗M is projective for a finite-dimensional Hopf algebra; projectives over a local algebra are free ⇒ J_3⊗J_2 ≅ J_3². ✓
- Recursion (a,b,c) ↦ (b, a, b+2c) from (1,0,0); a_m + b_m = 1, b_m = [m odd], c_m = (2^m − 1 − [m odd])/3, f(m) = 1 + (2^m − 1 − [m odd])/3. ✓ (f(m) = number of Jordan blocks = dim coker U. ✓)
- Sum: Σ_m C(d,m)(q−2)^{d−m} = (q−1)^d, Σ C(d,m)(q−2)^{d−m}2^m = q^d, Σ C(d,m)(q−2)^{d−m}[m odd] = ((q−1)^d − (q−3)^d)/2, which gives exactly the printed N; for q = 3 (d ≥ 1): N = 2^{d−1} + 3^{d−1} − 1. ✓ The list 1, 4, 12, 34, 96, 274 matches. **CORRECT** (K4 checks by machine).
### P9. §6, (T1)–(T3)
- **(T1)** correct. The argument given is a sketch («Ext¹(Δ,∇) = 0, so decompositions over F_p lift»). A precise statement exists: over a complete DVR R there is a unique indecomposable tilting T_R(λ), every tilting R-module is uniquely a sum of them, and T_R(λ) ⊗ R/m ≅ T_{R/m}(λ) — Jantzen RAGS II, Lemma E.19, Prop. E.22, E.20, as quoted (with these item numbers) in Heidersdorf–Wenzl arXiv:1912.09457v3, §5.4, Lemma 5.3 and Cor. 5.5 (I did not have Jantzen's book itself). V^{⊗m} ⊗ Z_p is tilting because good/Weyl filtrations can be checked mod p (ibid. Lemma 5.2 = Jantzen B.9–B.10) and V^{⊗m} over F_p is tilting. Citing (T1) as standard is acceptable in a preprint, but the item should be given. For p = 2 [DST, Lemma 3.3, Cor. 3.4, Thm 3.6] write it out (checked: DST pp. 13–15).
- **(T2)** correct; re-derived. Classification: λ ≤ p−1 or λ = (a+1)p−1 ≤ p²−1 gives L(λ) = St ⊗ L(a)^{[1]} (Steinberg), of dimension λ+1, so Δ(λ) = T(λ) is simple; otherwise λ−(p−1) = r + pa with r ≡ λ−p+1 mod p in [1,p−1], or λ = p²+p−1 with r = p, a = p−1. Characters: χ(p−1)·χ(n)(z^p) = χ(pn+p−1) (telescoping quotient), and χ(N)(z^r + z^{−r}) = χ(N+r) + χ(N−r) for r ≤ N+1 (multiset of weights); with N = pa+p−1 this gives χ(λ) + χ(λ−2r); for λ = p²+p−1, χ(p−1)·[χ(p)+χ(p−2)](z^p) = χ(p²+p−1) + χ(p²−p−1). Donkin's formula holds for SL₂ and all p (STWZ arXiv:2105.07724, Prop. 3.4(a); original [Don93, Prop. 2.1]). Attribution «Donkin 1993; Jantzen» correct. Non-split extension over F_p ⇒ non-split over Z_p ✓.
- **(T3)** correct: β(m,λ) = n_λ + Σ_{ν: ν⁻=λ} n_ν, and λ ↦ λ⁻ is injective in the range (λ⁻ ≡ p−1−r mod p for r ≤ p−1; λ⁻ = p²−p−1 ≡ p−1 only for r = p). Machine: (T3) = character multiplicities for p = 3, m ≤ 11 (k9.py) and the [DST] recursion = characters for p = 2, n ≤ 20 (k6_predict.py).
- (T1) for odd p «cited as standard, not proved»: acceptable for a preprint; the precise reference above should be added. **P9: CORRECT (citation of (T1) imprecise).**
### P10. Lemma 7
Re-derived line by line:
- ν by Kummer: r ≤ p−1: λ−r = (a+1)p−1 has digits (a, p−1); adding t ∈ [1,r] carries out of the units digit, and once more iff a = p−1 ⇒ ν = 1 + [a = p−1]. r = p: λ−r = p²−1; t < p carries twice, t = p once ⇒ ν = 1. ✓ (K7: 71/71.)
- f-recursion: f s̃_j − (j+1)s̃_{j+1} = [(j+r+1)x_j − (j+1)x_{j+1}] ℓ_{j+r+1} must lie in T ∩ Δ_Q(λ) = Δ_{Z_p}(λ) (purity of the sub). Inside a segment j+1 is a unit, so x_j ≡ [Π (i+r+1)/(i+1)] x_{kp} = C(j+r,j)C(kp+r,kp)^{−1} x_{kp} mod Z_p (the multiplier is p-integral). f^{(p)}-step: C((k+1)p,p) ≡ k+1 (Lucas), C((k+1)p+r,p) ≡ k+1 (r ≤ p−1) or k+2 (r = p, where μ = p²−p−1 forces k+2 ≤ p−1): all units; C(kp+r,kp) is also a unit (≡ 1 or k+1). The rational identity holds (both sides (n+r)!(n−p)!/(n!(n−p+r)!)). Hence x_j ≡ C(j+r,j)x_0. ✓
- e^{(t)}s̃_0 = x_0 C(λ−r+t,t) ℓ_{r−t} ⇒ v_p(x_0) ≥ −ν. ✓ If v_p(x_0) ≥ 1−ν, the image of s̃_0 in T⊗F_p is primitive of weight μ; by the universal property of Weyl modules (Hom_G(Δ(μ), M) ≅ U⁺-fixed vectors of weight μ, Frobenius reciprocity — true for every rational module, no condition on the other weights) it gives Δ(μ) → T(λ) whose composite with T(λ) → Δ(μ) fixes the generator, hence is the identity: the sequence splits, contradicting indecomposability. **Complete**, though the universal property is used without citation (Jantzen II.2.13).
- «The lattice so described IS T»: T exists by (T1)–(T2), and the argument shows T has exactly this form up to rescaling y by a unit; so stability needs no separate check. **Complete.** The lifts can be taken weight-homogeneous: T is the direct sum of its weight spaces (for B_m: the rank grading), and the Q-complement Δ_Q(μ) is canonical (Hom_Q(Δ(μ),Δ(λ)) = 0).
- K7 confirms everything by machine and shows why the indecomposability step is needed: the lattice with x = p^{1−ν} is also Dist-stable (but split mod p). **P10: CORRECT.**
### P11. Lemma 8
- Mℓ_i = N_iℓ_i + (i+1)ℓ_{i+1} ✓; M s̃_j = N_{j+r}s̃_j + (j+1)s̃_{j+1}, ℓ-component p^{−ν}[(j+r+1)C(j+r,j) − (j+1)C(j+r+1,j+1)] = 0 ✓; M s̃_μ = N_{μ+r}s̃_μ + u ℓ_{(a+1)p}, u = p^{−ν}C(μ+r,μ)(a+1)p, C(μ+r,μ) a unit by Lucas (digits (a,p−1) over (a,p−1−r), or (p−1,p−1) over (p−2,p−1) when r = p) ⇒ v_p(u) = v_p((a+1)p) − ν = 0 (r ≤ p−1) or 1 (r = p) ✓.
- Non-unit links: ℓ-chain i+1 = tp, 1 ≤ t ≤ a+1, valuation 1 except t = a+1 = p (τ = 2) ✓; s̃-chain j+1 = tp ≤ μ: a of them (r ≤ p−1), a−1 (r = p) ✓.
- Relations after rescaling (the generator–relation incidence graph is a tree, so all unit coefficients can be normalized to 1) ✓.
- Smith form: I redid the elimination with Schur complements. r ≤ p−1: use the unit on g_{a+1}; then the 2a pivots p at (R_t, g_{t+1}), (S_t, h_{t+1}) propagate to (R_a, g_0) = p^{A−α−a} = p^{E11}, (R_a, h_0) = ±p^{A'+τ−a} = p^{E12}, (R_end, h_0) = ±p^{A'+α−a} = p^{E22}, (R_end, g_0) = 0. r = p: the unit of M′ on g_{a+1} sits in the s̃-end relation; same 2×2. Smith of [[p^{E11}, ∗p^{E12}],[0,p^{E22}]] = (p^x, p^{E11+E22−x}) ✓. c = k = 0: column g_0 zero ⇒ Z_p and p^{min(E12,E22)} ✓. Simple blocks ✓. Remark a+1 < p: E12 ≤ E22 (α ≥ 1), E12 ≤ E11 (A−α = A' + Σ_{t<r}v_t ≥ A'+1), y = A−1−a ✓. Example p=3, λ=10, k=0, e=1: (x,y) = (11,11) for c=1, (10,12) for c=2 — recomputed by hand ✓.
- **PRESENTATION slip:** «Every entry has valuation ≥ 1, so the relation matrix is pM′» is false as placed when r ≤ p−1: the end relation of the s̃-chain has the unit coefficient p^{v_p(u)} = p^0 on g_{a+1}. It becomes true after eliminating g_{a+1}, which the next paragraph does; the conclusion is unaffected.
- K7: 2670/2670 cokernels on the lattices = Lemma 8. **P11: CORRECT (one misplaced sentence).**
### P12. Theorems F and G
- They follow from (T1)–(T3) + Lemmas 7–8 for every m ≤ p²+p−1 and every prime, p = 2 included (for p = 2 the two-factor λ are 2, 4 (a = p−1, ν = 2) and 5 (r = p); Theorem G = Theorem H for p = 2, m ≤ 5, c ≤ 8, e ≤ 4: 216/216).
- Precise enough: yes — my independent coding (checks/thmg.py) reproduces all 115 sealed groups and my 18 + 14 + 8 new predictions; two people compute the same group.
- F = the case m ≤ 2p−2 of G: only a = 0 occurs; x = E12 = A'+1 with A' = A_c(m, 2p−2−λ), y = A−1; n_λ = β(m,λ) − β(m, 2p−2−λ) for λ ≤ p−2, β(m,p−1) for λ = p−1, β(m,λ) for λ ≥ p; c = 0: free plus p^{min(E12,E22)} = p^{A'+1}. ✓
- m = p²+p is where four Weyl factors first appear: λ+1 = p²+p+1 = 111_p is the least number with three non-zero digits; every λ ≤ p²+p−1 has λ+1 ≤ 110_p ✓.
- **Remark after Theorem G** («The hypothesis e ≥ 1 is needed: for p ∤ q the formula fails, for instance when (q,p,d) = (4,3,4)»): as stated, **wrong example** — Theorem G's formula evaluated at e = 0 gives {1:108} = the computed Syl_3 K(H(4,4)), and agrees in 784/784 pieces with p ∤ q that I tried (checks/e0_scan.log); it is Theorem F's simplified form that fails at (4,3,4) ({1:92, 2:8}, checks/e0_thmF.log). Minor (the case p ∤ q is JNR Thm 2 anyway), but the sentence must be fixed or moved.
- **P12: CORRECT (with one wrong remark).**
### P13. Theorem H
- **[DST] statements for every α ≥ 1** (pages of material/DST…v10.pdf): §3.4 defines X^{(α)}(λ,i) = coker(F + 2^α(D+i) on T(λ)) for every α ≥ 1 (p. 15); **Theorem D** «for every family λ, every α ≥ 1 and every shift i ≥ 0» (p. 18); **Prop. 5.2** (cost form, general α, p. 19); **Prop. 5.4** (shift 0, R♯ with α; its valuation formula is for every α, its clock identity u_0 = k+K+x♯ is stated for α = 1 only, p. 20–21); **Theorem 7.10** «for every family λ, every α ≥ 1 and every shift i ≥ 1», with the i = 0 case (p. 28); **Theorem 3.6** (p. 14). So the claim is right **as a reading of [DST]**. Caveat: [DST] is an unrefereed preprint of the same author; its own verification table (§12, p. 45) covers α = 1, 2 for Theorems D and 7.10 (houses up to α ≤ 3–4).
- Reduction to f + 2^e(D_λ+i): correct (Lemma 2's recursion on floors; u odd is a unit of Z_2).
- §7 formula vs [DST]: small clocks = Theorem D; big clocks k + αK + κ(m,K) + ŷ_D = Thm 7.10 + the factor 2^k of Theorem D; i = 0: ∞ and k + αK + ŷ♯_D over D ≠ ∅ (Thm 7.10, Prop. 5.4); λ = 0: Z/2^{α+v_2(i)}. **Identical.**
- K6: 14/14 predictions (e = 2, 3, 4) confirmed; α = 1 control differs in 14/14. **P13: CORRECT (conditional on [DST]).**
### P15. Conjecture I
- Decomposition into Y_p(λ, i, e)^{n_λ(m)}: correct for every m, by (T1) and Lemma 2's rescaling (n_λ(m) = general tilting multiplicities).
- «Number of cyclic summands = dim T(λ)/p for λ ≥ p−1»: correct. Reason: T(λ) is a summand of St ⊗ T(λ−p+1) (tilting, top weight once), St is projective over G₁, so T(λ) is G₁-projective and hence free over F_p[f]/(f^p) ⊂ Dist(G₁) (PBW). The reference «[Jan03, Part II, Chapter E]» is to a whole chapter — imprecise. (K9: 12 = 36/3 summands in all 14 cells.)
- «Number of Weyl factors = 2^{|I(λ)|}»: character argument re-derived (λ+1 = r' + p(b+1) ⇒ |I(λ)| = [r'≠0] + |I(b)|) ✓; also stated in Tubbenhauer–Wedrich arXiv:1907.11560v2, §1 p. 2.
- Holds in the proved cases: for Theorem G the inequalities are right (E11 ≥ p+(p−1)a, E12, E22 ≥ (p−1)a+2, A−a ≥ (a+1)p−a; and λ = p−1 has k = 1 with A ≥ p ≥ 2) ✓. For p = 2 the text says «it follows from Theorem H», but the needed inequality (every big clock > θ) is **not proved** in the paper — only checked on the formulas (theirs: 9045 groups; mine: 9000 groups, λ ≤ 200, α ≤ 5, i ≤ 8, 0 exceptions, least margin exactly 1). **GAP (small, likely fillable).**
- Precise: yes. Plausible: yes; K9 confirms (i) and (ii) in 14 cells, including 8 new cells of λ = 12 (q = 9, 27; c = 4..6) and the **new block λ = 13** (3 cells). I found no reason it must fail. Small overstatement: «the conjecture predicts (Z/3)^8» uses the cell (3,0) already seen (the conjecture alone gives 8 summands of order ≤ 9, independent of (i,e)).
- **P15: CORRECT as a conjecture; one unproved step in «holds whenever the groups are known» (p = 2).**
### P14. Grades and numbers
- «We prove»: the proofs of A–H, Lemmas 2–5, 7, 8, Cor. 1, 6 check (gaps listed in P6, P11, P12, P15). Theorem H is proved **modulo [DST]** (unrefereed, same author).
- «New»: the **d = 2 case** of Theorems B, C, D, G, H (the whole group K(H(2,q)), all primes) is **already known**: Ducey–Gerhard–Watson, arXiv:1507.06583, Thm 1.1 (1.1) (my engine agrees, 34/34), and derivable from JNR03 Thm 13 + Example 11; the paper does not cite it. Theorem C for e = 0 = JNR Thm 2 (acknowledged). Jordan types in Cor. 6 classical (acknowledged). Otherwise NOT FOUND (L2).
- Numbers checked and right: N = 1, 4, 12, 34, 96, 274 (q = p = 3); the JNR-bound comparison (= for d ≤ 2, −1 at d = 3, smaller for 4 ≤ d ≤ 8, p ≤ 11); E = 11 at s = 9 (q = 3, d = 10); ranges d ≤ 11 (p=3), 29 (p=5), 5 (p=2); Example 9; the §10 table (7 rows); the §8 table (8 cells); md5 of the six sealed files; **all 115 sealed groups of files 1–5 reproduced** by my engine (checks/verify_paper_numbers.log); the count 9045 = 201·5·9 matches «λ ≤ 200, e ≤ 5, i ≤ 8».
- **«107 predictions (44 in version 1, 63 in version 3)»**: 44 = 30 (file 2) + 14 (file 3) ✓. 63 = 41 + 22 counts Syl_2 K(H(4,6)) and Syl_2 K(H(5,4)) **twice** (once from the pieces, once «again from its full Laplacian»): files 4 and 5 contain 40 + 21 = 61 distinct predicted groups, so 105 distinct groups in all (all correct). Also, the «before they were computed» cannot be verified externally: the md5s were published together with version 3 and files 4–6 carry no timestamp. PRESENTATION.
- Counts not reproducible from the text: «384 cases (m ≤ 11, e ≤ 4, c ≤ 4)» (the full grid has 12·4·5 = 240) and «all 112 cases with e ≥ 2» (3/4 of 384 would be 288); the subsets used should be described. PRESENTATION.
- Other: Theorem B's condition (j,k) ≠ (0,0) is vacuous (P4); Lemma 8's misplaced sentence (P11); the remark after Theorem G (P12, wrong example); Theorem D's citation of CSX15 for Wilson's range (P6, L3).

## JOB 2 — computations

### K1. Theorem A
`checks/k1_k4.py` → `checks/k1_k4.log` (07:53, 18 s, 57 MB). 20 cells (d,q,p), q^d ≤ 729: Syl_p from the full Laplacian of H(d,q) (my engine) = Syl_p from the pieces Σ_j C(d,j)(q−2)^j X_q(d−j,j), **20/20**. Cells: (5,3,3), (6,3,3), (6,3,2), (4,4,2), (4,4,3), (3,6,2), (3,6,3), (3,8,2), (2,9,3), (3,9,3), (2,10,2), (2,10,5), (2,12,2), (2,12,3), (2,27,3), (4,5,5), (4,5,2), (2,25,5), (3,7,7), (3,7,3) — includes p | q with p ≤ d ((5,3,3), (6,3,3), (4,4,2), (3,6,2), (3,6,3), (3,8,2), (3,9,3), (2,10,2), (2,12,2)), composite q (4, 6, 8, 9, 10, 12, 25, 27) and p ∤ q. **Control**: one extra copy of X_q(d−1,1) changes the group in 20/20. Example: Syl_2 K(H(3,8)) = {1:1, 3:216, 5:18, 7:110, 9:18} both ways.
### K2. Theorem B
Same run. 12 cells with p > d, formula of Thm B (coded from the statement) vs computation, **12/12**: from the full Laplacian (2,9,3) e=2 → {2:50, 4:14}; (2,5,5); (3,5,5); (4,5,5) → {1:137, 2:132, 3:57, 4:12}; (2,25,5) e=2 → {2:530, 4:46}; (3,7,7); (4,7,7) → {1:777, 2:540, 3:153, 4:20}; (2,10,5); from the pieces (Thm A, verified in K1): (4,10,5), (3,15,5), (4,25,5) e=2 → {2:283017, 4:48852, 6:3177, 8:92}, (3,49,7) e=2.
### K3. Theorem C
Same run. 21 cells with q ≥ 3, **21/21** agree with E = max_s(es + v_p(s)) (e ≥ 1) or ⌊log_p d⌋ (e = 0):
- (10,3,3) [pieces]: computed exponent 3^11, predicted 3^11 with the maximum at s = 9 only (the guess ed + v_p(d) = 10 fails) ✓; (9,3,3) 3^11 ✓; (6,3,3) [Laplacian] 3^7.
- p = 2, q even: (4,4,2) 2^10, (5,4,2) 2^10, (3,8,2) 2^9, (2,12,2) 2^5 [Laplacians]; (6,6,2) 2^7, (8,4,2) 2^19 [pieces].
- other: (3,9,3) e=2 3^7; (5,6,3) 3^5; (6,5,5) 5^6.
- p ∤ q (e = 0): (5,3,2) 2^2, (6,3,2) 2^2, (4,4,3) 3^1, (4,5,2) 2^2 [Laplacians]; (8,3,2) 2^3, (7,3,7) 7^1, (9,4,3) 3^2, (10,4,3) 3^2, (7,5,7) 7^1 [pieces].
- q = 2: Syl_2 K(Q_2) = Z/4 (computed), the bound 2^3 is not attained, as the paper says.
### K4. Theorem D and Corollary 6
Same run. 17 cells with p ≤ d, number of cyclic factors computed = N of Thm D, **17/17**; for the 9 cells with p = 3 also = Corollary 6, **9/9** (3 | q, q ≠ 3: (3,6,3) N=138, (4,6,3) 757, (3,9,3) 534, (3,12,3) 1362 [Laplacians], (5,15,3) 563508, (4,9,3) 4450, (5,6,3) 4194 [pieces]; q = 3: (4,3,3) 34, (6,3,3) 274, (8,3,3) 2314). Others: (4,4,2) 135, (5,4,2) 527, (3,10,2) 755, (5,5,5) 1557, (6,5,5) 7246, (7,7,7) 416609, (6,6,2) 25375.
- Rank of W_{s,s+1} over F_p by direct elimination vs r_p(m,s): 328 cases (p ∈ {2,3,5,7}, all s, m ≤ 11 and some larger), **0 mismatches**, including **24 middle ranks 2s = m−1 of odd m** (the case outside CSX15 (2)'s stated range, see P6).
- Comparison with the JNR Thm 3 bound for q = p: equality for d ≤ 2, one less for d = 3, strictly smaller for 4 ≤ d ≤ 8, p ∈ {3,5,7,11} (e.g. p=3: N = 34 vs 40 at d=4) — as the paper says (the content of JNR Thm 3 itself: see L1).
### K5. Theorem G (predictions before computation)
**Predictions written at Tue Oct 13 07:55:35 CEST 2026 (from `date`), before computing any of these pieces** (file `checks/k5_predictions.txt`, md5 5e459c53dcf5b4e0572b0a9d97c7d518; format {v: multiplicity of Z/p^v}, free = number of Z_p):
```
p=3 q=9 e=2 m=9 c=1 predicted Syl_p X_q(m,c) = {1: 45, 5: 1, 6: 41, 8: 41, 9: 7, 13: 27, 18: 7, 20: 2} free=0
p=3 q=9 e=2 m=10 c=0 predicted Syl_p X_q(m,c) = {1: 90, 2: 1, 3: 41, 7: 90, 11: 41, 12: 34, 14: 34, 16: 1, 20: 9} free=1
p=3 q=3 e=1 m=11 c=2 predicted Syl_p X_q(m,c) = {1: 221, 2: 1, 3: 131, 6: 131, 7: 34, 8: 109, 9: 35, 11: 20, 13: 1} free=0
p=3 q=9 e=2 m=11 c=1 predicted Syl_p X_q(m,c) = {1: 221, 5: 1, 6: 131, 8: 131, 9: 34, 14: 109, 15: 1, 18: 34, 20: 20, 25: 1} free=0
p=3 q=3 e=1 m=11 c=7 predicted Syl_p X_q(m,c) = {1: 221, 3: 1, 4: 262, 5: 34, 7: 109, 8: 1, 10: 34, 11: 20, 14: 1} free=0
p=3 q=27 e=3 m=10 c=4 predicted Syl_p X_q(m,c) = {1: 90, 5: 1, 6: 41, 11: 90, 16: 41, 17: 34, 23: 34, 25: 1, 29: 9, 33: 1} free=0
p=3 q=6 e=1 m=9 c=9 predicted Syl_p X_q(m,c) = {1: 45, 2: 1, 3: 41, 5: 41, 6: 7, 7: 27, 8: 7, 10: 1, 12: 1} free=0
p=2 q=4 e=2 m=4 c=9 predicted Syl_p X_q(m,c) = {1: 2, 3: 2, 8: 2, 10: 2} free=0
p=2 q=12 e=2 m=5 c=5 predicted Syl_p X_q(m,c) = {1: 6, 7: 4, 8: 1, 11: 4, 14: 1} free=0
p=2 q=32 e=5 m=5 c=6 predicted Syl_p X_q(m,c) = {1: 6, 13: 4, 14: 1, 23: 4, 32: 1} free=0
p=2 q=14 e=1 m=4 c=13 predicted Syl_p X_q(m,c) = {1: 2, 2: 2, 7: 2, 8: 2} free=0
p=2 q=2 e=1 m=5 c=0 predicted Syl_p X_q(m,c) = {1: 6, 3: 4, 4: 1, 6: 4} free=1
p=5 q=5 e=1 m=11 c=0 predicted Syl_p X_q(m,c) = {1: 12, 3: 89, 4: 43, 5: 55, 6: 220, 8: 43, 9: 1, 11: 10} free=1
p=5 q=5 e=1 m=11 c=3 predicted Syl_p X_q(m,c) = {1: 12, 2: 89, 3: 43, 5: 55, 6: 220, 9: 43, 10: 1, 11: 10, 12: 1} free=0
p=5 q=25 e=2 m=12 c=1 predicted Syl_p X_q(m,c) = {1: 24, 2: 89, 3: 43, 6: 144, 7: 153, 11: 275, 15: 153, 16: 1, 19: 43, 20: 11, 22: 11, 26: 1} free=0
p=5 q=10 e=1 m=12 c=4 predicted Syl_p X_q(m,c) = {1: 24, 2: 89, 3: 43, 4: 144, 5: 153, 6: 275, 7: 153, 8: 1, 9: 43, 10: 11, 12: 11, 14: 1} free=0
p=5 q=5 e=1 m=12 c=0 predicted Syl_p X_q(m,c) = {1: 113, 2: 43, 4: 144, 5: 153, 6: 275, 7: 153, 8: 1, 10: 43, 11: 22} free=1
```
**Results** (`checks/k5_compute3.log`, 07:57, 16 s, 144 MB): **17/17 agreements**, every group equal to the prediction, free parts included. Notable: p=3, q=27 (e=3), m=10, c=4 has a factor 3^33 (computed with 128-bit precision); p=5, q=25, m=12, c=1 has a factor 5^26 (completed from v_5(det), see STEP 8); X_3(11,2), X_9(11,1), X_3(11,7) contain the block λ = 11 = p²+p−1 (r = p); m = 9, 10 contain λ = 9, 10 (a = p−1, ν = 2); p=2 cells include e = 2 and e = 5 with c up to 13.

**Extra prediction written at Tue Oct 13 07:57:41 CEST 2026, before computing** (`checks/k5b_predictions.txt`, md5 87eb8ab69edcca80f5945361da33fffb): `p=5 q=15 e=1 m=13 c=2 predicted Syl_p X_q(m,c) = {1: 91, 2: 233, 3: 196, 5: 144, 6: 856, 7: 1, 9: 196, 10: 12, 11: 65, 12: 12, 15: 1} free=0` (n_λ: 13:1, 11:12, 9:65, 7:196, 5:428, 3:144, 1:233).

**Result** (`checks/k5b_compute.log`, 07:58, 17.5 s, 530 MB): computed = predicted, **AGREE**. Total K5: **18/18**.

Self-tests of my coding of the formula: Example 9 reproduced ({1:2, 2:7, 3:8, 4:17}); formula = Theorem E for all m < p, p ∈ {5,7}, c ≤ 7, e ≤ 2 (0 mismatches).
### K6. Theorem H
**Predictions written at Tue Oct 13 08:07:40 CEST 2026 (from `date`), before computing** (`checks/k6_predictions.txt`, md5 29c160942429df4ca20d4b66f5bf1e6a), from the §7 formula as printed (my code checks/thmh.py); each line carries the α = 1 control:
```
piece q=4 e=2 m=6 c=5 predicted={1: 12, 6: 4, 7: 1, 8: 4, 9: 1, 10: 4, 12: 4, 13: 1, 15: 1} free=0 | control alpha=1: {1: 12, 5: 8, 6: 2, 7: 8, 8: 2} free=0 differs=True
piece q=12 e=2 m=8 c=5 predicted={1: 56, 2: 2, 3: 8, 4: 6, 9: 8, 10: 6, 11: 28, 12: 6, 17: 6, 19: 2} free=0 | control alpha=1: {1: 56, 2: 10, 3: 6, 6: 8, 7: 40, 10: 6, 11: 2} free=0 differs=True
piece q=4 e=2 m=10 c=9 predicted={1: 240, 2: 20, 4: 16, 5: 26, 6: 16, 7: 26, 8: 48, 14: 48, 15: 26, 17: 27, 19: 1, 20: 16, 21: 1, 23: 1} free=0 | control alpha=1: {1: 240, 2: 20, 3: 32, 4: 52, 5: 48, 9: 48, 10: 52, 12: 20} free=0 differs=True
piece q=4 e=2 m=12 c=5 predicted={1: 992, 2: 132, 3: 32, 4: 100, 8: 32, 9: 100, 10: 328, 11: 102, 13: 10, 17: 100, 19: 108, 26: 10, 28: 2} free=0 | control alpha=1: {1: 992, 2: 164, 3: 100, 5: 32, 6: 528, 7: 2, 8: 10, 10: 100, 11: 108, 15: 10, 16: 2} free=0 differs=True
piece q=8 e=3 m=7 c=6 predicted={1: 28, 2: 1, 7: 8, 8: 6, 15: 14, 21: 6, 27: 1} free=0 | control alpha=1: {1: 28, 2: 1, 3: 8, 4: 6, 7: 14, 9: 6, 11: 1} free=0 differs=True
piece q=24 e=3 m=9 c=7 predicted={1: 120, 2: 10, 8: 16, 9: 26, 14: 48, 19: 26, 21: 1, 27: 8, 34: 1} free=0 | control alpha=1: {1: 120, 2: 10, 4: 16, 5: 26, 6: 48, 7: 26, 9: 1, 11: 8, 14: 1} free=0 differs=True
piece q=8 e=3 m=11 c=5 predicted={1: 496, 2: 66, 7: 32, 8: 100, 14: 164, 15: 1, 21: 100, 23: 10, 27: 44, 31: 10, 40: 1} free=0 | control alpha=1: {1: 496, 2: 66, 3: 32, 4: 100, 6: 164, 7: 1, 9: 100, 11: 64, 16: 1} free=0 differs=True
piece q=40 e=3 m=6 c=0 predicted={1: 12, 4: 4, 5: 1, 11: 4, 12: 1, 13: 4, 15: 4, 16: 1} free=1 | control alpha=1: {1: 12, 2: 4, 3: 1, 5: 4, 6: 10} free=1 differs=True
piece q=8 e=3 m=12 c=6 predicted={1: 992, 2: 132, 6: 32, 7: 100, 10: 32, 11: 100, 12: 164, 13: 1, 16: 164, 17: 101, 19: 10, 21: 100, 23: 10, 24: 44, 31: 44, 32: 10, 36: 10, 38: 1, 42: 1} free=0 | control alpha=1: {1: 992, 2: 132, 4: 64, 5: 200, 6: 328, 7: 202, 9: 20, 10: 44, 13: 44, 14: 20, 16: 2} free=0 differs=True
piece q=16 e=4 m=8 c=6 predicted={1: 56, 2: 2, 6: 8, 7: 6, 12: 8, 13: 6, 14: 14, 23: 14, 24: 6, 30: 6, 33: 1, 37: 1} free=0 | control alpha=1: {1: 56, 2: 2, 3: 16, 4: 12, 5: 14, 8: 14, 9: 12, 11: 2} free=0 differs=True
full d=3 q=12 e=2 predicted Syl_2 K(H(d,q))={1: 1, 2: 1000, 4: 30, 5: 302, 6: 30} free=1 | control alpha=1: {1: 1001, 3: 362} differs=True
full d=2 q=24 e=3 predicted Syl_2 K(H(d,q))={4: 485, 7: 44} free=1 | control alpha=1: {2: 485, 3: 44} differs=True
full d=2 q=40 e=3 predicted Syl_2 K(H(d,q))={4: 1445, 7: 76} free=1 | control alpha=1: {2: 1445, 3: 76} differs=True
full d=6 q=4 e=2 predicted Syl_2 K(H(d,q))={1: 364, 3: 308, 4: 1, 5: 312, 6: 368, 7: 132, 8: 244, 9: 61, 10: 216, 11: 61, 13: 12} free=1 | control alpha=1: {1: 364, 2: 308, 3: 193, 4: 608, 5: 256, 6: 338, 7: 12} differs=True
```
**Results** (`checks/k6_compute.log`, 08:08, 39 s, 141 MB): **14/14 agreements** — 10 pieces (e = 2: X_4(6,5), X_12(8,5), X_4(10,9), X_4(12,5); e = 3: X_8(7,6), X_24(9,7), X_8(11,5), X_40(6,0), X_8(12,6); e = 4: X_16(8,6)) and 4 full groups from the full Laplacian: Syl_2 K(H(3,12)) = {1:1, 2:1000, 4:30, 5:302, 6:30}, Syl_2 K(H(2,24)) = {4:485, 7:44}, Syl_2 K(H(2,40)) = {4:1445, 7:76}, Syl_2 K(H(6,4)) = {1:364, 3:308, 4:1, 5:312, 6:368, 7:132, 8:244, 9:61, 10:216, 11:61, 13:12} (4096 vertices, 32 s). **Control α = 1 instead of α = e: different from the computed group in 14/14.**

Self-tests of my coding: [DST] example Syl_2 K(Q_6) = {1:12, 2:4, 3:1, 5:4, 6:10} ✓; the [DST] recursion for m_λ(n) = the character multiplicities for n ≤ 20 ✓; Theorem H and Theorem G give the same group for p = 2, m ≤ 5, c ≤ 8, e ≤ 4 (216/216) ✓.
### K9. Conjecture I
**Predictions written at Tue Oct 13 07:58:54 CEST 2026 (from `date`, printed by the same command that wrote them), before computing.** Conjecture I, applied to cells §8 does not list:
- Block λ = 12, p = 3 (λ+1 = 111_3, k = 2, I = {0,1}), cells X_q(12,c) with (q,c) ∈ {(9,0), (9,1), (9,2), (9,3), (3,4), (3,5), (3,6), (27,2)}: the block group has exactly 4 cyclic summands of order > 3^2 (for c = 0: Z_3 plus 3 finite ones), and the remaining summands have order ≤ 3^2 and are the same in all cells; from §8's table this common part is (Z/3)^8. Total number of summands dim T(12)/3 = 12.
- Block λ = 13, p = 3 (λ+1 = 112_3, k = 2, I = {0,1}; T(13) = T(4)⊗T(3)^{[1]}, Weyl factors 13, 9, 7, 3, dim 36), cells X_q(13,c), (q,c) ∈ {(3,0), (3,1), (9,1)} (8192² dense, ≈ 530 MB each): exactly 4 summands of order > 3^2 (c = 0: Z_3 + 3), the others of order ≤ 3^2 and identical in the three cells; 12 summands in all. This block is not in the paper.
- **Results** (`checks/k9.log`, 07:59–08:00, 80 s, 532 MB). Extracted top blocks (consistency: no negative counts, 12 summands in every cell):
  - λ=12, q=9 (e=2): c=0: Z_3 ⊕ (Z/3)^8 ⊕ 3^12 ⊕ 3^17 ⊕ 3^23; c=1: (Z/3)^8 ⊕ 3^14 ⊕ 3^16 ⊕ 3^24 ⊕ 3^26; c=2: same as c=1; c=3: (Z/3)^8 ⊕ 3^13 ⊕ 3^17 ⊕ 3^23 ⊕ 3^27.
  - λ=12, q=3: c=4: (Z/3)^8 ⊕ (3^9)^2 ⊕ (3^13)^2; c=5: same; c=6: (Z/3)^8 ⊕ 3^7 ⊕ 3^10 ⊕ 3^12 ⊕ 3^15. q=27 (e=3), c=2: (Z/3)^8 ⊕ 3^19 ⊕ 3^23 ⊕ 3^35 ⊕ 3^39.
  - Check of my extraction against §8's table: q=3, c=0: Z_3 ⊕ (Z/3)^8 ⊕ 3^7 ⊕ 3^10 ⊕ 3^12 ✓; q=3, c=1: (Z/3)^8 ⊕ (3^9)^2 ⊕ (3^13)^2 ✓; q=6, c=3: (Z/3)^8 ⊕ 3^8 ⊕ 3^10 ⊕ 3^12 ⊕ 3^14 ✓ (the table is reproduced independently).
  - **New block λ=13** (m=13): q=3, c=0: Z_3 ⊕ (Z/3)^8 ⊕ 3^6 ⊕ (3^11)^2; q=3, c=1: (Z/3)^8 ⊕ 3^8 ⊕ 3^10 ⊕ 3^12 ⊕ 3^14; q=9, c=1: (Z/3)^8 ⊕ 3^12 ⊕ 3^18 ⊕ 3^22 ⊕ 3^28.
  - **Both statements of Conjecture I hold in all 14 cells**: (i) exactly 4 = 2^{|I|} summands of order > 3^2 (free counted), (ii) the rest is (Z/3)^8 in every cell, for λ = 12 and for λ = 13, for e = 1, 2, 3 and c = 0..6.
- Method: compute X_q(m,c) with psnf; the multiplicities n_λ(m) from characters (Donkin's recursion, as in §8, implemented in checks/k9.py); subtract the blocks λ ≤ 11 given by the formula of Theorem G (checked in K5); the remainder is the block. Consistency checks: the remainder must be a genuine group (no negative counts) with 12 summands.
### K7. Lattice of Lemma 7
`checks/k7.py` → `checks/k7b.log` (08:04–08:05, 55 s, 14 MB; the first run `k7.log` was inconclusive for large exponents, see STEP 10). My own construction: ambient Δ_Q(λ) ⊕ Δ_Q(μ) with f^{(t)}ℓ_i = C(i+t,t)ℓ_{i+t}, e^{(t)}ℓ_i = C(λ−i+t,t)ℓ_{i−t} (same for s_j), lattice spanned by ℓ_i and s̃_j = s_j + x·C(j+r,j)ℓ_{j+r}; stability = all images of all basis vectors under e^{(t)}, f^{(t)} (1 ≤ t ≤ λ) have p-integral coordinates in the lattice basis.
- **All λ ≤ p²+p−1 with two Weyl factors, p = 3, 5, 7: 71 lattices** (7, 21, 43), including a = 1 (e.g. p=3: λ = 6, 7; p=5: 10–13; p=7: 14–19), a = p−1 with ν = 2 (p=3: λ = 9, 10; p=5: 25–28; p=7: 49–54) and λ = p²+p−1 with r = p (11, 29, 55).
- ν from its definition = the value claimed in Lemma 7 in **71/71**.
- x = p^{−ν}: **stable in 71/71**; cokernel of q(c+H)+U on the lattice (q ∈ {p, p², 2p}, 0 ≤ c ≤ p+1, 0 ≤ k ≤ 2; 24 random of these for p = 7) = G_c(m,λ) of Lemma 8, free part included, in **2670/2670** cases (315 for p=3, 1323 for p=5, 1032 for p=7; 4067 Smith forms needed the p^400 fallback).
- Controls: x = p^{−ν−1}: **not stable** in 71/71 (some e^{(t)}-image has a coordinate of valuation −1). x = p^{1−ν}: stable in 71/71 but the cokernel differs from Lemma 8 in **every** case (e.g. p=3, λ=9, q=3, c=k=0: (Z/3)^5 ⊕ 3^9 ⊕ Z_3 instead of (Z/3)^4 ⊕ 3^10 ⊕ Z_3). x = 0 (split lattice): stable, differs in every case. So stability alone does not pin down T (x = p^{1−ν} is a Dist-stable lattice with split reduction); the indecomposability argument of Lemma 7 is what forces v_p(x_0) = −ν, and the machine confirms its outcome.
### K8. md5 of sealed files
`checks/k8_md5.log`: file 1 d5c36be3736079cbc2349f469751c627, file 2 1f5cc12e88f12e375022658da3eea6ce, file 3 341a2c489aef1c30349bae079ddcce81, file 4 9ef6b4fec30a93192b0de995519d75f3, file 5 a092c60102cfca163c8449b60680b1e1, file 6 a739d9c18622ab0c5dfc811f4cbd49f7: **all six equal to the md5 printed in §9** (§9 prints all six: five after «MD5» and 1f5cc12e… after «MD5 of the file»). MANIFEST_md5.txt: 14/14 match. Contents of files 1–5 recomputed: 115/115 groups reproduced (P14); file 6 (verbal) agrees with §8's table, which I reproduced (8/8).

## JOB 3 — literature

### L1. JNR03
- Original: V. Reiner's home page, `CritComplete.pdf` (16 pp., preprint version; md5 in checks/DOWNLOADS.md). No arXiv version exists (searched). The journal version (J. Graph Theory 44 (2003) 231–250) was not accessed.
- Theorem 2 (p. 2): for p dividing none of the n_i, Syl_p K ≅ ⊕_{∅≠S} Syl_p(Z/N_S)^{Π_{i∈S}(n_i−1)}, N_S = Σ_{i∈S} n_i. Theorem 3 (p. 2): at most ½(Π n_i + Π(n_i−2)) − 1 invariant factors. Theorem 13 (§4, p. 11): see P1.
- The sentence quoted in §1 («…appears to be difficult, due to bad behavior of its p-primary structure…») is **verbatim** in this version (p. 2).
- Theorem 2 gives the case p ∤ q of Theorem C: for n_i = q, Syl_p K = ⊕_{s=1}^{d} (Z/p^{v_p(s)})^{C(d,s)(q−1)^s}, exponent max_{s≤d} v_p(s) = ⌊log_p d⌋ (even for q = 2). **The paper's statement is correct.**
- **L1: CORRECT** (quotation exact; Thm 13 gives A with multiplicities; Thm 2 gives C for e = 0).
### L2. Priority
Searched (08:10–08:18): OpenAlex, all 45 works citing JNR03 (doi:10.1002/jgt.10139), titles read; web/arXiv searches «Hamming graph» + «critical group» / «sandpile group» / «Smith normal form»; Ducey–Jalil arXiv:1308.2335 (read: only primes p ∤ |G|, §4.1–4.4); CSX15 (adjacency/Smith group of the hypercube, q = 2); «Smith normal form» + up operator / Boolean lattice / differential posets (Cai–Stanley, Miller–Reiner, Shah: not the Boolean lattice); Jordan type of x_1+…+x_n on k[x]/(x_i²) in char p (Cook arXiv:1111.4979, Lundqvist–Nicklasson arXiv:1604.06820, Mnukhin–Siemons, located, not read in full); tilting lattices / Smith forms on tilting modules (Martin arXiv:1705.06980, Sheu arXiv:2512.24317, TW, STWZ: none computes cokernels of f + scalar·floor).
| item | verdict |
|---|---|
| Theorem B | **d = 2: ALREADY KNOWN** — Ducey–Gerhard–Watson arXiv:1507.06583 (EJC 23(4) 2016 #P4.9), Thm 1.1 (1.1): K(R_n) ≅ (Z/2n)^{(n−2)²+1} ⊕ (Z/2n²)^{2(n−2)}, R_n = K_n×K_n = H(2,n) (their Remark (1): also deducible from earlier work; JNR03 §4 after Prop. 14 says Thm 13 + Example 11 give K(K_{n1}×K_{n2})). d ≥ 3: NOT FOUND. |
| Theorem C (e ≥ 1) | d = 2 known (same); in general NOT FOUND. |
| Theorem D | d = 2 known (same); p-ranks of inclusion matrices classical (Wilson 1990, Frankl 1990); the formula for N: NOT FOUND. |
| Theorem E | NOT FOUND. |
| Theorems F, G | d = 2 known (same); otherwise NOT FOUND. |
| Theorem H | d = 2 known (same); otherwise NOT FOUND (rests on the author's [DST]). |
| Corollary 6 | Jordan decomposition classical (acknowledged); the closed form of N: NOT FOUND. |
| Conjecture I | NOT FOUND (the Weyl-factor count it uses is in TW arXiv:1907.11560, §1). |
CONTRADICTED: none. **Correction needed: cite Ducey–Gerhard–Watson (and JNR Ex. 11) for d = 2 and qualify «new».**
### L3. Wilson 1990
- The original (Europ. J. Combin. 11 (1990) 609–615) is not on arXiv and I found no author-page copy (searched 08:18); not accessed.
- Restatement on arXiv: arXiv:1302.4249, Theorem 2.1 «(R.M. Wilson [27]) For t ≤ min(k, v−k), W_{tk} has as a diagonal form …» with entries C(k−i,t−i), multiplicity C(v,i)−C(v,i−1), 0 ≤ i ≤ t; Ducey et al. arXiv:2310.09227 cite it as [Wil90, Theorem 2].
- CSX15 (2) (material/CSX15, p. 4) states it **only for t ≤ k ≤ n/2**.
- So the range used in Theorem D (t ≤ min(k, m−k)) is Wilson's own, but it is **not** «the statement as given in [CSX15, (2)]»: the case (t,k) = (s, s+1), m = 2s+1, lies outside CSX15's range. The statement used is true (Wilson's range; my machine check of r_p(m,s) includes 24 such middle ranks, 0 mismatches). **L3: GAP (citation) — cite [Wil90, Thm 2] directly.**
### L4. Tilting
- **Donkin's tensor product theorem for SL₂**: original [Don93] = S. Donkin, Math. Z. 212 (1993) 39–60, **Proposition 2.1** (as cited in Tubbenhauer–Wedrich arXiv:1907.11560v2, §1, p. 3). Explicit SL₂ statement on arXiv: Sutton–Tubbenhauer–Wedrich–Zhu, arXiv:2105.07724v2, **Proposition 3.4(a), formula (3-1)** (§3): T(v−1) ≅ T(a_j−1)^{(j)} ⊗ ⊗_i T(a_i+p−1)^{(i)} over the non-leading digits of v (mixed-characteristic version; in characteristic p it gives T(p−1+r'+pb) ≅ T(p−1+r') ⊗ T(b)^{[1]}), with character Π([a_i+p] + [−a_i+p]); they cite [And19, Prop. 5.2], [TW20, Prop. 4.7]. Weyl factors: TW §1, p. 2: if λ+1 has r+1 non-zero digits, T(λ) has exactly 2^r Weyl factors, obtained by negating non-leading digits.
- **Lifting to the p-adic integers**: Heidersdorf–Wenzl arXiv:1912.09457v3, §5.4: Lemma 5.3 (citing Jantzen RAGS Lemma E.19, Prop. E.22) — over a complete DVR R, unique indecomposable tilting T_R(λ), unique decomposition of every tilting module; Corollary 5.5 (citing Jantzen E.20) — T_R(λ) ⊗ R/m ≅ T_{R/m}(λ); Lemma 5.2 (Jantzen B.9, B.10) — filtrations can be checked modulo m. With R = Z_p this is (T1).
- **L4: FOUND (exact places above).**

## Log of steps

## STEP 1 — STATE: DONE
- 07:39–07:47 CEST (from `date`): read MISSION.md, CLAUDE.md, vigia.sh, MANIFEST_md5.txt and the whole paper `material/coloured_sand_theorem.md` (528 lines, §1–§10, Provenance, References).

## STEP 2 — md5 of sealed files (K8) and of the manifest — estimate
- Expected: the six sealed files have the md5 printed in §9 (d5c36be…, 1f5cc12e…, 341a2c48…, 9ef6b4fe…, a092c601…, a739d9c1…); all 14 entries of MANIFEST_md5.txt match. Also: the .md, .tex and .pdf versions should carry the same text (I diff the word streams).
- Estimate: < 2 s, < 50 MB.

## STEP 2 — STATE: DONE
- Ran `zsh vigia.sh checks/k8_md5.log 'zsh checks/k8_md5.sh'` → VIGIA-FIN-OK, peak 2.9 MB, 0 s.
- All six sealed files have exactly the md5 printed in §9 (list in K8). All 14 entries of MANIFEST_md5.txt match. PDF has 14 pages.
- Contents of the sealed files read (they are in `material/`): file 1 = 10 groups (Thm B), file 2 = 30 pieces p=7, file 3 = 14 full groups, file 4 = 36 pieces + 4 full groups, file 5 = 18 pieces + 3 full groups, file 6 = a verbal prediction for the block λ=12 (7 cells). No timestamp lines in files 4–6.

## STEP 3 — STATE: DONE (P1 pending its JNR half; P6 written in STEP 3b)
- Hand re-derivations of P1–P5, P7, P8 written in their sections.

## STEP 3b — STATE: DONE
- P6 written. CSX15 read at its §3 (pdftotext, lines 118–134 of the text dump): statement (2) is for t ≤ k ≤ n/2.

## STEP 4 — engine: checks/psnf.c (C), checks/snf.py (driver + exact Fraction algorithm), checks/t_engine.py — estimate
- Engine: local Smith form over Z_(p) modulo P = p^M < 2^50 (M = 49, 31, 21, 17 for p = 2, 3, 5, 7), pivoting level by level in the valuation, only rows with a nonzero in the pivot column updated. A result is accepted only if the number of divisors ≥ p^M equals the corank over Q (0 for c ≥ 1, 1 for c = 0 and for Laplacians), otherwise the driver raises.
- Test: 300 random matrices (≤ 12×12, p ∈ {2,3,5,7}) vs my exact Fraction algorithm; 9 pieces and 8 Laplacians vs the exact algorithm; 40 random matrices vs Sage `elementary_divisors` over ZZ.
- Expected: 0 mismatches everywhere. Estimate: compile < 5 s; tests < 60 s (Sage start-up ~10–20 s), < 400 MB.

## STEP 4 — STATE: DONE
- `checks/compile_psnf.log`: VIGIA-FIN-OK. `checks/t_engine2.log`: random 300/300, structured 17/17 (9 pieces, 8 Laplacians vs exact Fraction algorithm), Sage 40/40 agree (first run `t_engine.log` showed 21 «mismatches» that were only my zero-count convention: Sage lists one divisor per row; torsion parts all agreed; comparison fixed).

## STEP 5 — timing of the engine — estimate
- Run `psnf` on: piece p=3 m=10 c=1 q=3 (1024²), piece p=3 m=11 c=1 q=3 (2048²), Laplacian H(6,3) (729²).
- Expected: m=10 ≈ 1–5 s; m=11 ≈ 5–60 s; H(6,3) ≈ 1–5 s; memory ≤ 40 MB for m=11.

## STEP 5 — STATE: DONE
- `checks/timing.log`: m=10 piece 0 s, H(6,3) Laplacian 1 s, m=11 piece 0 s (sparse pivoting makes it fast), peak 36 MB. Side result: Syl_3 K(H(6,3)) from the full Laplacian = (38,37,36,117,24,16,6), the row d=6 of §10.

## STEP 6 — K1–K4 (checks/k1_k4.py) — estimate
- K1: 20 cells (d,q,p), q^d ≤ 729, Laplacian vs pieces, with control (+1 copy of X(d−1,1)). Expected: all agree, all controls differ.
- K2: 12 cells p > d (incl. (2,9,3) e=2, (2,25,5) e=2, (4,5,5), (4,7,7) d=4), formula of Thm B vs computation. Expected: all agree.
- K3: 21 cells with q ≥ 3 (incl. (10,3,3): E=11 at s=9; p=2 with q even; p ∤ q) + (2,2,2). Expected: all agree; Q_2 gives Z/4.
- K4: 17 cells with p ≤ d (7 with p=3 | q, among them q = 6, 9, 12, 15), N from Thm D and Cor 6 vs computed; rank of W_{s,s+1} mod p vs formula for all m ≤ 11 (and larger when small), middle rank of odd m included; the JNR Thm 3 comparison for q = p ≤ 11, d ≤ 8.
- Estimate: < 3 min, < 150 MB (largest dense matrix H(4,7): 2401², 46 MB).

## STEP 6 — STATE: DONE
- `checks/k1_k4.log`: VIGIA-FIN-OK, 18 s, peak 57 MB. K1 20/20 (+20/20 controls differ), K2 12/12, K3 21/21, K4 17/17 (+9/9 Cor 6), rank formula 328/328. Details in K1–K4.

## STEP 7 — K5 predictions (checks/thmg.py, checks/k5_predict.py) — estimate
- thmg.py codes (T2), (T3), v_t, A, A', α, τ, E_ij and G_c(m,λ) exactly as printed. Self-tests: Example 9 must give {1:2, 2:7, 3:8, 4:17}; for m < p the formula must coincide with Theorem E (0 mismatches expected).
- Then 17 predictions (p=3: m = 9, 10, 11 incl. e = 2, 3; p=2: m = 4, 5 incl. e = 2, 5; p=5: m = 11, 12 incl. e = 2), none of them in the paper's data (§9 lists p=3, m∈{9,10}, q∈{12,15,21}, c∈5..8; m=11, q∈{12,15}, c∈4..6; p=2, q∈{6,8,10}; p=2 Thm H data has c ≤ 4, e ≤ 4; the full groups use c = d − m only).
- Estimate: < 1 s, < 30 MB. Output: checks/k5_predictions.txt + its md5.

## STEP 7 — STATE: DONE
- `checks/k5_predict.log`: VIGIA-FIN-OK, 0 s. 17 predictions recorded in K5 at 07:55:35.

## STEP 8 — K5 computation (checks/k5_compute.py) — estimate
- Compute the 17 pieces with psnf (m ≤ 12, largest 4096² = 134 MB dense) and compare with checks/k5_predictions.txt.
- Expected: if Theorem G is right, 17/17. Estimate: < 3 min (m=12 pieces ≈ 10–60 s each), < 400 MB.

- First run (07:55, `checks/k5_compute.log`): 5/5 agreements, then the engine REFUSED the piece p=3, q=27, m=10, c=4 (one divisor ≥ 3^31; the prediction has 3^33), as designed. Fix: 128-bit products when 2^50 ≤ p^M < 2^62 (M = 61, 39, 26, 22 for p = 2, 3, 5, 7), retried automatically.
- Test of the 128-bit path (checks/t_big.py): 16 pieces fast vs big precision, 120 random matrices with entries up to p^25 vs exact algorithm. Expected 0 mismatches, < 20 s.

- `checks/t_big2.log`: 136/136 (first attempt `t_big.log` crashed in my driver: entries > 2^63 must be reduced mod p^M before writing; fixed). `checks/t_engine3.log`: still 300/300, 17/17, 40/40.
- Second run `checks/k5_compute2.log` (07:56): 14/14 agreements, then refused p=5, q=25, m=12, c=1 (one divisor ≥ 5^26 = the 128-bit limit; the prediction has 5^26). Fix (rigorous, no theory used): for c ≥ 1 the piece matrix is triangular, det = Π_S q(c+|S|); if exactly one divisor is undetermined its exponent is v_p(det) − Σ(determined exponents), and it must be ≥ M (asserted).

## STEP 8 — STATE: DONE
- `checks/k5_compute3.log`: 17/17 agreements (VIGIA-FIN-OK, 16 s, 144 MB).

## STEP 8b — K5 extra cell p=5, m=13 (8192² dense = 537 MB) — estimate
- Expected: the prediction above. Estimate: 20–90 s, ≈ 600 MB (below the 1.2 GB cap). m = 14 (2.1 GB dense) is not attempted: it cannot fit under the cap with my dense engine.

## STEP 8b — STATE: DONE
- `checks/k5b_compute.log`: AGREE (17.5 s, 530 MB). K5 total 18/18.

## STEP 9 — K9 (checks/k9.py) — estimate
- 11 cells at m = 12 (8 new + 3 of the paper's table as a check of my extraction) and 3 cells at m = 13 (block λ = 13, new). Expected (prediction in K9): 4 large summands, 12 summands, same small part (Z/3)^8 for λ = 12; same small part across cells for λ = 13; the three table cells reproduce §8.
- Estimate: ≈ 11×3 s + 3×20 s ≈ 1.5 min; peak ≈ 550 MB.

## STEP 9 — STATE: DONE
- `checks/k9.log`: VIGIA-FIN-OK, 80 s, 532 MB. Conjecture I holds in all 14 cells (details in K9).

## STEP 10 — K7 (checks/k7.py) — estimate
- For p = 3, 5, 7 and EVERY λ ≤ p²+p−1 with two Weyl factors (this includes a = 1, a = p−1 with ν = 2, and λ = p²+p−1 with r = p): build the lattice of Lemma 7 in Δ_Q(λ) ⊕ Δ_Q(μ) with my own sparse exact arithmetic; check stability under e^{(t)}, f^{(t)} for all 1 ≤ t ≤ λ; compute the cokernel of q(c+H)+U on it (q ∈ {p, p², 2p}, 0 ≤ c ≤ p+1, 0 ≤ k ≤ 2; random 24 of them for p = 7) and compare with G_c(m,λ) of Lemma 8; check ν by its definition vs the claim of Lemma 7.
- Controls x = p^{1−ν}, p^{−ν−1}, 0 instead of p^{−ν}.
- Expected: x = p^{−ν}: stable, all cokernels = Lemma 8; x = p^{−ν−1}: NOT stable (e^{(t)} leaves the lattice); x = p^{1−ν} and x = 0: stable but cokernels differ from Lemma 8 (split reduction). Estimate: 1–4 min, < 200 MB.

- First run `checks/k7.log` (08:02–08:03, 45 s, 14 MB): ν matches the claim for all 77 λ; stability results as expected; but for p = 7 (and large λ) the block exponents (e.g. 7^45, 7^57) exceed the 128-bit precision of psnf, so «0/24» there means *undetermined*, not disagreement. I added a pure-Python big-modulus fallback (p^400) used only when the C engine leaves more undetermined divisors than the corank (triangular operator: corank = [c = k = 0]).
- Test of the fallback (checks/t_py.py): 200 random matrices with entries up to p^40 vs the exact Fraction algorithm, expected 0 mismatches, < 30 s.

## STEP 10 — STATE: DONE
- `checks/t_py.log`: 200/200. `checks/k7b.log`: VIGIA-FIN-OK, 55 s, 14 MB; results in K7.

## STEP 11 — STATE: DONE
- Read in [DST] (pdftotext of material/DST…v10.pdf, 52 pp.): §1.2 (main theorem, clocks, pooling, «equivalent form»), §3.2–3.4 (Lemma 3.2–3.3, Cor. 3.4, Thm 3.6, definition of X^{(α)}(λ,i)), Theorem D (p. 18), §5 incl. Prop. 5.2–5.4 (pp. 19–21), §7.1 (fits), Thm 7.10 and §8 (p. 28), §12 verification table (p. 45). Findings in P13.

## STEP 12 — K6 predictions (checks/thmh.py, checks/k6_predict.py) — estimate
- thmh.py codes the §7 formula as printed (small clocks, big clocks θ + αΘ + κ(i−1,Θ) + ŷ_D, i = 0 with x♯, integer antitonic fit by PAVA, λ = 0 case) and m_λ(n) by the [DST] recursion.
- Self-tests expected: [DST] example Syl_2 K(Q_6) = {1:12, 2:4, 3:1, 5:4, 6:10}; recursion multiplicities = character multiplicities for n ≤ 20; Theorem H = Theorem G for p = 2, m ≤ 5 (two formulas of the paper).
- Predictions: 10 pieces (e = 2: q = 4, 12; e = 3: q = 8, 24, 40; e = 4: q = 16; m = 6..12; c ≥ 5 except one c = 0 — the paper's Thm H data has c ≤ 4) and 4 full groups Syl_2 K(H(d,q)): (3,12), (2,24), (2,40), (6,4) — none in the paper's list; each with the α = 1 control.
- Estimate: < 2 s, < 30 MB.

## STEP 12 — STATE: DONE
- `checks/k6_predict.log`: VIGIA-FIN-OK, 0 s. Predictions recorded in K6 at 08:07:40.

## STEP 13 — K6 computation (checks/k6_compute.py) — estimate
- 10 pieces (largest m = 12: 4096²) and 4 full Laplacians (H(3,12): 1728², H(2,24): 576², H(2,40): 1600², H(6,4): 4096², 134 MB).
- Expected: 14/14 agreements; controls already differ on paper. Estimate: 1–5 min (the 4096 Laplacian is the unknown), < 400 MB.

## STEP 13 — STATE: DONE
- `checks/k6_compute.log`: 14/14 agreements, controls 14/14 differ (VIGIA-FIN-OK, 39 s, 141 MB).

## STEP 14 — JOB 3, downloads — estimate
- Web search (08:09): no arXiv version of JNR03; Reiner's publication page (www-users.cse.umn.edu/~reiner/Papers/papers.html) links `CritComplete.pdf`. Download it with curl into `checks/downloads/` (data only; read with pdftotext). Expected: a PDF of ~20 pages, < 1 MB, < 10 s.

- `checks/dl_jnr.log`: downloaded (16 pp., md5 f882443a…). Read Thms 1–3, Def. 8–10, Prop. 9, 12, 14, Thm 13, Lemma 16, proof of Thm 2 (findings in L1).
- Searches (08:10–08:12): OpenAlex lists 45 works citing JNR03 (doi:10.1002/jgt.10139; list read in full); web searches for Hamming graph + critical/sandpile group / Smith normal form. Found Ducey–Gerhard–Watson, «The Smith and critical groups of the square rook's graph and its complement», arXiv:1507.06583 (EJC 23(4) 2016, #P4.9): the rook's graph R_n = K_n × K_n = H(2,n). Relevant to priority for d = 2.
- Next downloads (arXiv only): 1507.06583 (DGW) and 1308.2335 (Ducey–Jalil). Expected < 2 MB each, < 10 s.

- `checks/dl_arxiv1.log`: both downloaded (md5 in DOWNLOADS.md). DGW Theorem 1.1 (1.1): K(R_n) ≅ (Z/2n)^{(n−2)²+1} ⊕ (Z/2n²)^{2(n−2)} for n ≥ 3, i.e. K(H(2,q)) for every q ≥ 3, all primes; DGW Remark (1) says (1.1) can also be deduced from earlier work. DJ14 treats only primes p ∤ |G| (their §4.1, 4.3, 4.4.2).
- Further searches (08:13–08:16): Hamming graph sandpile 2024–26 (nothing new found), SNF of up operators / Boolean lattice, Jordan type of x_1+…+x_n on k[x]/(x_i²) in char p (Lundqvist–Nicklasson arXiv:1604.06820, Cook arXiv:1111.4979, Mnukhin–Siemons «modular homology in the Boolean algebra»), tilting lattices over Z_p, Donkin's formula on arXiv (Tubbenhauer–Wedrich arXiv:1907.11560; lifting over a complete DVR in arXiv:1912.09457 §5).
- Next downloads (arXiv): 1907.11560, 1912.09457. Expected < 2 MB each.

- `checks/dl_arxiv2.log`, `dl_arxiv3.log`, `dl_arxiv4.log`: arXiv:1907.11560 (TW), 1912.09457 (Heidersdorf–Wenzl), 2105.07724 (STWZ), 2310.09227 (Ducey et al.), 1302.4249 (Kelly-lemma paper). Findings in L3, L4. Wilson's 1990 original is not on arXiv nor on an author page I could find (searched 08:18); I use the arXiv restatements.

## STEP 14 — STATE: DONE (JOB 3 sources gathered; write-up in STEP 17)

## STEP 15 — P14: recompute every group printed or sealed by the paper (checks/verify_paper_numbers.py) — estimate
- Sealed files 1–5 (10 + 30 + 14 + 40 + 21 groups), Example 9, the §10 table (d = 5..11), the §8 table (8 cells), and Conjecture I (i)–(ii) on the §7 formula for p = 2 (λ ≤ 200, α ≤ 5, i ≤ 8: 9000 groups; does every big clock exceed 2^θ?).
- Expected: every sealed group reproduced (the paper says «all correct»); tables reproduced; no exception for p = 2. Estimate: 1–3 min, < 300 MB.

## STEP 15 — STATE: DONE
- `checks/verify_paper_numbers.log` (08:20, 25 s, 145 MB): **115/115** sealed groups of files 1–5 reproduced; Example 9 ✓; §10 table d = 5..11 ✓ (all 7 rows; the version-2 row d=9 indeed differs); §8 table 8/8 ✓; Conjecture I on the §7 formula for p = 2: 9000 groups, 0 exceptions, least margin (big clock − θ) = 1.

## STEP 16 — final checks (checks/final_checks.py) — estimate
- (a) Thm G formula with e = 0 at (q,p,d) = (4,3,4) vs the computed {1:108}: expected to differ (paper's remark). (b) DGW Thm 1.1 (1.1) for K(H(2,n)), n = 3..20, every p | 2n, vs my engine on the full Laplacian: expected all equal.
- Estimate: < 30 s (largest Laplacian 400²), < 100 MB.

- `checks/final_checks.log` (08:22): (b) DGW (1.1) = my engine in 34/34 (n = 3..20, every p | 2n). (a) **Unexpected**: the Thm G formula with e = 0 at (q,p,d) = (4,3,4) gives {1:108}, exactly the computed group — the paper says the formula fails there.
- STEP 16b (checks/e0_scan.py): scan pieces with p ∤ q (p ∈ {2,3,5}, 4 values of q each, m ≤ min(10, p²+p−1), c ≤ 6) and 16 full groups, formula with e = 0 vs computation. Expected: some differences (the hypothesis e ≥ 1 is used in Lemma 8: «every v_t ≥ 1»), but maybe not at (4,3,4). Estimate < 1 min, < 100 MB.

- `checks/e0_scan.log` (08:22): 784/784 pieces with p ∤ q (p ∈ {2,3,5}) agree with the Thm G formula evaluated at e = 0; 5 full groups agree; then my script stopped (ValueError) at (d,q,p) = (6,3,2) because d = 6 > p²+p−1 = 5 is outside (T2) — my list error, not a finding.
- `checks/e0_thmF.log` (08:23): at (q,p,d) = (4,3,4) with e = 0, Theorem F's printed form gives {1:92, 2:8} (+25 trivial factors) ≠ computed {1:108}, while Theorem G's form (with the minimum) gives {1:108} = computed. Same for (5,3,4). So the remark after Theorem G is true of the F/version-2 form only.

## STEP 16 — STATE: DONE

## STEP 17 — STATE: DONE
- Written: P1 (JNR half), P9–P15, P14, K8, L1–L4, summary table, corrections, first-line verdict HOLDS WITH CORRECTIONS.
- No process left running (every run ended with VIGIA-FIN-OK; the one exit=1 runs are recorded above). Nothing in material/ or _historico_* modified; nothing deleted.
- Procedural slip, recorded honestly: at 08:27 I ran a last integrity check (md5 of material/ against MANIFEST_md5.txt → identical; `pgrep psnf` → nothing running) directly in the shell, not under vigia.sh. Earlier, a few one-line grep/awk summaries of logs were also run outside vigia (text filtering of existing logs, no new computation).

NEXT: none — mission complete. (Possible extensions, not required: Thm G at p = 5, m = 14, needs a sparse engine for 16384² matrices; Conjecture I at p = 5 needs m ≥ 30.)
