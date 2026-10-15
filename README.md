# The Coloured Sand Theorem

### The $p$-part of the sandpile group of the Hamming graph $`K_q^{\,d}`$, for every prime $p$ dividing $q$ and every dimension $d$

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.23327608-blue.svg)](https://doi.org/10.5281/zenodo.23327608) [![Version 6 DOI](https://img.shields.io/badge/version_6_DOI-10.5281%2Fzenodo.23400922-blue.svg)](https://doi.org/10.5281/zenodo.23400922) [![Lean build](https://github.com/tretoef-estrella/coloured-sand-theorem/actions/workflows/lean-build.yml/badge.svg)](https://github.com/tretoef-estrella/coloured-sand-theorem/actions/workflows/lean-build.yml) [![ORCID](https://img.shields.io/badge/ORCID-0009--0008--6252--675X-a6ce39.svg)](https://orcid.org/0009-0008-6252-675X)

**Rafael Amichis Luengo** · Madrid · tretoef@gmail.com · preprint, version 6, 15 October 2026

> **Status.** A complete proof, published as a preprint. Every theorem has a written proof that can be checked with pencil and paper. The proofs were re-derived by readers who had not written them, and the paper and its Lean certificate were read cold four times; every correction is listed in the paper. **Every theorem of the paper, Theorems A–J, has also been checked in the proof assistant Lean 4, for every prime, with nothing cited** ([below](#formal-verification-in-lean-4)), **and GitHub's own machines have rebuilt that Lean proof from the published files** ([Lean build](https://github.com/tretoef-estrella/coloured-sand-theorem/actions/workflows/lean-build.yml)). All the readers are instances of the AI system Claude. **It has not been refereed by a human expert.**

**Read the paper:** [paper/coloured_sand_theorem.pdf](paper/coloured_sand_theorem.pdf) · [LaTeX source](paper/coloured_sand_theorem.tex) · permanent archive: [doi.org/10.5281/zenodo.23327608](https://doi.org/10.5281/zenodo.23327608) (this version: [doi.org/10.5281/zenodo.23400922](https://doi.org/10.5281/zenodo.23400922)) · **Lean certificate:** [lean/LEAN_CERTIFICATE_COLOURED_SAND_v2.pdf](lean/LEAN_CERTIFICATE_COLOURED_SAND_v2.pdf) ([Markdown](lean/LEAN_CERTIFICATE_COLOURED_SAND_v2.md)), the Lean project in [lean/](lean/README.md) · companion paper for $q=2$: [The Dancing Sand Theorem](https://github.com/tretoef-estrella/dancing-sand-theorem) ([doi.org/10.5281/zenodo.23188298](https://doi.org/10.5281/zenodo.23188298), [hexagon:2610.00205](https://hexagonmath.org/2610.00205))

---

## The problem

The sandpile group (critical group) $`K(\Gamma)`$ of a connected graph is the torsion part of the cokernel of its Laplacian; its order is the number of spanning trees. For the Hamming graph $`H(d,q)=K_q^{\,d}`$, Jacobson, Niedermaier and Reiner (J. Graph Theory 44, 2003) determined the $p$-part for every prime $p$ that does not divide $q$, and wrote that the other primes appear *"to be difficult, due to bad behavior of its p-primary structure"*. For $q=2$ (the hypercube) the $2$-part is the [Dancing Sand Theorem](https://github.com/tretoef-estrella/dancing-sand-theorem). This repository is about the primes $`p\mid q`$; we write $`e=v_p(q)`$.

**The paper determines $`\mathrm{Syl}_pK(H(d,q))`$ for every prime $`p\mid q`$ and every $d$, by an explicit rule** (Theorems I and J). For $d=2$ the whole group was known before (Ducey, Gerhard and Watson, Electron. J. Combin. 23(4), 2016); our results are new, to the best of our knowledge, for $`d\ge3`$.

## What is proved

- **Theorem A** (Jacobson–Niedermaier–Reiner, their Theorem 13, rewritten). $`\mathrm{coker} L(H(d,q))\cong\bigoplus_j X_q(d-j,j)^{\binom dj(q-2)^j}`$, where $`X_q(m,c)`$ is the cokernel of $q(c+H)+U$ on the Boolean lattice of $[m]$ ($H$ the size, $U$ the up operator).
- **Theorem B.** For every prime $p>d$ dividing $q$:
  $`\mathrm{Syl}_p K(H(d,q))\cong\bigoplus_{v=1}^d(\mathbb Z/p^{ev})^{n_v}`$, with $`n_v=\sum_{j+2k=d+1-v,\ (j,k)\neq(0,0)}\binom dj(q-2)^j\,\frac{v}{v+2k}\binom{v+2k}{k}`$ (ballot numbers).
- **Theorem C.** For every prime $p$ and $`q\ge3`$: the exponent of $`\mathrm{Syl}_pK(H(d,q))`$ is $`p^E`$ with $`E=\max_{1\le s\le d}(es+v_p(s))`$ if $`p\mid q`$, and $`E=\lfloor\log_pd\rfloor`$ if $`p\nmid q`$ (this last case also follows from Theorem 2 of Jacobson–Niedermaier–Reiner).
- **Theorem D.** For $`p\mid q`$: the number of cyclic factors, in closed form, from Wilson's diagonal form of inclusion matrices.
- **Theorem E.** For every prime $p$, the exact contribution of every piece $`X_q(m,c)`$ with $m<p$.
- **Theorem F (the Glue Theorem; a conjecture in version 1).** For every $`m\le 2p-2`$: on each pair of strings glued by the tilting module $`T(\lambda)`$, $`p\le\lambda\le2p-2`$, of $`SL_2`$ in characteristic $p$, exactly one factor $p$ moves from the long string to the short one.
- **Theorem G (two Weyl factors).** For every prime $p$ and every $`m\le p^2+p-1`$, $`\mathrm{Syl}_pX_q(m,c)`$ is a sum of explicit blocks, one per tilting module $`T(\lambda)`$ of $`SL_2`$ in characteristic $p$, obtained by writing down its lift to the $p$-adic integers. The glue is forced: $`\tilde s_j=s_j+p^{-\nu}\binom{j+r}{j}\ell_{j+r}`$ with $`\nu=\min_{1\le t\le r}v_p\binom{\lambda-r+t}{t}`$, which is $2$ for the blocks with $a=p-1$ and $1$ otherwise. With Theorem A this gives $`\mathrm{Syl}_pK(H(d,q))`$ for every $`d\le p^2+p-1`$. It contains Conjecture H of version 2.
- **Theorem H (the prime 2).** For every even $q$ and every $d$: $`\mathrm{Syl}_2K(H(d,q))`$, from the results of the [Dancing Sand Theorem](https://github.com/tretoef-estrella/dancing-sand-theorem) (its Theorem D, Proposition 5.4 and Theorem 7.10 hold for every power $`2^\alpha`$) at $`\alpha=v_2(q)`$.
- **Corollary 6.** For $`3\mid q`$ the number of cyclic factors is $`(q-1)^d+\frac{q^d-(q-1)^d}{3}-\frac{(q-1)^d-(q-3)^d}{6}-1`$; for $q=3$, $`3^{d-1}+2^{d-1}-1`$.
- **Theorem I (Conjecture I of version 3), every prime.** Write $`\lambda+1=\sum_{t\le k}d_tp^t`$ ($`d_k\ne0`$) and $`I=\{t<k:d_t\ne0\}`$. On the block of the tilting module $`T(\lambda)`$, exactly $`2^{|I|}`$ cyclic summands have order larger than $`p^k`$; the others form the group $`S_p(\lambda)=\bigoplus_{h=1}^{k-1}(\mathbb Z/p^h)^{(p-1)d_kp^{k-h-1}2^{|I|}}\oplus(\mathbb Z/p^k)^{(d_k-1)2^{|I|}}`$, which depends only on $p$ and the base-$`p`$ digits of $\lambda+1$.
- **Theorem J (the whole group), every odd prime.** The $`2^{|I|}`$ large summands are $`\mathbb Z/p^{\,k+eK+\kappa_p(i-1,K)+\hat y_D}`$, $`D\subseteq I`$, for every shift $`i\ge1`$ (for $i=0$ one of them is free), where $`K=d_kp^k`$, $`\kappa_p`$ counts base-$`p`$ carries and the $`\hat y_D`$ are obtained by pooling explicit integers (binomial valuations and carries) into a non-increasing sequence. With Theorem A this gives $`\mathrm{Syl}_pK(H(d,q))`$ for every prime $`p\mid q`$ and every $d$ ($p=2$ by Theorem H).

The proof writes down explicit $`\mathbb Z_p`$-lattices for all tilting modules of $`SL_2`$, one move per base-$`p`$ digit (a twist and a split), reduces each block to the Smith form of an explicit $`2^{|I|}\times2^{|I|}`$ matrix, and computes that form as in the [Dancing Sand Theorem](https://github.com/tretoef-estrella/dancing-sand-theorem) for the hypercube, the case $p=2$. The exact statements are in §8 of the paper and the proofs in §9.

## Status

A preprint, not refereed by a human expert. The proofs of Theorems A–H were re-derived by an independent reader with no access to our audits; it found one priority omission (the case $d=2$), three citation and presentation gaps and one wrong example in a remark, all corrected in version 4. The proofs of Theorems I and J were written by one reader, re-derived by a second and read cold by a third, who wrote the riskiest step, the floor of the Smith form for odd $p$, out in full and found no error and no gap; the reports are in [`v4-checks/`](v4-checks/). The Lean certificate and version 5 were read cold by a fourth reader, who found three claims wider than the Lean proof of that day (now all checked); the changes of version 6 were read cold by a fifth reader, who found no error in the mathematics or in the Lean statements. Every correction is listed in §13 of the paper. All these readers are instances of the AI system Claude.

## Formal verification in Lean 4

Every theorem of the paper, Theorems A–J, with Lemmas 2–5, 7 and 8, Corollaries 1 and 6 and Example 9, is proved in Lean 4 with Mathlib, for every prime, with no `sorry`, no `native_decide` and no axiom beyond Lean's three standard ones (`propext`, `Classical.choice`, `Quot.sound`). Nothing is cited from outside Lean and Mathlib.

- **The headline for odd primes:** `ColouredSand.OddTwist.oddTotal_S2` — for every odd prime $p$, every $q\ge2$ with $p\mid q$ and every $d$, the $p$-primary part of $K(H(d,q))$ is an explicit direct sum of cyclic groups (Theorem J). **The prime 2:** `ColouredSand.ThmH.T4` (Theorem H, every even $q$, every $d$).
- **Size:** 36 pieces, 254 files, 46 787 lines, 2 370 `theorem`/`lemma` lines, 0 `sorry`. A final check loads all 36 pieces in one environment and prints 451 `#print axioms` answers, all standard; the dependency cone of the headline theorems has 9 833 declarations in 335 modules.
- **Rebuilt by GitHub:** [Actions run 38724562833](https://github.com/tretoef-estrella/coloured-sand-theorem/actions/runs/38724562833) (15 October 2026, commit `51c25f0`) built the whole project from its sources, on Mathlib's published build, and ran the final check; its logs, in [`lean/actions/`](lean/actions/), are identical line for line to the runs on the author's machine.
- **What is not formalized** (§2 of the certificate): Theorem I and the blocks of Theorem J are proved for explicit dance lattices ($L(\lambda)$ for odd $p$, the lattices of the Dancing Sand Theorem for $p=2$); their identification with the tilting lattices $T_{\mathbb Z_p}(\lambda)$ is in the paper, not in Lean, and the statements on $K(H(d,q))$ do not need it. Theorem E is stated in the pieces for the $\mathbb Z_p$-cokernel; its form in the paper is checked by a separate file. Example 10 has no Lean statement.

The Lean proofs were written by Aristotle (Harmonic) from statements taken from the paper, piece by piece; each piece was compiled on the author's machine and audited (every result restated by hand in a check file, axioms printed). How to rebuild it yourself: [`lean/README.md`](lean/README.md).

## Verification

The numerical checks are evidence, not part of the proof. The checks of versions 1–3: run everything from [`engines/`](engines/) (Python 3 with NumPy; `sage_check.py` needs SageMath). Logs are in [`logs/`](logs/). The checks of Theorems I and J are in [`v4-checks/`](v4-checks/).

| Claim | Check | Result |
|---|---|---|
| Theorem A | `gate_reduction.py`: Sylow subgroups from the full Laplacian versus from the pieces, $27$ cells, $`p\in\{2,3,5,7\}`$ | 90 / 90 |
| Theorem B | ten predictions sealed in [`sealed/PREDICCION_SELLADA_1.txt`](sealed/PREDICCION_SELLADA_1.txt) (MD5 `d5c36be3736079cbc2349f469751c627`), computed afterwards (`logs/cell_*.log`) | 10 / 10 |
| Theorem C | `gate_exponent.py`, $143$ cells, with and without $`p\mid q`$, including $p=2$ | 143 / 143 |
| Theorem D | `gate_wilson.py` (rank of inclusion matrices) and `wilson_prank.py` (against the computed groups) | 264 / 264 and 23 / 23 |
| Glue Conjecture | $30$ pieces at $p=7$ sealed in [`sealed/PREDICCION_SELLADA_2.txt`](sealed/PREDICCION_SELLADA_2.txt) (MD5 `1f5cc12e88f12e375022658da3eea6ce`): `check_sealed2b.py 9` (exact Smith form up to $m=9$), `check_inverse.py` | 30 / 30 |
| Glue Conjecture | $14$ full groups with composite $q$ sealed in [`sealed/PREDICCION_SELLADA_3.txt`](sealed/PREDICCION_SELLADA_3.txt) (MD5 `341a2c489aef1c30349bae079ddcce81`): `check_sealed3.py` | 14 / 14 |
| Glue Conjecture, scope | `check_e0.py`: it fails when $`p\nmid q`$, as stated | stated |
| Theorems F, G: the lattices | `gate_glue_model.py`, `tilt3p.py`: stability under every $`e^{(t)},f^{(t)}`$, $`p\in\{3,5,7\}`$, $`p\le\lambda\le3p-2`$ | 2200 / 2200; 27 / 27 lattices |
| Theorems F, G: the blocks | model cokernels against the formula: `gate_glue_model.py` ($\lambda\le2p-2$), `tiltgen_probe2.py` ($\lambda\le p^2-2$), `check_c0.py` ($c=0$) | 292 / 292; 180 / 180; 60 / 60 |
| Theorem G vs direct computation | `tilt3p.py`: predicted pieces against Smith forms on $`B_m`$ ($p=3$, $m\le7$; $p=5$, $m\le10$); `tilt3p_probe.py` ($p=3$, $m=8$); `fullgroup_check.py` (full groups $p=q=3$, $d=5..8$) | 154 / 154; 5 / 5; 4 / 4 |
| Controls | split lattice `gate_glue_control_split.py`; formula F beyond $`2p-2`$; $m=9$ beyond the range (`tiltgen_probe2.py`) | fail 293 / 293; fail 12 / 18; fail, as stated |
| Theorem G at $p=2$ | `check_p2.py`: $m\le3$ matches; $m=4,5,6$ differ, as the hypothesis $a+1<p$ predicts | 30 / 30 and fail 30 / 30 |
| Theorem G, $`m\le p^2-1`$ | `gate_conjH.py`: block formula against the model lattice, $`p\in\{5,7\}`$, every $`\lambda\le p^2-1`$; control: split lattice; `gate_conjH.py`, `gate_conjH_G2p7.py`: stability of the lattices | 216 / 216; fail 52 / 52; 52 / 52 lattices |
| Theorem G, blocks with $a=p-1$ | sealed [`sealed/PREDICCION_SELLADA_4.txt`](sealed/PREDICCION_SELLADA_4.txt) (MD5 `9ef6b4fec30a93192b0de995519d75f3`): 36 pieces, full groups $`H(10,3)`$, $`H(9,6)`$ at $p=3$, $`H(4,6)`$, $`H(4,10)`$ at $p=2$, and $`H(4,6)`$ from its full Laplacian: `check_seal4.py` | 41 / 41 |
| Theorem G, the block $`\lambda=p^2+p-1`$ | `frontier_sharp.py`, `frontier_next.py` (the glue $1/p$ is forced there); sealed [`sealed/PREDICCION_SELLADA_5.txt`](sealed/PREDICCION_SELLADA_5.txt) (MD5 `a092c60102cfca163c8449b60680b1e1`): 18 pieces, full groups $`H(11,3)`$, $`H(5,4)`$, $`H(5,6)`$, and $`H(5,4)`$ from its full Laplacian: `check_seal5.py` | 22 / 22 |
| Theorem G, the data table | `check_table_v3.py`: rows $d=5..9$ for $p=q=3$ (the row $d=9$ was not explained by version 2) | 5 / 5 |
| Theorem H | `gate_dst_alpha.py`, `gate_dst_alpha2.py`: pieces on $`B_m`$ ($m\le11$, $e\le4$, $c\le4$) and seven full Laplacians; controls: $\alpha=1$ instead of $\alpha=e$, and no antitonic fit | 384 / 384 and 7 / 7; fail 112 / 112 and 16 / 128 |
| Conjecture I (now Theorem I), proved cases in version 3 | `check_conjI_proved.py`, `check_conjI_count.py`: on the formulas of Theorems G and H; number of summands $`=\dim T(\lambda)/p`$; Weyl factors $`=2^{|I|}`$ | 9045 + 4704 / 13749; 286 / 286; 363 / 363 |
| Conjecture I (now Theorem I), $\lambda=12$, $p=3$ | sealed [`sealed/PREDICCION_SELLADA_6.txt`](sealed/PREDICCION_SELLADA_6.txt) (MD5 `a739d9c18622ab0c5dfc811f4cbd49f7`) after one cell: `frontier_p3_m12.py` (stopped by the watchdog after 5 of 8 cells), `frontier_p3_m12_rest.py` (the other 3) | 7 / 7 |
| Conjecture I (now Theorem I), $`\lambda=12`$, $p=3$, $e=2$ (after version 3) | sealed [`sealed/PREDICCION_SELLADA_7.txt`](sealed/PREDICCION_SELLADA_7.txt) (MD5 `c6a4cca669b5da707ee23482d8f4bb62`) before computing: $q=9$, $c=1,2$, the block is $`(\mathbb Z/3)^8`$ plus exactly $4$ cyclic factors of order $`\ge 27`$: `frontier_p3_m12_e2.py` (counts the factors of exponent $1$, $2$ and $`\ge3`$, which are exact even where the engine's precision $3^{19}$ does not resolve the large exponents) | 2 / 2 |
| Theorems I, J: the lattices $`L(\lambda)`$ | $`\mathfrak{sl}_2`$ relations, character of $`T(\lambda)`$, stability under every $`E^{(r)},F^{(r)}`$, $`\dim T(\lambda)\le600`$, $`p\in\{3,5,7\}`$, by two readers with their own engines ([`v4-checks/`](v4-checks/)) | 569 / 569 lattices |
| Theorem $`\mathrm{D}_p`$ | the moves against a direct $p$-adic Smith form, $`p\in\{3,5\}`$; $1520$ cells sealed before computing (`SEALED_1.txt`, MD5 `0a9c3442e54c54c8cc880d9b2bc070b0`) | 1856 / 1856 |
| Theorem J | $`10\,710`$ cells, $`p\in\{3,5,7,11,13\}`$, sealed before computing (`SEALED_2.txt`, MD5 `2f931de9eb3933c51a4ff3efb03274ab`), against the exact Smith form of $`M_p`$ | 10 710 / 10 710 |
| Theorems I, J, independent of the lattices | length and number of cyclic summands of each block from the character ($20\,310$ cells); whole Hamming graphs against Kirchhoff's count and the corank of the Laplacian ($180$ groups, and $12$ more up to $d=60$ by the independent reader); direct Smith forms on $`B_{12}`$ at $p=3$, $q=9$ | all agree |
| Theorem J, the floor of the Smith form | every claim of §9.4 of the paper checked numerically ($`56\,246`$ houses; $`47\,310`$ more by the independent reader) | all hold |
| Corollary 6 | `gate_jordan_N.py`: $`\dim\mathrm{coker}\,U`$ over $`\mathbb F_p`$ against Jordan blocks, $`p\in\{3,5,7\}`$, $m\le12$ | 37 / 37 |

The Smith forms are computed over $`\mathbb Z/p^M`$ with $`p^M<2^{31}`$; divisors of valuation $`\ge M`$ are recovered exactly from $`p^E M^{-1}`$ (`check_inverse.py`).

## Provenance

The results were found on the night of 12–13 October 2026 by Claude (Anthropic), working for the author as «Grepy Terminator», the auditor of the author's previous projects: it chose the problem after a search of the literature, wrote the computations, found the formulas, sealed and checked the predictions, found the proofs, and found — when checking the literature before publication — that Theorem A is Theorem 13 of Jacobson–Niedermaier–Reiner. Version 2, the same night, also by Claude, in a new session («Grepy Connor»): the proof of the Glue Conjecture and its extension (Theorems F, G), Corollary 6 and Conjecture H. Version 3, the same night, same session: Theorem G up to $`m\le p^2+p-1`$ (which proves Conjecture H), Theorem H and Conjecture I. Version 4 (13–14 October 2026): Theorems I and J were found and proved by a separate session working as constructor, re-derived and re-computed by the session that audits the project, and read cold by a third session with no access to the audit; version 3 was read cold by a fourth. Versions 5 and 6 (14–15 October 2026): the Lean proof of every theorem, for every prime, written by Aristotle (Harmonic) and compiled and audited on the author's machine, rebuilt on GitHub's machines, and read cold twice. One error of the machine's own check was caught and is kept in the record (`logs/gate_glue_model_BUG_multiplier.log`: a random multiplier of $q$ divisible by $p$). The author takes responsibility for the work.

## How it was built

The route to Theorems I and J began with the author. When Conjecture I was open, he insisted that the Dancing Sand had to hold the key to closing this problem entirely, because he knew what its images had solved. The auditor checked, and he was right: the key was the dance of [The Dancing Sand Theorem](https://github.com/tretoef-estrella/dancing-sand-theorem) §3–§4. A constructor carried the dance to every odd prime, a cold reader checked the proof, and Lean checked it by machine. The dance itself was an auditor's proposal; the author's part here was knowing where to look, and the images whose mechanisms the proof reuses.

The author does not write proofs; as in the Dancing Sand, his part was to unblock the work. When the proof was stuck he gave an image in plain words, which was translated piece by piece into something that could be counted, and the translation was sealed before any measurement. Of the 27 images he gave for the Dancing Sand, 19 became the statement or the mechanism of a result and 6 served in part ([record/THE_IMAGES.md](https://github.com/tretoef-estrella/dancing-sand-theorem/blob/main/record/THE_IMAGES.md) of that repository). The proofs of Theorems I and J reuse that machinery for odd primes: the unique cheapest matching of the natural minor is his «orphan», the floor is the flat that settles its account with its mirror, and the carries are his climb «in the air».

The work is a collaboration: each part completes the other.

## Licence

Code (`.py`): MIT, see [LICENSE](LICENSE). Texts (paper, logs, this file): CC BY 4.0, see [LICENSE-TEXT.md](LICENSE-TEXT.md).
