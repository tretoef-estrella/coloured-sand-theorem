# The Coloured Sand Theorem

**The $p$-part of the sandpile group of the Hamming graph $`K_q^{\,d}`$, at the primes $p$ that divide $q$.**

Rafael Amichis Luengo · Madrid · 13 October 2026 (version 2) · [ORCID 0009-0008-6252-675X](https://orcid.org/0009-0008-6252-675X)

Paper: [`paper/coloured_sand_theorem.pdf`](paper/coloured_sand_theorem.pdf), the reference text (also [`.tex`](paper/coloured_sand_theorem.tex) and [`.md`](paper/coloured_sand_theorem.md)) · Zenodo (all versions): [doi:10.5281/zenodo.23327608](https://doi.org/10.5281/zenodo.23327608)

## The problem

The sandpile group (critical group) $`K(\Gamma)`$ of a connected graph is the torsion part of the cokernel of its Laplacian; its order is the number of spanning trees. For the Hamming graph $`H(d,q)=K_q^{\,d}`$, Jacobson, Niedermaier and Reiner (J. Graph Theory 44, 2003) determined the $p$-part for every prime $p$ that does not divide $q$, and wrote that the other primes appear *"to be difficult, due to bad behavior of its p-primary structure"*. For $q=2$ (the hypercube) the $2$-part is the [Dancing Sand Theorem](https://github.com/tretoef-estrella/dancing-sand-theorem). This repository is about the primes $`p\mid q`$; we write $`e=v_p(q)`$.

## What is proved

- **Theorem A** (Jacobson–Niedermaier–Reiner, their Theorem 13, rewritten). $`\mathrm{coker} L(H(d,q))\cong\bigoplus_j X_q(d-j,j)^{\binom dj(q-2)^j}`$, where $`X_q(m,c)`$ is the cokernel of $q(c+H)+U$ on the Boolean lattice of $[m]$ ($H$ the size, $U$ the up operator).
- **Theorem B.** For every prime $p>d$ dividing $q$:
  $`\mathrm{Syl}_p K(H(d,q))\cong\bigoplus_{v=1}^d(\mathbb Z/p^{ev})^{n_v}`$, with $`n_v=\sum_{j+2k=d+1-v,\ (j,k)\neq(0,0)}\binom dj(q-2)^j\,\frac{v}{v+2k}\binom{v+2k}{k}`$ (ballot numbers).
- **Theorem C.** For every prime $p$ and $`q\ge3`$: the exponent of $`\mathrm{Syl}_pK(H(d,q))`$ is $`p^E`$ with $`E=\max_{1\le s\le d}(es+v_p(s))`$ if $`p\mid q`$, and $`E=\lfloor\log_pd\rfloor`$ if $`p\nmid q`$ (this last case also follows from Theorem 2 of Jacobson–Niedermaier–Reiner).
- **Theorem D.** For $`p\mid q`$: the number of cyclic factors, in closed form, from Wilson's diagonal form of inclusion matrices.
- **Theorem E.** For every prime $p$, the exact contribution of every piece $`X_q(m,c)`$ with $m<p$.
- **Theorem F (the Glue Theorem; a conjecture in version 1).** For every $`m\le 2p-2`$: on each pair of strings glued by the tilting module $`T(\lambda)`$, $`p\le\lambda\le2p-2`$, of $`SL_2`$ in characteristic $p$, exactly one factor $p$ moves from the long string to the short one.
- **Theorem G (the tilting blocks).** For every $`m\le 3p-1`$ ($p$ odd; $m\le3$ for $p=2$), $`\mathrm{Syl}_pX_q(m,c)`$ is a sum of explicit blocks, one per tilting module, obtained by writing down the lift of $`T(\lambda)`$ to the $p$-adic integers (the glue is forced: $`\tilde s_j=s_j+\tfrac1p\binom{j+r}{j}\ell_{j+r}`$). With Theorem A this gives $`\mathrm{Syl}_pK(H(d,q))`$ for every $`d\le3p-1`$ ($p$ odd).
- **Corollary 6.** For $`3\mid q`$ the number of cyclic factors is $`(q-1)^d+\frac{q^d-(q-1)^d}{3}-\frac{(q-1)^d-(q-3)^d}{6}-1`$; for $q=3$, $`3^{d-1}+2^{d-1}-1`$.

What is left is the pieces with $`m\ge3p`$.

## What is conjectured

**Conjecture H.** For every odd prime $p$, the block formula of Theorem G holds for every $`m\le p^2-2`$. The bound is where the method of proof stops (for $a=p-1$ the glue may have denominator $p^2$); for $p=3$, $m=9$ the formula is indeed wrong by one factor.

Version 1 stated Theorem F as the Glue Conjecture. It was found from $88$ pieces with $p=3,5$ and then predicted, **before they were computed**, $44$ further cases, all correctly; version 2 proves it.

## Status

A preprint. The proofs were found and re-read by the AI system that wrote them (see *Provenance*) and checked against every computation below; **they have not yet been read by an independent reader.** The proofs of Theorems F and G use standard facts on tilting modules of $`SL_2`$ (Donkin; Jantzen), cited and not reproved. Version 2 also corrects version 1, which claimed as new the case $`p\nmid q`$ of Theorem C.

## Verification

Run everything from [`engines/`](engines/) (Python 3 with NumPy; `sage_check.py` needs SageMath). Logs are in [`logs/`](logs/).

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
| Corollary 6 | `gate_jordan_N.py`: $`\dim\mathrm{coker}\,U`$ over $`\mathbb F_p`$ against Jordan blocks, $`p\in\{3,5,7\}`$, $m\le12$ | 37 / 37 |

The Smith forms are computed over $`\mathbb Z/p^M`$ with $`p^M<2^{31}`$; divisors of valuation $`\ge M`$ are recovered exactly from $`p^E M^{-1}`$ (`check_inverse.py`).

## Provenance

The results were found on the night of 12–13 October 2026 by Claude (Anthropic), working for the author as «Grepy Terminator», the auditor of the author's previous projects: it chose the problem after a search of the literature, wrote the computations, found the formulas, sealed and checked the predictions, found the proofs, and found — when checking the literature before publication — that Theorem A is Theorem 13 of Jacobson–Niedermaier–Reiner. Version 2, the same night, also by Claude, in a new session («Grepy Connor»): the proof of the Glue Conjecture and its extension (Theorems F, G), Corollary 6 and Conjecture H. One error of the machine's own check was caught and is kept in the record (`logs/gate_glue_model_BUG_multiplier.log`: a random multiplier of $q$ divisible by $p$). The author takes responsibility for the work.

## Licence

Code (`.py`): MIT, see [LICENSE](LICENSE). Texts (paper, logs, this file): CC BY 4.0, see [LICENSE-TEXT.md](LICENSE-TEXT.md).
