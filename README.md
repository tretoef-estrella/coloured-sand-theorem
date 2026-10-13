# The Coloured Sand Theorem

**The $p$-part of the sandpile group of the Hamming graph $`K_q^{\,d}`$, at the primes $p$ that divide $q$.**

Rafael Amichis Luengo · Madrid · 13 October 2026 (version 3) · [ORCID 0009-0008-6252-675X](https://orcid.org/0009-0008-6252-675X)

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
- **Theorem G (two Weyl factors).** For every prime $p$ and every $`m\le p^2+p-1`$, $`\mathrm{Syl}_pX_q(m,c)`$ is a sum of explicit blocks, one per tilting module $`T(\lambda)`$ of $`SL_2`$ in characteristic $p$, obtained by writing down its lift to the $p$-adic integers. The glue is forced: $`\tilde s_j=s_j+p^{-\nu}\binom{j+r}{j}\ell_{j+r}`$ with $`\nu=\min_{1\le t\le r}v_p\binom{\lambda-r+t}{t}`$, which is $2$ for the blocks with $a=p-1$ and $1$ otherwise. With Theorem A this gives $`\mathrm{Syl}_pK(H(d,q))`$ for every $`d\le p^2+p-1`$. It contains Conjecture H of version 2.
- **Theorem H (the prime 2).** For every even $q$ and every $d$: $`\mathrm{Syl}_2K(H(d,q))`$, from the results of the [Dancing Sand Theorem](https://github.com/tretoef-estrella/dancing-sand-theorem) (its Theorem D, Proposition 5.4 and Theorem 7.10 hold for every power $`2^\alpha`$) at $`\alpha=v_2(q)`$.
- **Corollary 6.** For $`3\mid q`$ the number of cyclic factors is $`(q-1)^d+\frac{q^d-(q-1)^d}{3}-\frac{(q-1)^d-(q-3)^d}{6}-1`$; for $q=3$, $`3^{d-1}+2^{d-1}-1`$.

What is left is $p$ odd and the pieces with $`m\ge p^2+p`$, whose tilting summands can have four or more Weyl factors.

## What is conjectured

**Conjecture I.** Write $`\lambda+1=\sum_{t\le k}d_tp^t`$ ($`d_k\ne0`$) and $`I=\{t<k:d_t\ne0\}`$. On the block $`T(\lambda)`$, the cokernel of $`f+p^e(D+i)`$ has exactly $`2^{|I|}`$ cyclic summands of order $`>p^k`$, one for each Weyl factor of $`T(\lambda)`$, and the other summands have order $`\le p^k`$ and do not depend on $i$ or $e$. It holds wherever the blocks are known (Theorems G and H). The first block outside, $`\lambda=12`$ for $p=3$ (four Weyl factors), was computed on $`B_{12}`$: the conjecture was stated after one cell, and it predicted the other seven before they were computed, all correctly.

Version 1 stated Theorem F as the Glue Conjecture; version 2 proved it. Version 2 stated Conjecture H; version 3 proves it, as part of Theorem G. Over the three versions, $107$ predictions for Theorems F and G were written down **before they were computed**, all correct.

## Status

A preprint. The proofs were found and re-read by the AI system that wrote them (see *Provenance*) and checked against every computation below; **they have not yet been read by an independent reader.** The proofs of Theorems F and G use standard facts on tilting modules of $`SL_2`$ (Donkin; Jantzen), cited and not reproved; Theorem H uses the Dancing Sand Theorem. Version 2 also corrects version 1, which claimed as new the case $`p\nmid q`$ of Theorem C. A Lean formalisation is in progress (piece CS1, the strings and Theorem E, is certified); it is not in this repository yet.

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
| Theorem G, $`m\le p^2-1`$ | `gate_conjH.py`: block formula against the model lattice, $`p\in\{5,7\}`$, every $`\lambda\le p^2-1`$; control: split lattice; `gate_conjH.py`, `gate_conjH_G2p7.py`: stability of the lattices | 216 / 216; fail 52 / 52; 52 / 52 lattices |
| Theorem G, blocks with $a=p-1$ | sealed [`sealed/PREDICCION_SELLADA_4.txt`](sealed/PREDICCION_SELLADA_4.txt) (MD5 `9ef6b4fec30a93192b0de995519d75f3`): 36 pieces, full groups $`H(10,3)`$, $`H(9,6)`$ at $p=3$, $`H(4,6)`$, $`H(4,10)`$ at $p=2$, and $`H(4,6)`$ from its full Laplacian: `check_seal4.py` | 41 / 41 |
| Theorem G, the block $`\lambda=p^2+p-1`$ | `frontier_sharp.py`, `frontier_next.py` (the glue $1/p$ is forced there); sealed [`sealed/PREDICCION_SELLADA_5.txt`](sealed/PREDICCION_SELLADA_5.txt) (MD5 `a092c60102cfca163c8449b60680b1e1`): 18 pieces, full groups $`H(11,3)`$, $`H(5,4)`$, $`H(5,6)`$, and $`H(5,4)`$ from its full Laplacian: `check_seal5.py` | 22 / 22 |
| Theorem G, the data table | `check_table_v3.py`: rows $d=5..9$ for $p=q=3$ (the row $d=9$ was not explained by version 2) | 5 / 5 |
| Theorem H | `gate_dst_alpha.py`, `gate_dst_alpha2.py`: pieces on $`B_m`$ ($m\le11$, $e\le4$, $c\le4$) and seven full Laplacians; controls: $\alpha=1$ instead of $\alpha=e$, and no antitonic fit | 384 / 384 and 7 / 7; fail 112 / 112 and 16 / 128 |
| Conjecture I, proved cases | `check_conjI_proved.py`, `check_conjI_count.py`: on the formulas of Theorems G and H; number of summands $`=\dim T(\lambda)/p`$; Weyl factors $`=2^{|I|}`$ | 9045 + 4704 / 13749; 286 / 286; 363 / 363 |
| Conjecture I, $\lambda=12$, $p=3$ | sealed [`sealed/PREDICCION_SELLADA_6.txt`](sealed/PREDICCION_SELLADA_6.txt) (MD5 `a739d9c18622ab0c5dfc811f4cbd49f7`) after one cell: `frontier_p3_m12.py` (stopped by the watchdog after 5 of 8 cells), `frontier_p3_m12_rest.py` (the other 3) | 7 / 7 |
| Conjecture I, $`\lambda=12`$, $p=3$, $e=2$ (after version 3) | sealed [`sealed/PREDICCION_SELLADA_7.txt`](sealed/PREDICCION_SELLADA_7.txt) (MD5 `c6a4cca669b5da707ee23482d8f4bb62`) before computing: $q=9$, $c=1,2$, the block is $`(\mathbb Z/3)^8`$ plus exactly $4$ cyclic factors of order $`\ge 27`$: `frontier_p3_m12_e2.py` (counts the factors of exponent $1$, $2$ and $`\ge3`$, which are exact even where the engine's precision $3^{19}$ does not resolve the large exponents) | 2 / 2 |
| Corollary 6 | `gate_jordan_N.py`: $`\dim\mathrm{coker}\,U`$ over $`\mathbb F_p`$ against Jordan blocks, $`p\in\{3,5,7\}`$, $m\le12$ | 37 / 37 |

The Smith forms are computed over $`\mathbb Z/p^M`$ with $`p^M<2^{31}`$; divisors of valuation $`\ge M`$ are recovered exactly from $`p^E M^{-1}`$ (`check_inverse.py`).

## Provenance

The results were found on the night of 12–13 October 2026 by Claude (Anthropic), working for the author as «Grepy Terminator», the auditor of the author's previous projects: it chose the problem after a search of the literature, wrote the computations, found the formulas, sealed and checked the predictions, found the proofs, and found — when checking the literature before publication — that Theorem A is Theorem 13 of Jacobson–Niedermaier–Reiner. Version 2, the same night, also by Claude, in a new session («Grepy Connor»): the proof of the Glue Conjecture and its extension (Theorems F, G), Corollary 6 and Conjecture H. Version 3, the same night, same session: Theorem G up to $`m\le p^2+p-1`$ (which proves Conjecture H), Theorem H and Conjecture I. One error of the machine's own check was caught and is kept in the record (`logs/gate_glue_model_BUG_multiplier.log`: a random multiplier of $q$ divisible by $p$). The author takes responsibility for the work.

## Licence

Code (`.py`): MIT, see [LICENSE](LICENSE). Texts (paper, logs, this file): CC BY 4.0, see [LICENSE-TEXT.md](LICENSE-TEXT.md).
