# The Coloured Sand Theorem

**The $p$-part of the sandpile group of the Hamming graph $K_q^{\,d}$, at the primes $p$ that divide $q$.**

Rafael Amichis Luengo · Madrid · 13 October 2026 · [ORCID 0009-0008-6252-675X](https://orcid.org/0009-0008-6252-675X)

Paper: [`paper/coloured_sand_theorem.pdf`](paper/coloured_sand_theorem.pdf) (also [`.tex`](paper/coloured_sand_theorem.tex) and [`.md`](paper/coloured_sand_theorem.md)) · Zenodo: [doi:10.5281/zenodo.23327609](https://doi.org/10.5281/zenodo.23327609)

## The problem

The sandpile group (critical group) $K(\Gamma)$ of a connected graph is the torsion part of the cokernel of its Laplacian; its order is the number of spanning trees. For the Hamming graph $H(d,q)=K_q^{\,d}$, Jacobson, Niedermaier and Reiner (J. Graph Theory 44, 2003) determined the $p$-part for every prime $p$ that does not divide $q$, and wrote that the other primes appear *"to be difficult, due to bad behavior of its $p$-primary structure"*. For $q=2$ (the hypercube) the $2$-part is the [Dancing Sand Theorem](https://github.com/tretoef-estrella/dancing-sand-theorem). This repository is about the primes $p\mid q$; we write $e=v_p(q)$.

## What is proved

- **Theorem A** (Jacobson–Niedermaier–Reiner, their Theorem 13, rewritten). $\operatorname{coker} L(H(d,q))\cong\bigoplus_j X_q(d-j,j)^{\binom dj(q-2)^j}$, where $X_q(m,c)$ is the cokernel of $q(c+H)+U$ on the Boolean lattice of $[m]$ ($H$ the size, $U$ the up operator).
- **Theorem B.** For every prime $p>d$ dividing $q$:
  $\operatorname{Syl}_p K(H(d,q))\cong\bigoplus_{v=1}^d(\mathbb Z/p^{ev})^{n_v}$, with $n_v=\sum_{j+2k=d+1-v,\ (j,k)\neq(0,0)}\binom dj(q-2)^j\,\frac{v}{v+2k}\binom{v+2k}{k}$ (ballot numbers).
- **Theorem C.** For every prime $p$ and $q\ge3$: the exponent of $\operatorname{Syl}_pK(H(d,q))$ is $p^E$ with $E=\max_{1\le s\le d}(es+v_p(s))$ if $p\mid q$, and $E=\lfloor\log_pd\rfloor$ if $p\nmid q$.
- **Theorem D.** For $p\mid q$: the number of cyclic factors, in closed form, from Wilson's diagonal form of inclusion matrices.
- **Theorem E.** For every prime $p$, the exact contribution of every piece $X_q(m,c)$ with $m<p$.

What is left is the pieces with $m\ge p$.

## What is conjectured

**The Glue Conjecture** (Conjecture F in the paper) gives $\operatorname{Syl}_pX_q(m,c)$ for every $m\le2p-2$, hence $\operatorname{Syl}_pK(H(d,q))$ for every $d\le2p-2$: on each pair of strings glued by the tilting module $T(\lambda)$, $p\le\lambda\le2p-2$, of $SL_2$ in characteristic $p$, exactly one factor $p$ moves from the long string to the short one. It was found from $88$ pieces with $p=3,5$ and then predicted, **before they were computed**, $44$ further cases, all correctly.

## Status

A preprint. The proofs were found and re-read once by the AI system that wrote them (see *Provenance*) and checked against every computation below; **they have not yet been read by an independent reader.** The conjecture rests on computation only.

## Verification

Run everything from [`engines/`](engines/) (Python 3 with NumPy; `sage_check.py` needs SageMath). Logs are in [`logs/`](logs/).

| Claim | Check | Result |
|---|---|---|
| Theorem A | `gate_reduction.py`: Sylow subgroups from the full Laplacian versus from the pieces, $27$ cells, $p\in\{2,3,5,7\}$ | 90 / 90 |
| Theorem B | ten predictions sealed in [`sealed/PREDICCION_SELLADA_1.txt`](sealed/PREDICCION_SELLADA_1.txt) (MD5 `d5c36be3736079cbc2349f469751c627`), computed afterwards (`logs/cell_*.log`) | 10 / 10 |
| Theorem C | `gate_exponent.py`, $143$ cells, with and without $p\mid q$, including $p=2$ | 143 / 143 |
| Theorem D | `gate_wilson.py` (rank of inclusion matrices) and `wilson_prank.py` (against the computed groups) | 264 / 264 and 23 / 23 |
| Glue Conjecture | $30$ pieces at $p=7$ sealed in [`sealed/PREDICCION_SELLADA_2.txt`](sealed/PREDICCION_SELLADA_2.txt) (MD5 `1f5cc12e88f12e375022658da3eea6ce`): `check_sealed2b.py 9` (exact Smith form up to $m=9$), `check_inverse.py` | 30 / 30 |
| Glue Conjecture | $14$ full groups with composite $q$ sealed in [`sealed/PREDICCION_SELLADA_3.txt`](sealed/PREDICCION_SELLADA_3.txt) (MD5 `341a2c489aef1c30349bae079ddcce81`): `check_sealed3.py` | 14 / 14 |
| Glue Conjecture, scope | `check_e0.py`: it fails when $p\nmid q$, as stated | stated |

The Smith forms are computed over $\mathbb Z/p^M$ with $p^M<2^{31}$; divisors of valuation $\ge M$ are recovered exactly from $p^E M^{-1}$ (`check_inverse.py`).

## Provenance

The results were found on the night of 12–13 October 2026 by Claude (Anthropic), working for the author as «Grepy Terminator», the auditor of the author's previous projects: it chose the problem after a search of the literature, wrote the computations, found the formulas, sealed and checked the predictions, found the proofs, and found — when checking the literature before publication — that Theorem A is Theorem 13 of Jacobson–Niedermaier–Reiner. The author takes responsibility for the work.

## Licence

Code (`.py`): MIT, see [LICENSE](LICENSE). Texts (paper, logs, this file): CC BY 4.0, see [LICENSE-TEXT.md](LICENSE-TEXT.md).
