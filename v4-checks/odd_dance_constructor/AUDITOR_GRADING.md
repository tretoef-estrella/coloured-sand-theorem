# Grading of «The odd dance» — Grepy el Bailarín, constructor 1 of the Coloured Sand
Grepy Sand, auditor. Started Tue Oct 13 21:05:18 CEST 2026.

Report: `REPORT.md` (md5 `d9c2f1ab4b0aca544135f17e1dc726d3`, 327 lines, finished 21:02:40), copied with its 44 scripts, logs and sealed files into this folder (`MANIFEST_md5.txt`, 46 lines). The constructor's folder on the Desktop is not touched.

## Verdict
**HIGH MARK. The claim holds on the auditor's first reading and own checks; it is PROVED BY ONE HAND, not yet read cold.**

What it claims, in one sentence: for every prime `p`, every `q` with `p | q` and every `d`, the whole group `Syl_p K(H(d,q))`, in closed form (Theorem TOTAL); on the way, Conjecture I of v3 for every prime (Theorem I), Theorem D_p (the odd dance), and explicit `ℤ_p`-lattices for all tilting modules of `SL_2` (Theorem 1.6).

## What I checked, with code of my own that does not use the constructor's lattices
1. **Per block, the two invariants that do not depend on any lattice** (`lean/chk/gradeBailarin.py`, `lean/logs/gradeBailarin.log`, 8 s, 57 MB):
   - the length of `Y_p(λ,i,e)` equals `v_p det(F + p^e(D+i)) = Σ_w mult_{T(λ)}(w)·(e + v_p((λ−w)/2 + i))`;
   - the number of cyclic summands equals `dim T(λ)/p`, with `ch T(λ)` written by me from Donkin's product.

   Ranges: `p ∈ {3,5,7,11}`, `λ ≤ 400/400/300/250`, `e ≤ 3`, `1 ≤ i ≤ 5`. **20 310 cells, 0 failures;** the control (`e+1`) differs in all 20 310.
   *Limit, said plainly:* the antitonic fit preserves sums, so this test does not see the fit itself. It sees the characters, the carries `κ_p`, the `eK` term and the count.
2. **Whole Hamming graphs, against Kirchhoff and a rank** (same log):
   - the length of `Syl_p K(H(d,q))` equals `v_p((1/q^d)·Π_j (qj)^{C(d,j)(q−1)^j})`;
   - the number of cyclic factors equals `corank_{F_p} L − 1 = Σ_n C(d,n)(q−2)^{d−n} c_p(n) − 1`, where `c_p(n)` is the cokernel of `e_1` on `F_p[x]/(x_i²)`. `c_p(n)` comes from Wilson's rank formula, cross-checked against direct ranks for `n ≤ 12`, `p = 3,5,7`.

   Cells: `p = 3`, `d ≤ 20`, `q ∈ {3,6,9,12,27}`; `p = 5`, `d ≤ 14`; `p = 7`, `d ≤ 10`; `p = 11`, `d ≤ 8`. **180 cells, 0 failures**, including `p = 3`, `d = 12…20`, beyond everything proved before. The control (`v_p(q)+1`) differs in 180 of 180.
3. **New direct cells beyond the proved range** (`lean/chk/gradeBailarin_B12.py`, logs `gradeBailarin_B12a.log`, `_B12b.log`, 210 s and 0.93 GB each). The test is the Smith form of `q(c+H)+U` on `B_12`, computed directly at `p = 3`, `q = 9` (`e = 2`), `c = 0,1,2,3`. It is compared against Theorem G for `λ < 12` plus the constructor's closed formula for `λ = 12`. No one had computed these cells: the auditor's table of §2.4 had `q ∈ {3,6}`.

   **4 of 4 exact** in every exponent below 19, and in the number of summands of exponent `≥ 19` or free. The non-trivial exponents of the `λ = 12` block that fall below 19 are seen directly: `12, 17` (`c = 0`), `14, 16` (`c = 1, 2`), `13, 17` (`c = 3`).
4. Pencil, first reading:
   - Lemma 1.0;
   - Definition 1.1 and Proposition 1.2 (a), (b), (d);
   - the twist move (Prop. 2.1), the split move (Prop. 2.2) and the last level (Prop. 2.3);
   - the count of Theorem D_p;
   - Theorem I from Theorem D_p;
   - the consistency count `d_k p^{k−1}2^{|I|} = dim T(λ)/p`.

   These are correct as written. The relations of Definition 1.3 were checked on two cases by hand (`A_{p−1}n`, `C_{p−1}n`).

## What is not yet established (the provisos, in the constructor's own words and mine)
- **Theorem 4.4, the floor:** odd-`p` Theorem F is written as a list of changes to DST §7, not line by line. It has four window types instead of two. Every intermediate claim was checked in 56 246 houses. Nobody has read it cold. **This is the riskiest step.**
- **Theorem 1.6 cites** Donkin's tensor product theorem and the decomposition of tilting modules over `F_p` [Don93], [Jan03]. These are standard but were not opened. For Lean an elementary route is needed (see the plan).
- **Novelty:** one web search (PASO 0) found nothing. The integral `ℤ_p` forms of `SL_2` tilting modules may have literature: S. Martin; «SL_2 tilting modules in the mixed case» (Sutton–Tubbenhauer–Wedrich–Zhu, Selecta 2023). It must be swept in the originals before any priority sentence.
- **Independence beyond `p = 3`, `m = 12`:** the 10 710 sealed cells compare the closed formula against Theorem D_p on the constructor's own lattice, not against an object independent of it. My checks (1)–(2) are independent but aggregate; check (3) is independent and fine but only at `p = 3`.

## Errors of the constructor
Five, all disclosed by itself, none affecting a claim (two non-blind cells marked in the sealed file; one killed run kept apart; one draft sentence corrected). Its controls fire. It used no delegation.

## Next
1. A cold reader of the whole report, with Theorem F_p rewritten line by line. Rafa launches it.
2. The literature sweep for integral tilting lattices of `SL_2` in odd characteristic.
3. The Lean plan, stage 4: `lean/PLAN_LEAN_STAGE4_ODD_DANCE_v1.md`.
4. v4 of the paper (already pending for item 583).

Finished: see the registers (ESTADO_NOCHE, pending list 601).
