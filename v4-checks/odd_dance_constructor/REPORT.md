# REPORT — The odd dance (Grepy el Bailarín)
## First line: what closed (MINIMUM / GOOD / TOTAL / none), in one sentence
**TOTAL** (with one proviso) — for every odd prime p I built explicit Z_p-lattices for all tilting modules T(λ) of SL_2 and proved Theorem D_p, hence Conjecture I for every prime, and then the exact closed formula for every block Y_p(λ,i,e) (DST's clocks with base-p carries and K = d_k p^k, pooled by the antitonic fit), i.e. the whole Syl_p K(H(d,q)) for every d, every q and every prime p; the proviso is that the floor of the Smith form (odd-p Theorem F) is an adaptation of DST §7 written as a list of changes, checked step by step on 56246 houses and on 10710 + 1520 sealed blind cells with 0 misses, but not yet read cold by anyone (Tue Oct 13 21:02:40 CEST 2026).
## PASO 0 — reading, gates reproduced, literature

PASO 0 — ESTADO: CERRADO — Tue Oct 13 19:32:10 CEST 2026 (started Tue Oct 13 19:28 CEST 2026)

Engine estimates (written before running):
- E0.1 `gate_auditor_theoremG.py` (closed-form only): < 50 MB, < 30 s.
- E0.2 `gate_auditor_simple_blocks.py` (exact Smith mod p^400 on chains of size <= 200, 192 cells x 2): < 100 MB, < 300 s.
- E0.3 `work/frontier_cell_3_0.py` (copy of `frontier_p3_m12.py`, only (q,c)=(3,0)): ~930 MB peak, ~100 s (auditor's measurement).
Reading. DST v10 §1–§4 read in full (§3.1 doubling functor, §3.2 Lemmas 3.2/3.3, Cor. 3.4, §3.3 dance lattices, §4.1–4.5 payment systems, twist/split moves, Theorem 4.4 windows, Lemma 4.5 deficit law); §5 read (cost form, Props 5.2–5.4); §6–§7 only skimmed at this point. Coloured Sand v3 §1, §2, §6 (Lemma 7 glue, Lemma 8 blocks, (T1)–(T3)), §7, §8 (Conjecture I), §9 read.

Observation on DST §3.2 (to be proved properly in PASO 1(c)): Lemma 3.2 uses only (K), weights and integrality; Lemma 3.3 uses Weyl's theorem over Q, the Newton forward-difference integrality of weight projectors, the duality ι, and the short exact sequence 0 → N →(×2) N → N⊗F_2 → 0; Cor. 3.4 uses completeness of Z_2 (1 + 2h invertible). Replacing 2 by p changes nothing in any of these arguments.

Gates reproduced (watchdog, last line VIGIA-FIN-OK):
- `work/gateG.log` (= `material/engines/gate_auditor_theoremG.log` line for line): `test cells 6900 bad 0`, `control cells 6900 bad 4560`. Peak 22 MB, 0 s. MEASURED (6900 cells, control fires).
- `work/gateS.log` (= `material/engines/gate_auditor_simple_blocks.log`): `test (192, 0)`, `control (192, 128)`. Peak 11.5 MB, 4 s. MEASURED (192 cells, control fires).
- `work/frontier_cell_3_0.log`: cell (q,c) = (3,0) of the table of MISSION §2.4: block λ=12 = `{1: 8, 7: 1, 10: 1, 12: 1}` plus one free summand (free direct 1, free rest 0), i.e. Z_3 ⊕ (Z/3)^8 ⊕ Z/3^7 ⊕ Z/3^10 ⊕ Z/3^12, as in the table; neg = {} (no negative remainder). Peak 783 MB, 112 s. MEASURED (1 cell).

Literature (one search, extended web search, Tue 13 Oct 2026, query «sandpile critical group Hamming graph Laplacian Smith normal form p divides q tilting modules SL2 odd characteristic integral lattice Frobenius twist»). Found nothing that computes the Smith form of f + p^e(D+i) on tilting modules of SL_2 for odd p, nothing on the Laplacian of H(d,q) at p | q beyond what v3 already cites ([JNR03] says it is difficult), and no integral (Z_p-lattice) form of the Frobenius twist for odd p. Closest items returned: the Smith/critical groups of Grassmann graphs by Sin's school (people.clas.ufl.edu/sin/files/grassmann2.pdf), which split the problem at the defining characteristic; S. Martin, «On certain tilting modules for SL_2» (arXiv:1705.06980) and its part II (arXiv:2004.01153), which describe when ∇ ⊗ Δ is tilting over a field of characteristic p via p-adic digits; «SL_2 tilting modules in the mixed case» (Selecta Math. 2023, doi 10.1007/s00029-023-00835-0), over fields. None works over Z_p and none computes a cokernel. I rely on none of them (so I quote none). Grade: the absence is a search result, not a theorem.

## PASO 1 — the lattices
PASO 1 — ESTADO: CERRADO — Tue Oct 13 20:05:05 CEST 2026 (started Tue Oct 13 19:33 CEST 2026)

Engine estimates (written before running):
- E1.1 `work/explore_psi.py` (exact rationals; models of rank <= 60; E recovered from F,H via primitive vectors; integrality of E^(r), F^(r)): < 100 MB, < 120 s.
- E1.3 `work/explore_iota.py` (F,H-equivariant maps Model_r(Delta(b)) -> V (x) Model_{r-1}(Delta(b)), exact rationals, rank <= 80): < 150 MB, < 300 s.
- E1.4 `work/sanity_oddlat.py` (sl2 relations of the explicit formulas for all lambda with dim <= 200, p in {3,5,7}; E formula vs E recovered from F,H on dims <= 60; lambda=12 table): < 200 MB, < 300 s.
- E1.5 `work/gateA.py struct p` for p = 3, 5, 7 separately (every lambda with dim T(lambda) <= 600: sl2 relations, character, integrality of f^(r), e^(r) for all r by exact integer powers): each < 300 MB, 60–500 s (if a run is killed by time, it is split by lambda range).
- E1.6 `work/gateA.py compare` (Y_p on L(lambda) vs block_cf for every lambda <= p^2+p-1, p in {3,5,7}, e in {1,2,3}, i in {0..4}; the lambda=12 table; two controls): < 200 MB, < 500 s.
- E1.7 `work/gateA_intcontrol.py` (integrality control: coupling eps=p instead of 1, and wrap without p; E recovered from (F,H) over Q; dims <= 60): < 100 MB, < 120 s.
- E1.2 `work/explore_E.py` (prints E of the eps=1 model on Delta(b) in the model basis, p=5, r'=1..4, b<=3; rank <= 40): < 100 MB, < 120 s.


Progress note (before Gate A): explicit lattices built in `work/oddlat.py` (Phi = digit 0, Psi_r = digit r, ending on Delta(d_k-1)).
- `work/explore_psi.log`: the eps=1 model of Psi_r(Delta(b)) is Dist-integral (min v_p of all E^(r), F^(r) = 0) for p in {3,5}, all r, b <= 2; the eps=0 (uncoupled) model carries no sl_2-structure at all. MEASURED (18 integral ε=1 models, 18 ε=0 models without sl_2-structure, plus 6 Φ lattices).
- `work/sanity_oddlat.log`: the explicit E-formulas satisfy [E,F]=H and the weight rules on 267 lattices (p in {3,5,7}, dim <= 200): 0 failures; the formula-E equals the E recovered from (F,H) on 101 lattices (dim <= 60): 0 mismatches. On L(12) = Psi_1(Psi_1(Delta(0))) (p=3, dim 36): Y_3(12,i,1) for i=0..3 equals the table of MISSION §2.4 in all four cells; Y_3(12,i,2), i=1,2: {1:8, 14:1, 16:1, 24:1, 26:1} (eight Z/3 and four summands of order >= 27, as measured by the auditor). MEASURED (4+2 cells).

### PASO 1 — results (Tue 13 Oct 2026, 20:03 CEST)

Conventions. `p` odd, `A = ℤ_p`, `Dist_A = A ⊗ Dist_ℤ(SL_2)` (Kostant form, DST §2.2). A *lattice* is a `Dist_A`-module, free of finite rank over `A`, which is the direct sum of its weight spaces with integer weights. `u := −1` (any unit `≡ −1 mod p` would do; `p/u = −p`). For `n` in a lattice `N`, `w` denotes its weight and `X := F E` (an integral operator on `N`, weight 0). `Δ_A(μ)`, `∇_A(μ)` are as in DST §2.3 (basis `e_s = F^{(s)}v`, `F e_s = (s+1)e_{s+1}`; dual basis `w_s`, `F w_s = (μ−s)w_{s+1}`).

**Lemma 1.0 (E is determined by F and H).** Let `X, Y` be finite-dimensional `U_ℚ(sl_2)`-modules and `φ: X → Y` a linear map with `φF = Fφ`, `φH = Hφ`. Then `φE = Eφ`. Consequently: (i) on a finite-dimensional vector space with given `F, H` there is at most one `E` making it an `sl_2`-module; (ii) a weight-preserving `A`-isomorphism of lattices that commutes with `F` is an isomorphism of `Dist_A`-lattices. — PROVED (pencil).
*Proof.* `D := φE − Eφ` raises weights by 2 and `DF − FD = φ[E,F] − [E,F]φ = φH − Hφ = 0`. `X` is spanned by the `F^k x` with `x` primitive (`Ex = 0`) of weight `h ≥ 0`, and `F^{h+1}x = 0`. Then `F^{h+1}Dx = DF^{h+1}x = 0`, while `F^{h+1}` is injective on `Y_{h+2}` (on `Δ(c)` a vector of weight `μ` is killed by `F^k` only if `k > (c+μ)/2 ≥ μ`). So `Dx = 0` and `D F^k x = F^k Dx = 0`. For (ii): the map commutes with `E` over `ℚ`, hence with all `E^{(r)}, F^{(r)}` and with the `C(H,r)`. ∎

**Definition 1.1 (the twist `Φ_p`, digit 0).** `Φ_p(N) := ⊕_{j=0}^{p−1} b_j ⊗ N` (write `b_j n`), with, for `n` of weight `w`:
- `H(b_j n) = (pw + p − 1 − 2j) b_j n`;
- `F(b_j n) = b_{j+1} n` (`j ≤ p−2`), `F(b_{p−1} n) = pu · b_0 (Fn)`;
- `E(b_j n) = b_{j−1} g_j n` with `g_j := p²X + j(pw + p − j)` (`j ≥ 1`), `E(b_0 n) = (p/u) · b_{p−1}(En)`;
- `Φ_p(f) := 1 ⊗ f` on morphisms.

**Proposition 1.2.** (a) `Φ_p(N)` is a lattice; `Φ_p` is an exact functor that preserves saturated sublattices. (b) For `r = ps + t` (`0 ≤ t ≤ p−1`): `F^{(r)}(b_j n) = (pu)^c c!/r! · b_{j+r−pc} F^{(c)} n` with `c = ⌊(j+r)/p⌋`. (c) `Φ_p(N) ⊗ 𝔽_p ≅ St ⊗ (N ⊗ 𝔽_p)^{[1]}`, `St = Δ(p−1) = T(p−1)`. (d) `Φ_p(Δ_A(μ)) ≅ Δ_A(pμ+p−1)`, `Φ_p(∇_A(μ)) ≅ ∇_A(pμ+p−1)`, `Φ_p(A) = St_A`. — PROVED (pencil); MEASURED as part of Gate A.
*Proof.* (a) *Relations.* `[E,F](b_j n) = (g_{j+1} − g_j) n = (pw + p − 1 − 2j)` for `1 ≤ j ≤ p−2`; on `b_0 n`: `EF − FE = g_1 − (p/u)(pu)·X = pw + p − 1`; on `b_{p−1}n`: `EF − FE = p²·EF − g_{p−1} = p²(X + w) − p²X − (p−1)(pw+1) = pw − p + 1`; these are the weights. `E` raises and `F` lowers weights by 2 (e.g. `b_{p−1}(En)` has weight `p(w+2) − p + 1 = (pw + p − 1) + 2`). So `Φ_p(N) ⊗ ℚ` is a `U_ℚ`-module. *Divided powers.* (b) follows from `F^r(b_j n) = (pu)^c b_{j+r−pc} F^c n` (one factor `pu` per passage `b_{p−1} → b_0`); its coefficient has `v_p(p^c c!/r!) = c + v_p(c!) − v_p(r!) ≥ 0` because `c ≥ ⌊r/p⌋`, `x ↦ x + v_p(x!)` is non-decreasing and `v_p(r!) = ⌊r/p⌋ + v_p(⌊r/p⌋!)` (Legendre). For `E`: `E^r(b_j n) = (p/u)^c b_{j''} P(X,H) E^c n` with `c = ⌊(r+p−1−j)/p⌋ ≥ ⌊r/p⌋` wraps and `P` an integer polynomial (move the `g`'s to the left with `E X = (X+H)E`, `EH = (H−2)E`); `E^c = c!E^{(c)}` and the same valuation count gives integrality. The `C(H,r)` act by integers. (c) Map `b'_j ⊗ n̄ ↦ b_j n̄`, where `b'_j := F^j b'_0` in `St`. Mod `p`, with `r = ps + t`: by (b), `F^{(r)}(b_j n) ≡ [j+t ≤ p−1]·(1/t!)·b_{j+t}F^{(s)}n`, using `(ps+t)!/(p^s s!) ≡ (−1)^s t!` and `u ≡ −1`; for `E`, `g_i ≡ −i² (mod p)` as a polynomial, a full cycle contributes `∏_{i=1}^{p−1}(−i²) ≡ 1`, so `E^{(r)}(b_j n) ≡ [t ≤ j]·(−1)^t (j!/(j−t)!)²/t! · b_{j−t}E^{(s)}n` (if `t > j` there are `s+1` wraps and the coefficient is `≡ 0`). These are the formulas of `St ⊗ N̄^{[1]}` computed with the coproduct (only `F^{(pβ)}, E^{(pβ)}` act on `N̄^{[1]}`, as `F^{(β)}, E^{(β)}`; in `St`, `F^{(t)}b'_j = b'_{j+t}/t!` and `E^{(t)}b'_j ≡ (−1)^t (j!/(j−t)!)²/t!·b'_{j−t}`, by `i!(p−1−i)! ≡ (−1)^{i+1}`); the weights agree. (d) In the basis `x_R := b_j e_s` (`R = ps + j`) of `Φ_p(Δ(μ))`: `F x_R = x_{R+1}` (`j ≤ p−2`), `F x_{ps+p−1} = pu(s+1)x_{p(s+1)}`; in `Δ(pμ+p−1)`, `F e_R = (R+1)e_{R+1}` with `R+1` a unit unless `j = p−1`, where it is `p(s+1)`. The diagonal map `e_R ↦ c_R x_R`, `c_0 = 1`, `c_{R+1} = c_R/(R+1)` (`j ≤ p−2`), `c_{R+1} = u c_R` (`j = p−1`), has unit entries and commutes with `F, H`: by Lemma 1.0(ii) it is a lattice isomorphism. Same for `∇` (`F w_R = (λ−R)w_{R+1}`, `λ − R = p(μ−s) + p−1−j`). Exactness: `Φ_p(N) = N^p` as `A`-modules and `Φ_p(f) = 1 ⊗ f` commutes with `F, H` (and then with `E`, Lemma 1.0). ∎

**Definition 1.3 (the split `Ψ_r`, digit `r`, `1 ≤ r ≤ p−1`).** `Ψ_r(N) := ⊕_{j=0}^{p−1} (A_j ⊗ N ⊕ C_j ⊗ N)`, with
- `H(A_j n) = (pw + p − 1 + r − 2j) A_j n`, `H(C_j n) = (pw + p − 1 − r − 2j) C_j n`;
- `F(A_j n) = A_{j+1} n`, `F(C_j n) = C_{j+1} n` (`j ≤ p−2`); **`F(A_{p−1} n) = pu·A_0(Fn) + p·C_{p−r} n`**, `F(C_{p−1} n) = pu·C_0(Fn)`;
- with `g^A_j := p²X + j(pw + p + r − j)`, `g^C_j := p²X + j(pw + p − r − j)`:
  `E(A_0 n) = (p/u)·A_{p−1}(En) − (p−r)(p/u)·C_{p−1−r}(En)`;
  `E(A_j n) = A_{j−1} g^A_j n + r(p/u)·C_{p+j−1−r}(En)` for `1 ≤ j ≤ r`;
  `E(A_j n) = A_{j−1} g^A_j n + r p²·C_{j−1−r}(Xn)` for `r+1 ≤ j ≤ p−1`;
  `E(C_0 n) = r·A_{r−1} n + (p/u)·C_{p−1}(En)`;
  `E(C_j n) = C_{j−1} g^C_j n + r·A_{j+r−1} n` for `1 ≤ j ≤ p−r`;
  `E(C_j n) = C_{j−1}(g^C_j + rp) n + r pu·A_{j+r−1−p}(Fn)` for `p−r+1 ≤ j ≤ p−1`;
- `Ψ_r(f) := 1 ⊗ f`.
Floors: if `N` has top weight `b` and `n` floor `f`, then `Ψ_r(N)` has top weight `pb + p − 1 + r`, `A_j n` sits on floor `pf + j` and `C_j n` on floor `pf + r + j`; in `Φ_p(N)`, `b_j n` sits on floor `pf + j`.
(The formulas for `E` were first read off the unique `E` of Lemma 1.0(i) on `Ψ_r(Δ(b))`, `p = 5`, `r = 2` (`work/explore_E_5_2_2.log`), then proved in general.)

**Proposition 1.4.** (a) `Ψ_r(N) ⊗ ℚ` is a `U_ℚ`-module (all relations). (b) For `r ≥ 2` the map `ι: Ψ_r(N) → V ⊗ Ψ_{r−1}(N)` given by `ι(A_j n) := F^j α(n)`, `ι(C_j n) := F^j γ(n)` (`0 ≤ j ≤ p−1`), with (primes for `Ψ_{r−1}`; `V = A b̂_0 ⊕ A b̂_1`)
  **`α(n) = b̂_0 ⊗ A'_0 n + (p/u)·b̂_1 ⊗ C'_{p−r}(En)`,  `γ(n) = b̂_0 ⊗ C'_1 n + b̂_1 ⊗ A'_{r−1} n − (pw + p − r)·b̂_1 ⊗ C'_0 n`,**
is a `Dist`-equivariant embedding with saturated image; for `r = 1`, `A_j n ↦ b̂_0⊗b_j n + j b̂_1⊗b_{j−1} n`, `C_j n ↦ b̂_1 ⊗ b_j n` is an isomorphism `Ψ_1(N) ≅ V ⊗ Φ_p(N)`. Hence **`Ψ_r(N)` is a lattice for every lattice `N`** (induction on `r`), and `Ψ_r` is an exact functor preserving saturated sublattices. (c) `Ψ_r(N) ⊗ 𝔽_p ≅ T(p−1+r) ⊗ (N⊗𝔽_p)^{[1]}`. (d) `Ψ_r(Δ_A(μ))` has a Δ-filtration with sublattice `Δ_A(pμ+p−1+r)` and quotient `Δ_A(pμ+p−1−r)`. — PROVED (pencil); MEASURED (Gate A).
*Proof.* (a) Direct check of `[E,F] = H` on every basis vector, in the cases of the definition (I did all of them; e.g. on `A_{p−1}n`, `r ≤ p−2`: `EF(A_{p−1}n) − FE(A_{p−1}n) = A_{p−1}[p²EF + pr − g^A_{p−1}]n + C_{p−1−r}[−(p−r)p²EF + p g^C_{p−r} − rp²X]n`, and the brackets are `pw − p + 1 + r` (the weight) and `0`; on `C_{p−1}n`, `r ≥ 2`: `p²(X+w) − g^C_{p−1} − rp = pw − p + 1 − r`; on `A_0 n`: `g^A_1 − p²X = pw + p − 1 + r`, the `C_{p−r}(En)`-terms cancel because `p − (p − r) = r`), and of the weight rules. Machine check: 267 lattices, 0 failures (`work/sanity_oddlat.log`), and the formula-`E` equals the `E` recovered from `(F,H)` on 101 lattices (same log).
(b) `F`-equivariance needs only `F^p γ(n) = pu·γ(Fn)` and `F^p α(n) = pu·α(Fn) + p·F^{p−r}γ(n)` (for `j ≤ p−2` it is the definition). Both are direct computations with `F(b̂_0⊗x) = b̂_1⊗x + b̂_0⊗Fx`, `F(b̂_1⊗x) = b̂_1⊗Fx` and the `F` of `Ψ_{r−1}`: `F^pγ(n) = pu[b̂_0⊗C'_1Fn + b̂_1⊗A'_{r−1}Fn + (p + r − pw) b̂_1⊗C'_0Fn] = pu·γ(Fn)` (`Fn` has weight `w − 2`); `F^pα(n) = pu b̂_0⊗A'_0Fn + p b̂_0⊗C'_{p−r+1}n + p b̂_1⊗A'_{p−1}n + p² b̂_1⊗C'_{p−r}Xn`, and `F^{p−r}γ(n) = b̂_0⊗C'_{p−r+1}n + b̂_1⊗A'_{p−1}n − pw·b̂_1⊗C'_{p−r}n`, `pu α(Fn) = pu b̂_0⊗A'_0Fn + p² b̂_1⊗C'_{p−r}(X + w)n`, which add up. Weights agree. By Lemma 1.0, `ι` commutes with `E` over `ℚ`, so `ι(Ψ_r(N))_ℚ` is a `U_ℚ`-submodule. Modulo `p`, `ι(A_j n) ≡ b̂_0⊗A'_j n + j b̂_1⊗A'_{j−1}n`, `ι(C_j n) ≡ b̂_0⊗C'_{j+1}n + (b̂_1-terms)` for `j ≤ p−2`, and `ι(C_{p−1}n) ≡ (r−1)·b̂_1⊗C'_{p−1}n`; on the coordinates `b̂_0⊗A'_j n`, `b̂_0⊗C'_{j+1}n` (`j ≤ p−2`), `b̂_1⊗C'_{p−1}n` the reduction of `ι` is diagonal with unit entries (`r − 1` is a unit since `2 ≤ r ≤ p−1`), so `ῑ` is injective and the image is saturated. A saturated `U_ℚ`-stable sublattice `Y` of a lattice `Z` is `Dist_A`-stable (`g·Y ⊂ Z ∩ Y_ℚ = Y`). Base: `Ψ_1(N) ≅ V ⊗ Φ_p(N)` (unitriangular, commutes with `F, H`: `F(b̂_0⊗b_{p−1}n + (p−1)b̂_1⊗b_{p−2}n) = pu b̂_0⊗b_0Fn + p b̂_1⊗b_{p−1}n`), and `V ⊗ Φ_p(N)` is a lattice. Exactness as for `Φ_p`.
(c) Induction on `r`; `r = 1`: `V⊗St = T(p)`. For `r ≥ 2`: `Z̄ := (V⊗Ψ_{r−1}(N))⊗𝔽_p ≅ V⊗T(p−2+r)⊗N̄^{[1]}`. Over `𝔽_p`, `V⊗T(p−2+r)` is tilting with Δ-factors `p−1+r, p−3+r, p+1−r, p−1−r`; the central element `Ω = 4FE + (H+1)²` acts on `Δ(ν)` by `(ν+1)²`, i.e. by `r²` on the first and last and by `(r−2)² ≢ r²` on the others (`r ≢ 1`). Its generalized `r²`-eigenspace is a tilting summand with character `χ(p−1+r) + χ(p−1−r)` containing `T(p−1+r)`; it equals `T(p−1+r)`, since otherwise `T(p−1+r) = Δ(p−1+r)` would be simple, while `F^{(r)}v ∈ Δ(p−1+r)` generates a proper submodule (`E^{(s)}F^{(r)}v = C(p−1+s, s)F^{(r−s)}v ≡ 0`, `1 ≤ s ≤ r`, by Lucas). On `M ⊗ N̄^{[1]}`, `Ω = Ω_M ⊗ 1`. On `Ψ_r(N)`, `Ω` is integral and its eigenvalues are `(p(b+1) ± r)² ≡ r²` (from the character, below), so `Ω̄ − r²` is nilpotent on `Ψ_r(N)⊗𝔽_p`; as `ῑ` is injective and `Dist`-equivariant, `ῑ(Ψ̄)` lies in `T(p−1+r)⊗N̄^{[1]}`, and the dimensions (`2p·rank N`) agree.
(d) Let `n_0` be the top of `Δ(μ)`, `L := pμ + p − 1`. Path counting in `F` (each passage through `A_{p−1}` branches once into the `C`-string with factor `p`, all branches ending on the same vector) gives, for `0 ≤ t ≤ r−1`, `F^{(p(μ+1)+t)}(A_0 n_0) = (unit)·C_{p−r+t} n_μ`, and for `k < p(μ+1)`, `F^{(k)}(A_0 n_0) = (unit)·A_{k mod p} n_{⌊k/p⌋} + (C-terms)`. So `F^{(k)}(A_0 n_0)`, `0 ≤ k ≤ L + r`, together with the remaining `C_j n_s` form a basis: `Dist·A_0 n_0 ≅ Δ_A(L+r)` (Lemma W) is saturated. In the quotient, `F^{(k)}(C̄_0 n_0) = (unit)·C̄_{k mod p} n_{⌊k/p⌋}` for `k ≤ L − r`, which is a basis of the quotient, so the quotient is `Δ_A(L − r)`. ∎

**Character.** `ch Φ_p(N) = χ(p−1)·(ch N)(z^p)`, `ch Ψ_r(N) = (z^r + z^{−r})·χ(p−1)·(ch N)(z^p)`; since `χ(p−1)χ(b)(z^p) = χ(pb+p−1)` and `(z^r + z^{−r})χ(L) = χ(L+r) + χ(L−r)` (`L ≥ r−1`), every Weyl factor `Δ(b)` of `N` gives `Δ(pb+p−1)`, respectively `Δ(pb+p−1±r)`. — PROVED (pencil).

**Lemma 1.5 (`ℤ_p`-versions of DST Lemma 3.2, Lemma 3.3, Corollary 3.4).** Verbatim with `2` replaced by `p`: (W) an extension `0 → N → X → Δ_A(λ) → 0` with the weights of `N` in `[−λ, λ]` splits; (Ext) `Ext¹(Δ_A(λ), ∇_A(μ)) = 0`, hence `Ext¹(M, N) = 0` if `M` has a Δ- and `N` a ∇-filtration, and `Hom(M, N) → Hom_{Dist_{𝔽_p}}(M̄, N̄)` is onto; (Lift) two lattices with Δ- and ∇-filtrations and isomorphic reductions are isomorphic. **Where DST uses `p = 2`: nowhere.** Lemma 3.2 uses (K) and weights; Lemma 3.3 uses Weyl's theorem over `ℚ`, the integrality of the weight projectors `P(H) = Σ_r (Δ^r P)(w_0) C(H − w_0, r)` (Newton forward differences, any `p`), the duality `ι`, and `0 → N →(×p) N → N̄ → 0`; Corollary 3.4 uses that `1 + p h` is invertible in `End(X)` (completeness). I add the one-sided form actually used: **(Lift′) if `X` has a Δ-filtration, `Y` is a direct summand of a lattice with a ∇-filtration, and `X̄ ≅ Ȳ`, then `X ≅ Y`** (lift `f̄` to `f` by (Ext); `det f̄ ≠ 0`, so `det f` is a unit). Also DST Lemma 2.4 (`V ⊗ Δ_A(m)` has a Δ-filtration, `V ⊗ ∇_A(m)` a ∇-filtration) does not use `p = 2`, so `V^{⊗m} ⊗ ℤ_p` has both filtrations. — PROVED (pencil).

**Theorem 1.6 (the dance lattices are the tilting lattices).** Define `L(λ) := Δ_A(λ)` if `λ + 1 < p`, and otherwise, with `λ + 1 = d_0 + p(b+1)` (`d_0` the last base-`p` digit), `L(λ) := Φ_p(L(b))` if `d_0 = 0`, `L(λ) := Ψ_{d_0}(L(b))` if `d_0 ≠ 0`. So `L(λ)` is built from `Δ_A(d_k − 1)` by one move per digit `t = k−1, …, 0` of `λ + 1`. Then for every odd `p` and every `λ ≥ 0`:
(i) `L(λ)` is a lattice of rank `d_k p^k 2^{|I(λ)|}` with a Δ-filtration whose factors are the `2^{|I(λ)|}` Weyl modules given by the recursion `b ↦ {pb + p − 1}` (digit 0), `b ↦ {pb + p − 1 ± d_0}` (digit `d_0 ≠ 0`);
(ii) `L(λ) ⊗ 𝔽_p ≅ T(λ)`;
(iii) `V^{⊗m} ⊗ ℤ_p ≅ ⊕_λ L(λ)^{n_λ(m)}` as lattices, `n_λ(m)` the multiplicity of `T(λ)` in `V^{⊗m}` over `𝔽_p`. In particular **`L(λ) ≅ T_{ℤ_p}(λ)`**, and `Y_p(λ, i, e) = coker(F + p^e(D + i) on L(λ))`.
— PROVED (pencil), citing two standard facts: Donkin's tensor product theorem `T(p−1+r+pb) ≅ T(p−1+r) ⊗ T(b)^{[1]}` (`0 ≤ r ≤ p−1`) [Don93], and the decomposition of a tilting module over `𝔽_p` into indecomposable `T(λ)`'s, `V^{⊗m}` being tilting [Jan03, E.6]. (I did not open these references in this session; the mission quotes the first, MISSION §1.3.)
*Proof.* (i) Induction on `λ`: exactness of `Φ_p, Ψ_r` and Propositions 1.2(d), 1.4(d) (refine the image of a Δ-filtration of `L(b)`); the rank multiplies by `p` or `2p`. (ii) Induction: `L̄(λ) ≅ St ⊗ T(b)^{[1]}` or `T(p−1+d_0) ⊗ T(b)^{[1]}` (Props 1.2(c), 1.4(c)), which is `T(λ)` by Donkin; base `Δ(λ) = T(λ)` for `λ ≤ p−2`. (iii) `X := ⊕ L(λ)^{n_λ(m)}` has a Δ-filtration, `Y := V^{⊗m} ⊗ ℤ_p` has a ∇-filtration, and `X̄ ≅ Ȳ` by (ii): apply (Lift′). The block-group identity then is v3 §8 (Lemma 2 of v3 lets `q` be replaced by `p^e`). ∎
Remark. The ∇-filtration of `Ψ_r(∇_A(μ))` (asked in (b) "with the same three properties") is **not proved**: it is not needed, because (Lift′) uses only the Δ-filtration of `L(λ)` and the ∇-filtration of `V^{⊗m}`.

**Gate A.** All in `work/` with the watchdog, last line `VIGIA-FIN-OK`.
- `work/gateA_struct3.log`, `work/gateA_struct5.log`, `work/gateA_struct7.log`: every `λ` with `dim T(λ) ≤ 600` (134, 200, 235 lattices for `p = 3, 5, 7`; `λ ≤ 485, 499, 342`): sl_2 relations 0 failures; character of `L(λ)` = the Donkin product `∏_{t<k} χ_{p−1}(z^{p^t})·(z^{d_tp^t}+z^{−d_tp^t})^{[d_t≠0]} · χ_{d_k−1}(z^{p^k})` and rank `= d_k p^k 2^{|I|}`: 0 failures (this also checks the dimension formula of MISSION §1.3 on 569 values of `λ`); integrality of `f^{(r)}` and `e^{(r)}` for **all** `r` (exact integer powers): 0 failures, min `v_p = 0`. MEASURED (569 lattices).
- `work/gateA_compare.log`: `Y_p` computed by exact p-adic Smith form on `L(λ)` equals `block_cf` (Theorem G, PROVED) for every `λ ≤ p²+p−1`, `p ∈ {3,5,7}`, `e ∈ {1,2,3}`, `i ∈ {0,…,4}`: **1470 cells, 0 failures**; the table of MISSION §2.4 (`λ = 12`, `p = 3`, `e = 1`, `i = 0..3`): **4 cells, 0 failures**. MEASURED.
- Controls (must fail): `CONTROL nop` (outermost move with the wrap `u·A_0(Fn)` instead of `pu·A_0(Fn)`): 1065 of 1290 cells differ from Theorem G; `CONTROL eps0` (split move without the coupling `p·C_{p−r}n`): 942 of 1290 differ (the cells that agree are those whose outermost digit is 0, where the control lattice is the true one). Integrality control `work/gateA_intcontrol.log`: coupling `p²` or `p³` instead of `p`, or the twist without `p`, with `E` recovered from `(F,H)`: 40 of 42 lattices are not `Dist`-stable; the 2 survivors are the twist without `p` on `Δ(0)`, where `F_N = 0` and the control changes nothing. Controls fire.

## PASO 2 — the moves and Theorem D_p
PASO 2 — ESTADO: CERRADO — Tue Oct 13 20:11:37 CEST 2026 (started Tue Oct 13 20:06 CEST 2026)

Engine estimates (written before running):
- Sealed: `work/SEALED_1.txt`, written Tue Oct 13 20:08:00 CEST 2026, md5 `0a9c3442e54c54c8cc880d9b2bc070b0`, 1520 cells (p=3, 12<=lam<=80; p=5, 30<=lam<=150; e in {1,2}; i in {0..3}). Not blind inside it: p=3 lam=12 e=1 (the auditor's table), p=3 lam=12 e=2 i=1,2 (computed in `work/sanity_oddlat.log` before sealing), p=3 lam=79 e=1 i=1 (timing run in `work/gateB_test.log`). All other 1513 cells are blind.
- E2.3 `work/gateB.py run P LO HI` (direct sparse Smith vs sealed/moves; controls 'nolast' and 'p2'): p=3 all lam<=80 in one run; p=5 split in lambda ranges; each run < 300 MB, < 550 s.
- E2.2 `work/gateB.py seal` (moves only, no direct computation; 1520 cells outside the proved range): < 100 MB, < 120 s.
- E2.1 `work/gateB.py test` (moves vs direct sparse Smith, p=3, lambda <= 11, e in {1,2}, i in {0..3}: proved range, no sealing needed; also timing of the direct engine on the largest p=3 lattice dim 432): < 300 MB, < 300 s.

### PASO 2 — results (Tue 13 Oct 2026, 20:10 CEST)

**Payment systems (as DST §4.1, any prime).** `N` a lattice graded by floors (`F` raises the floor by one). A payment system of size `R` on `N^{⊕R}` is `G(x ι_{s'}) = F x ι_{s'} + Σ_s P(φ)_{s s'} x ι_s` for `x` on floor `φ`, with `P(φ) ∈ M_R(A)` lower triangular (`P_{ss'} = 0` for `s < s'`; diagonal = the payments `π_s(φ)`, below = the couplings). It is *even* if every `P(φ) ∈ p·M_R(A)`. Writing the generators of the cokernel as row vectors `g(x) = (x ι_1, …, x ι_R)`, the relations of `G` read `g(Fx) + g(x)·P(φ) = 0`. `G ∼ G'` means equivalence over `A` (same Smith form). `σ = F + p^e(D + i)` on `L(λ)` is an even payment system of size 1 with `P_0(φ) = p^e(φ + i)` (`e ≥ 1`).

**Proposition 2.1 (twist move, odd p).** Let `N = Φ_p(N')` with its floors (`b_j n` on floor `pf + j` for `n` on floor `f`), and `G` even of size `R`. Then
  `G ∼ I_{(p−1)R·rank N'} ⊕ p·G'`,  `G'` even of size `R` on `N'` with  **`P'(f) = (−1)^{p−1} u^{−1} p^{−1} · P(pf) P(pf+1) ⋯ P(pf+p−1)`**
(product of `p` consecutive payment matrices, increasing floors left to right). Diagonal: `π'_s(f) = u^{−1}∏_{j=0}^{p−1} π_s(pf+j)/p` (`p` odd); couplings: the chain sums `K'_{ss'}(f) = u^{−1}p^{−1}Σ_{s = t_0 ≥ t_1 ≥ ⋯ ≥ t_p = s'} ∏_{j=0}^{p−1} P(pf+j)_{t_j t_{j+1}}` (for `p = 2`, `u = 1` this is DST Prop. 4.1, sign `(−1)^{p−1} = −1` included). `P'(f) ∈ p^{p−1}M_R(A)`: the new system is even. — PROVED (pencil).
*Proof.* For `j ≤ p−2` the relations `G(b_j n ι_{s'})` have coefficient `1` on `b_{j+1} n ι_{s'}` (because `F(b_j n) = b_{j+1} n`), and all their other terms lie on `b_j`; eliminating them (a unitriangular block, one per `n`, `s'`, `j`) gives `g_{j+1}(n) = −g_j(n) P(pf+j)`, so `g_{p−1}(n) = (−1)^{p−1} g_0(n) P(pf)⋯P(pf+p−2)`. The remaining relations are those of the `b_{p−1} n ι_{s'}`: `pu·g_0(Fn) + g_{p−1}(n) P(pf+p−1) = 0`, i.e. `pu·[g_0(Fn) + g_0(n) P'(f)] = 0`, which is `p·G'` (times the unit `u`) under `b_0 n ↦ n`. ∎

**Proposition 2.2 (split move, odd p, digit `r ∈ [1, p−1]`).** Let `N = Ψ_r(N')` (`A_j n` on floor `pf + j`, `C_j n` on floor `pf + r + j`) and `G` even of size `R`. Then
  `G ∼ I_{2(p−1)R·rank N'} ⊕ p·G''`,  `G''` even of size `2R` on `N'`, slots `(s, A)` and `(s, C)`, with block payment (rows = generator slot, columns = relation slot, order: all `A` slots, then all `C` slots)
  **`P''(f) = [[Q_A(f), 0], [K(f), Q_C(f)]]`,**
  `Q_A(f) = (−1)^{p−1}u^{−1}p^{−1} P(pf)⋯P(pf+p−1)`, `Q_C(f) = (−1)^{p−1}u^{−1}p^{−1} P(pf+r)⋯P(pf+r+p−1)`, **`K(f) = (−1)^{p−r} u^{−1} P(pf+r)⋯P(pf+p−1)`** (the last `p − r` floors of the `A`-window). `Q_A, Q_C ∈ p^{p−1}M_R`, `K ∈ p^{p−r}M_R ⊂ pM_R`: even. No coupling from a `C` slot to an `A` slot; `P''` is lower triangular in that slot order. — PROVED (pencil).
*Proof.* The relations of `A_j n ι_{s'}` and `C_j n ι_{s'}`, `j ≤ p−2`, have coefficient `1` on `A_{j+1} n ι_{s'}`, resp. `C_{j+1} n ι_{s'}` (exactly `2(p−1)` unit pivots per `n` and slot; this is the mission's `2p − 2`). Eliminating them: `a_j(n) = (−1)^j a_0(n) P(pf)⋯P(pf+j−1)`, `c_j(n) = (−1)^j c_0(n) P(pf+r)⋯P(pf+r+j−1)`. The relation of `A_{p−1} n` is `pu·a_0(Fn) + p·c_{p−r}(n) + a_{p−1}(n) P(pf+p−1) = 0` (from `F(A_{p−1}n) = pu A_0(Fn) + p C_{p−r} n`), i.e. `pu·[a_0(Fn) + a_0(n) Q_A(f) + c_0(n) K(f)] = 0`; the relation of `C_{p−1} n` is `pu·[c_0(Fn) + c_0(n) Q_C(f)] = 0`. ∎
**No non-unit pivot is ever needed:** every pivot eliminated by a move is exactly `1` (the bases of Definitions 1.1 and 1.3 make the string links equal to `1`), so the stop rule about non-unit pivots never triggers.

**Proposition 2.3 (the last level, on `Δ_A(d − 1)`, `1 ≤ d ≤ p−1`).** For `G` even of size `R` on `Δ_A(d−1)^{⊕R}` (floors `0, …, d−1`, `F e_s = (s+1) e_{s+1}`):
  `G ∼ I_{(d−1)R} ⊕ M`,  **`M = (−1)^{d−1}((d−1)!)^{−1} · P(0) P(1) ⋯ P(d−1)`** `∈ p^d M_R(A)`, lower triangular. — PROVED (pencil).
*Proof.* The pivots `s + 1 ≤ d − 1 ≤ p − 2` are units: `g_{s+1} = −g_s P(s)/(s+1)`, and the last relation is `g_{d−1}(e) P(d−1) = 0`. ∎ (For `p = 2`, `d = 1` and `M = P(0)`: DST never sees this level.)

**Theorem D_p.** Let `p` be an odd prime, `λ ≥ 0`, `e ≥ 1`, `i ≥ 0`, `λ + 1 = Σ_{t=0}^k d_t p^t` (`d_k ≥ 1`), `I = {t < k : d_t ≠ 0}`. Put `P_0(φ) := p^e(φ + i)` (`1 × 1`) and, for `t = 0, …, k−1`, `P_{t+1} := ` the twist (Prop. 2.1) of `P_t` if `d_t = 0`, the split with `r = d_t` (Prop. 2.2) if `d_t ≠ 0`. Let **`M_p(λ, i, e) := P_k(0) P_k(1) ⋯ P_k(d_k − 1)`**, a lower triangular matrix of size `2^{|I|}` with entries in `p^{d_k}ℤ_p`. Then
  **`Y_p(λ, i, e) ≅ ⊕_{h=1}^{k−1} (ℤ/p^h)^{(p−1) d_k p^{k−h−1} 2^{|I|}} ⊕ (ℤ/p^k)^{(d_k−1) 2^{|I|}} ⊕ coker(p^k M_p(λ, i, e))`,**
where `coker(p^k M)` has the Smith exponents of `M` raised by `k` (an exponent `∞`, i.e. a zero of the Smith form, gives `ℤ_p`). This is MISSION 3.4 exactly. — PROVED (pencil), from Theorem 1.6, Props 2.1–2.3.
*Proof.* By Theorem 1.6, `Y_p(λ, i, e) = coker σ` with `σ = F + p^e(D+i)` on `L(λ)`, an even system of size 1, and the floors of `L(λ)` are those of the moves (Defs 1.1, 1.3: `L(λ)` has top weight `λ`, `A_j n` on floor `pf + j`, etc.). Apply the move of digit `t` for `t = 0, 1, …, k−1`: the lattice before move `t` is `L(λ_t)` with `λ_t + 1 = Σ_{t' ≥ t} d_{t'} p^{t'−t}`, of rank `d_k p^{k−t} 2^{|I ∩ [t,k)|}`, carrying `R_t = 2^{|I ∩ [0,t)|}` slots; the move eliminates `(p−1)·R_t·(1 + [d_t ≠ 0])·rank L(λ_{t+1}) = (p−1) d_k p^{k−t−1} 2^{|I|}` unit pivots and multiplies the rest by `p`. After `k` moves the system lives on `L(λ_k) = Δ_A(d_k − 1)` with `2^{|I|}` slots and Proposition 2.3 applies. So `σ ∼ I_{n_0} ⊕ p(I_{n_1} ⊕ p(⋯ ⊕ p(I_{(d_k−1)2^{|I|}} ⊕ M)⋯))` with `n_t = (p−1)d_k p^{k−t−1}2^{|I|}`; the factor `(−1)^{d_k−1}/(d_k−1)!` is a unit. ∎
The slots are the dancers `D ⊆ I` (a split at digit `t` sends a slot to `(·, A)` (`t ∉ D`) and `(·, C)` (`t ∈ D`)).

**Gate B.** Engines `work/gateB.py` (`moves` = the right side of Theorem D_p from the recursion; `direct` = a generic sparse p-adic Smith form, modulo `p^{900}`, of `F + p^e(D+i)` on the lattice `L(λ)` of PASO 1, choosing pivots by least valuation and Markowitz cost, which uses nothing of the moves).
- `work/gateB_test.log`: `p = 3`, `λ ≤ 11` (proved range), `e ∈ {1,2}`, `i ≤ 3`: 96 cells, 0 differences.
- `work/gateB_run3.log`: `p = 3`, every `λ ≤ 80` (dim up to 432), `e ∈ {1,2}`, `i ∈ {0,1,2,3}`: **648 cells, moves = direct in all 648**; sealed cells: **552 hits, 0 misses**.
- `work/gateB_run5.log`: `p = 5`, every `λ ≤ 150` (dim up to 500), same `e, i`: **1208 cells, moves = direct in all 1208**; sealed cells: **968 hits, 0 misses**.
- MEASURED (1856 cells, controls fire). Peak memory 12.6 MB; 23 s and 77 s.
- Controls (in the same runs): `nolast` (moves with the leading-digit level omitted: `M = P_k(0)` and no `(ℤ/p^k)^{(d_k−1)2^{|I|}}`) differs from the direct Smith form in 318 of 648 (`p = 3`) and 738 of 1208 (`p = 5`) cells (the control changes nothing when `d_k = 1`; there are 320 and 744 cells with `d_k ≥ 2`, so it agrees on 2 and 6 of those — I believe these are `λ ≤ p−2`, `i = 0`, where both sides are `ℤ_p`, but I did not list them); `p2` (twist and split payments divided by `p²` instead of `p`) differs in 614 of 648 and 1150 of 1208. Controls fire.
- Sealed predictions: `work/SEALED_1.txt` (md5 `0a9c3442e54c54c8cc880d9b2bc070b0`, written Tue Oct 13 20:08:00 CEST 2026), 1520 cells outside the proved range, **1520 hits, 0 misses**; 1513 of them blind (see the note in the file and «Errors of my own»).
- No counterexample to the small part of 3.4 was found; the stop rule of MISSION §6 (second item) did not trigger.

## PASO 3 — Conjecture I
PASO 3 — ESTADO: CERRADO — Tue Oct 13 20:12:11 CEST 2026

**Theorem I (Conjecture I of v3 §8, every prime).** Let `p` be a prime, `λ ≥ 0`, `i ≥ 0`, `e ≥ 1`, `λ + 1 = Σ_{t=0}^k d_t p^t` with `d_k ≥ 1`, `I = I(λ) = {t < k : d_t ≠ 0}`. Then
(i) exactly `2^{|I|}` of the cyclic summands of `Y_p(λ, i, e)` have order larger than `p^k` (a free summand counted as one of them);
(ii) the other cyclic summands have order at most `p^k`, and together they form the group
  `S_p(λ) = ⊕_{h=1}^{k−1} (ℤ/p^h)^{(p−1) d_k p^{k−h−1} 2^{|I|}} ⊕ (ℤ/p^k)^{(d_k − 1) 2^{|I|}}`,
which depends only on `p` and the base-`p` digits of `λ + 1`, not on `i` or `e`.
Hypotheses used: `e ≥ 1` (the initial payment system `p^e(φ + i)` is even; for `p ∤ q` the statement is not claimed), and for odd `p` Theorem 1.6 (which cites Donkin's tensor product theorem and the tilting decomposition over `𝔽_p`, [Don93], [Jan03]); for `p = 2`, DST v10 Theorem D (stated and proved there for every `α ≥ 1`). — PROVED (pencil), given those.
*Proof.* Odd `p`: by Theorem D_p, `Y_p(λ, i, e) ≅ S_p(λ) ⊕ coker(p^k M)` with `M = M_p(λ, i, e)` of size `2^{|I|}` and all entries in `pℤ_p` (Theorem D_p: in `p^{d_k}ℤ_p`). The first determinantal divisor of `M` is then divisible by `p`, so every Smith exponent of `M` is `≥ 1` or `∞`: `coker(p^k M)` is the sum of exactly `2^{|I|}` cyclic `ℤ_p`-modules, each `ℤ_p` or of order `≥ p^{k+1}`. Every summand of `S_p(λ)` has order `≤ p^k`. By the uniqueness of the elementary divisors of a finitely generated `ℤ_p`-module, the cyclic summands of `Y_p(λ, i, e)` of order `> p^k` are exactly the `2^{|I|}` of `coker(p^k M)`, and the others form `S_p(λ)`. `p = 2`: DST Theorem D gives `X^{(α)}(λ, i) = Y_2(λ, i, α) ≅ ⊕_{a=1}^{k−1}(ℤ/2^a)^{2^{|I|+k−1−a}} ⊕ coker(2^k M)` with `M` the final matrix of an even payment system (DST Prop. 4.3), entries in `2ℤ_2`, of size `2^{|I|}`; the same argument applies, and `S_2(λ)` is the displayed formula with `p = 2`, `d_k = 1`. ∎

**Consistency.** The number of cyclic summands is `d_k 2^{|I|}(p^{k−1} − 1) + (d_k − 1)2^{|I|} + 2^{|I|} = d_k p^{k−1} 2^{|I|} = dim T(λ)/p` for `k ≥ 1`, which is the count of Jordan blocks of `f` on `T(λ)` stated in v3 §8 (projectivity over the first Frobenius kernel). PROVED (pencil; arithmetic).

**Consequence for the Hamming graph.** With v3 §8 (`ℤ_p^{[c=0]} ⊕ Syl_p X_q(m, c) ≅ ⊕_λ Y_p(λ, c + (m−λ)/2, v_p(q))^{n_λ(m)}`) and Theorem A of v3, `Syl_p K(H(d, q))` is, for every prime `p | q` and every `d`, a sum of copies of the groups `S_p(λ)` (explicit) and of the `2^{|I(λ)|}`-generated groups `coker(p^k M_p(λ, i, v_p(q)))` (explicit matrices, Theorem D_p). Their exact orders need the Smith form of `M_p` (PASO 4).

**Measured support.** All 1856 cells of Gate B and the 1470 cells of Gate A satisfy (i)–(ii) (they satisfy the stronger Theorem D_p). The auditor's gates (PASO 0) checked the same small part on 6900 + 192 cells.

## PASO 4 — the exact formula
PASO 4 — ESTADO: CERRADO — Tue Oct 13 20:56:33 CEST 2026 (started Tue Oct 13 20:13 CEST 2026). (a), (b), (c) closed; the floor of (b) is an adaptation of DST §7, written as a list of changes and checked step by step numerically; it has not been read cold by anyone.

Engine estimates (written before running):
- Sealed: `work/SEALED_2.txt`, written Tue Oct 13 (time in its first line), md5 `2f931de9eb3933c51a4ff3efb03274ab`, 10710 blind cells (the fit rule = Conjecture TOTAL_p).
- E4.4 `work/paso4.py check2 P` (Theorem D_p moves, i.e. the exact Smith form of M_p, against SEALED_2; precision cap = 2e(lam+1)+200), one run per p: < 300 MB, < 550 s each (p=3 heaviest: |I| up to 5).
- E4.4b the p=3 run of E4.4 was killed by the watchdog at 601 s (`work/check2_p3.log`, VIGIA-MATADO-TIEMPO, 0 misses printed up to then — not a result); re-run split as `check2 3 LO HI` over lam in [81,200], [201,280], [281,340], [341,400], each < 550 s.
- E4.6 `work/theoremF_p.py` (numerical check of every step of the odd-p Theorem F: Lemma 7.7_p, the potential V and (E),(M),(G),(Cut),(Λ_p), integrality of the real fit; all houses for p=3 k<=4, p=5 k<=3, sampled for p=7 k<=3; e in {1,2}): < 200 MB, < 550 s.
- E4.7 `work/paso4_final.py` (closed formula only: vs Theorem G block_cf for p in {3,5,7,11}, lam <= p^2+p-1, e<=3, i<=4; at p=2 vs DST's closed rule dst_alpha.X_alpha, lam<=200, alpha<=4, i<=6; the assembled Syl_3 K(H(d,3)) vs the table of v3 §10 for d=5..11; Theorem B for p>d): < 200 MB, < 300 s.
- E4.5 `work/paso4.py direct2` (independent direct sparse Smith on L(lambda) for the SEALED_2 cells with dim <= 1300, p=3,5): < 500 MB, < 550 s (split if killed).
- E4.3 `work/paso4.py seal2` (fit-rule predictions only, no Smith form of any new cell; ~9600 cells): < 100 MB, < 120 s.
- E4.2 `work/paso4.py fit` (post-hoc test of the clock + antitonic-fit rule for the Smith form of M_p on the 1856 cells already computed in Gate B, and on the proved range of p=7): < 200 MB, < 300 s.
- E4.1 `work/paso4.py windows` (closed form of M_p (windows x coefficient polynomial) vs the recursion of the moves, entry by entry, p in {3,5,7}, lambda <= 400, e in {1,2}, i <= 3; valuations of the coefficients): < 200 MB, < 300 s.


Progress note (Tue Oct 13 20:52 CEST 2026), PASO 4:
- `work/paso4_windows.log`: (a) the windows theorem (closed form of M_p = windows of consecutive payments x coefficients of q_k^{d_k}, q_0 = 1, q_{t+1} = q_t^p − [t∈I] y_t q_t^{p−d_t}) equals the recursion of the moves entry by entry in 2304 cells (p=3 lam<=80, p=5 lam<=150, p=7 lam<=55; e in {1,2}; i<=3): 0 failures; the deficit law v_p([q_k^{d_k}]_Δ) = k − |Δ| − min Δ holds in all 288 families; the cost form v_p(M_ab) = eK + κ_p(m,K) + R_m(a) − R_{m+K}(b) + γ(a∖b) holds for all 11136 entries (i>=1). MEASURED.
- `work/paso4_fit.log`: post-hoc (cells already known from Gate B): the fit rule (DST's clocks with base-p carries and K = d_k p^k, then the integer antitonic fit) equals Theorem D_p in all 2304 cells (|I| <= 3). MEASURED, not blind.
- `work/SEALED_2.txt` (md5 2f931de9eb3933c51a4ff3efb03274ab, written Tue Oct 13 20:17:05 CEST 2026): 10710 blind cells; checked against Theorem D_p (exact Smith form of M_p): p=13 404/404, p=11 1176/1176, p=7 3270/3270, p=5 3300/3300, p=3 2560/2560 (four runs; the first unsplit p=3 run was killed by the watchdog at 601 s and is in work/_old/, not counted). **10710 hits, 0 misses.**

### PASO 4 — results (Tue 13 Oct 2026, 20:55 CEST)

Notation (odd `p`). `λ + 1 = Σ_{t=0}^k d_t p^t`, `d_k ≥ 1`, `I = {t < k : d_t ≠ 0}`, **`K := d_k p^k`**; for `t ∈ I`, `next(t) := min{u ∈ I ∪ {k} : u > t}`, `h_t := next(t) − t`. Dancers `D ⊆ I`, **`o_D := Σ_{t∈D} d_t p^t`**; the o-order (increasing `o_D`) is the order of the masks, and `D ↦ I ∖ D` reverses it (`o_{I∖D} = o_I − o_D`). `κ_p(a, b)` := the number of carries of `a + b` in base `p` `= v_p C(a+b, a)` (Kummer). Gold `γ(Δ) := Σ_{u ∈ I∖Δ, u > min Δ} h_u` (`γ(∅) = 0`). Rulers `R_μ(E) := Σ_{t∈E}(h_t − e d_t p^t) − κ_p(μ, o_E)` and `R^♯(E) := Σ_{t∈E}(h_t − e d_t p^t) − (k − min E)` (`R^♯(∅) = 0`). Clocks: for `i ≥ 1`, `m := i − 1`, `x_D := R_m(D) − R_{m+K}(I ∖ D)`; for `i = 0`, `x^♯_D := R^♯(D) − R^♯(I ∖ D)` (`D ≠ ∅`). `ŷ`, `ŷ^♯` := their integer antitonic fits in o-order (pool-adjacent-violators, DST §1.2, §7.1). For `p = 2` (`d_t = 1`, `K = 2^k`) all of this is literally DST's notation with `α = e`.

**(a1) Theorem 4.1 (windows, odd p).** After `h` moves the slots are the `D ⊆ I ∩ [0,h)` and
  `P_h(f)_{DD'} = c^{(h)}_{D∖D'} · ∏_{d ∈ W} π_0(d)`, `W = [p^h f + o_D, p^h f + o_{D'} + p^h − 1]`, `π_0(d) = p^e(i + d)` (`D' ⊆ D`; `0` otherwise),
where `c^{(h)} ∈ ℚ[x_t : t ∈ I]/(x_t²)` has `c^{(0)} = 1`, **`c^{(h+1)} = a·(c^{(h)})^p + [h ∈ I]·b_h x_h (c^{(h)})^{p−d_h}`**, `a = (−1)^{p−1}/(up)`, `b_h = (−1)^{p−d_h}/u`. Consequently
  **`M_p(λ,i,e)_{DD'} = ((−1)^{d_k−1}/(d_k−1)!) · [(c^{(k)})^{d_k}]_{D∖D'} · ∏_{d=o_D}^{o_{D'}+K−1} p^e(i+d)`** (window of `K − o(D∖D')` floors),
and, with `c^{(h)} = a^{(p^h−1)/(p−1)} q_h(y)`, `y_t = −b_t(−p)^{1+d_t(p^t−1)/(p−1)} x_t` (`u = −1`), the coefficient polynomial is
  **`q_0 = 1`, `q_{t+1} = q_t^p − [t ∈ I]·y_t·q_t^{p−d_t}`** in `ℤ[y_t : t ∈ I]/(y_t²)`
(the odd-p analogue of DST's `q_{t+1} = q_t² − [t∈I] y_t q_t`; as predicted in MISSION 4(a): `q_t^p`, and one term per digit `r' = d_t`). — PROVED (pencil); MEASURED: equals the recursion of the moves entry by entry in 2304 cells (`work/paso4_windows.log`).
*Proof.* As DST Theorem 4.4. In Props 2.1/2.2 every entry of a product `P_h(φ_1)⋯P_h(φ_s)` over consecutive floors is a sum over chains `D = T_0 ⊇ T_1 ⊇ ⋯ ⊇ T_s = D'`; the windows of consecutive factors are adjacent (the window of `P_h(pf+j)_{T_jT_{j+1}}` ends at `p^{h+1}f + p^h j + o_{T_{j+1}} + p^h − 1`, the next starts at `p^{h+1}f + p^h(j+1) + o_{T_{j+1}}`), so every chain gives the same monomial in `π_0` and the coefficients add up to `[(c^{(h)})^s]_{D∖D'}` (`x_t² = 0` makes the parts disjoint). Twist: `s = p` from `pf`; split: `Q_A` (`s = p` from `pf`), `Q_C` (`s = p` from `pf + r`, slots `D ∪ {h}`, `o_{D∪{h}} = o_D + d_h p^h`), `K` (`s = p − r` from `pf + r`, the pair `(D ∪ {h}, D')`: coefficient of `x_h x^{D∖D'}`); last level `s = d_k` from floor `0`. The normalization is a substitution: `(p^{h+1}−1)/(p−1) = 1 + p(p^h−1)/(p−1)` and `a^{−1−d_h(p^h−1)/(p−1)} = (−p)^{1+d_h(p^h−1)/(p−1)}`. ∎

**(a2) Lemma 4.2 (deficit law, odd p).** `[q_k^{d_k}]_∅ = 1` and, for `∅ ≠ Δ ⊆ I`, **`v_p([q_k^{d_k}]_Δ) = k − |Δ| − min Δ = δ(Δ)`** — the same law as DST Lemma 4.5, independent of the digits. — PROVED (pencil); MEASURED in 288 families.
*Proof.* Induction on `|Δ|` and `t`: for `t > max Δ`, `v_p([q_t]_Δ) = t − |Δ| − min Δ`. With `m = max Δ`, `[q_{m+1}]_Δ = −[q_m^{p−d_m}]_{Δ∖{m}}`; for a power `N` of `q` and `Γ ≠ ∅`, `[q^N]_Γ = Σ_{set partitions of Γ into j ≤ N blocks} N(N−1)⋯(N−j+1) ∏_B [q]_B`. For `N = p − d_m ∈ [1, p−1]` the single-block term has the unit factor `N`; for `N = p` (every later move, twist or split: the extra `y_t`-term of a split does not touch `y^Δ`) every falling factorial `(p)_j`, `1 ≤ j ≤ p`, has `v_p = 1`. In both cases a partition into `j ≥ 2` blocks has valuation `≥` the single-block one plus `(j−1)(t − max Δ) > 0`, by induction (one block contains `min Δ`, the others have `min B ≤ m`). So the valuation is `m − (|Δ| − 1) − min Δ` at `t = m+1` and grows by exactly 1 per move; the final power `d_k` (a unit) is as `N = p − d_m`. ∎

**(a3) Proposition 4.3 (cost form, odd p).** For `b ⊆ a`: if `i ≥ 1`, **`v_p(M_{ab}) = eK + κ_p(m, K) + R_m(a) − R_{m+K}(b) + γ(a ∖ b)`**; if `i = 0`, the row `∅` is zero and, for `a ≠ ∅`, `v_p(M_{ab}) = eK + R^♯(a) − R^♯(b) + γ(a ∖ b)`. All entries `b ⊆ a` (`a ≠ ∅` when `i = 0`) are non-zero. — PROVED (pencil); MEASURED on 11136 entries.
*Proof.* From (a1), (a2): `v_p(M_{ab}) = −d_k(p^k−1)/(p−1) + Σ_{t∈Δ}(1 + d_t(p^t−1)/(p−1)) + δ(Δ) + e(K − o(Δ)) + Σ_{d=o_a}^{o_b+K−1} v_p(i+d)`, `Δ = a ∖ b`. Legendre `v_p(n!) = (n − s_p(n))/(p−1)` gives the last sum as `[(K − o(Δ)) − s_p(m + K + o_b) + s_p(m + o_a)]/(p−1)`; with `s_p(x + o_E) = s_p(x) + Σ_{t∈E}d_t − (p−1)κ_p(x, o_E)`, `s_p(K) = d_k`, `|Δ| + δ(Δ) = Σ_{t∈a}h_t − Σ_{t∈b}h_t + γ(Δ)` (DST Lemma 5.1, which only uses `I`), everything collapses to the stated form. For `i = 0`: `Σ_{d=x}^{y−1}v_p(d) = [(y−x) − s_p(y−1) + s_p(x−1)]/(p−1)` (`x ≥ 1`), `s_p(o_a − 1) = Σ_{t∈a}d_t − 1 + (p−1)min a`, `κ_p(K−1, o_E) = k − min E`. ∎

**(b) Theorem 4.4 (the Smith form of `M_p`).** For `i ≥ 1` the Smith exponents of `M_p(λ, i, e)` are `eK + κ_p(i−1, K) + ŷ_D` (`D ⊆ I`); for `i = 0` they are `∞` (once) and `eK + ŷ^♯_D` (`D ≠ ∅`). The real antitonic fits are integral. — PROVED (pencil, by adaptation of DST §6–§7: the statements that change are written below with their proofs, the others are used verbatim and cited by number); MEASURED: 10710 sealed blind cells, 0 misses; all 56246 houses of `work/theoremF_p.log`.
*Proof.* **Ceiling (DST §6).** Lemma 6.1 (tropical bound), Theorem 6.2 (Theorem O: the unique golden matching — a statement about `I` and `γ` only), Corollary 6.3 (natural minor: needs the cost form (a3), the non-vanishing of the entries in the support, and `F_r = {I∖D : D ∈ L_r}`), Lemma 6.4 (convexity) and Theorem 6.5 hold verbatim. **Floor (DST §7).** Lemmas 7.1–7.3 (fits, cuts, antisymmetric gluing) and Theorem 7.4 (Theorem U) are statements about sequences, verbatim. *Houses:* `H = (I, k, ℓ, e, (d_t))`, `0 ≤ ℓ < p^k`, `R_H(E) = Σ_{t∈E}(h_t − e d_t p^t) − κ_p(ℓ, o_E)`, **`J_H(E) = [ℓ + o_E ≥ p^k]`** (an up-set), `x_H`, `ĉ_H` as in DST. *Lemma 7.5_p:* with `ℓ = m mod p^k` and `r_k(μ)` := the number of consecutive digits `p−1` of `μ` from digit `k` on, `R_m = R_H − r_k(m)J_H`, `R_{m+K} = R_H − r_k(m+K)J_H` (the carry out of digit `k−1` runs through those digits; `m + K` has the same low part). *Lemma 7.6_p (gates, base p):* in the window `W_t = [t, next(t))` the addend has the single digit `d·d_t` (`d = [t∈E]`) at `t`; put `θ_t := p − ℓ_t ∈ [1, p]`, `κ_t := 1 + min(r_{t+1}(ℓ), h_t − 1)`, `sat_t := [κ_t = h_t]`. The window makes `κ_t` carries iff `d·d_t + c_t ≥ θ_t`, i.e. it has one of **four types**: **OR** (`θ_t = 1`: iff `d ∨ c_t`), **DIG** (`2 ≤ θ_t ≤ d_t`: iff `d`), **AND** (`θ_t = d_t + 1`: iff `d ∧ c_t`), **NEV** (`θ_t ≥ d_t + 2`: never); a carry leaves iff it carries and is saturated. (For `p = 2` only OR = DST's `T = 1` and AND = DST's `T = 0` exist.) *Lemma 7.7_p (top digit `c = max I`, `H' = (I∖{c}, c, ℓ mod p^c, e)`, `h = k − c`):*
  `R_H(D_0) = R_{H'}(D_0) − [OR] κ J'(D_0)`,  `R_H(D_0 ∪ {c}) = τ + R_{H'}(D_0) − [AND] κ J'(D_0)`,  **`τ := h − e d_c p^c − [OR ∨ DIG] κ`**,
  `J_H(D_0) = [OR]·sat·J'(D_0)`,  `J_H(D_0 ∪ {c}) = sat·([OR ∨ DIG] + [AND]·J'(D_0))`,
and the shift of the first half is `d_1(D_0) = −τ − [OR]κJ'(D_0) + [AND]κJ'(I'∖D_0)` (integer, non-increasing, changing only at the boundary of `J'` or its mirror; constant for DIG and NEV). *Theorem F_p (= DST Theorem 7.8 with (Λ) replaced by* **`(Λ_p) |ŷ_H| ≤ e·o_I`***):* DST's induction, steps 1–8, with these changes: step 2 uses `d_1 ≤ e d_c p^c − h + κ ≤ e d_c p^c` and `o_{I'} + d_c p^c = o_I`; in steps 3(a), 3(b) and 5 the quantity `α2^c − α(2^c − 1) = α` becomes `e(d_c p^c − o_{I'}) ≥ e` (as `o_{I'} ≤ p^c − 1`), and `h − α` becomes `h − e`; in 3(c), `X_2(b') = ŷ'(b') − e d_c p^c ≤ −e`; **the two new types fall into DST's existing cases**: DIG with `sat = 1` has `J_H = (0, 1)` and `d_1 ≡ e d_c p^c`, which is case 3(b) (the argument there never used `J' ≡ 0` beyond `d_1 = α2^c` on the first half), and DIG with `sat = 0`, and NEV, have `J_H ≡ 0`, case 3(d); steps 4 (inherited potential `v'(D_0) = V'(D_0) − [OR]κJ'(D_0)`, `v'(D_0∪{c}) = τ + V'(D_0) − [AND]κJ'(D_0)`), 6, 7, 8 are verbatim with `α → e`. *Lemma 7.9_p* (integrality of the real fits) and *Theorem 7.10_p* follow verbatim (penalty cells `Cell(H; r_k(m), r_k(m+K))`; for `i = 0` the house `ℓ = p^k − 1`, all windows of type OR, `J = [D ≠ ∅]`, `x^♯ = x_{H^♯}`). Every claim of this paragraph — Lemma 7.7_p, the gluing `ŷ_H = [max(X_1,0), min(X_2,0)]`, `(Λ_p)`, the strict (Cut), the potential `V` with (E), (M), (G), the non-empty interval for `c_F` in step 7, `F_1` a final segment, and integrality — was checked numerically in **56246 houses** (`p = 3`, all houses with `k ≤ 4`; `p = 5`, all with `k ≤ 3`; `p = 7`, sampled, `k ≤ 3`; `e ∈ {1,2}`; all four types occur, about 30000 times each): **0 failures** (`work/theoremF_p.log`). ∎

**(c) The exact formula (Theorem TOTAL).** For every odd prime `p`, `λ ≥ 0`, `e ≥ 1`, `i ≥ 0`:
  **`Y_p(λ, i, e) ≅ S_p(λ) ⊕ ⊕_{D ⊆ I} ℤ/p^{k + eK + κ_p(i−1, K) + ŷ_D}`** (`i ≥ 1`),  **`Y_p(λ, 0, e) ≅ S_p(λ) ⊕ ℤ_p ⊕ ⊕_{∅ ≠ D ⊆ I} ℤ/p^{k + eK + ŷ^♯_D}`**,
with `S_p(λ) = ⊕_{h=1}^{k−1}(ℤ/p^h)^{(p−1)d_k p^{k−h−1}2^{|I|}} ⊕ (ℤ/p^k)^{(d_k−1)2^{|I|}}` (Theorem I). For `p = 2` the same formula is the Dancing Sand Theorem (DST Theorem D + Theorem 7.10, for every `α = e`). Hence, for **every prime `p`, every `q` with `p | q`, `e = v_p(q)`, and every `d`**:
  **`ℤ_p ⊕ Syl_p K(H(d, q)) ≅ ⊕_{j=0}^{d} ⊕_{λ ≡ d−j (2)} Y_p(λ, j + (d−j−λ)/2, e)^{C(d,j)(q−2)^j · n_λ(d−j)}`,**
where `n_λ(m)` is the multiplicity of `T(λ)` in `V^{⊗m}`, obtained by peeling the characters `ch T(λ) = ∏_{t<k} χ_{p−1}(z^{p^t})·(z^{d_t p^t} + z^{−d_t p^t})^{[d_t ≠ 0]} · χ_{d_k−1}(z^{p^k})` off `(z + z^{−1})^m` from the top. (Theorem A of v3 = [JNR03, Thm 13]; Theorem 1.6(iii); Lemma 2 of v3.) — PROVED (pencil), given Theorem 1.6 (which cites Donkin) and Theorem 4.4 (adaptation of DST §6–§7); MEASURED as below.
Checks (`work/paso4_final.log`, `work/paso4_fit.log`, `work/check2_*.log`):
- against **Theorem G** (`block_cf`), `p ∈ {3,5,7,11}`, every `λ ≤ p²+p−1`, `e ≤ 3`, `i ≤ 4`: 3450 cells, 0 failures;
- at `p = 2` against **DST**'s closed rule (`material/engines/dst_alpha.py`), `λ ≤ 200`, `α ≤ 4`, `i ≤ 6`: 5628 cells, 0 failures (the odd-p formula contains DST);
- the **eight cells of MISSION §2.4** (`λ = 12`, `p = 3`, `q ∈ {3, 6}`, `c ≤ 3`): reproduced (they are among the 2304 post-hoc cells; for `q = 6` the block only depends on `e = 1`);
- the assembled **`Syl_3 K(H(d,3))`, `d = 5, …, 11`**, against the table of v3 §10 (computed there from Laplacians and pieces): 7 rows, 0 differences; against **Theorem B** (`p > d`): 128 groups, 0 differences;
- **sealed: `work/SEALED_2.txt`, 10710 blind cells, 10710 hits, 0 misses** (against the exact Smith form of `M_p` given by Theorem D_p; Theorem D_p itself was checked against the direct Smith form of the lattice in Gate B);
- for illustration (a consequence, not a new direct computation): `Syl_3 K(H(12,3)) = {1: 36952, 2: 10078, 3: 10319, 4: 14727, 5: 51128, 6: 13871, 7: 12101, 8: 24210, 9: 2619, 10: 1267, 11: 1843, 12: 67, 13: 12}` (exponent: count), the first row beyond v3's table; the only block outside Theorem G in it is `λ = 12`, the auditor's measured cell.

## Table of claims (statement · grade · where proved or which log)
| # | statement | grade | where |
|---|---|---|---|
| 1 | Lemma 1.0: an `F,H`-equivariant map between finite-dim `sl_2`-modules commutes with `E`; a graded `F`-isomorphism of lattices is a `Dist`-isomorphism | PROVED (pencil) | PASO 1 |
| 2 | `Φ_p(N)` (Def. 1.1) is a lattice; exact functor; `Φ_p(N)⊗𝔽_p ≅ St⊗N̄^{[1]}`; `Φ_p(Δ(μ)) ≅ Δ(pμ+p−1)`, `Φ_p(∇(μ)) ≅ ∇(pμ+p−1)` | PROVED (pencil); MEASURED (Gate A) | Prop. 1.2; `work/gateA_struct*.log` |
| 3 | `Ψ_r(N)` (Def. 1.3, explicit `E, F, H`) is a lattice for every lattice `N`, via the saturated embedding `ι: Ψ_r(N) ↪ V⊗Ψ_{r−1}(N)`; exact functor; `Ψ_r(N)⊗𝔽_p ≅ T(p−1+r)⊗N̄^{[1]}`; `Ψ_r(Δ(μ))` has a Δ-filtration `Δ(pμ+p−1+r)`, `Δ(pμ+p−1−r)` | PROVED (pencil); MEASURED (Gate A) | Prop. 1.4; `work/sanity_oddlat.log`, `work/gateA_*.log` |
| 4 | ∇-filtration of `Ψ_r(∇(μ))` | **not proved** (not needed) | PASO 1, Remark |
| 5 | `ℤ_p`-versions of DST Lemma 3.2, Lemma 3.3, Cor. 3.4 (+ one-sided Lift′); DST never uses `p = 2` there | PROVED (pencil) | Lemma 1.5 |
| 6 | Theorem 1.6: the dance lattice `L(λ)` (one move per base-`p` digit, ending on `Δ(d_k−1)`) has rank `d_k p^k 2^{|I|}`, a Δ-filtration with `2^{|I|}` factors, `L(λ)⊗𝔽_p ≅ T(λ)`, and `V^{⊗m}⊗ℤ_p ≅ ⊕ L(λ)^{n_λ(m)}`; so `L(λ) ≅ T_{ℤ_p}(λ)` | PROVED (pencil), citing Donkin's tensor product theorem and the tilting decomposition [Don93, Jan03] | PASO 1 |
| 7 | Gate A: sl_2 relations, character, integrality of all `f^{(r)}, e^{(r)}` on 569 lattices (`p = 3,5,7`, dim ≤ 600); `Y_p` on `L(λ)` = Theorem G in 1470 cells; = table §2.4 in 4 cells | MEASURED (2043 checks, controls fire) | `work/gateA_*.log` |
| 8 | Twist move (Prop. 2.1), split move (Prop. 2.2), last level (Prop. 2.3); every eliminated pivot is exactly `1` (or a unit `s+1 < p` at the last level) | PROVED (pencil) | PASO 2 |
| 9 | **Theorem D_p** (MISSION 3.4) for every odd `p`, every `λ, i`, `e ≥ 1`, with `M_p` the product of the payment matrices of the last level | PROVED (pencil); MEASURED (1856 cells vs direct Smith, 1520 sealed, 0 misses) | PASO 2; `work/gateB_run3.log`, `work/gateB_run5.log` |
| 10 | **Theorem I = Conjecture I of v3 §8, for every prime** | PROVED (pencil) from #9 (odd `p`) and DST Theorem D (`p = 2`) | PASO 3 |
| 11 | Number of cyclic summands `= dim T(λ)/p` (`k ≥ 1`) | PROVED (pencil) | PASO 3 |
| 12 | Theorem 4.1 (windows) and the coefficient recursion `q_{t+1} = q_t^p − [t∈I] y_t q_t^{p−d_t}` | PROVED (pencil); MEASURED (2304 cells) | PASO 4(a1); `work/paso4_windows.log` |
| 13 | Lemma 4.2 (deficit law `v_p = k − |Δ| − min Δ`, same as DST) | PROVED (pencil); MEASURED (288 families) | PASO 4(a2) |
| 14 | Proposition 4.3 (cost form with base-`p` carries, `K = d_k p^k`; and `i = 0`) | PROVED (pencil); MEASURED (11136 entries) | PASO 4(a3) |
| 15 | Lemmas 7.5_p, 7.6_p (four window types OR/DIG/AND/NEV), 7.7_p; Theorem F_p with `(Λ_p) |ŷ_H| ≤ e·o_I` | PROVED (pencil, adaptation of DST §7, changes written out); MEASURED (56246 houses, every step) | PASO 4(b); `work/theoremF_p.log` |
| 16 | Theorem 4.4: Smith exponents of `M_p` = `eK + κ_p(i−1,K) + ŷ_D` (`i ≥ 1`), `∞` and `eK + ŷ^♯_D` (`i = 0`) | PROVED (pencil, by #12–#15 and DST §6 verbatim); MEASURED (10710 sealed cells, 0 misses; 306 of them also by direct Smith on the lattice) | PASO 4(b); `work/check2_*.log`, `work/direct2.log` |
| 17 | **Theorem TOTAL**: `Y_p(λ,i,e)` in closed form for every prime; hence the whole `Syl_p K(H(d,q))` for every `d`, every `q`, every prime `p` | PROVED (pencil), with the provisos of #6 (cited facts) and #15 (adaptation, not read cold); MEASURED as in #16 and #18 | PASO 4(c) |
| 18 | The closed formula contains Theorem G (3450 cells), DST (`p = 2`, 5628 cells), reproduces v3 §10 (`Syl_3K(H(d,3))`, `d = 5..11`) and Theorem B (128 groups) | MEASURED | `work/paso4_final.log` |
| 19 | The explicit `E`-formulas for `Ψ_r` were read off a computation before being proved | (provenance) | `work/explore_E_5_2_2.log` |
| 20 | No published Smith form of `f + p^e(D+i)` on tilting modules for odd `p`, nor an integral odd-p Frobenius-twist functor, was found (one search) | search result, not a theorem | PASO 0 |

## Sealed predictions (file, md5, time, hit/miss)
| file | md5 | written (from `date`) | cells | hits | misses | blind |
|---|---|---|---|---|---|---|
| `work/SEALED_1.txt` (prediction = right side of Theorem D_p by the moves; checked against the direct p-adic Smith form on `L(λ)`) | `0a9c3442e54c54c8cc880d9b2bc070b0` | Tue Oct 13 20:08:00 CEST 2026 | 1520 (p=3: 552, p=5: 968) | **1520** | **0** | 1513 (not blind: p=3 λ=12 e=1 ×4 — the auditor's table; p=3 λ=12 e=2 i=1,2 — computed in `work/sanity_oddlat.log` before sealing; p=3 λ=79 e=1 i=1 — computed in the timing run of `work/gateB_test.log`) |
| `work/SEALED_2.txt` (prediction = Conjecture/Theorem TOTAL, the fit rule; checked against the exact Smith form of `M_p` (Theorem D_p), and a sample of 306 cells against the direct Smith form on `L(λ)`) | `2f931de9eb3933c51a4ff3efb03274ab` | Tue Oct 13 20:17:05 CEST 2026 | 10710 (p=3: 2560, p=5: 3300, p=7: 3270, p=11: 1176, p=13: 404) | **10710** (direct sample: 306/306) | **0** | 10710 |

Misses reported with the same prominence as hits: there are none. The post-hoc test of the fit rule (2304 cells already known, `work/paso4_fit.log`) is not a prediction and is not counted here.

## Controls (each gate's control, and that it fails)
| gate | control (must fail) | result | log |
|---|---|---|---|
| auditor's Theorem G gate (PASO 0) | drop the leading-digit term | 4560 of 6900 cells fail | `work/gateG.log` |
| auditor's simple-blocks gate (PASO 0) | drop `(ℤ/p^k)^{d−1}` | 128 of 192 fail | `work/gateS.log` |
| Gate A, comparison | outermost twist/split wrap without the `p` (`u·A_0(Fn)`) | 1065 of 1290 cells differ from Theorem G | `work/gateA_compare.log` |
| Gate A, comparison | split move without the coupling `p·C_{p−r}n` | 942 of 1290 differ (the rest have last digit 0, where the control lattice is the true one) | `work/gateA_compare.log` |
| Gate A, integrality | coupling `p²`, `p³` instead of `p`; twist without `p`; `E` recovered from `(F,H)` | 40 of 42 lattices not `Dist`-stable; the 2 survivors are the twist without `p` on `Δ(0)` (vacuous: `F_N = 0`) | `work/gateA_intcontrol.log` |
| Gate A, sl_2 | the uncoupled model (`ε = 0`) | has no `sl_2`-structure at all (18 of 18 models with ε = 0, p ∈ {3,5}, b ≤ 2; the 18 models with ε = 1 are integral) | `work/explore_psi.log` |
| Gate B | leading-digit level omitted | differs in 318 of 648 (p=3) and 738 of 1208 (p=5) cells; it changes nothing when `d_k = 1` | `work/gateB_run3.log`, `work/gateB_run5.log` |
| Gate B | twist/split payments divided by `p²` instead of `p` | differs in 614 of 648 and 1150 of 1208 | same |
| Theorem 4.4 | (the checks of `work/theoremF_p.py` are of claimed identities and inequalities; their failure counters are live — e.g. a wrong `τ` makes Lemma 7.7_p fail — but no separate deliberately-wrong run was made) | — | `work/theoremF_p.log` |

## Errors of my own, and what I did not do
Errors of my own (all found and handled during the work):
1. **Rule 6 broken twice (minor, disclosed in SEALED_1):** the exact values `Y_3(12, i, 2) = {1:8, 14:1, 16:1, 24:1, 26:1}` (`i = 1, 2`) were computed in `work/sanity_oddlat.py` before any sealed prediction (the auditor had only measured «eight `ℤ/3` and four of exponent `≥ 3`»); and the timing line of `work/gateB.py test` computed the cell `p = 3`, `λ = 79`, `e = 1`, `i = 1` before sealing. Both cells are marked «not blind» in `work/SEALED_1.txt`.
2. The first `check2 3` run (all of p=3 in one go) was killed by the watchdog at 601 s (`VIGIA-MATADO-TIEMPO`); it is not a result, it is kept in `work/_old/check2_p3_killed.log`, and p=3 was re-run in four ranges (the last one took 597 s).
3. A coding slip (the `seal` function defined after the main block of `work/gateB.py`) was found and fixed before the sealed file was produced.
4. `work/gateB.py` was edited after the Gate B runs (a `cap` parameter, default 900 = the value used in Gate B) and `work/paso4.py` after its first runs (new modes only); the functions used by the earlier logs were not changed. The md5 below are of the final versions.
5. In an intermediate draft I wrote that the `nolast` control fails «exactly» on the cells with `d_k ≥ 2`; it agrees on 2 (p=3) and 6 (p=5) of them, which I did not list (I believe they are `λ ≤ p − 2`, `i = 0`). Corrected in the text.

What I did not do:
- The ∇-filtration of `Ψ_r(∇_A(μ))` is not proved (claim #4); the lifting argument (Lift′) does not need it.
- I did not open [Don93] or [Jan03]: Donkin's tensor product theorem and the decomposition of tilting modules over `𝔽_p` are cited as standard (as v3 and MISSION do), not reproved.
- The floor of Theorem 4.4 (odd-p Theorem F) is written as a list of the changes to DST §7 (the four window types, the new constants `τ`, `(Λ_p)`, and which DST case each new type falls into), with the unchanged steps cited by number; it is not rewritten line by line, and nobody has read it cold. Every intermediate claim of it was checked numerically in 56246 houses.
- Lemma 7.5_p (penalties) was not machine-checked separately; it is a two-line carry argument and is covered end to end by the 10710 sealed cells.
- Independence: the only cells outside the proved range that do not go through my lattice `L(λ)` are the auditor's `λ = 12` cells (B_12); `B_13` exceeds the memory cap and was not attempted. All other checks beyond the proved range compare three computations on `L(λ)` (direct Smith form, moves, closed formula); the identification `L(λ) ≅ T_{ℤ_p}(λ)` is Theorem 1.6 and was also checked against Theorem G and the `λ = 12` table.
- `p = 2`: I did not re-prove DST; Theorem I and TOTAL at `p = 2` rest on DST v10 (Lean-checked there), and the odd-p closed formula specializes to DST's rule (5628 cells).
- Literature: one search (PASO 0); none in later steps.
- The «ultracode» workflow mode offered by the environment was not used: MISSION §0.1 forbids any delegation.

## Files (every script and log in work/, with md5)
All scripts and logs in `work/` (md5, final versions, `Tue Oct 13 21:00 CEST 2026`). Every log ends with `VIGIA-FIN-OK` except the killed one in `work/_old/`.
| md5 | file | what |
|---|---|---|
| `0a9c3442e54c54c8cc880d9b2bc070b0` | `work/SEALED_1.txt` | sealed predictions 1 (Theorem D_p, 1520 cells) |
| `2f931de9eb3933c51a4ff3efb03274ab` | `work/SEALED_2.txt` | sealed predictions 2 (closed formula, 10710 cells) |
| `60b10cb7bf523ac86bd5163f3c47b77c` | `work/_old/check2_p3_killed.log` | killed run (not a result) |
| `60a25d849a858a83edac27c9439af364` | `work/check2_p11.log` | SEALED_2 check p=11 |
| `d51837f407bacc22a51e4e6a73b306b4` | `work/check2_p13.log` | SEALED_2 check p=13 |
| `63d2d432a5281087cccba005f9b587c1` | `work/check2_p3a.log` | SEALED_2 check p=3, λ 81–200 |
| `e4436b934936c3698473d76390fc2ad3` | `work/check2_p3b.log` | SEALED_2 check p=3, λ 201–280 |
| `48043eb446d0e0d4daf82ea681925004` | `work/check2_p3c.log` | SEALED_2 check p=3, λ 281–340 |
| `0bdc90199d0ce23e0195e7a8dbe832d8` | `work/check2_p3d.log` | SEALED_2 check p=3, λ 341–400 |
| `d2b3555564c24dadfc03818a646a1fb5` | `work/check2_p5.log` | SEALED_2 check p=5 |
| `9cbce5469891301c8dd4486022645ad2` | `work/check2_p7.log` | SEALED_2 check p=7 |
| `09e0c555e1cdfc2fa9e3050cb692c19e` | `work/direct2.log` | direct Smith on L(λ) vs SEALED_2 sample (306 cells) |
| `11cdd18896162b147ad13865990ea8c2` | `work/explore_E.py` | prints E of the model (exploration) |
| `4769e169800ee1908eac0aae0e3886b0` | `work/explore_E_5_2_2.log` | E of Ψ_2(Δ(2)), p=5 |
| `39c9840d3ea65388cfc16c840e2962ab` | `work/explore_iota.py` | equivariant maps Model_r → V⊗Model_{r−1} (exploration) |
| `e99a575d5ccf949c5bf9e83dffa7e84e` | `work/explore_iota_5_2_3.log` | the 2-dim Hom space, p=5, r=2, b=3 (source of ι) |
| `be2901322f5aabedbc4dd2a2fdc60682` | `work/explore_psi.log` | ε=1 models integral, ε=0 no sl_2 |
| `1ed29569cbccd03b899b3a430265e7dc` | `work/explore_psi.py` | exploration: models, E from (F,H), integrality |
| `a9b4f5c634d0d15c94d756e55f39fb10` | `work/frontier_cell_3_0.log` | cell (q,c)=(3,0) of table 2.4 reproduced |
| `c6bf0db9a28489e7cccd9655078dd7e1` | `work/frontier_cell_3_0.py` | copy of frontier_p3_m12.py, cell (3,0) |
| `a846347bc89875c3b947f636555900ff` | `work/gateA.py` | Gate A |
| `2bbb09e9825a9981dd93e0c7ad885832` | `work/gateA_compare.log` | Gate A: vs Theorem G, table 2.4, controls |
| `97a28430a0f0f25f8e159a4517536a05` | `work/gateA_intcontrol.log` | integrality control log |
| `f18558e7833e25423009419a4bc83336` | `work/gateA_intcontrol.py` | Gate A integrality control |
| `2129ed9f35987eed7792757fc4a24b3a` | `work/gateA_struct3.log` | Gate A structure p=3 |
| `8f4cc00c4188f884a3d6d15d50c4ef89` | `work/gateA_struct5.log` | Gate A structure p=5 |
| `f61f391755c529fead7924de1c8a8b75` | `work/gateA_struct7.log` | Gate A structure p=7 |
| `60a11abb9708c7874f13be8a69255943` | `work/gateB.py` | Gate B: moves, direct sparse Smith, sealing |
| `f37b919c9c17f72aa8e770bdd37ff8d4` | `work/gateB_run3.log` | Gate B p=3 |
| `63ccbf22ab33efa768c614e56d94505c` | `work/gateB_run5.log` | Gate B p=5 |
| `0f6470e06d54bb1deb92298a4d0c1177` | `work/gateB_test.log` | Gate B test (proved range) + timing |
| `bc4d49552080205832655e55117404d5` | `work/gateG.log` | auditor gate Theorem G reproduced |
| `aef28aba7c1162c1296589f0db4598e6` | `work/gateS.log` | auditor gate simple blocks reproduced |
| `8da4b3afa088039874d7edf20caf70a9` | `work/oddlat.py` | the lattices Δ, Φ_p, Ψ_r, L(λ); checks; dense Smith |
| `432655f0e6c6f3da9fdd9623046fff21` | `work/paso4.py` | PASO 4: windows, deficit, cost form, fit rule, SEALED_2 checks |
| `49bff1edc0a53687179a1b55bb554f71` | `work/paso4_final.log` | closed formula vs Theorem G, DST, v3 §10, Theorem B |
| `17ad70595a5e34463c62462cb105d270` | `work/paso4_final.py` | PASO 4(c) checks |
| `b2cedaadc814908ae79a1c37969b9cbb` | `work/paso4_fit.log` | post-hoc fit rule test (2304 cells) |
| `e7e3f2a656cb207a0c039c8049416741` | `work/paso4_windows.log` | windows, deficit law, cost form |
| `ba34c83d4ab700133956e3946f08e23f` | `work/sanity_oddlat.log` | sl_2 relations, E formula, λ=12 table |
| `8babbab35dc7f0bc3adfce2154d2a766` | `work/sanity_oddlat.py` | sanity checks |
| `5ad4737fc50bedc6f3b6dfe3cbe4e14e` | `work/seal1.log` | raw output of the sealing run 1 |
| `8bf8217bcdd4a54e40c6d4ddb461745e` | `work/seal2.log` | raw output of the sealing run 2 |
| `fdd8a2d8ca21a9d52cec110acc0a4f7d` | `work/theoremF_p.log` | 56246 houses, 0 failures |
| `c33617a0fe631da91d8f861137f329af` | `work/theoremF_p.py` | odd-p Theorem F, every step, numerically |

FIN — Tue Oct 13 21:02:40 CEST 2026
