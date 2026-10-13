# Logs

Every log ends with the watchdog's line: `VIGIA-FIN-OK` (finished; peak memory and time) or `VIGIA-MATADO-…` (stopped by the watchdog, not a result).

| Files | Engine | What |
|---|---|---|
| `gate_reduction.log` | `gate_reduction.py` | Theorem A against the full Laplacian, 90 comparisons |
| `run_*.log` | `hamming_syl.py p d` | the cells used to find Theorem B ($d\le4$) and the cell $(d,p)=(5,7)$ |
| `cell_d*_p*.log` | `hamming_syl.py` | the ten sealed predictions of Theorem B, computed after sealing; `cell_d6_p5.log` is a cell with $p\le d$ |
| `sage_7_3.log`, `sage_11_2.log` | `sage_check.py` | independent check with Sage from the full Laplacian |
| `sage_5_4.log` | `sage_check.py` | stopped by the watchdog for memory; not used |
| `gate_exponent.log` | `gate_exponent.py` | Theorem C, 143 cells |
| `gate_wilson.log` | `gate_wilson.py` | the rank formula of Theorem D, 264 cases |
| `perfil_p3.log` | `perfil_test.py` | Lemma 2 (only the valuations matter), 540 cases |
| `hb_q_p_d.log` | `hamming_bool.py q p d` | full Sylow groups for $q=p\in\{3,5,7\}$, $p\le d$ |
| `xm_3.log`, `tilt2_p3.log`, `tilt2_p5.log` | `xm.py`, `tilt2.py` | the pieces with $m\ge p$ used to find the Glue Conjecture ($p=3,5$) |
| `check_sealed2b.log`, `check_sealed2c.log`, `check_inverse.log` | `check_sealed2b.py`, `check_inverse.py` | the 30 sealed pieces at $p=7$ (`check_sealed2b.log` is the first run, whose 5 failures were a bug of the checker in counting level 10; `check_sealed2c.log` is the corrected run; `check_inverse.log` pins the factors of valuation $\ge 11$ exactly) |
| `check_sealed3.log` | `check_sealed3.py` | the 14 sealed full groups with composite $q$ |
| `check_e0.log` | `check_e0.py` | the Glue Conjecture fails for $p\nmid q$, as the paper states |
| `gate_glue_model.log` | `gate_glue_model.py` | Theorem F: stability of the lattice of Lemma 7 (2200 checks) and the block cokernel against the formula (292 cases), $\lambda\le2p-2$ |
| `gate_glue_model_BUG_multiplier.log` | `gate_glue_model.py` (before the fix) | the first run: 32 «failures» caused by the checker, whose random multiplier of $q$ could be divisible by $p$; kept as a record |
| `gate_glue_control_split.log` | `gate_glue_control_split.py` | control: the split lattice (no glue) fails 293 of 293 |
| `tilt3p.log` | `tilt3p.py` | Theorem G: 27 lattices stable; 154 pieces against direct Smith forms ($p=3$, $m\le7$; $p=5$, $m\le10$) |
| `tilt3p_probe.log` | `tilt3p_probe.py` | control (formula F beyond $2p-2$ fails 12 of 18); $p=3$, $m=8$ matches 5 of 5; $m=9,10$ outside the range |
| `tiltgen_probe.log` | `tiltgen_probe.py` | stopped by the watchdog at 10 minutes during the $p=7$ stability part; the $p=3,5$ lines it printed are valid |
| `tiltgen_probe2.log` | `tiltgen_probe2.py` | the block formula against the model, $\lambda\le p^2-2$ (180 cases); $p=3$, $m=9,10$ with the general rule differ by one factor, as Conjecture H's bound predicts |
| `check_c0.log` | `check_c0.py` | the $c=0$ clause of the block formula, 60 cases |
| `fullgroup_check.log` | `fullgroup_check.py` | full groups $p=q=3$, $d=5..8$ reproduced exactly; $d=9$ differs (version 2 formula, outside its range; version 3: `check_table_v3.log`) |
| `gate_jordan_N.log` | `gate_jordan_N.py` | Corollary 6: 37 cases, control (characteristic 0) differs in 7 |
| `check_p2.log` | `check_p2.py` | Theorem G at $p=2$: valid for $m\le3$ (30 of 30), fails for $m=4,5,6$ (the block $\lambda=4$ has $a=p-1$), as stated |
| `gate_conjH.log`, `gate_conjH_G2p7.log` | `gate_conjH.py`, `gate_conjH_G2p7.py` | version 3: blocks with $a+1<p$ for every $\lambda\le p^2-1$ ($p=5,7$): formula against model 216/216, split control 52/52, stability of the lattices (all $p=5$, sample $p=7$; then all 36 at $p=7$); G3: blocks with $a=p-1$ need the new glue |
| `frontier_data.log` | `frontier_data.py` | version 3: direct Smith forms at $m=p^2$ ($p=2,3$) and $m=p^2+1$ ($p=3$), used to find the blocks with $a=p-1$ |
| `seal4.log`, `check_seal4.log` | `seal4.py`, `check_seal4.py` | the 41 predictions of `PREDICCION_SELLADA_4.txt`, written and then computed |
| `frontier_sharp.log`, `frontier_next.log` | `frontier_sharp.py`, `frontier_next.py` | the formula with glue $1/p^2$ fails at $\lambda=p^2+p-1$ (20/20); there the glue $1/p$ is forced and the model matches 20/20 |
| `seal5.log`, `check_seal5.log` | `seal5.py`, `check_seal5.py` | the 22 predictions of `PREDICCION_SELLADA_5.txt`, written and then computed |
| `check_table_v3.log` | `check_table_v3.py` | the data table of the paper ($p=q=3$, $d=5..9$) from Theorems A and G |
| `gate_dst_alpha.log`, `gate_dst_alpha2.log` | `gate_dst_alpha.py`, `gate_dst_alpha2.py` | Theorem H: 360 + 24 pieces, 7 full Laplacians, two controls |
| `frontier_p3_m12.log`, `frontier_p3_m12_rest.log` | `frontier_p3_m12.py`, `frontier_p3_m12_rest.py` | the block $\lambda=12$ at $p=3$ (Conjecture I); the first run was stopped by the watchdog after 5 of its 8 cells (its last line says so), the second run did the other 3 |
| `frontier_p3_m12_e2.log` | `frontier_p3_m12_e2.py` | after version 3: sealed prediction 7 (`PREDICCION_SELLADA_7.txt`), the block $\lambda=12$ at $p=3$ with $q=9$, $c=1,2$: $8$ factors of exponent $1$, none of exponent $2$, $4$ of exponent $\ge3$, in both cells, as predicted |
| `check_conjI_proved.log`, `check_conjI_count.log` | `check_conjI_proved.py`, `check_conjI_count.py` | Conjecture I on the proved formulas; number of summands and of Weyl factors |
