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
