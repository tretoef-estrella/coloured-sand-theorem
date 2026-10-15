module

public import RequestProject.Divisors.CauchyBinet
public import RequestProject.Divisors.Basic
public import RequestProject.Divisors.Invariance
public import RequestProject.Divisors.Diagonal
public import RequestProject.Divisors.TheoremB

/-!
# Determinantal divisors at the prime 2, and Theorem 6.5 (`C5_divisors_theorem_65.md`)

Index of the formalization (namespace `Divisors`):

* `CauchyBinet.lean` — the **Cauchy–Binet formula** (`cauchy_binet`), not available in Mathlib,
  used in the proof of Lemma A1.
* `Basic.lean` — **Part A, Setting**: minors `det M[A, B]` (`minor`, rows and columns in
  increasing order via `Finset.orderEmbOfFin`), Cauchy–Binet for minors (`minor_mul`), the set of
  2-adic valuations of the non-zero `r × r` minors (`minorVals`) and the **2-adic determinantal
  divisor** `dd_r(M)` (`dd`, its minimum); non-emptiness for `det M ≠ 0`
  (`minorVals_nonempty`), `dd_0(M) = 0` (`dd_zero`) and `dd_n(M) = v_2(det M)` (`dd_top`).
* `Invariance.lean` — **Lemma A1** (`lemma_A1`).
* `Diagonal.lean` — **Lemma A2** (`lemma_A2`) and **Corollary A3** (`corollary_A3_sum`,
  `corollary_A3_increment`, `corollary_A3_convex`).
* `TheoremB.lean` — **Part B**: `d̂` (`dHat`), **Theorem B (Theorem 6.5)** (`theorem_B`, with
  the unused hypothesis (M), and `theorem_B_without_M`) and **Corollary B′** (`corollary_B'`),
  built on `AntitonicFit.ifit` (piece C1) and `SmithBounds.lemma_6_4` (piece C2).
-/
