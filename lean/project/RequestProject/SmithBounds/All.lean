module

public import RequestProject.SmithBounds.TropicalBound
public import RequestProject.SmithBounds.LeastTerm
public import RequestProject.SmithBounds.Basic
public import RequestProject.SmithBounds.Convexity
public import RequestProject.SmithBounds.TheoremU

/-!
# Bounds for determinantal divisors (`C2_smith_bounds.md`)

Index of the formalization (namespace `SmithBounds`):

* `TropicalBound.lean` — **Part A**: the minor `M[A, B]` (`minor`), matchings (`IsMatching`),
  costs (`cost`), **Lemma A** (`lemma_A1`, `lemma_A2`).
* `LeastTerm.lean` — **Part B**: **Lemma B** (`lemma_B`) and **Corollary B′**
  (`corollary_B'`).
* `Basic.lean` — sums over the last `r` positions (`tailSum`), non-increasing sequences
  (`NonIncrOn`), used in Parts C and D.
* `Convexity.lean` — **Part C**: `U`, `Y`, convexity (`IsConvexOn`), **Lemma C0**
  (`lemma_C0_total`, `lemma_C0`) and **Lemma 6.4** (`lemma_6_4`), built on `AntitonicFit.ifit`
  and `AntitonicFit.consequence_L` from piece C1.
* `TheoremU.lean` — **Part D**: **Lemma D0** (`lemma_D0`), `r`-matchings (`IsRMatching`) and
  **Theorem 7.4 (Theorem U)** (`theorem_U`).
-/
