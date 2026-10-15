module

public import RequestProject.OddDeficit.Basic
public import RequestProject.OddDeficit.Algebra
public import RequestProject.OddDeficit.Polynomials
public import RequestProject.OddDeficit.Partition
public import RequestProject.OddDeficit.DeficitLaw
public import RequestProject.OddDeficit.Lambda

/-!
# `CSI11_the_odd_deficit_law.md` — the odd coefficient polynomials and the odd deficit law

Namespace `ColouredSand.OddTwist`.  This reuses, without modification, C10's `Deficit.starMul`,
`Deficit.a` and `Deficit.lemma_4_5`, C3's `Rulers.delta` and `Rulers.minOr`, and CSI10's
`digitL`, `kTop` and `Iset`.

Files:
* `Basic.lean` — Setting and **(Q0)**: `starPow`, `Iod` (`I(ds)`), `aP` (`[q_t]_Δ`),
  `setPartitions`.  The docstring there explains all the encodings.
* `Algebra.lean` — bilinearity of `starMul`, the supports of powers, the bookkeeping predicate
  `Small`, and the power expansion `f^N = 1 + N g + C(N,2) g² + (order 2)`.
* `Polynomials.lean` — **Part Q**: `Q0_zero`, `Q0_succ`, `Q0_succ_I`, **(Q1)** `Q1_support`,
  **(Q2)** `Q2_const`, **(Q3)** `Q3_const`.
* `Partition.lean` — **(Q3)**, the set-partition formula: `starPow_eq_sum_partitions` (any `f`
  with `f(∅) = 1`) and `Q3_partition` (for `q_t`).
* `DeficitLaw.lean` — **Part D**: `aP_exact` (the induction), **(D2)** `D2`, **(D1)** `D1`,
  `D1_delta` (with C3's `δ`), `D1_indep` (the same valuation as C10's `a`).
* `Lambda.lean` — (D1) for `λ` with CSI10's digits: `dsL`, `Iod_lambda`, `D1_lambda`.

Hypotheses: `p` prime and odd (`hp : p.Prime`, `hodd : Odd p`) and every digit `< p` are needed
only in Part D.  Oddness is used only for `p ∣ C(p,2)`.  Part Q holds for any `p` and any digits.
-/
