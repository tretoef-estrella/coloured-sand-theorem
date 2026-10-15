module

public import RequestProject.TheoremF.All

/-!
# Theorem F, second half: the *Setting* of `C8_theorem_F_potential.md`

## Encoding

* A **house** `H = (I, k, ℓ, α)` is given by its components `I : Finset ℕ`, `k ℓ : ℕ`, `α : ℤ`;
  the house conditions are hypotheses `hI : ∀ t ∈ I, t < k`, `hℓ : ℓ < 2 ^ k`, `hα : 1 ≤ α`
  (each theorem carries only those its proof uses; this is said in its docstring).
  `N = 2^{|I|}` is `2 ^ #I`.
* Positions are natural numbers; sequences are functions `ℕ → ℤ` of which only the positions
  `< N` matter (as in pieces C1 and C7).  The dancer at position `p` is `TheoremF.dancer I p`.
* `yhat I k ℓ α = AntitonicFit.ifit (2 ^ #I) (TheoremF.xHseq I k ℓ α)` is `ŷ_H`.
* `cHat I k ℓ α p q = Houses.cHatH I k ℓ α (dancer I p) (dancer I q)` is `ĉ_H(p, q)`.
* `IsArrow I p q` (an **arrow** `p → q`) is `p < N ∧ q < N ∧ dancer I q ⊂ dancer I p`.
* `IsPotential I k ℓ α V` (`V : ℕ → ℤ` is a **potential** for `H`) is the conjunction (a
  structure) of (E), (M), (G) exactly as in the *Setting*.
* For the recursion: `c = max I` is `hne : I.Nonempty`, `hc : c = I.max' hne`; `I' = I.erase c`,
  `M = 2 ^ #(I.erase c)`, `h = k − c` (the natural number `k - c`, cast to `ℤ`),
  `H' = (I.erase c, c, ℓ % 2 ^ c, α)`, `T = Houses.typ ℓ c`, `κ = Houses.kap I k ℓ c`,
  `τ = Houses.tau I k ℓ α c`, `J' = TheoremF.JHseq (I.erase c) c (ℓ % 2 ^ c)`,
  `d = TheoremF.dWalk I k ℓ α c`, and `X1 I k ℓ α c p = ŷ'(p) + d(p)` is `X_1`.
* `vPrime I k ℓ α c V'` is `v'` of Part 1: at `p < M` it is `V'(p) − [T = 1] κ J'(p)`, and at
  `p ≥ M` it is `τ + V'(p − M) − [T = 0] κ J'(p − M)` (so that `v'(M + p)` is as in the file).
  Indicators `[P] κ` are `if P then (κ : ℤ) else 0`.
-/

@[expose] public section

namespace Potential

open Finset AntitonicFit TheoremF

/-- *Setting* of `C8_theorem_F_potential.md`: `ŷ_H := ifit_N(x_H)`, `N = 2^{|I|}`. -/
noncomputable def yhat (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) : ℕ → ℤ :=
  ifit (2 ^ #I) (xHseq I k ℓ α)

/-- *Setting* of `C8_theorem_F_potential.md`:
`ĉ_H(p, q) := Houses.cHatH I k ℓ α (dancer_I(p)) (dancer_I(q))`. -/
def cHat (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (p q : ℕ) : ℤ :=
  Houses.cHatH I k ℓ α (dancer I p) (dancer I q)

/-- *Setting* of `C8_theorem_F_potential.md`: an **arrow** `p → q` is a pair of positions
`p, q < N` with `dancer_I(q) ⊊ dancer_I(p)`. -/
def IsArrow (I : Finset ℕ) (p q : ℕ) : Prop :=
  p < 2 ^ #I ∧ q < 2 ^ #I ∧ dancer I q ⊂ dancer I p

/-- *Setting* of `C8_theorem_F_potential.md`: `V : ℕ → ℤ` is a **potential** for the house
`H = (I, k, ℓ, α)` if (E), (M) and (G) hold. -/
structure IsPotential (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (V : ℕ → ℤ) : Prop where
  /-- (E) `V(p) − V(N − 1 − p) = ŷ_H(p)` for every `p < N`. -/
  E : ∀ p < 2 ^ #I, V p - V (2 ^ #I - 1 - p) = yhat I k ℓ α p
  /-- (M) `V(q) ≤ V(p)` whenever `p ≤ q < N`. -/
  M : ∀ p q, p ≤ q → q < 2 ^ #I → V q ≤ V p
  /-- (G) `V(p) − V(q) ≤ ĉ_H(p, q)` for every arrow `p → q`. -/
  G : ∀ p q, IsArrow I p q → V p - V q ≤ cHat I k ℓ α p q

/-- *Setting* of `C8_theorem_F_potential.md`: `X_1(p) := ŷ'(p) + d(p)`, where `ŷ'` is the integer
fit of the house `H' = (I ∖ {c}, c, ℓ mod 2^c, α)` and `d = dWalk` (C7). -/
noncomputable def X1 (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c : ℕ) : ℕ → ℤ :=
  fun p => yhat (I.erase c) c (ℓ % 2 ^ c) α p + dWalk I k ℓ α c p

/-- *Part 1* of `C8_theorem_F_potential.md`: the inherited potential
`v'(p) := V'(p) − [T = 1] κ J'(p)` and `v'(M + p) := τ + V'(p) − [T = 0] κ J'(p)` for `p < M`
(here written at a position `p ≥ M` as `τ + V'(p − M) − [T = 0] κ J'(p − M)`). -/
def vPrime (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (c : ℕ) (V' : ℕ → ℤ) : ℕ → ℤ := fun p =>
  if p < 2 ^ #(I.erase c) then
    V' p - (if Houses.typ ℓ c = 1 then (Houses.kap I k ℓ c : ℤ) else 0) *
      JHseq (I.erase c) c (ℓ % 2 ^ c) p
  else
    Houses.tau I k ℓ α c + V' (p - 2 ^ #(I.erase c)) -
      (if Houses.typ ℓ c = 0 then (Houses.kap I k ℓ c : ℤ) else 0) *
        JHseq (I.erase c) c (ℓ % 2 ^ c) (p - 2 ^ #(I.erase c))

variable {I : Finset ℕ} {k ℓ : ℕ}

/-- *Setting* of `C8_theorem_F_potential.md`: for an arrow `p → q`, `q < p` (by Lemma 0b of C7,
since `o_b < o_a`). -/
theorem IsArrow.lt {p q : ℕ} (h : IsArrow I p q) : q < p := by
  obtain ⟨-, hq, hsub⟩ := h
  by_contra hle
  push_neg at hle
  have h1 := oE_dancer_mono hle (I := I) hq
  have h2 : Rulers.oE (dancer I q) < Rulers.oE (dancer I p) := by
    unfold Rulers.oE
    obtain ⟨t, htp, htq⟩ := exists_of_ssubset hsub
    exact sum_lt_sum_of_subset hsub.subset htp htq (by positivity) (fun _ _ _ => by positivity)
  omega

/-- The value of `v'` at a position `M + p` (*Part 1* of `C8_theorem_F_potential.md`). -/
lemma vPrime_high (α : ℤ) (c : ℕ) (V' : ℕ → ℤ) (p : ℕ) :
    vPrime I k ℓ α c V' (2 ^ #(I.erase c) + p) = Houses.tau I k ℓ α c + V' p -
      (if Houses.typ ℓ c = 0 then (Houses.kap I k ℓ c : ℤ) else 0) *
        JHseq (I.erase c) c (ℓ % 2 ^ c) p := by
  simp [vPrime]

/-- The value of `v'` at a position `p < M` (*Part 1* of `C8_theorem_F_potential.md`). -/
lemma vPrime_low (α : ℤ) (c : ℕ) (V' : ℕ → ℤ) {p : ℕ} (hp : p < 2 ^ #(I.erase c)) :
    vPrime I k ℓ α c V' p = V' p -
      (if Houses.typ ℓ c = 1 then (Houses.kap I k ℓ c : ℤ) else 0) *
        JHseq (I.erase c) c (ℓ % 2 ^ c) p := by
  simp [vPrime, hp]

end Potential
