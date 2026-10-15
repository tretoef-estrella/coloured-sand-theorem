module

public import Mathlib

/-!
# The matrices and numbers of Lemma 8 (CSG1, preamble, §1 and §2)

This file contains the definitions of `CSG1_lemma_8_the_blocks.md`, written literally.

## Encoding

* `R = ℤ_[p]` (Mathlib's `p`-adic integers, `[Fact p.Prime]`).
* `Nt p q c k t = N t = ((q * (c + k + t) : ℕ) : ℤ_[p])` and
  `vt p q c k t = v t = padicValNat p q + padicValNat p (c + k + t)` (preamble).
* §1: `lam p r a = λ = p − 1 + r + p a`, `mu p r a = μ = λ − 2r`,
  `nu p r a = ν = if r ≤ p − 1 ∧ a = p − 1 then 2 else 1`,
  `uGlue p r a = u = (C(μ+r, μ) (a+1) p) / p^ν` (natural-number division).
* `Mblk p q c k r a : Matrix ι ι ℤ_[p]` with `ι = Fin (λ + 1) ⊕ Fin (μ + 1)` (`inl i` is `ℓ_i`,
  `inr j` is `s̃_j`); column `y` is the image of the basis vector `y`, so the operator is
  `Matrix.mulVecLin (Mblk …)` and its range is spanned by the columns.  The entries are exactly
  those of §1.
* The numbers `A, A', α, τ, E₁₁, E₁₂, E₂₂, x, y` of §1 are `blkA`, `blkA'`, `blkAlpha`,
  `blkTau`, `E11`, `E12`, `E22`, `blkX`, `blkY` (natural numbers, with truncated subtraction as
  in the file).
* §2: the chain matrix `Mch p q c k lam : Matrix (Fin (λ+1)) (Fin (λ+1)) ℤ_[p]` and
  `chA p q c k lam = Σ_{t ∈ range (λ+1)} v t`.
* The cokernel of a matrix `M` is `(ι → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin M)`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Blocks

variable (p : ℕ) [Fact p.Prime] (q c k : ℕ)

/-- `N t = q (c + k + t)`, as an element of `ℤ_[p]`. -/
noncomputable def Nt (t : ℕ) : ℤ_[p] := ((q * (c + k + t) : ℕ) : ℤ_[p])

/-- `v t = e + v_p(c + k + t)` with `e = v_p(q)` (Mathlib's convention `v_p(0) = 0`). -/
def vt (t : ℕ) : ℕ := padicValNat p q + padicValNat p (c + k + t)

/-- `λ = p − 1 + r + p a`. -/
def lam (r a : ℕ) : ℕ := p - 1 + r + p * a

/-- `μ = λ − 2 r`. -/
def mu (r a : ℕ) : ℕ := lam p r a - 2 * r

/-- The glue exponent `ν = if r ≤ p − 1 ∧ a = p − 1 then 2 else 1`. -/
def nu (r a : ℕ) : ℕ := if r ≤ p - 1 ∧ a = p - 1 then 2 else 1

/-- The glue entry `u = C(μ + r, μ) (a + 1) p / p^ν`. -/
def uGlue (r a : ℕ) : ℕ := (Nat.choose (mu p r a + r) (mu p r a) * (a + 1) * p) / p ^ nu p r a

/-- **The block matrix `Mblk`** of §1 (the model of Lemma 7 at levels `k, …, k + λ`). -/
noncomputable def Mblk (r a : ℕ) :
    Matrix (Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1)) (Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1))
      ℤ_[p] :=
  Matrix.of fun x y => match x, y with
    | .inl i', .inl i =>
        if i' = i then Nt p q c k i else if (i' : ℕ) = i + 1 then ((i : ℕ) + 1 : ℤ_[p]) else 0
    | .inr j', .inr j =>
        if j' = j then Nt p q c k (j + r) else if (j' : ℕ) = j + 1 then ((j : ℕ) + 1 : ℤ_[p])
        else 0
    | .inl i', .inr j =>
        if (j : ℕ) = mu p r a ∧ (i' : ℕ) = mu p r a + r + 1 then (uGlue p r a : ℤ_[p]) else 0
    | .inr _, .inl _ => 0

/-- `A = Σ_{t ∈ range (λ + 1)} v t`. -/
def blkA (r a : ℕ) : ℕ := ∑ t ∈ range (lam p r a + 1), vt p q c k t

/-- `A' = Σ_{t ∈ Icc r (r + μ)} v t`. -/
def blkA' (r a : ℕ) : ℕ := ∑ t ∈ Icc r (r + mu p r a), vt p q c k t

/-- `α = Σ_{t ∈ Icc ((a + 1) p) λ} v t`. -/
def blkAlpha (r a : ℕ) : ℕ := ∑ t ∈ Icc ((a + 1) * p) (lam p r a), vt p q c k t

/-- `τ = if a = p − 1 then 2 else 1`. -/
def blkTau (a : ℕ) : ℕ := if a = p - 1 then 2 else 1

/-- `E₁₁ = A − α − a`. -/
def E11 (r a : ℕ) : ℕ := blkA p q c k r a - blkAlpha p q c k r a - a

/-- `E₁₂ = A' − a + τ`. -/
def E12 (r a : ℕ) : ℕ := blkA' p q c k r a - a + blkTau p a

/-- `E₂₂ = A' − a + α`. -/
def E22 (r a : ℕ) : ℕ := blkA' p q c k r a - a + blkAlpha p q c k r a

/-- `x = min E₁₁ (min E₁₂ E₂₂)`. -/
def blkX (r a : ℕ) : ℕ := min (E11 p q c k r a) (min (E12 p q c k r a) (E22 p q c k r a))

/-- `y = E₁₁ + E₂₂ − x`. -/
def blkY (r a : ℕ) : ℕ := E11 p q c k r a + E22 p q c k r a - blkX p q c k r a

/-- **The chain matrix `Mch`** of §2 (the simple blocks). -/
noncomputable def Mch (lam : ℕ) : Matrix (Fin (lam + 1)) (Fin (lam + 1)) ℤ_[p] :=
  Matrix.of fun i' i =>
    if i' = i then Nt p q c k i else if (i' : ℕ) = i + 1 then ((i : ℕ) + 1 : ℤ_[p]) else 0

/-- `A = Σ_{t ∈ range (λ + 1)} v t` for the chain matrix. -/
def chA (lam : ℕ) : ℕ := ∑ t ∈ range (lam + 1), vt p q c k t

end ColouredSand.Blocks
