module

public import RequestProject.Deficit.Basic

/-!
# `CSI11_the_odd_deficit_law.md` — *Setting* and **(Q0)**

Namespace `ColouredSand.OddTwist`.  This is the `p`-odd analogue of C10
(`RequestProject/Deficit/`), and it reuses C10's encoding without redefining it.

## Encoding

* **Coefficient functions.** An element of `ℤ[y_t : t ∈ I]/(y_t²)` is a function
  `Finset ℕ → ℤ`; its value at `Δ` is the coefficient `[q]_Δ` of the monomial
  `y^Δ = ∏_{t ∈ Δ} y_t`.  (This is C10's encoding.)
* **Product.** The product is C10's `Deficit.starMul`:
  `(f ⋆ g)(Δ) = Σ_{Δ₁ ⊆ Δ} f(Δ₁) · g(Δ ∖ Δ₁)`.
* **Powers** (*Setting*, «Powers»). `starPow f n` is `f ⋆ (f ⋆ (⋯ ⋆ f))` with `n` factors,
  defined by `starPow f 0 = [Δ = ∅]` and `starPow f (n+1) = f ⋆ starPow f n`.
* **Indicators** `[P]` are written `if P then 1 else 0`.
* **Digits.** The digit list is `ds : List ℕ`, lowest digit first.  Its length is `k`, and
  the digit `d_t` is `ds.getD t 0`.  The top digit `d_k` is passed separately, as a natural
  number `dk`.  The hypothesis «every entry `< p`» is `∀ d ∈ ds, d < p`.
* **The set `I`.** `I(ds) = {t < k : d_t ≠ 0}` is `Iod ds`, a `Finset ℕ`.
* **The coefficients of `q_t`.** `aP p ds t Δ` is the coefficient of `y^Δ` in `q_t`.  It is
  defined by recursion on `t`, exactly as in (Q0).  Note that `aP p ds 0 = [Δ = ∅]` starts at
  `+1`, while C10's `Deficit.a I 0 = −[Δ = ∅]` starts at `−1`.
* **Set partitions** (used in (Q3)). A partition of `Γ` is a `Finset` of non-empty, pairwise
  disjoint blocks whose union is `Γ`.  `setPartitions Γ` is the finite set of all of them,
  carved out of `Γ.powerset.powerset`.
* **Valuations.** Valuations are `padicValInt p`.  The deficit `k − |Δ| − min Δ` uses natural
  subtraction and `Δ.min' h`; it never truncates (`card_add_min'_le`).
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset

/-- **Powers** in `ℤ[y_t]/(y_t²)` (*Setting* of `CSI11_the_odd_deficit_law.md`):
`starPow f n = f ⋆ f ⋆ ⋯ ⋆ f` (`n` factors), with `starPow f 0 = [Δ = ∅]` and
`starPow f (n+1) = f ⋆ starPow f n`.  The product is C10's `Deficit.starMul`. -/
def starPow {R : Type*} [CommRing R] (f : Finset ℕ → R) : ℕ → Finset ℕ → R
  | 0 => fun Δ => if Δ = ∅ then 1 else 0
  | n + 1 => Deficit.starMul f (starPow f n)

/-- The set `I(ds) = {t < k : d_t ≠ 0}` (*Setting* of `CSI11_the_odd_deficit_law.md`).  Here
`k = ds.length` and `d_t = ds.getD t 0`. -/
def Iod (ds : List ℕ) : Finset ℕ :=
  (range ds.length).filter (fun t => ds.getD t 0 ≠ 0)

/-- **(Q0)** of `CSI11_the_odd_deficit_law.md`: `aP p ds t Δ` is the coefficient of `y^Δ` in
`q_t`:
* `aP 0 Δ = [Δ = ∅]`;
* `aP (t+1) Δ = (starPow (aP t) p)(Δ) − [t < k ∧ d_t ≠ 0]·[t ∈ Δ]·(starPow (aP t) (p − d_t))(Δ ∖ {t})`.

That is, `q_{t+1} = q_t^p − [t ∈ I] y_t q_t^{p − d_t}`.  Here `k = ds.length` and
`d_t = ds.getD t 0`. -/
def aP (p : ℕ) (ds : List ℕ) : ℕ → Finset ℕ → ℤ
  | 0, Δ => if Δ = ∅ then 1 else 0
  | t + 1, Δ => starPow (aP p ds t) p Δ -
      (if t < ds.length ∧ ds.getD t 0 ≠ 0 then 1 else 0) * (if t ∈ Δ then 1 else 0) *
        starPow (aP p ds t) (p - ds.getD t 0) (Δ \ {t})

/-- The partitions of a finite set `Γ` into non-empty blocks, used in **(Q3)** of
`CSI11_the_odd_deficit_law.md`.  A partition is a finite set `P` of blocks such that every
block is non-empty, the blocks are pairwise disjoint, and their union is `Γ`. -/
def setPartitions (Γ : Finset ℕ) : Finset (Finset (Finset ℕ)) :=
  Γ.powerset.powerset.filter (fun P =>
    (∀ B ∈ P, B.Nonempty) ∧ (∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B') ∧ P.sup id = Γ)

end ColouredSand.OddTwist
