module

public import Mathlib
public import RequestProject.Payment.Basic

/-!
# The *Setting* and *Part T* of `CSI7_the_twist_move.md`

Namespace `ColouredSand.OddTwist`. The setting is C11's (`RequestProject/Payment/`, namespace
`Payment`), reused without modification.

## Encoding

* `A` is an arbitrary commutative ring and `p : ℕ` is used as `(p : A)`.
* A **graded family** `(ι, fl, N, F)` is exactly as in C11: `ι` with `[DecidableEq ι]`,
  `fl : ι → ℕ`, `A`-modules `N i`, and an `A`-linear `F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)`; elements
  of `M = ⨁ i, N i` are finitely supported (`DirectSum`).
* A **slot type** `S` is a type with `[Fintype S] [DecidableEq S]`; no order is used.
* The module of a system is C11's `Payment.Sys N S = ⨁ q : S × ι, N q.2` (`= M^S`).
  C11's generators `Payment.slotLof` and `Payment.slotEmb` are stated with a `[LinearOrder S]`
  argument (which they do not use); since no order is wanted here, the same maps are written
  `oslot A N S s i` (`x ↦ x ι_{s,i}`, i.e. `DirectSum.lof` at `(s, i)`) and `oslotE A N S s`
  (`m ↦ m ι_s`). For any linear order on `S` they *are* C11's maps, by definition:
  `oslot_eq_slotLof`, `oslotE_eq_slotEmb` (both `rfl`).
* **Data** are matrices `Q : ℕ → Matrix S S A` (the payment divided by `p`), and the **system**
  `Gp p fl F Q : Sys N S →ₗ[A] Sys N S` is defined on generators (`DirectSum.toModule`):
  `Gp (x ι_{s',i}) = (F x) ι_{s'} + Σ_{s ∈ S} ((p : A) * Q (fl i) s s') • x ι_{s,i}`
  (the row-vector convention of the file: `g(Fx) + g(x)·(p Q(φ))`).
* **The odd twist (Part T)**: index type `ι × Fin p`; floor `flT p fl (i, j) = p * fl i + j`
  (`j` read through `Fin.val`); module `NT p N (i, j) = N i` (the element `x` at `(i, j)` is the
  paper's `b_j x`); `embT p j : M →ₗ[A] ⨁ q, NT p N q` places `x` at `i` as `x` at `(i, j)`; the
  operator `FT p F` is defined with `DirectSum.toModule` by
  `FT (x at (i, j)) = x at (i, j+1)` if `j + 1 < p`, and
  `FT (x at (i, p−1)) = −(p : A) • embT p 0 (F x)`.
* **The twisted data**: `QT p Q f = −(p : A)^(p−2) • (Q (p f) * Q (p f + 1) * ⋯ * Q (p f + p − 1))`,
  written `-(p : A) ^ (p - 2) • ((List.range p).map (fun j => Q (p * f + j))).prod`, exactly as in
  the file. For the sign question of step 3 of the *Proof* (even `p`), the variant with the sign
  `(−1)^p` built in is `QTsign p Q f = ((−1)^p * p^(p−2)) • (same product)`; for odd `p` the two
  agree (`QTsign_of_odd`).
-/

@[expose] public section

namespace ColouredSand.OddTwist

open DirectSum

/-- The modules of the odd twist: `NT p N (i, j) = N i` (the element `x` at `(i, j)` is the
paper's `b_j x`) (*Part T* of `CSI7_the_twist_move.md`). -/
abbrev NT (p : ℕ) {ι : Type*} (N : ι → Type*) (q : ι × Fin p) : Type _ := N q.1

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable (S : Type*)

section Generators

variable [DecidableEq S]

variable (A) in
/-- `x ↦ x ι_{s,i}`: `x ∈ N i` placed at `(s, i)` in `M^S = Payment.Sys N S` (*Setting* of
`CSI7_the_twist_move.md`; C11's `Payment.slotLof` without the unused order on `S`). -/
def oslot (s : S) (i : ι) : N i →ₗ[A] Payment.Sys N S :=
  DirectSum.lof A (S × ι) (fun q => N q.2) (s, i)

variable (A) in
/-- `m ↦ m ι_s`: the linear map `M → M^S` sending `x` at `i` to `x ι_{s,i}` (*Setting* of
`CSI7_the_twist_move.md`; C11's `Payment.slotEmb` without the unused order on `S`). -/
def oslotE (s : S) : (⨁ i, N i) →ₗ[A] Payment.Sys N S :=
  DirectSum.toModule A ι (Payment.Sys N S) (fun i => oslot A N S s i)

end Generators

section Bridge

variable [LinearOrder S]

/-- For any linear order on `S`, `oslot` is C11's `Payment.slotLof` (*Setting* of
`CSI7_the_twist_move.md`). -/
lemma oslot_eq_slotLof (s : S) (i : ι) :
    oslot A N S s i = Payment.slotLof A N S s i := rfl

/-- For any linear order on `S`, `oslotE` is C11's `Payment.slotEmb` (*Setting* of
`CSI7_the_twist_move.md`). -/
lemma oslotE_eq_slotEmb (s : S) :
    oslotE A N S s = Payment.slotEmb A N S s := rfl

end Bridge

variable {N S} [DecidableEq S] [Fintype S]

/-- **The payment system with matrix data** `Gp p fl F Q : M^S → M^S` (*Setting* of
`CSI7_the_twist_move.md`), defined on generators:
`Gp (x ι_{s',i}) = (F x) ι_{s'} + Σ_{s ∈ S} ((p : A) * Q (fl i) s s') • x ι_{s,i}`. -/
def Gp (p : ℕ) (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) :
    Payment.Sys N S →ₗ[A] Payment.Sys N S :=
  DirectSum.toModule A (S × ι) (Payment.Sys N S) (fun q =>
    oslotE A N S q.1 ∘ₗ F ∘ₗ DirectSum.lof A ι N q.2
      + ∑ s, ((p : A) * Q (fl q.2) s q.1) • oslot A N S s q.2)

variable (p : ℕ)

/-- The floor of the odd twist: `flT p fl (i, j) = p · fl i + j` (*Part T* of
`CSI7_the_twist_move.md`). -/
def flT (fl : ι → ℕ) (q : ι × Fin p) : ℕ := p * fl q.1 + q.2.val

variable (A N) in
/-- `b_j : M → ⨁ q, NT p N q`, placing `x` at `i` as `x` at `(i, j)` (*Part T* of
`CSI7_the_twist_move.md`). -/
def embT (j : Fin p) : (⨁ i, N i) →ₗ[A] (⨁ q, NT p N q) :=
  DirectSum.toModule A ι _ (fun i => DirectSum.lof A (ι × Fin p) (NT p N) (i, j))

/-- **The operator of the odd twist** (*Part T* of `CSI7_the_twist_move.md`; digit `0`,
`u = −1`): `FT (x at (i, j)) = x at (i, j+1)` for `j < p − 1`, and
`FT (x at (i, p−1)) = −(p : A) • embT p 0 (F x)`. -/
def FT (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) : (⨁ q, NT p N q) →ₗ[A] (⨁ q, NT p N q) :=
  DirectSum.toModule A (ι × Fin p) _ (fun q =>
    if h : q.2.val + 1 < p then DirectSum.lof A (ι × Fin p) (NT p N) (q.1, ⟨q.2.val + 1, h⟩)
    else -(p : A) • (embT A N p ⟨0, q.2.pos⟩ ∘ₗ F ∘ₗ DirectSum.lof A ι N q.1))

/-- **The twisted data** (*Part T* of `CSI7_the_twist_move.md`):
`QT p Q f = −(p : A)^(p−2) • (Q (p f) * Q (p f + 1) * ⋯ * Q (p f + p − 1))`. -/
def QT (Q : ℕ → Matrix S S A) (f : ℕ) : Matrix S S A :=
  -(p : A) ^ (p - 2) • ((List.range p).map (fun j => Q (p * f + j))).prod

/-- The twisted data with the sign `(−1)^p` built in (step 3 of the *Proof* of (A1) of
`CSI7_the_twist_move.md`, the "your choice" for even `p`):
`QTsign p Q f = ((−1)^p · p^(p−2)) • (Q (p f) * ⋯ * Q (p f + p − 1))`. -/
def QTsign (Q : ℕ → Matrix S S A) (f : ℕ) : Matrix S S A :=
  ((-1 : A) ^ p * (p : A) ^ (p - 2)) • ((List.range p).map (fun j => Q (p * f + j))).prod

/-- For odd `p`, `QTsign p Q = QT p Q` (step 3 of the *Proof* of (A1) of
`CSI7_the_twist_move.md`). -/
lemma QTsign_of_odd {p : ℕ} (hp : Odd p) (Q : ℕ → Matrix S S A) : QTsign p Q = QT p Q := by
  funext f
  simp [QTsign, QT, hp.neg_one_pow]

end ColouredSand.OddTwist
