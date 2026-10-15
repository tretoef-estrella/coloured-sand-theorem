module

public import Mathlib

/-!
# The *Setting* of `C11_payment_systems_twist.md`

## Encoding (namespace `Payment`)

* `A` is an arbitrary commutative ring (`[CommRing A]`).
* A **graded family** `(ι, fl, N, F)` is: an index type `ι` with `[DecidableEq ι]`, a floor
  function `fl : ι → ℕ`, a family `N : ι → Type*` of `A`-modules, and an `A`-linear map
  `F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)` on the direct sum `M = ⨁ i, N i` (`DirectSum`, finite
  support).  No hypothesis on `F` is made (as in the file).
* A **slot type** is a type `S` with `[Fintype S] [LinearOrder S]`.
* The module of a system is `Sys N S := ⨁ q : S × ι, N q.2` (`= M^S`).  The element
  `x ι_{s,i}` (for `x : N i`) is `slotLof A N S s i x := DirectSum.lof A (S × ι) _ (s, i) x`, and
  `m ι_s` (for `m : M`) is `slotEmb A N S s m`, where `slotEmb A N S s : M →ₗ[A] Sys N S` is the
  `DirectSum.toModule` map sending `x` at `i` to `x ι_{s,i}`.
* **Halved data** are functions `p : S → ℕ → A` and `κ : S → S → ℕ → A`; the payment system is
  `G fl F p κ : Sys N S →ₗ[A] Sys N S`, defined on generators with `DirectSum.toModule`:
  `G (x ι_{s',i}) = (F x) ι_{s'} + (2 * p s' (fl i)) • x ι_{s',i}
                     + Σ_{s ∈ univ.filter (s' < ·)} (2 * κ s s' (fl i)) • x ι_{s,i}`,
  where `F x` is `F (DirectSum.lof A ι N i x)`.
* **The double `Φ`**: index type `ι × Fin 2`; floor `flΦ fl (i, e) = 2 * fl i + e` (with `e`
  read as `0` or `1` via `Fin.val`); module `NΦ N (i, e) = N i`; operator `FΦ F` defined with
  `DirectSum.toModule` by `FΦ (x at (i,0)) = x at (i,1)` and
  `FΦ (x at (i,1)) = 2 • (embΦ A N 0 (F x))`, where `embΦ A N e : M →ₗ[A] ⨁ q, NΦ N q` places `x`
  at `i` as `x` at `(i, e)` (the paper's `b_e`).  The module of a system on `Φ` is
  `Sys (NΦ N) S = ⨁ q : S × (ι × Fin 2), N q.2.1`, and `G_Φ = G (flΦ fl) (FΦ F) p κ`.
* **The twisted data** `pT p` and `κT p κ` (the file's `p'`, `κ'`) are given by the formulas
  of the Setting, with no division.
-/

@[expose] public section

namespace Payment

open DirectSum Finset

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable (S : Type*) [Fintype S] [LinearOrder S]

/-- The module `M^S = ⨁_{(s,i) ∈ S × ι} N i` of a system with slot type `S`
(*Setting*, "Slots", of `C11_payment_systems_twist.md`). -/
abbrev Sys := ⨁ q : S × ι, N q.2

variable (A)

/-- `x ↦ x ι_{s,i}`: an element of `N i` placed at `(s, i)` in `M^S`
(*Setting*, "Slots", of `C11_payment_systems_twist.md`). -/
def slotLof (s : S) (i : ι) : N i →ₗ[A] Sys N S :=
  DirectSum.lof A (S × ι) (fun q => N q.2) (s, i)

/-- `m ↦ m ι_s`: the linear map `M → M^S` sending `x` at `i` to `x ι_{s,i}`
(*Setting*, "Slots", of `C11_payment_systems_twist.md`). -/
def slotEmb (s : S) : (⨁ i, N i) →ₗ[A] Sys N S :=
  DirectSum.toModule A ι (Sys N S) (fun i => slotLof A N S s i)

variable {A N S}

/-- The even payment system `G = G[fl, F, p, κ] : M^S → M^S` with halved data `(p, κ)`,
defined on generators by `DirectSum.toModule`:
`G(x ι_{s',i}) = (F x) ι_{s'} + 2 p_{s'}(fl i) · x ι_{s',i}
  + Σ_{s ∈ S, s > s'} 2 κ_{s s'}(fl i) · x ι_{s,i}`
(*Setting*, "Even payment systems (halved data)", of `C11_payment_systems_twist.md`). -/
def G (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A) (κ : S → S → ℕ → A) :
    Sys N S →ₗ[A] Sys N S :=
  DirectSum.toModule A (S × ι) (Sys N S) (fun q =>
    slotEmb A N S q.1 ∘ₗ F ∘ₗ DirectSum.lof A ι N q.2
      + (2 * p q.1 (fl q.2)) • slotLof A N S q.1 q.2
      + ∑ s ∈ Finset.univ.filter (q.1 < ·), (2 * κ s q.1 (fl q.2)) • slotLof A N S s q.2)

variable (N) in
/-- The modules of the double `Φ`: `N^Φ(i, e) = N i` (the element `x` at `(i, e)` is the
paper's `b_e x`) (*Setting*, "The doubling `Φ`", of `C11_payment_systems_twist.md`). -/
abbrev NΦ (q : ι × Fin 2) : Type _ := N q.1

/-- The floor of the double: `fl^Φ(i, e) = 2 fl(i) + e`
(*Setting*, "The doubling `Φ`", of `C11_payment_systems_twist.md`). -/
def flΦ (fl : ι → ℕ) (q : ι × Fin 2) : ℕ := 2 * fl q.1 + q.2.val

variable (A N) in
/-- `b_e : M → M_Φ`, sending `x` at `i` to `x` at `(i, e)`
(*Setting*, "The doubling `Φ`", of `C11_payment_systems_twist.md`). -/
def embΦ (e : Fin 2) : (⨁ i, N i) →ₗ[A] (⨁ q, NΦ N q) :=
  DirectSum.toModule A ι _ (fun i => DirectSum.lof A (ι × Fin 2) (NΦ N) (i, e))

/-- The operator of the double: `F^Φ(x at (i,0)) = x at (i,1)` and
`F^Φ(x at (i,1)) = 2 · (F x)` placed with `e = 0`, defined with `DirectSum.toModule`
(*Setting*, "The doubling `Φ`", of `C11_payment_systems_twist.md`). -/
def FΦ (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) : (⨁ q, NΦ N q) →ₗ[A] (⨁ q, NΦ N q) :=
  DirectSum.toModule A (ι × Fin 2) _ (fun q =>
    if q.2 = 0 then DirectSum.lof A (ι × Fin 2) (NΦ N) (q.1, 1)
    else (2 : A) • (embΦ A N 0 ∘ₗ F ∘ₗ DirectSum.lof A ι N q.1))

/-- The twisted payments (halved): `p'_s(f) := −p_s(2f) · p_s(2f + 1)`
(*Setting*, "The twisted data", of `C11_payment_systems_twist.md`). -/
def pT (p : S → ℕ → A) (s : S) (f : ℕ) : A := -(p s (2 * f) * p s (2 * f + 1))

/-- The twisted couplings (halved):
`κ'_{u s'}(f) := −[p_{s'}(2f+1) κ_{u s'}(2f) + κ_{u s'}(2f+1) p_u(2f)
  + Σ_{s ∈ S, s' < s < u} κ_{s s'}(2f+1) κ_{u s}(2f)]`
(*Setting*, "The twisted data", of `C11_payment_systems_twist.md`). -/
def κT (p : S → ℕ → A) (κ : S → S → ℕ → A) (u s' : S) (f : ℕ) : A :=
  -(p s' (2 * f + 1) * κ u s' (2 * f) + κ u s' (2 * f + 1) * p u (2 * f)
    + ∑ s ∈ Finset.univ.filter (fun s => s' < s ∧ s < u), κ s s' (2 * f + 1) * κ u s (2 * f))

end Payment
