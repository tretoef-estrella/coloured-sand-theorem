module

public import RequestProject.Rulers.Family

/-!
# The *Setting* of `C10_deficit_law.md`

## Encoding (namespace `Deficit`)

* A **coefficient function** (an element of `ℤ[y_t]/(y_t^2)`, resp. `ℚ[y_t]/(y_t^2)`) is a
  function `Finset ℕ → ℤ` (resp. `Finset ℕ → ℚ`); its value at `Δ` is the coefficient of the
  monomial `y^Δ = ∏_{t∈Δ} y_t`.
* The **product** `(f ⋆ g)(Δ) := Σ_{Δ₁ ⊆ Δ} f(Δ₁) · g(Δ ∖ Δ₁)` is `starMul f g Δ`, the sum running
  over `Δ.powerset` (ordered decompositions `Δ = Δ₁ ⊔ Δ₂`).  It is defined over any commutative
  ring, and used for `ℤ` and `ℚ`.
* Indicators `[P]` are written `if P then 1 else 0`.
* `a I t Δ` is `a_t(Δ)`, the coefficient of `y^Δ` in `q_t`, defined by recursion on `t`
  exactly as in the Setting:
  `a_0(Δ) = −[Δ = ∅]`, `a_{t+1}(Δ) = (a_t ⋆ a_t)(Δ) − [t ∈ I]·[t ∈ Δ]·a_t(Δ ∖ {t})`.
* `c I h Δ` is `c_h(Δ) ∈ ℚ`:
  `c_0(Δ) = [Δ = ∅]`, `c_{h+1}(Δ) = −½ (c_h ⋆ c_h)(Δ) − [h ∈ I]·[h ∈ Δ]·c_h(Δ ∖ {h})`.
* `Mc I k α i D D'` is the closed-form entry `Mc(D, D')`:
  `−2^{1 − K + o(D ∖ D')} · a_k(D ∖ D') · ∏_{d ∈ [o_D, o_{D'} + K)} π_0(d)` in `ℚ`, with `K = 2^k`,
  `α : ℤ`, the power of `2` an integer power (`zpow`), and `π_0(d) = 2^α (i + d)` (`pi0`).
  The product is over `Finset.Ico (oE D) (oE D' + 2 ^ k)`.
* `o_E` is `Rulers.oE E`, `min` with the convention `min ∅ = k` is `Rulers.minOr k`, the deficit
  `δ` is `Rulers.delta k`, and `v_2` of a natural number is `Rulers.v2` (`= padicValNat 2`).
  The valuations of integers are `padicValInt 2`, those of rationals `padicValRat 2`.
* The hypothesis `I ⊆ {0, …, k − 1}` is written `hI : ∀ t ∈ I, t < k`.
-/

@[expose] public section

namespace Deficit

open Finset

/-- The product `(f ⋆ g)(Δ) := Σ_{Δ₁ ⊆ Δ} f(Δ₁) · g(Δ ∖ Δ₁)` of the algebra `ℤ[y_t]/(y_t^2)`
on coefficient functions (*Setting* of `C10_deficit_law.md`). -/
def starMul {R : Type*} [CommRing R] (f g : Finset ℕ → R) (Δ : Finset ℕ) : R :=
  ∑ Δ₁ ∈ Δ.powerset, f Δ₁ * g (Δ \ Δ₁)

/-- The coefficients `a_t(Δ)` of the polynomials `q_t` (*Setting* of `C10_deficit_law.md`,
*The polynomials `q_t`*): `a_0(Δ) = −[Δ = ∅]`,
`a_{t+1}(Δ) = (a_t ⋆ a_t)(Δ) − [t ∈ I]·[t ∈ Δ]·a_t(Δ ∖ {t})`. -/
def a (I : Finset ℕ) : ℕ → Finset ℕ → ℤ
  | 0, Δ => -(if Δ = ∅ then 1 else 0)
  | t + 1, Δ => starMul (a I t) (a I t) Δ -
      (if t ∈ I then 1 else 0) * (if t ∈ Δ then 1 else 0) * a I t (Δ \ {t})

/-- The rescaled coefficients `c_h(Δ) ∈ ℚ` (*Setting* of `C10_deficit_law.md`,
*The rescaled coefficients*): `c_0(Δ) = [Δ = ∅]`,
`c_{h+1}(Δ) = −½ (c_h ⋆ c_h)(Δ) − [h ∈ I]·[h ∈ Δ]·c_h(Δ ∖ {h})`. -/
def c (I : Finset ℕ) : ℕ → Finset ℕ → ℚ
  | 0, Δ => if Δ = ∅ then 1 else 0
  | h + 1, Δ => -(1 / 2) * starMul (c I h) (c I h) Δ -
      (if h ∈ I then 1 else 0) * (if h ∈ Δ then 1 else 0) * c I h (Δ \ {h})

/-- `π_0(d) := 2^α (i + d)` in `ℚ` (*Setting* of `C10_deficit_law.md`, *The closed-form
entries*). -/
def pi0 (α : ℤ) (i d : ℕ) : ℚ := (2 : ℚ) ^ α * ((i : ℚ) + d)

/-- The closed-form entry
`Mc(D, D') := −2^{1 − K + o(D ∖ D')} · a_k(D ∖ D') · ∏_{d = o_D}^{o_{D'} + K − 1} π_0(d)` in `ℚ`,
`K = 2^k`, the product over `o_D ≤ d < o_{D'} + K` (*Setting* of `C10_deficit_law.md`, *The
closed-form entries*). -/
def Mc (I : Finset ℕ) (k : ℕ) (α : ℤ) (i : ℕ) (D D' : Finset ℕ) : ℚ :=
  -(2 : ℚ) ^ ((1 : ℤ) - 2 ^ k + Rulers.oE (D \ D')) * (a I k (D \ D') : ℚ) *
    ∏ d ∈ Ico (Rulers.oE D) (Rulers.oE D' + 2 ^ k), pi0 α i d

end Deficit
