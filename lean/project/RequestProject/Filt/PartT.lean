module

public import RequestProject.Filt.PartV

/-!
# `C29_filtrations_and_dance_lattices.md`: Part T — the dance lattices and the tensor powers;
# Part Z — the case of `ℤ_[2]`

Encodings (namespace `Filt`):

* `T A : ℕ → DPLattice A` (the dance lattices `T(λ)`, **[Φ]**) is defined by well-founded
  recursion: `T A 0 = one A` and `T A (n + 1) = phi (T A (n / 2))` if `n` is even,
  `tensorV (phi (T A (n / 2)))` if `n` is odd; the three equations of (T0) are the theorems
  `T_zero`, `T_odd`, `T_even`.
* `tpow A : ℕ → DPLattice A` (`V^{⊗n} ⊗ A`) is `tpow A 0 = one A`,
  `tpow A (n + 1) = tensorV (tpow A n)` (`tpow_zero`, `tpow_succ`).
* The direct sum is C22's `Lemma35.dsum`; `ℤ_[2]` is Mathlib's `PadicInt 2`, with C20's instance
  `OddUnits ℤ_[2]`.
-/

@[expose] public section

noncomputable section

namespace Filt

open DPLattice WeylFilt Doubling LemmaW Cocycle Finset

/-! ### (T0) -/

section T0

variable (A : Type*) [CommRing A]

/-- (T0) the dance lattices `T : ℕ → DPLattice A` **[Φ]**: `T 0 = one A`,
`T (2l+1) = phi (T l)`, `T (2l+2) = tensorV (phi (T l))` (well-founded recursion, written as
`T (n + 1) = phi (T (n / 2))` for even `n` and `tensorV (phi (T (n / 2)))` for odd `n`). -/
def T [IsDomain A] [CharZero A] [OddUnits A] : ℕ → DPLattice A
  | 0 => one A
  | n + 1 => if n % 2 = 0 then phi (T (n / 2)) else tensorV (phi (T (n / 2)))
decreasing_by all_goals omega

/-- (T0) the tensor powers `tpow n = V^{⊗n} ⊗ A`: `tpow 0 = one A`,
`tpow (n+1) = tensorV (tpow n)`. -/
def tpow : ℕ → DPLattice A
  | 0 => one A
  | n + 1 => tensorV (tpow n)

/-- (T0) `tpow 0 = one A`. -/
theorem tpow_zero : tpow A 0 = one A := rfl

/-- (T0) `tpow (n+1) = tensorV (tpow n)`. -/
theorem tpow_succ (n : ℕ) : tpow A (n + 1) = tensorV (tpow A n) := rfl

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- (T0) `T 0 = one A`. -/
theorem T_zero : T A 0 = one A := by rw [T]

/-- (T0) `T (2l+1) = phi (T l)`. -/
theorem T_odd (l : ℕ) : T A (2 * l + 1) = phi (T A l) := by
  rw [T, if_pos (by omega), show 2 * l / 2 = l by omega]

/-- (T0) `T (2l+2) = tensorV (phi (T l))`. -/
theorem T_even (l : ℕ) : T A (2 * l + 2) = tensorV (phi (T A l)) := by
  rw [show 2 * l + 2 = (2 * l + 1) + 1 by omega, T, if_neg (by omega),
    show (2 * l + 1) / 2 = l by omega]

/-- (T0) the defining equations of the dance lattices and of the tensor powers:
`T 0 = one A`, `T (2l+1) = phi (T l)`, `T (2l+2) = tensorV (phi (T l))`, `tpow 0 = one A`,
`tpow (n+1) = tensorV (tpow n)`. -/
theorem T0 : T A 0 = one A ∧ (∀ l, T A (2 * l + 1) = phi (T A l)) ∧
    (∀ l, T A (2 * l + 2) = tensorV (phi (T A l))) ∧ tpow A 0 = one A ∧
    (∀ n, tpow A (n + 1) = tensorV (tpow A n)) :=
  ⟨T_zero A, T_odd A, T_even A, tpow_zero A, tpow_succ A⟩

end T0

/-! ### (T1), (T2), (T3) -/

variable {A : Type*} [CommRing A]

/-- (T2) **[char 0]** for every `n`: `HasDeltaFilt (tpow n)` and `HasNablaFilt (tpow n)`. -/
theorem T2 [IsDomain A] [CharZero A] (n : ℕ) :
    HasDeltaFilt (tpow A n) ∧ HasNablaFilt (tpow A n) := by
  induction n with
  | zero => exact ⟨I2_delta_one, I2_nabla_one⟩
  | succ n ih => exact ⟨V1_delta ih.1, V1_nabla ih.2⟩

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- (T1) **[Φ]** for every `λ`: `HasDeltaFilt (T λ)` and `HasNablaFilt (T λ)`. -/
theorem T1 (l : ℕ) : HasDeltaFilt (T A l) ∧ HasNablaFilt (T A l) := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' l
    · rcases k with _ | k
      · rw [T_zero]; exact ⟨I2_delta_one, I2_nabla_one⟩
      · have h := ih k (by omega)
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, T_even]
        exact ⟨V1_delta (V2_delta h.1), V1_nabla (V2_nabla h.2)⟩
    · have h := ih k (by omega)
      rw [T_odd]
      exact ⟨V2_delta h.1, V2_nabla h.2⟩

/-- (T3) **[Φ]** for every DP-lattice `N` with `HasDeltaFilt N` and `HasNablaFilt N`, the two
lattices of C24 (Lemma 3.5, second sentence), `tensorV (tensorV (phi N))` and
`dsum (dsum (phi N) (phi N)) (phi (tensorV N))`, both have a `Δ`-filtration and a
`∇`-filtration. -/
theorem T3 {N : DPLattice A} (hΔ : HasDeltaFilt N) (hN : HasNablaFilt N) :
    (HasDeltaFilt (tensorV (tensorV (phi N))) ∧ HasNablaFilt (tensorV (tensorV (phi N)))) ∧
    (HasDeltaFilt (Lemma35.dsum (Lemma35.dsum (phi N) (phi N)) (phi (tensorV N))) ∧
      HasNablaFilt (Lemma35.dsum (Lemma35.dsum (phi N) (phi N)) (phi (tensorV N)))) :=
  ⟨⟨V1_delta (V1_delta (V2_delta hΔ)), V1_nabla (V1_nabla (V2_nabla hN))⟩,
    ⟨E3_delta (E3_delta (V2_delta hΔ) (V2_delta hΔ)) (V2_delta (V1_delta hΔ)),
      E3_nabla (E3_nabla (V2_nabla hN) (V2_nabla hN)) (V2_nabla (V1_nabla hN))⟩⟩

/-- (T3) in particular for `N = T l`, every `l`. -/
theorem T3_T (l : ℕ) :
    (HasDeltaFilt (tensorV (tensorV (phi (T A l)))) ∧
      HasNablaFilt (tensorV (tensorV (phi (T A l))))) ∧
    (HasDeltaFilt (Lemma35.dsum (Lemma35.dsum (phi (T A l)) (phi (T A l)))
        (phi (tensorV (T A l)))) ∧
      HasNablaFilt (Lemma35.dsum (Lemma35.dsum (phi (T A l)) (phi (T A l)))
        (phi (tensorV (T A l))))) :=
  T3 (T1 l).1 (T1 l).2

/-! ### Part Z -/

/-- (Z1) **The case of the paper**: (T1), (T2), (T3) for `A = ℤ_[2]` (Mathlib's `PadicInt 2`,
with C20's instance `OddUnits ℤ_[2]`). -/
theorem Z1 :
    (∀ l, HasDeltaFilt (T ℤ_[2] l) ∧ HasNablaFilt (T ℤ_[2] l)) ∧
    (∀ n, HasDeltaFilt (tpow ℤ_[2] n) ∧ HasNablaFilt (tpow ℤ_[2] n)) ∧
    (∀ N : DPLattice ℤ_[2], HasDeltaFilt N → HasNablaFilt N →
      (HasDeltaFilt (tensorV (tensorV (phi N))) ∧ HasNablaFilt (tensorV (tensorV (phi N)))) ∧
      (HasDeltaFilt (Lemma35.dsum (Lemma35.dsum (phi N) (phi N)) (phi (tensorV N))) ∧
        HasNablaFilt (Lemma35.dsum (Lemma35.dsum (phi N) (phi N)) (phi (tensorV N))))) :=
  ⟨T1, T2, fun _ hΔ hN => T3 hΔ hN⟩

end Filt
