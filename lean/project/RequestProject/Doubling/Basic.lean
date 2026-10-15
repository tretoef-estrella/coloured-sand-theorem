module

public import RequestProject.WeylFilt.Basic

/-!
# `C20_the_doubling_functor.md`: Setting

Encodings (namespace `Doubling`), reusing C18 (namespace `DPLattice`: `DPLattice`, `IsDP`, `H`,
`Hom`, `one`, `V`, `bvec`, `delta`, `nabla`, the (T5) lemmas) and C19 (namespace `WeylFilt`:
`Hom.id`, `Hom.comp`, `ShortExact`):

* The ring: `A` is a commutative ring with `[IsDomain A] [CharZero A]` and the class
  `[OddUnits A]`, whose only field is exactly the hypothesis
  `hodd : ∀ k : ℕ, IsUnit ((2 * k + 1 : ℕ) : A)` of the file ("every odd integer is a unit").
  `ℤ_[2]` is an instance (`padicInt_two_hodd`, and the instance `OddUnits ℤ_[2]`).
* `k!!` is Mathlib's `Nat.doubleFactorial k` (notation `k‼`), and `⅟(2s−1)!!` is
  `dfi s := Ring.inverse ((2 s − 1)‼ : A)` (the inverse in `A`, a unit by `hodd`); for `s = 0`
  this is `⅟(−1)!! = 1` (the natural subtraction gives `(0)‼ = 1`), and `⅟(2s+1)!! = dfi (s+1)`.
* For a DP-lattice `N`, `F := N.Fd 1`, `E := N.Ed 1`, and for a finite set `S` of indices and
  integers `c j`, `piOp N S c = Π_{c}` is the operator `∏_{j ∈ S} (4FE + c_j)`, encoded as the
  polynomial `∏_{j ∈ S} (4X + c_j)` evaluated at the operator `F ∘ E` (so the factors commute and
  the empty product is the identity). The lists of the file are `S = range s` (`0 ≤ j < s`),
  `S = range (s + 1)` (`0 ≤ j ≤ s`) and `S = Icc 1 s` (`1 ≤ j ≤ s`); `cE w s j` is
  `(w + 2s + 1)² − (w + 2j)²`.
-/

@[expose] public section

noncomputable section

namespace Doubling

open DPLattice Finset Polynomial

open scoped Nat

/-- Setting: every odd integer is a unit of `A` (the hypothesis
`hodd : ∀ k : ℕ, IsUnit ((2 * k + 1 : ℕ) : A)` of the file, packaged as a class). -/
class OddUnits (A : Type*) [CommRing A] : Prop where
  /-- Setting: `hodd`. -/
  hodd : ∀ k : ℕ, IsUnit ((2 * k + 1 : ℕ) : A)

/-- Setting: the instance check, `ℤ_[2]` satisfies `hodd`. -/
theorem padicInt_two_hodd : ∀ k : ℕ, IsUnit ((2 * k + 1 : ℕ) : ℤ_[2]) := by
  intro k
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff, Nat.coprime_two_left]
  exact odd_two_mul_add_one k

/-- Setting: the instance check, `ℤ_[2]` is an admissible ring (domain, characteristic zero,
odd integers are units). -/
instance : OddUnits ℤ_[2] := ⟨padicInt_two_hodd⟩

example : IsDomain ℤ_[2] := inferInstance
example : CharZero ℤ_[2] := inferInstance

variable {A : Type*} [CommRing A]

/-- Setting: `⅟(2s−1)!!`, the inverse in `A` of the odd double factorial `(2s−1)!!`
(`(−1)!! = 1`). -/
def dfi (s : ℕ) : A := Ring.inverse (((2 * s - 1)‼ : ℕ) : A)

/-- Setting: `Π_{c} = ∏_{j ∈ S} (4FE + c_j)` as an operator on the DP-lattice `N`
(`F = N.Fd 1`, `E = N.Ed 1`). -/
def piOp (N : DPLattice A) (S : Finset ℕ) (c : ℕ → ℤ) : Module.End A (N.ι → A) :=
  aeval (N.Fd 1 * N.Ed 1) (∏ j ∈ S, (4 * X + C ((c j : ℤ) : A)))

/-- Setting: the integers `c_j = (w + 2s + 1)² − (w + 2j)²` of the `E`-formulas. -/
def cE (w : ℤ) (s : ℕ) (j : ℕ) : ℤ := (w + 2 * s + 1) ^ 2 - (w + 2 * j) ^ 2

/-! ### Odd double factorials -/

@[simp] lemma dfi_zero : dfi (A := A) 0 = 1 := by simp [dfi]

section odd

variable [OddUnits A]

lemma isUnit_df (s : ℕ) : IsUnit (((2 * s - 1)‼ : ℕ) : A) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rcases s with _ | s
    · simp
    · have : 2 * (s + 1 + 1) - 1 = (2 * s + 1) + 2 := by omega
      rw [this, Nat.doubleFactorial_add_two, Nat.cast_mul]
      have h2 : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
      rw [h2] at ih
      refine IsUnit.mul ?_ ih
      have := OddUnits.hodd (A := A) (s + 1)
      convert this using 2

lemma dfi_mul (s : ℕ) : dfi (A := A) s * (((2 * s - 1)‼ : ℕ) : A) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_df s)

lemma mul_dfi (s : ℕ) : (((2 * s - 1)‼ : ℕ) : A) * dfi s = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_df s)

/-- `(2s+1) · ⅟(2s+1)!! = ⅟(2s−1)!!`. -/
lemma odd_mul_dfi_succ (s : ℕ) : ((2 * s + 1 : ℕ) : A) * dfi (s + 1) = dfi s := by
  have key : (((2 * (s + 1) - 1)‼ : ℕ) : A) = ((2 * s + 1 : ℕ) : A) * (((2 * s - 1)‼ : ℕ) : A) := by
    rcases s with _ | s
    · simp
    · have : 2 * (s + 1 + 1) - 1 = (2 * s + 1) + 2 := by omega
      rw [this, Nat.doubleFactorial_add_two, Nat.cast_mul]
      have h2 : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
      rw [h2]; push_cast; ring
  have h1 := dfi_mul (A := A) (s + 1)
  rw [key] at h1
  calc ((2 * s + 1 : ℕ) : A) * dfi (s + 1)
      = ((2 * s + 1 : ℕ) : A) * dfi (s + 1) * ((((2 * s - 1)‼ : ℕ) : A) * dfi s) := by
        rw [mul_dfi, mul_one]
    _ = (dfi (s + 1) * (((2 * s + 1 : ℕ) : A) * (((2 * s - 1)‼ : ℕ) : A))) * dfi s := by ring
    _ = dfi s := by rw [h1, one_mul]

end odd

/-! ### Torsion-freeness -/

lemma cancel_smul {A : Type*} [CommRing A] [IsDomain A] {M : Type*} [AddCommGroup M] [Module A M]
    [Module.IsTorsionFree A M] {c : A} (hc : c ≠ 0) {x y : M} (h : c • x = c • y) : x = y :=
  smul_right_injective M hc h

lemma natCast_succ_ne_zero {A : Type*} [CommRing A] [CharZero A] (n : ℕ) : ((n : A) + 1) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero n

/-! ### Weight vectors -/

section weights

variable {ι : Type*}

lemma Hop_of_inWt {wt : ι → ℤ} {μ : ℤ} {y : ι → A} (hy : InWt wt μ y) :
    Hop wt y = ((μ : ℤ) : A) • y := by
  funext j
  simp only [Hop_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : wt j = μ
  · rw [h]
  · rw [hy j h, mul_zero, mul_zero]

lemma inWt_add {wt : ι → ℤ} {μ : ℤ} {x y : ι → A} (hx : InWt wt μ x) (hy : InWt wt μ y) :
    InWt wt μ (x + y) := fun j hj => by simp [hx j hj, hy j hj]

lemma inWt_smul {wt : ι → ℤ} {μ : ℤ} (c : A) {x : ι → A} (hx : InWt wt μ x) :
    InWt wt μ (c • x) := fun j hj => by simp [hx j hj]

lemma inWt_zero {wt : ι → ℤ} {μ : ℤ} : InWt wt μ (0 : ι → A) := fun _ _ => rfl

lemma inWt_congr {wt : ι → ℤ} {μ ν : ℤ} (h : μ = ν) {x : ι → A} (hx : InWt wt μ x) :
    InWt wt ν x := h ▸ hx

/-- Decomposition of a vector of weight `w` along the basis vectors of weight `w`. -/
lemma eq_on_inWt [Fintype ι] [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module A M] {wt : ι → ℤ} {w : ℤ}
    (T U : (ι → A) →ₗ[A] M) (h : ∀ i, wt i = w → T (Pi.single i 1) = U (Pi.single i 1))
    {x : ι → A} (hx : InWt wt w x) : T x = U x := by
  have hx' : x = ∑ i, x i • (Pi.single i (1 : A) : ι → A) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [hx', map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : wt i = w
  · rw [map_smul, map_smul, h i hi]
  · rw [hx i hi, zero_smul, map_zero, map_zero]

end weights

end Doubling
