module

public import Mathlib

/-!
# `C18_divided_power_lattices_and_the_dictionary.md`: Setting

Encodings (namespace `DPLattice`), for a commutative ring `A`:

* A *DP-lattice* `M : DPLattice A` (Setting, "Divided-power lattice") consists of a finite type
  `M.ι : Type` with decidable equality (the basis), a weight `M.wt : M.ι → ℤ`, and two families
  `M.Fd M.Ed : ℕ → Module.End A (M.ι → A)` (`F^{(r)}` and `E^{(s)}`) acting on the module
  `M.ι → A`, whose basis vectors are `δ_i = Pi.single i 1`. The axioms (W), (P0), (P1), (K) of the
  file are bundled in the field `M.isDP : IsDP M.wt M.Fd M.Ed`; the predicate `IsDP` is also used
  on raw data, before it is packaged as a lattice.
* (W) "`F^{(r)} δ_i` is a combination of the `δ_j` with `wt j = wt i − 2r`" is encoded as
  "every coordinate `j` with `wt j ≠ wt i − 2r` of `F^{(r)} δ_i` vanishes" (the basis is finite, so
  this is the same); similarly for `E^{(r)}` with `wt i + 2r`.
* Binomial coefficients `C(a, b)` with `a ∈ ℤ` are Mathlib's `Ring.choose a b : ℤ`, cast to `A`.
* `H M` is the diagonal operator `H δ_i = wt i · δ_i`, i.e. `(H f) i = wt i * f i`.
* A morphism (`Hom M N`) is an `A`-linear map commuting with every `F^{(r)}`, every `E^{(s)}` and
  `H`.
* `DataEquiv M N e` ("equal data under the bijection `e : M.ι ≃ N.ι`", used in (T5)) says that
  `e` preserves weights and that `F^{(r)}`, `E^{(s)}` of `N` are those of `M` transported along
  `e` (on functions: `N.Fd r (f ∘ e.symm) = (M.Fd r f) ∘ e.symm`).
-/

@[expose] public section

noncomputable section

namespace DPLattice

open Finset

variable {A : Type*} [CommRing A]

/-- Setting: the diagonal operator `H δ_i := wt i · δ_i` attached to a weight function. -/
def Hop {ι : Type*} (wt : ι → ℤ) : Module.End A (ι → A) where
  toFun f i := (wt i : A) * f i
  map_add' f g := by funext i; simp [mul_add]
  map_smul' c f := by funext i; simp; ring

@[simp] lemma Hop_apply {ι : Type*} (wt : ι → ℤ) (f : ι → A) (i : ι) :
    Hop (A := A) wt f i = (wt i : A) * f i := rfl

/-- Setting: the axioms (W), (P0), (P1), (K) of a DP-lattice, for raw data
`(ι, wt, F^{(·)}, E^{(·)})`, with `δ_i = Pi.single i 1`. -/
structure IsDP {ι : Type*} [DecidableEq ι] (wt : ι → ℤ) (Fd Ed : ℕ → Module.End A (ι → A)) : Prop where
  /-- (W) for `F`: `F^{(r)} δ_i` is a combination of the `δ_j` with `wt j = wt i − 2r`. -/
  W_F : ∀ (i : ι) (r : ℕ) (j : ι), wt j ≠ wt i - 2 * r → Fd r (Pi.single i 1) j = 0
  /-- (W) for `E`: `E^{(r)} δ_i` is a combination of the `δ_j` with `wt j = wt i + 2r`. -/
  W_E : ∀ (i : ι) (r : ℕ) (j : ι), wt j ≠ wt i + 2 * r → Ed r (Pi.single i 1) j = 0
  /-- (P0): `F^{(0)} = 1`. -/
  P0_F : Fd 0 = 1
  /-- (P0): `E^{(0)} = 1`. -/
  P0_E : Ed 0 = 1
  /-- (P1): `F^{(a)} ∘ F^{(b)} = C(a + b, a) · F^{(a+b)}`. -/
  P1_F : ∀ a b : ℕ, Fd a ∘ₗ Fd b = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • Fd (a + b)
  /-- (P1): `E^{(a)} ∘ E^{(b)} = C(a + b, a) · E^{(a+b)}`. -/
  P1_E : ∀ a b : ℕ, Ed a ∘ₗ Ed b = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • Ed (a + b)
  /-- (K), Kostant's formula on a basis vector:
  `E^{(s)} F^{(r)} δ_i = Σ_{j=0}^{min(r,s)} C(wt i + s − r, j) · F^{(r−j)} E^{(s−j)} δ_i`. -/
  K : ∀ (i : ι) (r s : ℕ), Ed s (Fd r (Pi.single i 1)) =
    ∑ j ∈ range (min r s + 1),
      ((Ring.choose (wt i + s - r) j : ℤ) : A) • Fd (r - j) (Ed (s - j) (Pi.single i 1))

/-- Setting: a divided-power lattice (DP-lattice) over `A`: a finite basis `ι` with decidable
equality, a weight `wt : ι → ℤ`, two families `Fd r = F^{(r)}`, `Ed s = E^{(s)}` of endomorphisms
of `M = ι → A`, satisfying (W), (P0), (P1) and Kostant's formula (K) (the field `isDP`). -/
structure _root_.DPLattice (A : Type*) [CommRing A] where
  /-- Setting: the basis -/
  ι : Type
  [fintype : Fintype ι]
  [decEq : DecidableEq ι]
  /-- Setting: the weight of a basis vector -/
  wt : ι → ℤ
  /-- Setting: the divided powers `F^{(r)}` -/
  Fd : ℕ → Module.End A (ι → A)
  /-- Setting: the divided powers `E^{(s)}` -/
  Ed : ℕ → Module.End A (ι → A)
  /-- the axioms (W), (P0), (P1), (K) -/
  isDP : IsDP wt Fd Ed

attribute [instance] DPLattice.fintype DPLattice.decEq

/-- Setting: the operator `H` of a DP-lattice, `H δ_i = wt i · δ_i`. -/
abbrev H (M : DPLattice A) : Module.End A (M.ι → A) := Hop M.wt

/-- Setting: a morphism of DP-lattices, an `A`-linear map commuting with every `F^{(r)}`, every
`E^{(s)}` and with `H`. -/
structure Hom (M N : DPLattice A) where
  /-- Setting: the underlying linear map -/
  toLin : (M.ι → A) →ₗ[A] (N.ι → A)
  comm_F : ∀ r, toLin ∘ₗ M.Fd r = N.Fd r ∘ₗ toLin
  comm_E : ∀ s, toLin ∘ₗ M.Ed s = N.Ed s ∘ₗ toLin
  comm_H : toLin ∘ₗ H M = H N ∘ₗ toLin

/-- (T5) "equal data under a bijection `e : M.ι ≃ N.ι`": weights correspond, and `F^{(r)}`,
`E^{(s)}` of `N` are those of `M` transported along `e`. -/
structure DataEquiv (M N : DPLattice A) (e : M.ι ≃ N.ι) : Prop where
  wt_eq : ∀ i, N.wt (e i) = M.wt i
  Fd_eq : ∀ r (f : M.ι → A), N.Fd r (f ∘ e.symm) = (M.Fd r f) ∘ e.symm
  Ed_eq : ∀ r (f : M.ι → A), N.Ed r (f ∘ e.symm) = (M.Ed r f) ∘ e.symm

/-! ### Weight vectors -/

/-- Setting, (W) (auxiliary): a vector `v` is of weight `w`: its coordinates outside `{wt = w}` vanish. -/
def InWt {ι : Type*} (wt : ι → ℤ) (w : ℤ) (v : ι → A) : Prop := ∀ j, wt j ≠ w → v j = 0

lemma inWt_single {ι : Type*} [DecidableEq ι] (wt : ι → ℤ) (i : ι) :
    InWt wt (wt i) (Pi.single i (1 : A)) := by
  intro j hj
  have : j ≠ i := fun h => hj (h ▸ rfl)
  simp [this]

lemma inWt_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ}
    (T : Module.End A (ι → A)) (d : ℤ)
    (hT : ∀ i j, wt j ≠ wt i + d → T (Pi.single i (1 : A)) j = 0) {w : ℤ} {v : ι → A}
    (hv : InWt wt w v) : InWt wt (w + d) (T v) := by
  intro j hj
  have hv' : v = ∑ i, v i • (Pi.single i (1 : A) : ι → A) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [hv', map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : wt i = w
  · rw [hT i j (by rw [hi]; exact hj), mul_zero]
  · rw [hv i hi, zero_mul]

lemma IsDP.inWt_Fd {ι : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ}
    {Fd Ed : ℕ → Module.End A (ι → A)} (h : IsDP wt Fd Ed) (r : ℕ) {w : ℤ} {v : ι → A}
    (hv : InWt wt w v) : InWt wt (w - 2 * r) (Fd r v) := by
  have := inWt_of_basis (Fd r) (-(2 * r)) (fun i j hj => h.W_F i r j (by omega)) hv
  simpa [sub_eq_add_neg] using this

lemma IsDP.inWt_Ed {ι : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ}
    {Fd Ed : ℕ → Module.End A (ι → A)} (h : IsDP wt Fd Ed) (r : ℕ) {w : ℤ} {v : ι → A}
    (hv : InWt wt w v) : InWt wt (w + 2 * r) (Ed r v) :=
  inWt_of_basis (Ed r) (2 * r) (fun i j hj => h.W_E i r j hj) hv

/-! ### Transfer along a surjective intertwiner -/

lemma ext_single {ι N : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup N] [Module A N]
    {f g : (ι → A) →ₗ[A] N} (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g :=
  (Pi.basisFun A ι).ext fun i => by simpa using h i

/-- (T4, auxiliary) If `φ : (ι → A) → (κ → A)` intertwines the divided powers of a DP-lattice with raw data on
`κ`, and every basis vector of `κ` is the image of a basis vector of the same weight, then the
raw data satisfy (P0), (P1), (K); with (W) they form a DP-lattice. -/
lemma IsDP.of_surj {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {wt : ι → ℤ} {Fd Ed : ℕ → Module.End A (ι → A)} (h : IsDP wt Fd Ed)
    {wt' : κ → ℤ} {Fd' Ed' : ℕ → Module.End A (κ → A)}
    (hWF : ∀ (i : κ) (r : ℕ) (j : κ), wt' j ≠ wt' i - 2 * r → Fd' r (Pi.single i 1) j = 0)
    (hWE : ∀ (i : κ) (r : ℕ) (j : κ), wt' j ≠ wt' i + 2 * r → Ed' r (Pi.single i 1) j = 0)
    (φ : (ι → A) →ₗ[A] (κ → A)) (hF : ∀ r, φ ∘ₗ Fd r = Fd' r ∘ₗ φ)
    (hE : ∀ r, φ ∘ₗ Ed r = Ed' r ∘ₗ φ)
    (hsurj : ∀ k, ∃ i, φ (Pi.single i 1) = Pi.single k 1 ∧ wt i = wt' k) :
    IsDP wt' Fd' Ed' := by
  have hF' : ∀ r v, φ (Fd r v) = Fd' r (φ v) := fun r v => LinearMap.congr_fun (hF r) v
  have hE' : ∀ r v, φ (Ed r v) = Ed' r (φ v) := fun r v => LinearMap.congr_fun (hE r) v
  refine ⟨hWF, hWE, ?_, ?_, ?_, ?_, ?_⟩
  · refine ext_single fun k => ?_
    obtain ⟨i, hi, -⟩ := hsurj k
    rw [← hi, ← hF', h.P0_F]; rfl
  · refine ext_single fun k => ?_
    obtain ⟨i, hi, -⟩ := hsurj k
    rw [← hi, ← hE', h.P0_E]; rfl
  · intro a b
    refine ext_single fun k => ?_
    obtain ⟨i, hi, -⟩ := hsurj k
    rw [← hi, LinearMap.comp_apply, ← hF', ← hF', LinearMap.smul_apply, ← hF', ← map_smul,
      ← LinearMap.smul_apply, ← h.P1_F]
    rfl
  · intro a b
    refine ext_single fun k => ?_
    obtain ⟨i, hi, -⟩ := hsurj k
    rw [← hi, LinearMap.comp_apply, ← hE', ← hE', LinearMap.smul_apply, ← hE', ← map_smul,
      ← LinearMap.smul_apply, ← h.P1_E]
    rfl
  · intro k r s
    obtain ⟨i, hi, hw⟩ := hsurj k
    rw [← hi, ← hF', ← hE', h.K, map_sum, ← hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hF', hE']

end DPLattice
