module

public import Mathlib

/-!
# Antitonic fits: setting, definition, existence and uniqueness

This file formalizes the *Setting* section of `C1_antitonic_fits.md` and statement **(0)**
(existence and uniqueness of the antitonic fit).

## Encoding of finite sequences

* A finite sequence of length `N` (positions `0, …, N-1`) is encoded as a function
  `x : ℕ → ℝ` together with the length `N`.  Every notion below (non-increasing, distance,
  fit, level sets, cuts, …) only looks at the values `x 0, …, x (N-1)`; values at positions
  `≥ N` are irrelevant.  Equality of two sequences of length `N` is therefore written
  `∀ j < N, u j = v j`.  The fit `fit N x` is normalised to be `0` at positions `≥ N`.
* The prefix `x_{<b}` is encoded as the *same* function `x`, used with length `b`
  (e.g. `fit b x` is `fit(x_{<b})`).
* The suffix `x_{≥b}` is encoded as `shift b x = fun j => x (b + j)`, used with length `N - b`
  (e.g. `fit (N - b) (shift b x)` is `fit(x_{≥b})`).
* The concatenation `[u, v]` of a sequence `u` of length `M` with a sequence `v` is
  `concat M u v = fun j => if j < M then u j else v (j - M)`.
* The mirror-negative `u^*` of a sequence `u` of length `M` is
  `mirror M u = fun j => -u (M - 1 - j)`; `x` is antisymmetric of length `N` iff
  `IsAntisymm N x`, i.e. `x (N - 1 - j) = -x j` for all `j < N`.
* Sequences of integers are functions `ℕ → ℤ`; they are viewed as real sequences through
  `toR` (defined in `RequestProject/AntitonicFit/IntegerFit.lean`).
* Sums of sequences (`x + δ`) and entrywise `max`/`min` are pointwise operations on functions.
-/

@[expose] public section

namespace AntitonicFit

open Finset

/-- *Setting* of `C1_antitonic_fits.md`: a sequence `z` of length `N` is **non-increasing**
if `z_i ≥ z_{i+1}` for every `i` with `i + 1 < N`. -/
def NonIncr (N : ℕ) (z : ℕ → ℝ) : Prop := ∀ i, i + 1 < N → z (i + 1) ≤ z i

/-- *Setting* of `C1_antitonic_fits.md`: the squared Euclidean distance
`‖x − z‖² = Σ_{j<N} (x_j − z_j)²` between two sequences of length `N`. -/
def sqDist (N : ℕ) (x z : ℕ → ℝ) : ℝ := ∑ j ∈ range N, (x j - z j) ^ 2

/-- *Definition (antitonic fit)* of `C1_antitonic_fits.md`: `z` is a non-increasing minimizer
of `‖x − z‖²` among all non-increasing sequences of length `N`. -/
def IsFit (N : ℕ) (x z : ℕ → ℝ) : Prop :=
  NonIncr N z ∧ ∀ y, NonIncr N y → sqDist N x z ≤ sqDist N x y

/-- *Setting* of `C1_antitonic_fits.md`: the suffix `x_{≥b}`, as the function
`j ↦ x (b + j)` (to be used with length `N - b`). -/
def shift {α : Type*} (b : ℕ) (x : ℕ → α) : ℕ → α := fun j => x (b + j)

/-- *Setting* of `C1_antitonic_fits.md`: the concatenation `[u, v]` of a sequence `u` of
length `M` with a sequence `v`. -/
def concat {α : Type*} (M : ℕ) (u v : ℕ → α) : ℕ → α :=
  fun j => if j < M then u j else v (j - M)

/-- *Definition (antisymmetric)* of `C1_antitonic_fits.md`: the mirror-negative
`u^*_j = −u_{M−1−j}` of a sequence `u` of length `M`. -/
def mirror {α : Type*} [Neg α] (M : ℕ) (u : ℕ → α) : ℕ → α := fun j => -u (M - 1 - j)

/-- *Definition (antisymmetric)* of `C1_antitonic_fits.md`: `x` of length `N` is antisymmetric
if `x_{N−1−j} = −x_j` for every `j < N`. -/
def IsAntisymm {α : Type*} [Neg α] (N : ℕ) (x : ℕ → α) : Prop :=
  ∀ j < N, x (N - 1 - j) = -x j

variable {N : ℕ} {x x' z z' y : ℕ → ℝ}

theorem NonIncr.anti (h : NonIncr N z) {i j : ℕ} (hij : i ≤ j) (hj : j < N) : z j ≤ z i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (h k hj).trans (ih (by omega))

theorem NonIncr.congr (h : NonIncr N z) (he : ∀ j < N, z j = z' j) : NonIncr N z' := by
  intro i hi
  rw [← he i (by omega), ← he (i + 1) hi]
  exact h i hi

theorem NonIncr.mono {M : ℕ} (h : NonIncr N z) (hM : M ≤ N) : NonIncr M z :=
  fun i hi => h i (by omega)

theorem sqDist_congr (hx : ∀ j < N, x j = x' j) (hz : ∀ j < N, z j = z' j) :
    sqDist N x z = sqDist N x' z' := by
  unfold sqDist
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [hx j hj, hz j hj]

theorem IsFit.congr (h : IsFit N x z) (hx : ∀ j < N, x j = x' j) (hz : ∀ j < N, z j = z' j) :
    IsFit N x' z' := by
  refine ⟨h.1.congr hz, fun y hy => ?_⟩
  rw [← sqDist_congr hx hz, ← sqDist_congr hx (fun _ _ => rfl)]
  exact h.2 y hy

lemma clip_sq {a b u v : ℝ} (hau : a ≤ u) (hub : u ≤ b) :
    (u - max a (min b v)) ^ 2 ≤ (u - v) ^ 2 := by
  rcases le_total v b with h | h
  · rw [min_eq_right h]
    rcases le_total a v with h' | h'
    · rw [max_eq_right h']
    · rw [max_eq_left h']; nlinarith
  · rw [min_eq_left h, max_eq_right (hau.trans hub)]; nlinarith

/-- Existence part of **(0)** in `C1_antitonic_fits.md`. -/
theorem exists_isFit (N : ℕ) (x : ℕ → ℝ) : ∃ z, IsFit N x z := by
  set B : ℝ := ∑ j ∈ range N, |x j| with hB
  have hxB : ∀ j < N, |x j| ≤ B := fun j hj =>
    single_le_sum (f := fun j => |x j|) (fun i _ => abs_nonneg _) (mem_range.2 hj)
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
  let K : Set (Fin N → ℝ) := {z | ∀ i j : Fin N, i ≤ j → z j ≤ z i} ∩
    Set.univ.pi (fun _ => Set.Icc (-B) B)
  have hKc : IsCompact K := by
    apply (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_left
    have : {z : Fin N → ℝ | ∀ i j : Fin N, i ≤ j → z j ≤ z i} =
        ⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {z | z j ≤ z i} := by ext; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply j) (continuous_apply i)
  have hKn : K.Nonempty := ⟨0, by simp [K, Pi.le_def, hB0]⟩
  obtain ⟨z0, hz0K, hmin⟩ := hKc.exists_isMinOn hKn
    (f := fun z : Fin N → ℝ => ∑ j : Fin N, (x j - z j) ^ 2) (by fun_prop)
  refine ⟨fun j => if h : j < N then z0 ⟨j, h⟩ else 0, ?_, ?_⟩
  · intro i hi
    simp only [dif_pos hi, dif_pos (show i < N by omega)]
    exact hz0K.1 ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp [Fin.le_def])
  · intro y hy
    let y' : Fin N → ℝ := fun j => max (-B) (min B (y j))
    have hy'K : y' ∈ K := by
      refine ⟨fun i j hij => ?_, fun j _ => ?_⟩
      · have : y j ≤ y i := hy.anti (Fin.le_def.1 hij) j.2
        simp only [y']
        exact max_le_max le_rfl (min_le_min le_rfl this)
      · simp only [y', Set.mem_Icc]
        exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    have h1 := isMinOn_iff.mp hmin y' hy'K
    calc sqDist N x (fun j => if h : j < N then z0 ⟨j, h⟩ else 0)
        = ∑ j : Fin N, (x j - z0 j) ^ 2 := by rw [sqDist, sum_range]; simp
      _ ≤ ∑ j : Fin N, (x j - y' j) ^ 2 := h1
      _ ≤ ∑ j : Fin N, (x j - y j) ^ 2 := by
          refine sum_le_sum fun j _ => ?_
          have := hxB j j.2
          exact clip_sq (by linarith [neg_abs_le (x j)]) (by linarith [le_abs_self (x j)])
      _ = sqDist N x y := by rw [sqDist, sum_range]

/-- *Definition (antitonic fit)* of `C1_antitonic_fits.md`: `fit N x` is the (unique, by **(0)**)
non-increasing minimizer of `‖x − z‖²`, chosen among the minimizers given by `exists_isFit`
and normalised to `0` at positions `≥ N`.  It is defined by its minimizing property, not by an
algorithm. -/
noncomputable def fit (N : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun j => if j < N then (exists_isFit N x).choose j else 0

theorem fit_isFit (N : ℕ) (x : ℕ → ℝ) : IsFit N x (fit N x) :=
  (exists_isFit N x).choose_spec.congr (fun _ _ => rfl) (fun j hj => by simp [fit, hj])

theorem fit_of_le {j : ℕ} (hj : N ≤ j) : fit N x j = 0 := by
  simp [fit, show ¬ j < N by omega]

/-- First-order (variational) inequality for a minimizer. (Auxiliary result for Lemma 7.1 (necessity) and (0) (uniqueness) of `C1_antitonic_fits.md`.) -/
theorem IsFit.inner_le (hz : IsFit N x z) (hy : NonIncr N y) :
    ∑ j ∈ range N, (x j - z j) * (y j - z j) ≤ 0 := by
  set A := ∑ j ∈ range N, (x j - z j) * (y j - z j) with hA_def
  set C := ∑ j ∈ range N, (y j - z j) ^ 2 with hC_def
  by_contra hA
  push_neg at hA
  have hC : 0 ≤ C := sum_nonneg fun _ _ => sq_nonneg _
  set t := min 1 (A / (C + 1)) with ht_def
  have ht0 : 0 < t := lt_min one_pos (div_pos hA (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have hyt : NonIncr N (fun j => z j + t * (y j - z j)) := by
    intro i hi
    have h1 := hz.1 i hi
    have h2 := hy i hi
    simp only
    nlinarith
  have hexp : sqDist N x (fun j => z j + t * (y j - z j)) = sqDist N x z - 2 * t * A + t ^ 2 * C := by
    simp only [sqDist, hA_def, hC_def, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  have hle := hz.2 _ hyt
  rw [hexp] at hle
  have h2 : 2 * A ≤ t * C := by nlinarith
  have h3 : t * C ≤ A / (C + 1) * C := mul_le_mul_of_nonneg_right (min_le_right _ _) hC
  have h4 : A / (C + 1) * C < A := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Uniqueness part of **(0)** in `C1_antitonic_fits.md`. -/
theorem IsFit.unique (hz : IsFit N x z) (hz' : IsFit N x z') : ∀ j < N, z j = z' j := by
  have h1 := hz.inner_le hz'.1
  have h2 := hz'.inner_le hz.1
  have h3 : ∑ j ∈ range N, (z' j - z j) ^ 2 =
      ∑ j ∈ range N, (x j - z j) * (z' j - z j) + ∑ j ∈ range N, (x j - z' j) * (z j - z' j) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  have h4 : ∑ j ∈ range N, (z' j - z j) ^ 2 = 0 :=
    le_antisymm (by linarith) (sum_nonneg fun _ _ => sq_nonneg _)
  intro j hj
  have := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (z' j - z j))).1 h4 j (mem_range.2 hj)
  have : z' j - z j = 0 := by simpa using this
  linarith

/-- **(0)** of `C1_antitonic_fits.md` (existence and uniqueness): for every `x`, a non-increasing
minimizer of `‖x − z‖²` exists, and any two such minimizers agree on all positions `j < N`. -/
theorem existsUnique_fit (N : ℕ) (x : ℕ → ℝ) :
    (∃ z, IsFit N x z) ∧ ∀ z z', IsFit N x z → IsFit N x z' → ∀ j < N, z j = z' j :=
  ⟨exists_isFit N x, fun _ _ hz hz' => hz.unique hz'⟩

theorem fit_unique (hz : IsFit N x z) : ∀ j < N, fit N x j = z j :=
  (fit_isFit N x).unique hz

/-- `fit N x` only depends on the values of `x` at positions `< N`. (Auxiliary result for *Setting* (prefixes/suffixes) of `C1_antitonic_fits.md`.) -/
theorem fit_congr (hx : ∀ j < N, x j = x' j) : fit N x = fit N x' := by
  funext j
  by_cases hj : j < N
  · exact fit_unique ((fit_isFit N x').congr (fun i hi => (hx i hi).symm) (fun _ _ => rfl)) j hj
  · rw [fit_of_le (by omega), fit_of_le (by omega)]

theorem fit_nonIncr (N : ℕ) (x : ℕ → ℝ) : NonIncr N (fit N x) := (fit_isFit N x).1

end AntitonicFit
