module

public import RequestProject.Doubling.Basic

/-!
# `C20_the_doubling_functor.md`: divided powers from single operators (proof sketch of (A1))

This file contains the general fact used in the proof sketch of (A1): over a domain of
characteristic zero, if raw data `(ι, wt, F^{(·)}, E^{(·)})` satisfy (W), (P0), the recursions
`F^{(1)} F^{(r)} = (r+1) F^{(r+1)}`, `E^{(1)} E^{(r)} = (r+1) E^{(r+1)}` and the Lie relation
`[E, F] = H`, then they satisfy (P1) and Kostant's formula (K), i.e. they form a DP-lattice
(`isDP_of_rec`). It also contains the fact used in (D1), (D2): a linear map between DP-lattices
commuting with `F^{(1)}`, `E^{(1)}` and `H` commutes with every divided power (`homOfOne`).
-/

@[expose] public section

noncomputable section

namespace Doubling

open DPLattice Finset

variable {A : Type*} [CommRing A]

/-- A binomial identity: `(n+1) C(x, n+1) = (x − n) C(x, n)` in `ℤ`. -/
lemma choose_succ_mul' (x : ℤ) (n : ℕ) :
    ((n : ℤ) + 1) * Ring.choose x (n + 1) = (x - n) * Ring.choose x n := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose x (n + 1)
  have h2 := Ring.descPochhammer_eq_factorial_smul_choose x n
  rw [descPochhammer_succ_right, Polynomial.smeval_mul, h2] at h1
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, nsmul_eq_mul,
    npow_one, npow_zero, Nat.factorial_succ] at h1
  push_cast at h1
  have hf : ((n.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  apply mul_left_cancel₀ hf
  linear_combination h1.symm

/-- The divided powers extended by `0` to negative indices. -/
def Fz {ι : Type*} (Fd : ℕ → Module.End A (ι → A)) (k : ℤ) : Module.End A (ι → A) :=
  if k < 0 then 0 else Fd k.toNat

lemma Fz_natCast {ι : Type*} (Fd : ℕ → Module.End A (ι → A)) (n : ℕ) : Fz Fd n = Fd n := by
  simp [Fz]

lemma Fz_neg {ι : Type*} (Fd : ℕ → Module.End A (ι → A)) {k : ℤ} (hk : k < 0) : Fz Fd k = 0 := by
  simp [Fz, hk]

/-- Hypotheses of `isDP_of_rec`: (W), (P0), the recursions of the divided powers and the Lie
relation `[E, F] = H` for the raw data `(wt, Fd, Ed)`. -/
structure RecData {ι : Type*} [DecidableEq ι] (wt : ι → ℤ) (Fd Ed : ℕ → Module.End A (ι → A)) :
    Prop where
  W_F : ∀ (i : ι) (r : ℕ) (j : ι), wt j ≠ wt i - 2 * r → Fd r (Pi.single i 1) j = 0
  W_E : ∀ (i : ι) (r : ℕ) (j : ι), wt j ≠ wt i + 2 * r → Ed r (Pi.single i 1) j = 0
  P0_F : Fd 0 = 1
  P0_E : Ed 0 = 1
  rec_F : ∀ (r : ℕ) (x : ι → A), Fd 1 (Fd r x) = ((r : A) + 1) • Fd (r + 1) x
  rec_E : ∀ (r : ℕ) (x : ι → A), Ed 1 (Ed r x) = ((r : A) + 1) • Ed (r + 1) x
  lie : ∀ x : ι → A, Ed 1 (Fd 1 x) = Fd 1 (Ed 1 x) + Hop wt x

section rec

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ}
  {Fd Ed : ℕ → Module.End A (ι → A)}

lemma RecData.inWt_F (h : RecData wt Fd Ed) (r : ℕ) {w : ℤ} {v : ι → A} (hv : InWt wt w v) :
    InWt wt (w - 2 * r) (Fd r v) := by
  have := inWt_of_basis (Fd r) (-(2 * r)) (fun i j hj => h.W_F i r j (by omega)) hv
  simpa [sub_eq_add_neg] using this

lemma RecData.inWt_E (h : RecData wt Fd Ed) (r : ℕ) {w : ℤ} {v : ι → A} (hv : InWt wt w v) :
    InWt wt (w + 2 * r) (Ed r v) :=
  inWt_of_basis (Ed r) (2 * r) (fun i j hj => h.W_E i r j hj) hv

/-- `E F^{(n+1)} y = F^{(n+1)} E y + (μ − n) F^{(n)} y` for `y` of weight `μ`. -/
lemma RecData.EF [IsDomain A] [CharZero A] (h : RecData wt Fd Ed) (n : ℕ) {μ : ℤ} {y : ι → A} (hy : InWt wt μ y) :
    Ed 1 (Fd (n + 1) y) = Fd (n + 1) (Ed 1 y) + ((μ - n : ℤ) : A) • Fd n y := by
  induction n with
  | zero =>
    rw [h.lie, Hop_of_inWt hy, h.P0_F]; simp
  | succ n ih =>
    apply cancel_smul (natCast_succ_ne_zero (A := A) (n + 1))
    have hF := h.rec_F (n + 1)
    have hy1 := h.inWt_F (n + 1) hy
    rw [← map_smul, ← hF, h.lie, ih, Hop_of_inWt hy1, map_add, map_smul, h.rec_F, h.rec_F n]
    rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul]
    congr 2; push_cast; ring

/-- `E F^{(k)} y = F^{(k)} E y + (μ − k + 1) F^{(k−1)} y` for `y` of weight `μ`, `k ∈ ℤ`
(with `F^{(k)} = 0` for `k < 0`). -/
lemma RecData.EFz [IsDomain A] [CharZero A] (h : RecData wt Fd Ed) (k : ℤ) {μ : ℤ} {y : ι → A} (hy : InWt wt μ y) :
    Ed 1 (Fz Fd k y) = Fz Fd k (Ed 1 y) + ((μ - k + 1 : ℤ) : A) • Fz Fd (k - 1) y := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · rw [Fz_neg _ hk, Fz_neg _ (by omega)]; simp
  · rw [Fz_neg _ (by omega : (0:ℤ) - 1 < 0), show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, Fz_natCast,
      h.P0_F]; simp
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 1 := ⟨(k - 1).toNat, by omega⟩
    have e1 : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, Fz_natCast, show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring,
      Fz_natCast, h.EF n hy]
    congr 3; push_cast; ring

omit [Fintype ι] in
/-- `F F^{(k)} = (k+1) F^{(k+1)}` for `k ≥ -1`. -/
lemma RecData.F_Fz (h : RecData wt Fd Ed) (k : ℤ) (hk : -1 ≤ k) (x : ι → A) :
    Fd 1 (Fz Fd k x) = ((k + 1 : ℤ) : A) • Fz Fd (k + 1) x := by
  rcases eq_or_lt_of_le hk with rfl | hk
  · simp [Fz_neg]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, by omega⟩
    rw [Fz_natCast, h.rec_F, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, Fz_natCast]
    push_cast; rfl

/-- Kostant's formula in the extended form: `E^{(s)} F^{(r)} y = Σ_{j ≤ s} C(μ + s − r, j)
F^{(r−j)} E^{(s−j)} y`, for `y` of weight `μ`. -/
lemma RecData.K_ext [IsDomain A] [CharZero A] (h : RecData wt Fd Ed) (r s : ℕ) {μ : ℤ} {y : ι → A} (hy : InWt wt μ y) :
    Ed s (Fd r y) = ∑ j ∈ range (s + 1),
      ((Ring.choose (μ + s - r) j : ℤ) : A) • Fz Fd ((r : ℤ) - j) (Ed (s - j) y) := by
  induction s with
  | zero =>
    simp [h.P0_E, Fz_natCast]
  | succ s ih =>
    apply cancel_smul (natCast_succ_ne_zero (A := A) s)
    rw [← h.rec_E, ih, map_sum, Finset.smul_sum]
    set x : ℤ := μ + s - r with hx
    -- expand each term
    have hterm : ∀ j ∈ range (s + 1),
        Ed 1 (((Ring.choose x j : ℤ) : A) • Fz Fd ((r : ℤ) - j) (Ed (s - j) y)) =
        (((Ring.choose x j * ((s : ℤ) + 1 - j)) : ℤ) : A) •
            Fz Fd ((r : ℤ) - j) (Ed (s + 1 - j) y) +
        (((Ring.choose x j * (x + s - (j + 1 : ℕ) + 2)) : ℤ) : A) •
            Fz Fd ((r : ℤ) - (j + 1 : ℕ)) (Ed (s + 1 - (j + 1)) y) := by
      intro j hj
      have hj' : j ≤ s := Nat.lt_succ_iff.mp (mem_range.mp hj)
      rw [map_smul, h.EFz _ (h.inWt_E (s - j) hy), h.rec_E,
        show s - j + 1 = s + 1 - j by omega, show s + 1 - (j + 1) = s - j by omega, map_smul,
        smul_add, smul_smul, smul_smul, show (r : ℤ) - j - 1 = (r : ℤ) - (j + 1 : ℕ) by
          push_cast; ring]
      congr 2
      · push_cast [Nat.cast_sub hj']; ring
      · rw [hx]; push_cast [Nat.cast_sub hj']; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    -- the target
    set T : ℕ → ι → A := fun j => Fz Fd ((r : ℤ) - j) (Ed (s + 1 - j) y) with hT
    have hx1 : μ + ((s + 1 : ℕ) : ℤ) - r = x + 1 := by rw [hx]; push_cast; ring
    rw [hx1]
    have h1 : ∑ j ∈ range (s + 1),
        (((Ring.choose x j * ((s : ℤ) + 1 - j)) : ℤ) : A) • T j =
        ∑ j ∈ range (s + 1 + 1), (((Ring.choose x j * ((s : ℤ) + 1 - j)) : ℤ) : A) • T j := by
      rw [Finset.sum_range_succ _ (s + 1)]; push_cast; simp
    have h2 : ∑ j ∈ range (s + 1),
        (((Ring.choose x j * (x + s - (j + 1 : ℕ) + 2)) : ℤ) : A) • T (j + 1) =
        ∑ j ∈ range (s + 1 + 1), (((if j = 0 then 0 else
          Ring.choose x (j - 1) * (x + s - j + 2)) : ℤ) : A) • T j := by
      rw [Finset.sum_range_succ' _ (s + 1)]; simp
    simp only [hT] at h1 h2
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← add_smul]
    congr 1
    rcases j with _ | k
    · simp
    · simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero k)]
      have key := choose_succ_mul' x k
      have e := Ring.choose_succ_succ x k
      push_cast
      rw [e]
      have key' : ((k : A) + 1) * ((Ring.choose x (k + 1) : ℤ) : A) =
          ((x : A) - k) * ((Ring.choose x k : ℤ) : A) := by
        exact_mod_cast key
      push_cast
      linear_combination (-(1 : A)) * key'

end rec

end Doubling

namespace Doubling

open DPLattice Finset

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι] {wt : ι → ℤ}
  {Fd Ed : ℕ → Module.End A (ι → A)}

omit [Fintype ι] [DecidableEq ι] in
lemma RecData.P1_aux [IsDomain A] [CharZero A] (G : ℕ → Module.End A (ι → A)) (h0 : G 0 = 1)
    (hrec : ∀ (r : ℕ) (x : ι → A), G 1 (G r x) = ((r : A) + 1) • G (r + 1) x) (a b : ℕ) :
    G a ∘ₗ G b = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • G (a + b) := by
  induction a with
  | zero => simp [h0]; rfl
  | succ a ih =>
    refine LinearMap.ext fun x => ?_
    apply cancel_smul (natCast_succ_ne_zero (A := A) a)
    have hx := LinearMap.congr_fun ih x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hx ⊢
    rw [← hrec, hx, map_smul, hrec, smul_smul, smul_smul, choose_natAdd, choose_natAdd,
      show a + 1 + b = a + b + 1 by omega]
    congr 1
    have := Nat.add_one_mul_choose_eq (a + b) a
    have h' : ((a + b + 1 : ℕ) : A) * ((a + b).choose a : ℕ) =
        ((a + b + 1).choose (a + 1) : ℕ) * ((a + 1 : ℕ) : A) := by exact_mod_cast this
    push_cast at h' ⊢
    linear_combination h'

/-- (A1, proof sketch) Over a domain of characteristic zero, raw data satisfying (W), (P0), the
recursions `F^{(1)} F^{(r)} = (r+1) F^{(r+1)}`, `E^{(1)} E^{(r)} = (r+1) E^{(r+1)}` and the Lie
relation `[E, F] = H` satisfy all the axioms of a DP-lattice. -/
theorem isDP_of_rec [IsDomain A] [CharZero A] (h : RecData wt Fd Ed) : IsDP wt Fd Ed where
  W_F := h.W_F
  W_E := h.W_E
  P0_F := h.P0_F
  P0_E := h.P0_E
  P1_F := RecData.P1_aux Fd h.P0_F h.rec_F
  P1_E := RecData.P1_aux Ed h.P0_E h.rec_E
  K i r s := by
    rw [h.K_ext r s (inWt_single wt i)]
    rw [← Finset.sum_subset (s₁ := range (min r s + 1))
      (Finset.range_subset_range.mpr (by omega)) ?_]
    · refine Finset.sum_congr rfl fun j hj => ?_
      simp only [mem_range] at hj
      rw [show (r : ℤ) - j = ((r - j : ℕ) : ℤ) by omega, Fz_natCast]
    · intro j hj hj'
      simp only [mem_range] at hj hj'
      rw [Fz_neg _ (by omega)]; simp

omit [Fintype ι] [DecidableEq ι] in
/-- (B2, general form) If `F^{(1)} F^{(r)} = (r+1) F^{(r+1)}` and `F^{(0)} = 1`, then
`r! F^{(r)} = (F^{(1)})^r`. -/
lemma factorial_smul_of_rec (G : ℕ → Module.End A (ι → A)) (h0 : G 0 = 1)
    (hrec : ∀ (r : ℕ) (x : ι → A), G 1 (G r x) = ((r : A) + 1) • G (r + 1) x) (r : ℕ) :
    ((r.factorial : ℕ) : A) • G r = G 1 ^ r := by
  induction r with
  | zero => simp [h0]
  | succ r ih =>
    rw [pow_succ', ← ih]
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, hrec, smul_smul,
      Nat.factorial_succ]
    push_cast; ring_nf

/-- In a DP-lattice, `F^{(1)} F^{(r)} = (r+1) F^{(r+1)}` (from (P1)). -/
lemma dp_rec_F (M : DPLattice A) (r : ℕ) (x : M.ι → A) :
    M.Fd 1 (M.Fd r x) = ((r : A) + 1) • M.Fd (r + 1) x := by
  have := LinearMap.congr_fun (M.isDP.P1_F 1 r) x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
  rw [this, show ((1 : ℕ) : ℤ) + r = ((1 + r : ℕ) : ℤ) by push_cast; ring, Ring.choose_natCast,
    Nat.choose_one_right, add_comm 1 r]
  push_cast; ring_nf

/-- In a DP-lattice, `E^{(1)} E^{(r)} = (r+1) E^{(r+1)}` (from (P1)). -/
lemma dp_rec_E (M : DPLattice A) (r : ℕ) (x : M.ι → A) :
    M.Ed 1 (M.Ed r x) = ((r : A) + 1) • M.Ed (r + 1) x := by
  have := LinearMap.congr_fun (M.isDP.P1_E 1 r) x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
  rw [this, show ((1 : ℕ) : ℤ) + r = ((1 + r : ℕ) : ℤ) by push_cast; ring, Ring.choose_natCast,
    Nat.choose_one_right, add_comm 1 r]
  push_cast; ring_nf

omit [Fintype ι] [DecidableEq ι] in
/-- (D1), (D2), proof sketch: over a domain of characteristic zero, an `A`-linear map between
DP-lattices that commutes with `F^{(1)}`, `E^{(1)}` and `H` commutes with every `F^{(r)}` and
`E^{(s)}` (by the recursions of the divided powers and cancellation of `r + 1`). -/
lemma comm_of_rec [IsDomain A] [CharZero A] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : ℕ → Module.End A (ι → A)) (G' : ℕ → Module.End A (κ → A)) (h0 : G 0 = 1) (h0' : G' 0 = 1)
    (hrec : ∀ (r : ℕ) (x : ι → A), G 1 (G r x) = ((r : A) + 1) • G (r + 1) x)
    (hrec' : ∀ (r : ℕ) (x : κ → A), G' 1 (G' r x) = ((r : A) + 1) • G' (r + 1) x)
    (f : (ι → A) →ₗ[A] (κ → A)) (h1 : f ∘ₗ G 1 = G' 1 ∘ₗ f) (r : ℕ) :
    f ∘ₗ G r = G' r ∘ₗ f := by
  induction r with
  | zero => rw [h0, h0']; rfl
  | succ r ih =>
    refine LinearMap.ext fun x => ?_
    apply cancel_smul (natCast_succ_ne_zero (A := A) r)
    simp only [LinearMap.comp_apply]
    rw [← map_smul, ← hrec, ← hrec', ← LinearMap.comp_apply f (G 1), h1, LinearMap.comp_apply,
      ← LinearMap.comp_apply f, ih, LinearMap.comp_apply]

/-- (D1), (D2), proof sketch: a linear map between DP-lattices commuting with `F^{(1)}`,
`E^{(1)}` and `H` is a morphism (over a domain of characteristic zero). -/
def homOfOne [IsDomain A] [CharZero A] {M N : DPLattice A} (f : (M.ι → A) →ₗ[A] (N.ι → A))
    (hF : f ∘ₗ M.Fd 1 = N.Fd 1 ∘ₗ f) (hE : f ∘ₗ M.Ed 1 = N.Ed 1 ∘ₗ f)
    (hH : f ∘ₗ H M = H N ∘ₗ f) : Hom M N where
  toLin := f
  comm_F := comm_of_rec M.Fd N.Fd M.isDP.P0_F N.isDP.P0_F (dp_rec_F M) (dp_rec_F N) f hF
  comm_E := comm_of_rec M.Ed N.Ed M.isDP.P0_E N.isDP.P0_E (dp_rec_E M) (dp_rec_E N) f hE
  comm_H := hH

end Doubling
