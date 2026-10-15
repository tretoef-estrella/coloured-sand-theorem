module

public import RequestProject.Twist.PartR

/-!
# `C21_reduction_mod_2_and_the_twist.md`: Part T, the Frobenius twist (`2 = 0` in `B`)

Encodings:
* `h2 : (2 : B) = 0` is the hypothesis of the file.
* `frobOp F r` is `F^{(r/2)}` if `r` is even and `0` if `r` is odd.
* `frob h2 M` is `M^{[1]}`: basis `M.ι`, weights `2 · M.wt i`, `F^{(r)} := frobOp M.Fd r`,
  `E^{(r)} := frobOp M.Ed r` (so `F^{(2s)}, E^{(2s)}` act as `F^{(s)}, E^{(s)}`, the odd divided
  powers act as `0`, and `H` acts as `2H`, `H_frob`). The proof `h2` is needed to show that the
  data form a DP-lattice ((T1)).
* `frobHom h2 f` is the morphism `M^{[1]} → N^{[1]}` given by the same linear map as `f`.
-/

@[expose] public section

noncomputable section

namespace Twist

open DPLattice Finset WeylFilt Doubling

variable {B : Type*} [CommRing B]

/-! ### (T0) Lucas at 2 -/

section lucas

variable (h2 : (2 : B) = 0)

include h2 in
lemma choose_add_two (y : ℤ) (k : ℕ) :
    ((Ring.choose (y + 1 + 1) (k + 2) : ℤ) : B) =
      ((Ring.choose y k : ℤ) : B) + ((Ring.choose y (k + 2) : ℤ) : B) := by
  rw [Ring.choose_succ_succ, Ring.choose_succ_succ, Ring.choose_succ_succ (y) (k + 1)]
  push_cast
  have : ((Ring.choose y (k + 1) : ℤ) : B) + ((Ring.choose y (k + 1) : ℤ) : B) = 0 := by
    rw [← two_mul, h2, zero_mul]
  linear_combination this

/-- The statement of (T0) at the top `x`. -/
def LucasAt (B : Type*) [CommRing B] (x : ℤ) : Prop :=
  ∀ j : ℕ, ((Ring.choose (2 * x) (2 * j) : ℤ) : B) = ((Ring.choose x j : ℤ) : B) ∧
    ((Ring.choose (2 * x) (2 * j + 1) : ℤ) : B) = 0

include h2 in
lemma choose_two_mul_one (x : ℤ) : ((Ring.choose (2 * x) 1 : ℤ) : B) = 0 := by
  rw [Ring.choose_one_right]; push_cast; rw [h2, zero_mul]

lemma lucasAt_zero : LucasAt B 0 := by
  intro j
  rcases j with _ | j
  · simp
  · simp only [mul_zero]
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring]
    simp [Ring.choose_zero_succ]

include h2 in
lemma lucasAt_succ (x : ℤ) (h : LucasAt B x) : LucasAt B (x + 1) := by
  intro j
  have hx : 2 * (x + 1) = 2 * x + 1 + 1 := by ring
  rw [hx]
  rcases j with _ | j
  · refine ⟨by simp, ?_⟩
    have := choose_two_mul_one h2 (x + 1)
    rwa [hx] at this
  · refine ⟨?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring, choose_add_two h2, (h j).1,
        ← show 2 * (j + 1) = 2 * j + 2 by ring, (h (j + 1)).1, Ring.choose_succ_succ]
      push_cast; ring
    · rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, choose_add_two h2, (h j).2,
        show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring, (h (j + 1)).2, add_zero]

include h2 in
lemma lucasAt_pred (x : ℤ) (h : LucasAt B (x + 1)) : LucasAt B x := by
  have hx : 2 * (x + 1) = 2 * x + 1 + 1 := by ring
  intro j
  induction j with
  | zero => exact ⟨by simp, choose_two_mul_one h2 x⟩
  | succ j ih =>
    have h1 := (h (j + 1)).1
    have h3 := (h (j + 1)).2
    rw [hx, show 2 * (j + 1) = 2 * j + 2 by ring, choose_add_two h2, ih.1] at h1
    rw [hx, show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, choose_add_two h2, ih.2] at h3
    refine ⟨?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring]
      rw [Ring.choose_succ_succ] at h1
      push_cast at h1
      linear_combination h1
    · rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring]
      linear_combination h3

include h2 in
lemma lucasAt_all (x : ℤ) : LucasAt B x := by
  induction x using Int.induction_on with
  | zero => exact lucasAt_zero
  | succ i ih => exact lucasAt_succ h2 _ ih
  | pred i ih => exact lucasAt_pred h2 _ (by rwa [sub_add_cancel])

include h2 in
/-- (T0) Lucas at 2. In a commutative ring `B` with `2 = 0`, for every integer `x` (possibly
negative) and every `j : ℕ`: `C(2x, 2j) = C(x, j)` and `C(2x, 2j + 1) = 0` (images in `B`). -/
theorem T0 (x : ℤ) (j : ℕ) :
    ((Ring.choose (2 * x) (2 * j) : ℤ) : B) = ((Ring.choose x j : ℤ) : B) ∧
    ((Ring.choose (2 * x) (2 * j + 1) : ℤ) : B) = 0 :=
  lucasAt_all h2 x j

end lucas

/-! ### The twist -/

section twist

variable {ι : Type*}

/-- Part T: `frobOp F r` is `F^{(r/2)}` for `r` even and `0` for `r` odd. -/
def frobOp (F : ℕ → Module.End B (ι → B)) (r : ℕ) : Module.End B (ι → B) :=
  if r % 2 = 0 then F (r / 2) else 0

lemma frobOp_even (F : ℕ → Module.End B (ι → B)) (s : ℕ) : frobOp F (2 * s) = F s := by
  simp [frobOp]

lemma frobOp_odd (F : ℕ → Module.End B (ι → B)) (s : ℕ) : frobOp F (2 * s + 1) = 0 := by
  simp [frobOp, Nat.add_mod]

lemma frobOp_of_odd (F : ℕ → Module.End B (ι → B)) {n : ℕ} (hn : Odd n) : frobOp F n = 0 := by
  obtain ⟨s, rfl⟩ := hn; exact frobOp_odd F s

lemma sum_range_two_mul_add_one {X : Type*} [AddCommMonoid X] (g : ℕ → X) (m : ℕ) :
    ∑ j ∈ range (2 * m + 1), g j = ∑ j ∈ range (m + 1), g (2 * j) + ∑ j ∈ range m, g (2 * j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun j => g (2 * j)) (m + 1), sum_range_succ (fun j => g (2 * j + 1)) m,
      show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
    abel

variable [DecidableEq ι] (h2 : (2 : B) = 0)

include h2 in
/-- (T1) If `2 = 0` in `B`, the data of `M^{[1]}` (basis `M.ι`, weights `2 · M.wt`,
`F^{(r)} = frobOp M.Fd r`, `E^{(r)} = frobOp M.Ed r`) satisfy `IsDP`: (W), (P0), (P1), (K). -/
theorem T1 {wt : ι → ℤ} {F E : ℕ → Module.End B (ι → B)} (hM : IsDP wt F E) :
    IsDP (fun i => 2 * wt i) (frobOp F) (frobOp E) where
  W_F i r j h := by
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
    · rw [frobOp_even]; exact hM.W_F i s j (by push_cast at h; omega)
    · rw [frobOp_odd]; rfl
  W_E i r j h := by
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
    · rw [frobOp_even]; exact hM.W_E i s j (by push_cast at h; omega)
    · rw [frobOp_odd]; rfl
  P0_F := by rw [show (0 : ℕ) = 2 * 0 from rfl, frobOp_even, hM.P0_F]
  P0_E := by rw [show (0 : ℕ) = 2 * 0 from rfl, frobOp_even, hM.P0_E]
  P1_F a b := by
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' a <;> obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' b
    · rw [frobOp_even, frobOp_even, show 2 * a + 2 * b = 2 * (a + b) by ring, frobOp_even,
        hM.P1_F]
      congr 1
      push_cast
      rw [show 2 * (a : ℤ) + 2 * b = 2 * ((a : ℤ) + b) by ring, (T0 h2 _ a).1]
    · rw [frobOp_odd, show 2 * a + (2 * b + 1) = 2 * (a + b) + 1 by ring, frobOp_odd]; simp
    · rw [frobOp_odd, show 2 * a + 1 + 2 * b = 2 * (a + b) + 1 by ring, frobOp_odd]; simp
    · rw [frobOp_odd, LinearMap.zero_comp]
      push_cast
      rw [show 2 * (a : ℤ) + 1 + (2 * b + 1) = 2 * ((a : ℤ) + b + 1) by ring, (T0 h2 _ a).2,
        zero_smul]
  P1_E a b := by
    obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' a <;> obtain ⟨b, rfl | rfl⟩ := Nat.even_or_odd' b
    · rw [frobOp_even, frobOp_even, show 2 * a + 2 * b = 2 * (a + b) by ring, frobOp_even,
        hM.P1_E]
      congr 1
      push_cast
      rw [show 2 * (a : ℤ) + 2 * b = 2 * ((a : ℤ) + b) by ring, (T0 h2 _ a).1]
    · rw [frobOp_odd, show 2 * a + (2 * b + 1) = 2 * (a + b) + 1 by ring, frobOp_odd]; simp
    · rw [frobOp_odd, show 2 * a + 1 + 2 * b = 2 * (a + b) + 1 by ring, frobOp_odd]; simp
    · rw [frobOp_odd, LinearMap.zero_comp]
      push_cast
      rw [show 2 * (a : ℤ) + 1 + (2 * b + 1) = 2 * ((a : ℤ) + b + 1) by ring, (T0 h2 _ a).2,
        zero_smul]
  K i r s := by
    obtain ⟨r', hr | hr⟩ := Nat.even_or_odd' r <;> obtain ⟨s', hs | hs⟩ := Nat.even_or_odd' s
    · -- both even
      subst hr hs
      rw [frobOp_even, frobOp_even, hM.K i r' s',
        show min (2 * r') (2 * s') = 2 * min r' s' by omega, sum_range_two_mul_add_one]
      rw [sum_eq_zero (s := range (min r' s')) fun j hj => ?_, add_zero]
      · refine sum_congr rfl fun j hj => ?_
        simp only [mem_range] at hj
        rw [show 2 * r' - 2 * j = 2 * (r' - j) by omega, show 2 * s' - 2 * j = 2 * (s' - j) by omega,
          frobOp_even, frobOp_even]
        congr 1
        push_cast
        rw [show 2 * wt i + 2 * (s' : ℤ) - 2 * r' = 2 * (wt i + s' - r') by ring, (T0 h2 _ j).1]
      · simp only [mem_range] at hj
        rw [frobOp_of_odd F (n := 2 * r' - (2 * j + 1)) ⟨r' - j - 1, by omega⟩]
        simp
    all_goals
      have lhs : frobOp E s (frobOp F r (Pi.single i 1)) = 0 := by
        rcases Nat.even_or_odd r with h | h
        · rw [Nat.even_iff] at h
          rw [frobOp_of_odd E (by rw [Nat.odd_iff]; omega)]; rfl
        · rw [frobOp_of_odd F h]; simp
      rw [lhs]; symm
      refine sum_eq_zero fun j hj => ?_
      simp only [mem_range] at hj
      rcases Nat.even_or_odd (r - j) with h3 | h3
      · rcases Nat.even_or_odd (s - j) with h4 | h4
        · -- both odd, `j` odd
          obtain ⟨k, hk⟩ : ∃ k, j = 2 * k + 1 := by
            rw [Nat.even_iff] at h3 h4; exact ⟨j / 2, by omega⟩
          obtain ⟨t, ht⟩ : ∃ t : ℤ, 2 * wt i + (s : ℤ) - r = 2 * t := by
            rw [Nat.even_iff] at h3 h4; exact ⟨wt i + (s / 2 : ℕ) - (r / 2 : ℕ), by push_cast; omega⟩
          rw [ht, hk, (T0 h2 t k).2]; simp
        · rw [frobOp_of_odd E h4]; simp
      · rw [frobOp_of_odd F h3]; simp

/-- (T1) `M^{[1]}` (`frob h2 M`) for a DP-lattice `M` over `B` with `2 = 0`: basis `M.ι`,
weights `2 · M.wt`, `F^{(2s)} = F^{(s)}`, `E^{(2s)} = E^{(s)}`, odd divided powers `0`. -/
def frob (M : DPLattice B) : DPLattice B where
  ι := M.ι
  wt i := 2 * M.wt i
  Fd := frobOp M.Fd
  Ed := frobOp M.Ed
  isDP := T1 h2 M.isDP

end twist

section frobFacts

variable (h2 : (2 : B) = 0) (M : DPLattice B)

/-- Part T: the data of `M^{[1]}`: `F^{(2s)} = F^{(s)}`, `F^{(2s+1)} = 0`, `E^{(2s)} = E^{(s)}`,
`E^{(2s+1)} = 0`, weights `2 · wt`. -/
theorem frob_data (s : ℕ) :
    (frob h2 M).Fd (2 * s) = M.Fd s ∧ (frob h2 M).Fd (2 * s + 1) = 0 ∧
    (frob h2 M).Ed (2 * s) = M.Ed s ∧ (frob h2 M).Ed (2 * s + 1) = 0 ∧
    (∀ i, (frob h2 M).wt i = 2 * M.wt i) :=
  ⟨frobOp_even _ s, frobOp_odd _ s, frobOp_even _ s, frobOp_odd _ s, fun _ => rfl⟩

/-- Part T: `H` acts on `M^{[1]}` as `2H`. -/
theorem H_frob : H (frob h2 M) = (2 : B) • H M := by
  refine LinearMap.ext fun x => ?_
  funext i
  simp [frob, mul_assoc]

end frobFacts

section T2

variable (h2 : (2 : B) = 0)

/-- (T2) A morphism `f : Hom M N` is a morphism `M^{[1]} → N^{[1]}` (same linear map). -/
def frobHom {M N : DPLattice B} (f : Hom M N) : Hom (frob h2 M) (frob h2 N) where
  toLin := f.toLin
  comm_F r := by
    show f.toLin ∘ₗ frobOp M.Fd r = frobOp N.Fd r ∘ₗ f.toLin
    unfold frobOp; split_ifs
    · exact f.comm_F _
    · simp
  comm_E r := by
    show f.toLin ∘ₗ frobOp M.Ed r = frobOp N.Ed r ∘ₗ f.toLin
    unfold frobOp; split_ifs
    · exact f.comm_E _
    · simp
  comm_H := by
    rw [H_frob, H_frob]
    show f.toLin ∘ₗ ((2 : B) • H M) = ((2 : B) • H N) ∘ₗ f.toLin
    rw [LinearMap.comp_smul, LinearMap.smul_comp, f.comm_H]

/-- (T2) For `f : Hom M N`, the same linear map is a `Hom (M^{[1]}) (N^{[1]})`; this sends
`Hom.id` to `Hom.id` and composites to composites. -/
theorem T2 :
    (∀ {M N : DPLattice B} (f : Hom M N), (frobHom h2 f).toLin = f.toLin) ∧
    (∀ M : DPLattice B, frobHom h2 (Hom.id M) = Hom.id (frob h2 M)) ∧
    (∀ {M N P : DPLattice B} (g : Hom N P) (f : Hom M N),
      frobHom h2 (Hom.comp g f) = Hom.comp (frobHom h2 g) (frobHom h2 f)) :=
  ⟨fun _ => rfl, fun _ => Hom.ext' rfl, fun _ _ => Hom.ext' rfl⟩

end T2

end Twist
