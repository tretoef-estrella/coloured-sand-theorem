module

public import RequestProject.OddTwist.All
public import RequestProject.Twist.All
public import RequestProject.Tensor2.All

/-!
# `CSI2_reduction_mod_p.md`: Setting and Part T — the Frobenius twist at `p`

Encodings (namespace `ColouredSand.OddTwist`, following C21's `RequestProject/Twist/PartT.lean`
with `2` replaced by a prime `p`):

* `p : ℕ` with `[Fact p.Prime]`; `B` is a commutative ring and `hp : (p : B) = 0` is the
  hypothesis "`p = 0` in `B`" of the Setting. The hypothesis `p ≠ 2` is never used: all results of
  this folder hold for every prime `p` (more general than the file).
* Binomial coefficients with integer top are Mathlib's `Ring.choose x k : ℤ` (as in C18), cast to
  `B`.
* `frobOpP p F r` is `F^{(r/p)}` if `p ∣ r` and `0` otherwise.
* `frobP hp M` is `M^{[1]}`: basis `M.ι`, weights `p · M.wt i`, `F^{(r)} := frobOpP p M.Fd r`,
  `E^{(r)} := frobOpP p M.Ed r`. The proof `hp` is needed to show that these data form a
  DP-lattice ((T1)).
* `frobPHom hp f` is the morphism `M^{[1]} → N^{[1]}` given by the same linear map as `f` ((T2)).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset WeylFilt

variable {B : Type*} [CommRing B] {p : ℕ} [Fact p.Prime] (hp : (p : B) = 0)

/-! ### Setting: integers divisible by `p` vanish, integers prime to `p` are units -/

omit [Fact p.Prime] in
include hp in
/-- Setting: a natural number divisible by `p` is `0` in `B`. -/
lemma natCast_eq_zero_of_dvd {n : ℕ} (h : p ∣ n) : (n : B) = 0 := by
  obtain ⟨m, rfl⟩ := h; push_cast; rw [hp, zero_mul]

omit [Fact p.Prime] in
include hp in
/-- Setting: an integer divisible by `p` is `0` in `B`. -/
lemma intCast_eq_zero_of_dvd {n : ℤ} (h : (p : ℤ) ∣ n) : (n : B) = 0 := by
  obtain ⟨m, rfl⟩ := h; push_cast; rw [hp, zero_mul]

omit [Fact p.Prime] in
include hp in
/-- Setting: two integers congruent modulo `p` have the same image in `B`. -/
lemma intCast_eq_of_dvd_sub {m n : ℤ} (h : (p : ℤ) ∣ m - n) : (m : B) = (n : B) := by
  have := intCast_eq_zero_of_dvd hp h
  push_cast at this
  exact sub_eq_zero.mp this

omit [Fact p.Prime] in
include hp in
/-- Setting (note): in `B`, every integer prime to `p` is a unit: if `gcd(m, p) = 1` then
`m·u + p·v = 1` for some integers `u, v`, so `m·u = 1` in `B`. -/
theorem isUnit_intCast_of_coprime {m : ℤ} (h : IsCoprime m (p : ℤ)) : IsUnit (m : B) := by
  obtain ⟨u, v, huv⟩ := h
  have := congrArg (fun z : ℤ => (z : B)) huv
  push_cast at this
  rw [hp, mul_zero, add_zero, mul_comm] at this
  exact IsUnit.of_mul_eq_one (u : B) this

omit [Fact p.Prime] in
include hp in
/-- Setting (note): a natural number prime to `p` is a unit of `B`. -/
theorem isUnit_natCast_of_coprime' {m : ℕ} (h : Nat.Coprime m p) : IsUnit (m : B) := by
  have := isUnit_intCast_of_coprime hp (m := (m : ℤ)) (Nat.isCoprime_iff_coprime.mpr h)
  simpa using this

include hp in
/-- Setting (note): `t!` is a unit of `B` for `t ≤ p − 1`. -/
theorem isUnit_factorial {t : ℕ} (ht : t ≤ p - 1) : IsUnit ((t.factorial : ℕ) : B) := by
  have hpp : p.Prime := Fact.out
  refine isUnit_natCast_of_coprime' hp ?_
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).mpr fun hd => ?_)
  rw [hpp.dvd_factorial] at hd
  have := hpp.two_le
  omega

/-! ### (T0) Lucas at `p` -/

section lucas

include hp in
lemma choose_p_cast (b : ℕ) :
    ((Ring.choose (p : ℤ) b : ℤ) : B) = if b = 0 ∨ b = p then 1 else 0 := by
  have hpp : p.Prime := Fact.out
  rw [Ring.choose_natCast, Int.cast_natCast]
  by_cases h0 : b = 0
  · subst h0; simp
  by_cases hb : b = p
  · subst hb; simp
  rw [if_neg (by tauto)]
  rcases lt_or_gt_of_ne hb with h | h
  · exact natCast_eq_zero_of_dvd hp (hpp.dvd_choose_self h0 h)
  · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

include hp in
/-- (T0, proof) Vandermonde modulo `p`: `C(px + p, k) = C(px, k) + C(px, k − p)` in `B`. -/
lemma choose_mul_succ (x : ℤ) (k : ℕ) :
    ((Ring.choose ((p : ℤ) * (x + 1)) k : ℤ) : B) =
      ((Ring.choose ((p : ℤ) * x) k : ℤ) : B) +
        if p ≤ k then ((Ring.choose ((p : ℤ) * x) (k - p) : ℤ) : B) else 0 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [show (p : ℤ) * (x + 1) = p * x + p by ring, Ring.add_choose_eq k (Commute.all _ _),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => Ring.choose ((p : ℤ) * x) a * Ring.choose (p : ℤ) b) k]
  push_cast
  simp_rw [choose_p_cast hp]
  split_ifs with hk
  · rw [Finset.sum_eq_add (a := k) (b := k - p) (by omega)]
    · simp [show k - (k - p) = p by omega, (Nat.ne_of_gt hp0).symm]
    · intro c hc hne
      simp only [mem_range] at hc
      rw [if_neg (by omega), mul_zero]
    · intro h; simp at h
    · intro h; simp only [mem_range] at h; omega
  · rw [Finset.sum_eq_single k]
    · simp
    · intro c hc hne
      simp only [mem_range] at hc
      rw [if_neg (by omega), mul_zero]
    · intro h; simp at h

/-- (T0, proof) the right-hand side of Lucas at `p`: `C(x, k/p)` if `p ∣ k`, `0` otherwise. -/
def lucasRHS (B : Type*) [CommRing B] (p : ℕ) (x : ℤ) (k : ℕ) : B :=
  if p ∣ k then ((Ring.choose x (k / p) : ℤ) : B) else 0

lemma lucasRHS_succ (x : ℤ) (k : ℕ) :
    lucasRHS B p (x + 1) k = lucasRHS B p x k + if p ≤ k then lucasRHS B p x (k - p) else 0 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  unfold lucasRHS
  by_cases hk : p ∣ k
  · obtain ⟨j, rfl⟩ := hk
    rcases j with _ | j
    · simp; omega
    · have h1 : p ≤ p * (j + 1) := Nat.le_mul_of_pos_right p (by omega)
      have h2 : p * (j + 1) - p = p * j := by rw [Nat.mul_succ]; omega
      rw [if_pos h1, h2, if_pos (dvd_mul_right _ _), if_pos (dvd_mul_right _ _),
        if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hp0, Nat.mul_div_cancel_left _ hp0,
        Ring.choose_succ_succ]
      push_cast; ring
  · rw [if_neg hk, if_neg hk]
    split_ifs with h1 h2
    · exact absurd ((Nat.dvd_sub_iff_left h1 dvd_rfl).mp h2) hk
    · simp
    · simp

include hp in
lemma lucas_all (x : ℤ) : ∀ k : ℕ, ((Ring.choose ((p : ℤ) * x) k : ℤ) : B) = lucasRHS B p x k := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  induction x using Int.induction_on with
  | zero =>
    intro k
    unfold lucasRHS
    rcases k with _ | k
    · simp
    · rw [mul_zero, Ring.choose_zero_succ]
      split_ifs with h
      · obtain ⟨j, hj⟩ := h
        rcases j with _ | j
        · omega
        · rw [hj, Nat.mul_div_cancel_left _ hp0, Ring.choose_zero_succ]
      · simp
  | succ i ih =>
    intro k
    rw [choose_mul_succ hp, ih, lucasRHS_succ]
    split_ifs <;> simp [ih]
  | pred i ih =>
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      have h1 := choose_mul_succ hp (-(i : ℤ) - 1) k
      have h2 := lucasRHS_succ (B := B) (p := p) (-(i : ℤ) - 1) k
      rw [sub_add_cancel, ih k] at h1
      rw [sub_add_cancel] at h2
      split_ifs at h1 h2 with hk
      · rw [ihk (k - p) (by omega)] at h1
        linear_combination h2 - h1
      · linear_combination h2 - h1

include hp in
/-- (T0) Lucas at `p`. In a commutative ring `B` with `p = 0`, for every integer `x` (possibly
negative), every `j : ℕ` and every `1 ≤ t ≤ p − 1`: `C(px, pj) = C(x, j)` and
`C(px, pj + t) = 0` (images in `B`). -/
theorem T0 (x : ℤ) (j : ℕ) :
    ((Ring.choose ((p : ℤ) * x) (p * j) : ℤ) : B) = ((Ring.choose x j : ℤ) : B) ∧
    ∀ t : ℕ, 1 ≤ t → t ≤ p - 1 → ((Ring.choose ((p : ℤ) * x) (p * j + t) : ℤ) : B) = 0 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨?_, fun t ht1 htp => ?_⟩
  · rw [lucas_all hp, lucasRHS, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hp0]
  · rw [lucas_all hp, lucasRHS, if_neg]
    intro h
    have := (Nat.dvd_add_right (dvd_mul_right p j)).mp h
    have := Nat.le_of_dvd (by omega) this
    omega

include hp in
/-- (T0), the form used below: `C(px, k) = 0` in `B` whenever `p ∤ k`. -/
lemma choose_mul_of_not_dvd (x : ℤ) {k : ℕ} (hk : ¬ p ∣ k) :
    ((Ring.choose ((p : ℤ) * x) k : ℤ) : B) = 0 := by
  rw [lucas_all hp, lucasRHS, if_neg hk]

end lucas

/-! ### The twist -/

section twist

variable {ι : Type*}

variable (p) in
/-- Part T: `frobOpP p F r` is `F^{(r/p)}` if `p ∣ r` and `0` otherwise. -/
def frobOpP (F : ℕ → Module.End B (ι → B)) (r : ℕ) : Module.End B (ι → B) :=
  if p ∣ r then F (r / p) else 0

omit [Fact p.Prime] in
lemma frobOpP_of_not_dvd (F : ℕ → Module.End B (ι → B)) {r : ℕ} (h : ¬ p ∣ r) :
    frobOpP p F r = 0 := by
  simp [frobOpP, h]

lemma frobOpP_mul (F : ℕ → Module.End B (ι → B)) (s : ℕ) : frobOpP p F (p * s) = F s := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  simp [frobOpP, Nat.mul_div_cancel_left _ hp0]

lemma sum_range_mul_add_one {X : Type*} [AddCommMonoid X] (g : ℕ → X) (m : ℕ)
    (hg : ∀ j, j ≤ p * m → ¬ p ∣ j → g j = 0) :
    ∑ j ∈ range (p * m + 1), g j = ∑ j ∈ range (m + 1), g (p * j) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [← Finset.sum_image (s := range (m + 1)) (g := fun j => p * j)
    (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp0 h)]
  symm
  refine Finset.sum_subset (fun j hj => ?_) (fun j hj hj' => ?_)
  · simp only [mem_image, mem_range] at hj ⊢
    obtain ⟨a, ha, rfl⟩ := hj
    have : p * a ≤ p * m := Nat.mul_le_mul_left _ (by omega)
    omega
  · simp only [mem_image, mem_range] at hj hj' ⊢
    refine hg j (by omega) fun ⟨a, ha⟩ => hj' ?_
    refine ⟨a, ?_, ha.symm⟩
    by_contra h
    have : p * (m + 1) ≤ p * a := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this
    omega

variable [DecidableEq ι]

omit [DecidableEq ι] in
include hp in
lemma frob_P1 {F : ℕ → Module.End B (ι → B)}
    (hF : ∀ a b : ℕ, F a ∘ₗ F b = ((Ring.choose ((a : ℤ) + b) a : ℤ) : B) • F (a + b)) (a b : ℕ) :
    frobOpP p F a ∘ₗ frobOpP p F b =
      ((Ring.choose ((a : ℤ) + b) a : ℤ) : B) • frobOpP p F (a + b) := by
  by_cases ha : p ∣ a
  · obtain ⟨a', rfl⟩ := ha
    by_cases hb : p ∣ b
    · obtain ⟨b', rfl⟩ := hb
      rw [frobOpP_mul, frobOpP_mul, ← mul_add, frobOpP_mul, hF]
      congr 1
      push_cast
      rw [← mul_add, (T0 hp _ a').1]
    · have : ¬ p ∣ p * a' + b := fun h => hb ((Nat.dvd_add_right (dvd_mul_right _ _)).1 h)
      rw [frobOpP_of_not_dvd _ hb, frobOpP_of_not_dvd _ this]; simp
  · rw [frobOpP_of_not_dvd _ ha, LinearMap.zero_comp]
    by_cases hab : p ∣ a + b
    · obtain ⟨c, hc⟩ := hab
      have : ((Ring.choose ((a : ℤ) + b) a : ℤ) : B) = 0 := by
        rw [show ((a : ℤ) + b) = p * (c : ℤ) by exact_mod_cast hc]
        exact choose_mul_of_not_dvd hp _ ha
      rw [this, zero_smul]
    · rw [frobOpP_of_not_dvd _ hab, smul_zero]

include hp in
lemma frob_K {wt : ι → ℤ} {F E : ℕ → Module.End B (ι → B)} (hM : IsDP wt F E) (i : ι)
    (r s : ℕ) :
    frobOpP p E s (frobOpP p F r (Pi.single i 1)) =
      ∑ j ∈ range (min r s + 1), ((Ring.choose ((p : ℤ) * wt i + s - r) j : ℤ) : B) •
        frobOpP p F (r - j) (frobOpP p E (s - j) (Pi.single i 1)) := by
  by_cases hrs : p ∣ r ∧ p ∣ s
  · obtain ⟨⟨r', rfl⟩, ⟨s', rfl⟩⟩ := hrs
    rw [frobOpP_mul, frobOpP_mul, hM.K i r' s', Nat.mul_min_mul_left,
      sum_range_mul_add_one]
    · refine sum_congr rfl fun j hj => ?_
      simp only [mem_range] at hj
      rw [← Nat.mul_sub, ← Nat.mul_sub, frobOpP_mul, frobOpP_mul]
      congr 1
      push_cast
      rw [show (p : ℤ) * wt i + p * s' - p * r' = p * (wt i + s' - r') by ring, (T0 hp _ j).1]
    · intro j hjm hj
      have hjr : j ≤ p * r' := le_trans hjm (Nat.mul_le_mul_left _ (min_le_left _ _))
      have : ¬ p ∣ p * r' - j := fun h =>
        hj ((Nat.dvd_sub_iff_right hjr (dvd_mul_right _ _)).mp h)
      rw [frobOpP_of_not_dvd _ this]; simp
  · have lhs : frobOpP p E s (frobOpP p F r (Pi.single i 1)) = 0 := by
      by_cases hr : p ∣ r
      · rw [frobOpP_of_not_dvd E (fun h => hrs ⟨hr, h⟩)]; rfl
      · rw [frobOpP_of_not_dvd F hr]; simp
    rw [lhs]; symm
    refine sum_eq_zero fun j hj => ?_
    simp only [mem_range] at hj
    have hjr : j ≤ r := by omega
    have hjs : j ≤ s := by omega
    by_cases h1 : p ∣ r - j
    · by_cases h2 : p ∣ s - j
      · have hj : ¬ p ∣ j := fun h => hrs
          ⟨by rw [← Nat.sub_add_cancel hjr]; exact dvd_add h1 h,
           by rw [← Nat.sub_add_cancel hjs]; exact dvd_add h2 h⟩
        obtain ⟨a, ha⟩ := h1
        obtain ⟨b, hb⟩ := h2
        have : (p : ℤ) * wt i + s - r = p * (wt i + b - a) := by
          have ha' : ((r : ℤ) - j) = p * a := by rw [← Nat.cast_sub hjr, ha]; push_cast; ring
          have hb' : ((s : ℤ) - j) = p * b := by rw [← Nat.cast_sub hjs, hb]; push_cast; ring
          linear_combination hb' - ha'
        rw [this, choose_mul_of_not_dvd hp _ hj, zero_smul]
      · rw [frobOpP_of_not_dvd E h2]; simp
    · rw [frobOpP_of_not_dvd F h1]; simp

include hp in
/-- (T1) If `p = 0` in `B`, the data of `M^{[1]}` (basis `M.ι`, weights `p · M.wt`,
`F^{(r)} = frobOpP p M.Fd r`, `E^{(r)} = frobOpP p M.Ed r`) satisfy `IsDP`: (W), (P0), (P1), (K). -/
theorem T1 {wt : ι → ℤ} {F E : ℕ → Module.End B (ι → B)} (hM : IsDP wt F E) :
    IsDP (fun i => (p : ℤ) * wt i) (frobOpP p F) (frobOpP p E) where
  W_F i r j h := by
    by_cases hr : p ∣ r
    · obtain ⟨s, rfl⟩ := hr
      rw [frobOpP_mul]; exact hM.W_F i s j (fun h' => h (by rw [h']; push_cast; ring))
    · rw [frobOpP_of_not_dvd _ hr]; rfl
  W_E i r j h := by
    by_cases hr : p ∣ r
    · obtain ⟨s, rfl⟩ := hr
      rw [frobOpP_mul]; exact hM.W_E i s j (fun h' => h (by rw [h']; push_cast; ring))
    · rw [frobOpP_of_not_dvd _ hr]; rfl
  P0_F := by rw [show (0 : ℕ) = p * 0 by simp, frobOpP_mul, hM.P0_F]
  P0_E := by rw [show (0 : ℕ) = p * 0 by simp, frobOpP_mul, hM.P0_E]
  P1_F := frob_P1 hp hM.P1_F
  P1_E := frob_P1 hp hM.P1_E
  K i r s := frob_K hp hM i r s

/-- (T1) `M^{[1]}` (`frobP hp M`) for a DP-lattice `M` over `B` with `p = 0`: basis `M.ι`,
weights `p · M.wt`, `F^{(r)} = M.Fd (r / p)` and `E^{(r)} = M.Ed (r / p)` if `p ∣ r`, and `0`
otherwise. -/
def frobP (M : DPLattice B) : DPLattice B where
  ι := M.ι
  wt i := p * M.wt i
  Fd := frobOpP p M.Fd
  Ed := frobOpP p M.Ed
  isDP := T1 hp M.isDP

end twist

section frobFacts

variable (M : DPLattice B)

/-- Part T: the data of `M^{[1]}`: `F^{(ps)} = F^{(s)}`, `E^{(ps)} = E^{(s)}`, `F^{(r)} = 0` and
`E^{(r)} = 0` for `p ∤ r`, weights `p · wt`. -/
theorem frobP_data (s : ℕ) :
    (frobP hp M).Fd (p * s) = M.Fd s ∧ (frobP hp M).Ed (p * s) = M.Ed s ∧
    (∀ r, ¬ p ∣ r → (frobP hp M).Fd r = 0 ∧ (frobP hp M).Ed r = 0) ∧
    (∀ i, (frobP hp M).wt i = p * M.wt i) :=
  ⟨frobOpP_mul _ s, frobOpP_mul _ s, fun _ h => ⟨frobOpP_of_not_dvd _ h, frobOpP_of_not_dvd _ h⟩,
    fun _ => rfl⟩

/-- Part T: `H` acts on `M^{[1]}` as `p · H`. -/
theorem H_frobP : H (frobP hp M) = (p : B) • H M := by
  refine LinearMap.ext fun x => ?_
  funext i
  simp [frobP, mul_assoc]

end frobFacts

section T2

/-- (T2) A morphism `f : Hom M N` is a morphism `M^{[1]} → N^{[1]}` (same linear map). -/
def frobPHom {M N : DPLattice B} (f : Hom M N) : Hom (frobP hp M) (frobP hp N) where
  toLin := f.toLin
  comm_F r := by
    show f.toLin ∘ₗ frobOpP p M.Fd r = frobOpP p N.Fd r ∘ₗ f.toLin
    unfold frobOpP; split_ifs
    · exact f.comm_F _
    · simp
  comm_E r := by
    show f.toLin ∘ₗ frobOpP p M.Ed r = frobOpP p N.Ed r ∘ₗ f.toLin
    unfold frobOpP; split_ifs
    · exact f.comm_E _
    · simp
  comm_H := by
    rw [H_frobP, H_frobP]
    show f.toLin ∘ₗ ((p : B) • H M) = ((p : B) • H N) ∘ₗ f.toLin
    rw [LinearMap.comp_smul, LinearMap.smul_comp, f.comm_H]

/-- (T2) For `f : Hom M N`, the same linear map is a `Hom (M^{[1]}) (N^{[1]})`; this sends
`Hom.id` to `Hom.id` and composites to composites. -/
theorem T2 :
    (∀ {M N : DPLattice B} (f : Hom M N), (frobPHom hp f).toLin = f.toLin) ∧
    (∀ M : DPLattice B, frobPHom hp (Hom.id M) = Hom.id (frobP hp M)) ∧
    (∀ {M N P : DPLattice B} (g : Hom N P) (f : Hom M N),
      frobPHom hp (Hom.comp g f) = Hom.comp (frobPHom hp g) (frobPHom hp f)) :=
  ⟨fun _ => rfl, fun _ => Hom.ext' rfl, fun _ _ => Hom.ext' rfl⟩

end T2

end ColouredSand.OddTwist
