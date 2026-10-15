module

public import RequestProject.TiltDec.Rule

/-!
# `CSG5_the_induction.md`, Part W — the multiplicities are those of (T3)

## Encoding (namespace `ColouredSand.TiltDec`)

* Formal sums are `List ℕ` up to `List.Perm`, as in Part M (`RequestProject/TiltDec/Rule.lean`).
* **(W1)** `weylP p l = [l]` if `l` is simple and `[l, l − 2 * rT p l]` otherwise (the Weyl
  factors of `T(l)`); `cgRule 0 = [1]`, `cgRule (l + 1) = [l + 2, l]` (the Clebsch–Gordan rule),
  `CG 0 = [0]`, `CG (n + 1) = (CG n).flatMap cgRule`.
* **(W2)** `W2_rule` (one step) and `W2` (`((LP p n).flatMap (weylP p)).Perm (CG n)`).
* **(W3)** `betaCG n l : ℤ` is `C(n, k) − C(n, k − 1)` with `k = (n − l)/2` when `l ≤ n` and
  `l ≡ n (mod 2)`, with the convention `C(n, −1) = 0` (encoded as: the subtracted term is `0` when
  `k = 0`), and `0` otherwise.  It is integer-valued so that no truncated subtraction occurs.
  `W3 : ((CG n).count l : ℤ) = betaCG n l`.
* **(W4)** `l⁺` is encoded by the `Finset` `plusSet p n l` of the non-simple `m ≤ n` with
  `m − 2 * rT p m = l`; `W4_inj` is the injectivity, so `plusSet p n l` has at most one element
  (`plusSet_subsingleton`).  `W4` is the recursion
  `mP p l n + Σ_{m ∈ plusSet p n l} mP p m n = betaCG n l`; `W4_of_plus` and `W4_of_no_plus` are
  the two cases ("`l⁺` exists and `l⁺ ≤ n`" or not).
* **(W5)** `rankT p l = l + 1` if `l` is simple, `l + (l − 2 rT p l) + 2` otherwise;
  `W5 : ((LP p n).map (rankT p)).sum = 2 ^ n`.  `card_Ttilt` (in `Decomp.lean`) identifies
  `rankT p l` with the rank of `Ttilt p l`.

As in Part M, only `3 ≤ p` is assumed (which holds for primes `p ≠ 2`); primality is not needed.
-/

@[expose] public section

namespace ColouredSand.TiltDec

open ColouredSand.TiltP ColouredSand.Blocks

/-! ### (W1) -/

open Classical in
/-- **(W1)** (`CSG5_the_induction.md`, Part W, (W1)) the Weyl factors of `T(l)`: `[l]` if `l` is
simple, `[l, l − 2 rT p l]` otherwise. -/
noncomputable def weylP (p l : ℕ) : List ℕ := if IsSimpleWt p l then [l] else [l, l - 2 * rT p l]

/-- **(W1)** the Clebsch–Gordan rule: `cgRule 0 = [1]`, `cgRule (l + 1) = [l + 2, l]`. -/
def cgRule : ℕ → List ℕ
  | 0 => [1]
  | l + 1 => [l + 2, l]

/-- **(W1)** `CG 0 = [0]`, `CG (n + 1) = (CG n).flatMap cgRule` (the Weyl factors of `V^{⊗n}`). -/
def CG : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => (CG n).flatMap cgRule

/-- (W1) `weylP p l = [l]` for simple `l`. -/
theorem weylP_simple {p l : ℕ} (hs : IsSimpleWt p l) : weylP p l = [l] := by
  classical
  unfold weylP; rw [if_pos hs]

/-- (W1) `weylP p l = [l, l − 2 rT p l]` for non-simple `l`. -/
theorem weylP_not_simple {p l : ℕ} (hs : ¬ IsSimpleWt p l) : weylP p l = [l, l - 2 * rT p l] := by
  classical
  unfold weylP; rw [if_neg hs]

/-- (W1) `cgRule 0 = [1]`. -/
theorem cgRule_zero : cgRule 0 = [1] := rfl

/-- (W1) `cgRule (l + 1) = [l + 2, l]`. -/
theorem cgRule_succ (l : ℕ) : cgRule (l + 1) = [l + 2, l] := rfl

/-- (W1) `cgRule l = [l + 1, l − 1]` for `l ≥ 1`. -/
theorem cgRule_pos {l : ℕ} (h : 1 ≤ l) : cgRule l = [l + 1, l - 1] := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  rfl

/-- `weylP p (lam p r a) = [λ, λ − 2r]` for `1 ≤ r ≤ p − 1`. -/
lemma weylP_lam {p r : ℕ} (a : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ p - 1) :
    weylP p (lam p r a) = [lam p r a, lam p r a - 2 * r] := by
  rw [weylP_not_simple (not_simple_lam a hr1 hr), rT_lam a hr1 (by omega)]

/-- `weylP p (lam p p (p − 1)) = [λ, λ − 2p]`. -/
lemma weylP_lam_top {p : ℕ} (hp : 1 ≤ p) :
    weylP p (lam p p (p - 1)) = [lam p p (p - 1), lam p p (p - 1) - 2 * p] := by
  rw [weylP_not_simple (not_simple_lam_top hp), rT_lam (p - 1) hp le_rfl]

/-! ### (W2) -/

/-- (W2), auxiliary: the permutation `[x, a, y, z] ~ [x, y, z, a]`. -/
lemma perm_shape (x a y z : ℕ) : [x, a, y, z].Perm [x, y, z, a] :=
  List.Perm.cons x (List.perm_append_comm (l₁ := [a]) (l₂ := [y, z]))

/-- Closing an equality of explicit lists of natural numbers by `omega`. -/
macro "tiltDecListEq" : tactic => `(tactic| (
  simp only [List.cons_append, List.nil_append, List.append_nil, List.cons.injEq, and_true,
    true_and] <;> omega))

/-- **(W2)**, one step (`CSG5_the_induction.md`, Part W, (W2)): for `l ≤ p² + p − 2` (and
`p ≥ 3`), `((VdotP p l).flatMap (weylP p)).Perm ((weylP p l).flatMap cgRule)`. -/
theorem W2_rule {p l : ℕ} (hp : 3 ≤ p) (hl : l ≤ p ^ 2 + p - 2) :
    ((VdotP p l).flatMap (weylP p)).Perm ((weylP p l).flatMap cgRule) := by
  rcases cases_weight hp hl with rfl | ⟨h1, h2⟩ | ⟨b, hb, hlb⟩ | ⟨r, a, hr1, hr, ha, rfl⟩
  · rw [VdotP_zero, weylP_simple (simple_of_le (Nat.zero_le _))]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      weylP_simple (simple_of_le (by omega) : IsSimpleWt p 1)]
    exact List.Perm.refl _
  · rw [VdotP_simple_small (simple_of_le (by omega)) h1 h2, weylP_simple (simple_of_le (by omega))]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      weylP_simple (simple_of_le (by omega) : IsSimpleWt p (l + 1)),
      weylP_simple (simple_of_le (by omega) : IsSimpleWt p (l - 1)), cgRule_pos h1]
    exact List.Perm.refl _
  · obtain ⟨e1, e2⟩ := lam_one_of_simple (by omega) hlb
    have hs : IsSimpleWt p l := by
      have := simple_mul_sub_one (p := p) (b := b + 1) (by omega) (by omega)
      rwa [← hlb, Nat.add_sub_cancel] at this
    have hl1 : 1 ≤ l := by
      have : p ≤ (b + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hw : weylP p (l + 1) = [l + 1, l - 1] := by
      have h2 : lam p 1 b - 2 * 1 = l - 1 := by rw [e2]; rfl
      rw [e1, weylP_lam (p := p) b le_rfl (by omega), h2]
    have hbp : p ≤ (b + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
    rw [VdotP_simple_large (by omega) hs (by omega), weylP_simple hs]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hw, cgRule_pos hl1]
    exact List.Perm.refl _
  · obtain ⟨hLM, hMr⟩ := lam_mu_facts (p := p) (r := r) a hr1 hr
    have hpa : p ≤ p * (a + 1) := Nat.le_mul_of_pos_right _ (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hMr hpa
    rw [weylP_lam a hr1 hr]
    rcases (show r = 1 ∨ (2 ≤ r ∧ r ≤ p - 2) ∨ r = p - 1 by omega) with rfl | ⟨hr2, hr3⟩ | rfl
    · -- `r = 1`
      have w1 : weylP p (lam p 1 a + 1) = [lam p 1 a + 1, lam p 1 a + 1 - 2 * 2] := by
        rw [lam_add_one_eq, weylP_lam a (by omega) (by omega)]
      have w2 : weylP p (lam p 1 a - 1) = [lam p 1 a - 1] :=
        weylP_simple (simple_lam_one_pred ha (by omega))
      have c1 := cgRule_pos (show 1 ≤ lam p 1 a by omega)
      have c2 := cgRule_pos (show 1 ≤ lam p 1 a - 2 * 1 by omega)
      rw [VdotP_lam_one hp a]
      generalize lam p 1 a = L at *
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, w1, w2, c1, c2]
      exact (List.Perm.of_eq (by tiltDecListEq)).trans
        ((perm_shape (L + 1) (L - 3) (L - 1) (L - 1)).trans (List.Perm.of_eq (by tiltDecListEq)))
    · -- `2 ≤ r ≤ p − 2`
      have w1 : weylP p (lam p r a + 1) = [lam p r a + 1, lam p r a + 1 - 2 * (r + 1)] := by
        rw [lam_add_one_eq, weylP_lam a (by omega) (by omega)]
      have w2 : weylP p (lam p r a - 1) = [lam p r a - 1, lam p r a - 1 - 2 * (r - 1)] := by
        rw [lam_sub_one_eq a hr2, weylP_lam a (by omega) (by omega)]
      have c1 := cgRule_pos (show 1 ≤ lam p r a by omega)
      have c2 := cgRule_pos (show 1 ≤ lam p r a - 2 * r by omega)
      rw [VdotP_lam_mid a hr2 hr3]
      generalize lam p r a = L at *
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, w1, w2, c1, c2]
      exact (List.Perm.of_eq (by tiltDecListEq)).trans
        ((perm_shape (L + 1) (L - 2 * r - 1) (L - 1) (L - 2 * r + 1)).trans
          (List.Perm.of_eq (by tiltDecListEq)))
    · -- `r = p − 1`
      have w2 : weylP p (lam p (p - 1) a - 1) =
          [lam p (p - 1) a - 1, lam p (p - 1) a - 1 - 2 * (p - 1 - 1)] := by
        rw [lam_sub_one_eq a (by omega), weylP_lam a (by omega) (by omega)]
      have c1 := cgRule_pos (show 1 ≤ lam p (p - 1) a by omega)
      rcases (show (1 ≤ a ∧ a ≤ p - 2) ∨ a = 0 ∨ a = p - 1 by omega) with ⟨ha1, ha2⟩ | rfl | rfl
      · have w1 : weylP p (lam p (p - 1) a + 1) = [lam p (p - 1) a + 1] :=
          weylP_simple (simple_lam_top_succ (by omega) ha2)
        have w3 : weylP p (mu p (p - 1) a - 1) = [mu p (p - 1) a - 1] :=
          weylP_simple (simple_mu_top_pred (by omega) ha1 ha)
        have hpa' : p ≤ p * a := Nat.le_mul_of_pos_right _ (by omega)
        have c2 := cgRule_pos (show 1 ≤ lam p (p - 1) a - 2 * (p - 1) by omega)
        rw [VdotP_lam_top_pos hp ha1 ha2]
        generalize lam p (p - 1) a = L at *
        generalize mu p (p - 1) a = M at *
        generalize p * a = X at *
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, w1, w2, w3, c1, c2]
        exact List.Perm.of_eq (by tiltDecListEq)
      · have w1 : weylP p (lam p (p - 1) 0 + 1) = [lam p (p - 1) 0 + 1] :=
          weylP_simple (simple_lam_top_succ (by omega) (by omega))
        have hz : lam p (p - 1) 0 - 2 * (p - 1) = 0 := by unfold lam; omega
        rw [VdotP_lam_top_ext hp (Or.inl rfl), hz]
        generalize lam p (p - 1) 0 = L at *
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, w1, w2, c1, cgRule_zero]
        exact List.Perm.of_eq (by tiltDecListEq)
      · have w1 : weylP p (lam p (p - 1) (p - 1) + 1) =
            [lam p (p - 1) (p - 1) + 1, lam p (p - 1) (p - 1) + 1 - 2 * p] := by
          rw [lam_top_add_one p (by omega), weylP_lam_top (by omega)]
        have hpa' : p ≤ p * (p - 1) := Nat.le_mul_of_pos_right _ (by omega)
        have c2 := cgRule_pos (show 1 ≤ lam p (p - 1) (p - 1) - 2 * (p - 1) by omega)
        rw [VdotP_lam_top_ext hp (Or.inr rfl)]
        generalize lam p (p - 1) (p - 1) = L at *
        generalize mu p (p - 1) (p - 1) = M at *
        generalize p * (p - 1) = X at *
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, w1, w2, c1, c2]
        exact (List.Perm.of_eq (by tiltDecListEq)).trans
          ((perm_shape (L + 1) (L - 2 * (p - 1) - 1) (L - 1) (L - 2 * (p - 1) + 1)).trans
            (List.Perm.of_eq (by tiltDecListEq)))

/-- **(W2)** (`CSG5_the_induction.md`, Part W, (W2)): for `n ≤ p² + p − 1` (and `p ≥ 3`),
`((LP p n).flatMap (weylP p)).Perm (CG n)`. -/
theorem W2 {p n : ℕ} (hp : 3 ≤ p) (hn : n ≤ p ^ 2 + p - 1) :
    ((LP p n).flatMap (weylP p)).Perm (CG n) := by
  induction n with
  | zero =>
    rw [LP_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      weylP_simple (simple_of_le (Nat.zero_le _) : IsSimpleWt p 0)]
    exact List.Perm.refl _
  | succ n ih =>
    have ih' := ih (by omega)
    rw [LP_succ, List.flatMap_assoc]
    refine (List.Perm.flatMap_left _ (fun l hl => W2_rule hp ?_)).trans ?_
    · have := (M3 (by omega) n l hl).1; omega
    · rw [← List.flatMap_assoc]; exact ih'.flatMap_right cgRule

/-! ### (W3) -/

/-- **(W3)** (`CSG5_the_induction.md`, Part W, (W3)) `β n l = C(n, k) − C(n, k − 1)` with
`k = (n − l)/2` if `l ≤ n` and `l ≡ n (mod 2)` (with `C(n, −1) = 0`), and `0` otherwise
(integer-valued). -/
def betaCG (n l : ℕ) : ℤ :=
  if l ≤ n ∧ l % 2 = n % 2 then
    (n.choose ((n - l) / 2) : ℤ) - (if (n - l) / 2 = 0 then 0 else (n.choose ((n - l) / 2 - 1) : ℤ))
  else 0

/-- (W3), auxiliary: counting in `L.flatMap cgRule`. -/
lemma count_flatMap_cgRule (L : List ℕ) (l : ℕ) :
    (L.flatMap cgRule).count l = L.count (l + 1) + (if 1 ≤ l then L.count (l - 1) else 0) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons, List.count_append, ih]
    clear ih
    split_ifs with hl <;> rcases a with _ | a <;>
      simp only [cgRule_zero, cgRule_succ, List.count_cons, List.count_nil, beq_iff_eq] <;>
      split_ifs with h1 h2 h3 <;> (try subst h1) <;> simp_all <;> omega

/-- (W3), auxiliary: `g n k = C(n, k) − C(n, k − 1)` (with `C(n, −1) = 0`). -/
def gCG (n k : ℕ) : ℤ := (n.choose k : ℤ) - (if k = 0 then 0 else (n.choose (k - 1) : ℤ))

/-- (W3), auxiliary: `β n l = g n k` when `n = l + 2k`. -/
lemma betaCG_of {n l k : ℕ} (h : n = l + 2 * k) : betaCG n l = gCG n k := by
  unfold betaCG gCG
  rw [if_pos (by omega), show (n - l) / 2 = k by omega]

/-- (W3), auxiliary: `β n l = 0` when `n − l` is not a non-negative even number. -/
lemma betaCG_of_not {n l : ℕ} (h : ∀ k, n ≠ l + 2 * k) : betaCG n l = 0 := by
  unfold betaCG
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact h ((n - l) / 2) (by omega)

/-- (W3), auxiliary: Pascal's rule for `g`. -/
lemma gCG_succ (n j : ℕ) : gCG (n + 1) (j + 1) = gCG n j + gCG n (j + 1) := by
  unfold gCG
  rcases j with _ | i
  · simp [Nat.choose_succ_succ]
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, Nat.choose_succ_succ]
    push_cast; ring

/-- (W3), auxiliary: `g n 0 = 1`. -/
lemma gCG_zero (n : ℕ) : gCG n 0 = 1 := by simp [gCG]

/-- (W3), auxiliary: the recursion `β (n + 1) l = β n (l + 1) + [l ≥ 1] β n (l − 1)`. -/
lemma betaCG_succ (n l : ℕ) :
    betaCG (n + 1) l = betaCG n (l + 1) + (if 1 ≤ l then betaCG n (l - 1) else 0) := by
  by_cases hA : ∃ k, n + 1 = l + 2 * k
  · obtain ⟨k, hk⟩ := hA
    rw [betaCG_of hk]
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      obtain rfl : n = 2 * j + 1 := by omega
      rw [if_neg (by omega), betaCG_of (k := j) (by omega), add_zero, gCG_succ]
      have : gCG (2 * j + 1) (j + 1) = 0 := by
        unfold gCG; rw [if_neg (by omega), Nat.add_sub_cancel, Nat.choose_symm_half]; ring
      rw [this, add_zero]
    · rw [if_pos (show 1 ≤ l by omega)]
      rcases k with _ | j
      · rw [betaCG_of_not (by intro k; omega), betaCG_of (k := 0) (by omega), gCG_zero,
          gCG_zero, zero_add]
      · rw [betaCG_of (k := j) (by omega), betaCG_of (k := j + 1) (by omega), gCG_succ]
  · push_neg at hA
    rw [betaCG_of_not hA, betaCG_of_not (by intro k; have := hA (k + 1); omega)]
    split_ifs
    · rw [betaCG_of_not (by intro k; have := hA k; omega)]; ring
    · ring

/-- **(W3)** (`CSG5_the_induction.md`, Part W, (W3)): `(CG n).count l = β n l`. -/
theorem W3 (n l : ℕ) : ((CG n).count l : ℤ) = betaCG n l := by
  induction n generalizing l with
  | zero =>
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · rw [betaCG_of (k := 0) rfl, gCG_zero]; simp [CG]
    · rw [betaCG_of_not (by intro k; omega)]; simp [CG, List.count_cons]; omega
  | succ n ih =>
    rw [show CG (n + 1) = (CG n).flatMap cgRule from rfl, count_flatMap_cgRule, betaCG_succ]
    push_cast
    rw [ih]
    split_ifs
    · rw [ih]
    · simp

/-! ### (W4) -/

/-- (W4), auxiliary: a non-simple `m ≤ p² + p − 1` satisfies
`(m − 2 rT p m) + rT p m + 1 = p (aT p m + 1)` and `1 ≤ rT p m ≤ p` (for `p ≥ 2`). -/
lemma mu_add_r_of_not_simple {p m : ℕ} (hp : 2 ≤ p) (hs : ¬ IsSimpleWt p m)
    (hm : m ≤ p ^ 2 + p - 1) :
    (m - 2 * rT p m) + rT p m + 1 = p * (aT p m + 1) ∧ 1 ≤ rT p m ∧ rT p m ≤ p := by
  obtain ⟨-, hr1, hrp, ha, htop, hlam⟩ := T3 hp hs hm
  refine ⟨?_, hr1, hrp⟩
  have key : ∀ r a, 1 ≤ r → r ≤ p → (r = p → a = p - 1) →
      lam p r a - 2 * r + r + 1 = p * (a + 1) := by
    intro r a h1 h2 h3
    unfold lam; rw [Nat.mul_add, Nat.mul_one]
    rcases (show r ≤ p - 1 ∨ r = p by omega) with h | rfl
    · omega
    · have := h3 rfl; subst this
      have : r ≤ r * (r - 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  have := key (rT p m) (aT p m) hr1 hrp htop
  rwa [hlam] at this

/-- **(W4)**, injectivity (`CSG5_the_induction.md`, Part W, (W4)): the map `l ↦ l − 2 rT p l` is
injective on the non-simple `l ≤ p² + p − 1` (for every `p ≥ 2`). -/
theorem W4_inj {p m₁ m₂ : ℕ} (hp : 2 ≤ p) (hs₁ : ¬ IsSimpleWt p m₁) (hs₂ : ¬ IsSimpleWt p m₂)
    (hm₁ : m₁ ≤ p ^ 2 + p - 1) (hm₂ : m₂ ≤ p ^ 2 + p - 1)
    (h : m₁ - 2 * rT p m₁ = m₂ - 2 * rT p m₂) : m₁ = m₂ := by
  obtain ⟨e₁, r₁1, r₁p⟩ := mu_add_r_of_not_simple hp hs₁ hm₁
  obtain ⟨e₂, r₂1, r₂p⟩ := mu_add_r_of_not_simple hp hs₂ hm₂
  obtain ⟨-, -, -, -, -, hl₁⟩ := T3 hp hs₁ hm₁
  obtain ⟨-, -, -, -, -, hl₂⟩ := T3 hp hs₂ hm₂
  have ha : aT p m₁ = aT p m₂ := by
    rcases lt_trichotomy (aT p m₁) (aT p m₂) with hlt | heq | hgt
    · have : p * (aT p m₁ + 1) + p ≤ p * (aT p m₂ + 1) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    · exact heq
    · have : p * (aT p m₂ + 1) + p ≤ p * (aT p m₁ + 1) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega
  have hr : rT p m₁ = rT p m₂ := by rw [ha] at e₁; omega
  rw [← hl₁, ← hl₂, ha, hr]

open Classical in
/-- **(W4)** the weight `l⁺`, encoded as the `Finset` of the non-simple `m ≤ n` with
`m − 2 rT p m = l` (it has at most one element by `W4_inj`, when `n ≤ p² + p − 1`). -/
noncomputable def plusSet (p n l : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun m => ¬ IsSimpleWt p m ∧ m - 2 * rT p m = l)

/-- (W4) `plusSet p n l` has at most one element for `n ≤ p² + p − 1`, `p ≥ 2`. -/
theorem plusSet_subsingleton {p n : ℕ} (hp : 2 ≤ p) (hn : n ≤ p ^ 2 + p - 1) (l : ℕ) :
    ∀ m₁ ∈ plusSet p n l, ∀ m₂ ∈ plusSet p n l, m₁ = m₂ := by
  intro m₁ h₁ m₂ h₂
  simp only [plusSet, Finset.mem_filter, Finset.mem_range] at h₁ h₂
  exact W4_inj hp h₁.2.1 h₂.2.1 (by omega) (by omega) (h₁.2.2.trans h₂.2.2.symm)

open Classical in
/-- (W4), auxiliary: counting `l` in `L.flatMap (weylP p)`. -/
lemma count_flatMap_weylP (p : ℕ) (L : List ℕ) (l : ℕ) :
    (L.flatMap (weylP p)).count l =
      L.count l + L.countP (fun m => decide (¬ IsSimpleWt p m ∧ m - 2 * rT p m = l)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons, List.count_append, ih, List.count_cons, List.countP_cons]
    by_cases hs : IsSimpleWt p a
    · rw [weylP_simple hs]
      have : decide (¬ IsSimpleWt p a ∧ a - 2 * rT p a = l) = false := by simp [hs]
      rw [this]
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> first | contradiction | omega
    · rw [weylP_not_simple hs]
      by_cases h : a - 2 * rT p a = l
      · have : decide (¬ IsSimpleWt p a ∧ a - 2 * rT p a = l) = true := by simp [hs, h]
        rw [this]
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        split_ifs <;> first | contradiction | omega
      · have : decide (¬ IsSimpleWt p a ∧ a - 2 * rT p a = l) = false := by simp [h]
        rw [this]
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        split_ifs <;> first | contradiction | omega

/-- (W4), auxiliary: for a list with all entries `< k`, `countP P` is the sum of the counts over
`(range k).filter P`. -/
lemma countP_eq_sum_count (L : List ℕ) (k : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hL : ∀ x ∈ L, x < k) :
    L.countP (fun m => decide (P m)) = ∑ m ∈ (Finset.range k).filter P, L.count m := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.countP_cons, ih (fun x hx => hL x (by simp [hx]))]
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq]
    have ha := hL a (by simp)
    simp only [Finset.mem_filter, Finset.mem_range, ha, true_and]
    by_cases h : P a <;> simp [h]

/-- **(W4)** (T3) (`CSG5_the_induction.md`, Part W, (W4)): for `n ≤ p² + p − 1` (and `p ≥ 3`)
and every `l`, `mP p l n + Σ_{m ∈ plusSet p n l} mP p m n = β n l`, where `plusSet p n l` is
`{l⁺}` if `l⁺` exists and `l⁺ ≤ n`, and `∅` otherwise. -/
theorem W4 {p n : ℕ} (hp : 3 ≤ p) (hn : n ≤ p ^ 2 + p - 1) (l : ℕ) :
    (mP p l n : ℤ) + ∑ m ∈ plusSet p n l, (mP p m n : ℤ) = betaCG n l := by
  classical
  rw [← W3, ← (W2 hp hn).count_eq, count_flatMap_weylP,
    countP_eq_sum_count (LP p n) (n + 1) _ (fun x hx => Nat.lt_succ_of_le (M3 (by omega) n x hx).1)]
  push_cast
  rfl

/-- **(W4)**, case "`l⁺` exists and `l⁺ ≤ n`": if `m ≤ n` is non-simple with
`m − 2 rT p m = l`, then `mP p l n + mP p m n = β n l` (`n ≤ p² + p − 1`, `p ≥ 3`). -/
theorem W4_of_plus {p n l m : ℕ} (hp : 3 ≤ p) (hn : n ≤ p ^ 2 + p - 1) (hs : ¬ IsSimpleWt p m)
    (hmn : m ≤ n) (hm : m - 2 * rT p m = l) : (mP p l n : ℤ) + mP p m n = betaCG n l := by
  have hmem : m ∈ plusSet p n l := by
    simp only [plusSet, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hs, hm⟩
  have hset : plusSet p n l = {m} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hmem, fun x hx => plusSet_subsingleton (by omega) hn l x hx m hmem⟩
  rw [← W4 hp hn l, hset, Finset.sum_singleton]

/-- **(W4)**, case "`l⁺` does not exist or `l⁺ > n`": if no non-simple `m ≤ n` has
`m − 2 rT p m = l`, then `mP p l n = β n l` (`n ≤ p² + p − 1`, `p ≥ 3`). -/
theorem W4_of_no_plus {p n l : ℕ} (hp : 3 ≤ p) (hn : n ≤ p ^ 2 + p - 1)
    (h : ∀ m ≤ n, ¬ IsSimpleWt p m → m - 2 * rT p m ≠ l) : (mP p l n : ℤ) = betaCG n l := by
  have hset : plusSet p n l = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro m hm
    simp only [plusSet, Finset.mem_filter, Finset.mem_range] at hm
    exact h m (by omega) hm.2.1 hm.2.2
  rw [← W4 hp hn l, hset, Finset.sum_empty, add_zero]

/-! ### (W5) -/

open Classical in
/-- **(W5)** the rank of `Ttilt p l`: `l + 1` if `l` is simple, `l + μ + 2` otherwise, with
`μ = l − 2 rT p l`. -/
noncomputable def rankT (p l : ℕ) : ℕ :=
  if IsSimpleWt p l then l + 1 else l + (l - 2 * rT p l) + 2

/-- (W5), auxiliary: `rankT p l` is the sum of `x + 1` over the Weyl factors `x` of `T(l)`. -/
lemma rankT_eq_sum (p l : ℕ) : rankT p l = ((weylP p l).map (· + 1)).sum := by
  classical
  unfold rankT
  by_cases hs : IsSimpleWt p l
  · rw [if_pos hs, weylP_simple hs]; simp
  · rw [if_neg hs, weylP_not_simple hs]; simp; omega

/-- (W5), auxiliary: `Σ_{x ∈ CG n} (x + 1) = 2^n`. -/
lemma sum_CG (n : ℕ) : ((CG n).map (· + 1)).sum = 2 ^ n := by
  have key : ∀ L : List ℕ, ((L.flatMap cgRule).map (· + 1)).sum = 2 * (L.map (· + 1)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih]
      rcases a with _ | a <;> simp [cgRule] <;> ring
  induction n with
  | zero => simp [CG]
  | succ n ih => rw [show CG (n + 1) = (CG n).flatMap cgRule from rfl, key, ih]; ring

/-- **(W5)** dimension check (`CSG5_the_induction.md`, Part W, (W5)): for `n ≤ p² + p − 1`
(and `p ≥ 3`), `Σ_{λ ∈ LP p n} rank (Ttilt p λ) = 2^n`, with `rank` given by `rankT`. -/
theorem W5 {p n : ℕ} (hp : 3 ≤ p) (hn : n ≤ p ^ 2 + p - 1) :
    ((LP p n).map (rankT p)).sum = 2 ^ n := by
  have h1 : ((LP p n).map (rankT p)).sum = (((LP p n).flatMap (weylP p)).map (· + 1)).sum := by
    clear hn
    induction LP p n with
    | nil => simp
    | cons a L ih => simp [List.flatMap_cons, ih, rankT_eq_sum]
  rw [h1, ((W2 hp hn).map (· + 1)).sum_eq, sum_CG]

end ColouredSand.TiltDec
