module

public import RequestProject.OddDeficit.Basic

/-!
# `CSI11_the_odd_deficit_law.md` — the algebra of `ℤ[y_t]/(y_t²)` used in Parts Q and D

Namespace `ColouredSand.OddTwist`.  This file is auxiliary for Parts Q and D of
`CSI11_the_odd_deficit_law.md`.  It contains:
* the bilinearity of C10's product `Deficit.starMul` and the unit `[Δ = ∅]`;
* the constant term and the support of the powers `starPow` (used for (Q1)–(Q3));
* the predicate `Small p S t c h`.  It says that `h` has no constant term, that `h` is
  supported on subsets of `S`, and that `p^{t + c − |Γ| − min Γ}` divides `h(Γ)` for every
  non-empty `Γ ⊆ S`.  This is the «valuation `≥` deficit `+ c`» bookkeeping of the proof of
  Lemma 4.2 (Part D);
* the power expansion `f^N = 1 + N g + C(N,2) g² + (order 2)`, with `g = f − 1`.  This replaces
  the set-partition formula in the proof of (D1): the single-block term is `N g`, and all
  partitions into `j ≥ 2` blocks are swept into `C(N,2) g² + (order 2)`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset Deficit

/-- The unit `[Δ = ∅]` of `ℤ[y_t]/(y_t²)`. -/
def unitF : Finset ℕ → ℤ := fun Δ => if Δ = ∅ then 1 else 0

/-! ### Bilinearity of `starMul` -/

lemma starMul_add_left (f g h : Finset ℕ → ℤ) :
    starMul (f + g) h = starMul f h + starMul g h := by
  funext Δ; simp [starMul, add_mul, sum_add_distrib]

lemma starMul_add_right (f g h : Finset ℕ → ℤ) :
    starMul f (g + h) = starMul f g + starMul f h := by
  funext Δ; simp [starMul, mul_add, sum_add_distrib]

lemma starMul_smul_left (c : ℤ) (f h : Finset ℕ → ℤ) :
    starMul (c • f) h = c • starMul f h := by
  funext Δ; simp [starMul, mul_sum, mul_assoc]

lemma starMul_smul_right (c : ℤ) (f h : Finset ℕ → ℤ) :
    starMul f (c • h) = c • starMul f h := by
  funext Δ; simp only [starMul, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

lemma starMul_unitF_left (h : Finset ℕ → ℤ) : starMul unitF h = h := by
  funext Δ
  unfold starMul unitF
  rw [sum_eq_single ∅]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; simp at h

lemma starMul_unitF_right (h : Finset ℕ → ℤ) : starMul h unitF = h := by
  funext Δ
  unfold starMul unitF
  rw [sum_eq_single Δ]
  · simp
  · intro b hb hbΔ
    have : Δ \ b ≠ ∅ := by
      intro he; exact hbΔ (le_antisymm (mem_powerset.1 hb) (sdiff_eq_empty_iff_subset.1 he))
    simp [this]
  · intro h; simp at h

lemma starMul_empty (f g : Finset ℕ → ℤ) : starMul f g ∅ = f ∅ * g ∅ := by
  simp [starMul]

lemma starPow_zero_eq (f : Finset ℕ → ℤ) : starPow f 0 = unitF := rfl

lemma starPow_succ_eq (f : Finset ℕ → ℤ) (n : ℕ) :
    starPow f (n + 1) = starMul f (starPow f n) := rfl

/-- The constant term of a power: `[f^N]_∅ = f(∅)^N`. -/
lemma starPow_empty (f : Finset ℕ → ℤ) (N : ℕ) : starPow f N ∅ = f ∅ ^ N := by
  induction N with
  | zero => simp [starPow]
  | succ n ih => rw [starPow_succ_eq, starMul_empty, ih, pow_succ, mul_comm]

/-- Supports multiply: if `f` and `g` vanish off the subsets of `S`, so does `f ⋆ g`. -/
lemma starMul_support {S : Finset ℕ} {f g : Finset ℕ → ℤ} (hf : ∀ Γ, ¬ Γ ⊆ S → f Γ = 0)
    (hg : ∀ Γ, ¬ Γ ⊆ S → g Γ = 0) (Γ : Finset ℕ) (hΓ : ¬ Γ ⊆ S) : starMul f g Γ = 0 := by
  unfold starMul
  refine sum_eq_zero fun Γ₁ hΓ₁ => ?_
  by_cases h1 : Γ₁ ⊆ S
  · have h2 : ¬ Γ \ Γ₁ ⊆ S := by
      intro h2; apply hΓ
      intro x hx
      by_cases hx1 : x ∈ Γ₁
      · exact h1 hx1
      · exact h2 (mem_sdiff.2 ⟨hx, hx1⟩)
    rw [hg _ h2, mul_zero]
  · rw [hf _ h1, zero_mul]

/-- Powers keep the support: if `f` vanishes off the subsets of `S`, so does every `f^N`. -/
lemma starPow_support {S : Finset ℕ} {f : Finset ℕ → ℤ} (hf : ∀ Γ, ¬ Γ ⊆ S → f Γ = 0)
    (N : ℕ) (Γ : Finset ℕ) (hΓ : ¬ Γ ⊆ S) : starPow f N Γ = 0 := by
  induction N generalizing Γ with
  | zero =>
    have : Γ ≠ ∅ := by rintro rfl; exact hΓ (empty_subset _)
    simp [starPow, this]
  | succ n ih => exact starMul_support hf ih Γ hΓ

/-! ### The deficit bookkeeping -/

/-- A non-empty `Γ` all of whose elements are `< t` has `|Γ| + min Γ ≤ t`. -/
lemma card_add_min'_le {t : ℕ} (Γ : Finset ℕ) (h : Γ.Nonempty) (ht : ∀ s ∈ Γ, s < t) :
    Γ.card + Γ.min' h ≤ t := by
  have hs : Γ ⊆ Ico (Γ.min' h) t := fun x hx => mem_Ico.2 ⟨min'_le _ _ hx, ht x hx⟩
  have := card_le_card hs
  rw [Nat.card_Ico] at this
  have := ht _ (min'_mem Γ h)
  omega

/-- `Small p S t c h`: `h` has no constant term, vanishes off the subsets of `S`, and
`p^{t + c − |Γ| − min Γ}` divides `h(Γ)` for every non-empty `Γ ⊆ S`. -/
def Small (p : ℕ) (S : Finset ℕ) (t c : ℕ) (h : Finset ℕ → ℤ) : Prop :=
  h ∅ = 0 ∧ (∀ Γ, ¬ Γ ⊆ S → h Γ = 0) ∧
    ∀ Γ (hΓ : Γ.Nonempty), Γ ⊆ S → (p : ℤ) ^ (t + c - Γ.card - Γ.min' hΓ) ∣ h Γ

variable {p : ℕ} {S : Finset ℕ} {t : ℕ}

lemma Small.zero (c : ℕ) : Small p S t c 0 :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ => dvd_zero _⟩

lemma Small.add {c : ℕ} {g h : Finset ℕ → ℤ} (hg : Small p S t c g) (hh : Small p S t c h) :
    Small p S t c (g + h) :=
  ⟨by simp [hg.1, hh.1], fun Γ hΓ => by simp [hg.2.1 Γ hΓ, hh.2.1 Γ hΓ],
    fun Γ hΓ hS => dvd_add (hg.2.2 Γ hΓ hS) (hh.2.2 Γ hΓ hS)⟩

lemma Small.smul {c : ℕ} {h : Finset ℕ → ℤ} (m : ℤ) (hh : Small p S t c h) :
    Small p S t c (m • h) :=
  ⟨by simp [hh.1], fun Γ hΓ => by simp [hh.2.1 Γ hΓ],
    fun Γ hΓ hS => Dvd.dvd.mul_left (hh.2.2 Γ hΓ hS) _⟩

lemma Small.sub {c : ℕ} {g h : Finset ℕ → ℤ} (hg : Small p S t c g) (hh : Small p S t c h) :
    Small p S t c (g - h) := by
  have := hg.add (hh.smul (-1))
  simpa [sub_eq_add_neg] using this

lemma Small.mono {c c' : ℕ} (hcc : c' ≤ c) {h : Finset ℕ → ℤ} (hh : Small p S t c h) :
    Small p S t c' h :=
  ⟨hh.1, hh.2.1, fun Γ hΓ hS => (pow_dvd_pow _ (by omega)).trans (hh.2.2 Γ hΓ hS)⟩

/-- Multiplying by a multiple of `p` raises the order by one. -/
lemma Small.smul_p (hS : ∀ s ∈ S, s < t) {c : ℕ} {h : Finset ℕ → ℤ} {m : ℤ}
    (hm : (p : ℤ) ∣ m) (hh : Small p S t c h) : Small p S t (c + 1) (m • h) := by
  refine ⟨by simp [hh.1], fun Γ hΓ => by simp [hh.2.1 Γ hΓ], fun Γ hΓ hΓS => ?_⟩
  have hle := card_add_min'_le Γ hΓ (fun s hs => hS s (hΓS hs))
  have : t + (c + 1) - Γ.card - Γ.min' hΓ = (t + c - Γ.card - Γ.min' hΓ) + 1 := by omega
  rw [this, pow_succ, mul_comm, Pi.smul_apply, smul_eq_mul]
  exact mul_dvd_mul hm (hh.2.2 Γ hΓ hΓS)

/-- **The key estimate.** Products of small functions are smaller: the orders add, plus one.
(For a split `Γ = Γ₁ ⊔ Γ₂` into non-empty parts, the deficits add up to the deficit of `Γ`
plus `t − max ≥ 1`.) -/
lemma Small.starMul (hS : ∀ s ∈ S, s < t) {a b : ℕ} {g h : Finset ℕ → ℤ}
    (hg : Small p S t a g) (hh : Small p S t b h) : Small p S t (a + b + 1) (starMul g h) := by
  refine ⟨by simp [starMul_empty, hg.1], starMul_support hg.2.1 hh.2.1, fun Γ hΓ hΓS => ?_⟩
  unfold Deficit.starMul
  refine dvd_sum fun Γ₁ hΓ₁ => ?_
  rw [mem_powerset] at hΓ₁
  rcases Γ₁.eq_empty_or_nonempty with h1 | h1
  · simp [h1, hg.1]
  rcases (Γ \ Γ₁).eq_empty_or_nonempty with h2 | h2
  · simp [h2, hh.1]
  have hS1 : Γ₁ ⊆ S := hΓ₁.trans hΓS
  have hS2 : Γ \ Γ₁ ⊆ S := sdiff_subset.trans hΓS
  have e1 := card_add_min'_le Γ₁ h1 (fun s hs => hS s (hS1 hs))
  have e2 := card_add_min'_le (Γ \ Γ₁) h2 (fun s hs => hS s (hS2 hs))
  have hc : Γ.card = Γ₁.card + (Γ \ Γ₁).card := by
    rw [card_sdiff_of_subset hΓ₁]; have := card_le_card hΓ₁; omega
  have hm1 : Γ.min' hΓ ≤ Γ₁.min' h1 := min'_subset _ hΓ₁
  have hm2 : Γ.min' hΓ ≤ (Γ \ Γ₁).min' h2 := min'_subset _ sdiff_subset
  have hmin : Γ₁.min' h1 ≤ Γ.min' hΓ ∧ (Γ \ Γ₁).min' h2 + 1 ≤ t ∨
      (Γ \ Γ₁).min' h2 ≤ Γ.min' hΓ ∧ Γ₁.min' h1 + 1 ≤ t := by
    have hmem := min'_mem Γ hΓ
    by_cases hx : Γ.min' hΓ ∈ Γ₁
    · left
      exact ⟨min'_le _ _ hx, hS _ (hS2 (min'_mem _ h2))⟩
    · right
      exact ⟨min'_le _ _ (mem_sdiff.2 ⟨hmem, hx⟩), hS _ (hS1 (min'_mem _ h1))⟩
  refine (pow_dvd_pow _ ?_).trans
    (pow_add (p : ℤ) _ _ ▸ mul_dvd_mul (hg.2.2 Γ₁ h1 hS1) (hh.2.2 _ h2 hS2))
  omega

lemma Small.mono_set {S' : Finset ℕ} (hSS : S ⊆ S') {c : ℕ} {h : Finset ℕ → ℤ}
    (hh : Small p S t c h) : Small p S' t c h := by
  refine ⟨hh.1, fun Γ hΓ => hh.2.1 Γ (fun h => hΓ (h.trans hSS)), fun Γ hΓ hΓS => ?_⟩
  by_cases h : Γ ⊆ S
  · exact hh.2.2 Γ hΓ h
  · rw [hh.2.1 Γ h]; exact dvd_zero _

/-! ### The power expansion -/

/-- The remainder `r_N = f^N − 1 − N g − C(N,2) g²` of the power expansion, `g = f − 1`. -/
def powRem (f : Finset ℕ → ℤ) (N : ℕ) : Finset ℕ → ℤ :=
  starPow f N - unitF - (N : ℤ) • (f - unitF) -
    ((N.choose 2 : ℕ) : ℤ) • starMul (f - unitF) (f - unitF)

/-- **The power expansion.** If `g = f − 1` is small of order `0`, then
`f^N − 1 − N g − C(N,2) g²` is small of order `2`. -/
lemma powRem_small (hS : ∀ s ∈ S, s < t) {f : Finset ℕ → ℤ}
    (hg : Small p S t 0 (f - unitF)) (N : ℕ) : Small p S t 2 (powRem f N) := by
  induction N with
  | zero =>
    have : powRem f 0 = 0 := by
      funext Δ; simp [powRem, starPow_zero_eq]
    rw [this]; exact Small.zero 2
  | succ n ih =>
    set g := f - unitF with hgdef
    have hf : f = unitF + g := by rw [hgdef]; abel
    have hpow : starPow f n = unitF + (n : ℤ) • g + ((n.choose 2 : ℕ) : ℤ) • starMul g g
        + powRem f n := by
      simp only [powRem, ← hgdef]; abel
    have key : powRem f (n + 1) = powRem f n +
        ((n.choose 2 : ℕ) : ℤ) • starMul g (starMul g g) + starMul g (powRem f n) := by
      have e2 : powRem f (n + 1) = starPow f (n + 1) - unitF - ((n : ℤ) + 1) • g -
          (((n.choose 2 : ℕ) : ℤ) + n) • starMul g g := by
        simp only [powRem, ← hgdef, Nat.choose_succ_succ, Nat.choose_one_right]
        push_cast
        module
      rw [e2, starPow_succ_eq, hpow]
      generalize powRem f n = R
      rw [hf]
      simp only [starMul_add_left, starMul_add_right, starMul_smul_right, starMul_unitF_left,
        starMul_unitF_right]
      module
    rw [key]
    have hg2 : Small p S t 1 (starMul g g) := by simpa using hg.starMul hS hg
    have hg3 : Small p S t 2 (starMul g (starMul g g)) := by simpa using hg.starMul hS hg2
    refine (ih.add (hg3.smul _)).add ?_
    exact (hg.starMul hS ih).mono (by omega)

/-- The constant term `[f^N]_∅ = 1` when `f(∅) = 1` (part of (Q3)). -/
lemma starPow_empty_of_one {f : Finset ℕ → ℤ} (hf : f ∅ = 1) (N : ℕ) : starPow f N ∅ = 1 := by
  rw [starPow_empty, hf, one_pow]

/-- **The power expansion, order 1.** `f^N − 1 − N g` is small of order `1`. -/
lemma pow_sub_small_one (hS : ∀ s ∈ S, s < t) {f : Finset ℕ → ℤ}
    (hg : Small p S t 0 (f - unitF)) (N : ℕ) :
    Small p S t 1 (starPow f N - unitF - (N : ℤ) • (f - unitF)) := by
  have hg2 : Small p S t 1 (starMul (f - unitF) (f - unitF)) := by simpa using hg.starMul hS hg
  have := ((powRem_small hS hg N).mono (by omega : 1 ≤ 2)).add
    (hg2.smul ((N.choose 2 : ℕ) : ℤ))
  convert this using 1
  simp only [powRem]; abel

/-- **The power expansion at `N = p`, `p` odd.** Since `p ∣ C(p,2)`, `f^p − 1 − p g` is small
of order `2`. -/
lemma pow_p_sub_small_two (hp : p.Prime) (hodd : Odd p) (hS : ∀ s ∈ S, s < t)
    {f : Finset ℕ → ℤ} (hg : Small p S t 0 (f - unitF)) :
    Small p S t 2 (starPow f p - unitF - (p : ℤ) • (f - unitF)) := by
  have hg2 : Small p S t 1 (starMul (f - unitF) (f - unitF)) := by simpa using hg.starMul hS hg
  have hdvd : (p : ℤ) ∣ ((p.choose 2 : ℕ) : ℤ) := by
    exact_mod_cast hp.dvd_choose_self (by norm_num) (by
      have := hp.two_le; rcases hodd with ⟨m, hm⟩; omega)
  have := (powRem_small hS hg p).add (hg2.smul_p hS hdvd)
  convert this using 1
  simp only [powRem]; abel

end ColouredSand.OddTwist
