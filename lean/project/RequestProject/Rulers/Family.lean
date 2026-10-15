module

public import RequestProject.Rulers.Basic

/-!
# The family, the deficit, the gold, the rulers and the clocks (`C3_rulers_gold_clocks.md`,
*Setting*), with **Lemma 5.0** and **Lemma 5.1**

Encodings (namespace `Rulers`).  The family is given by `k : ℕ` and `I : Finset ℕ`; the
hypothesis `I ⊆ {0, …, k − 1}` is written `hI : ∀ t ∈ I, t < k` and is assumed wherever needed.
All the definitions below take `k` and `I` as explicit arguments.

* `minOr k E` is `min E`, with the convention `min ∅ := k` of the file.
* `next k I t` (the file's `next(t) := min{u ∈ I ∪ {k} : u > t}`) is
  `minOr k ((insert k I).filter (t < ·))`.  For `t ∈ I` the set contains `k`, so the convention
  for `∅` is never used.
* `h k I t` (the file's `h_t := next(t) − t`) is `next k I t - t` (a natural number, `≥ 1` for
  `t ∈ I`, see `one_le_h`).
* `t₁ := min I` (or `k` if `I = ∅`) is `minOr k I`.
* `hSum k I E` is the file's `h(E) := Σ_{t∈E} h_t`, and `G k I E` is the file's
  `G(E) := Σ_{t∈E} (h_t − 1)`, taken in `ℤ`.
* `oE E` is `o_E := Σ_{t∈E} 2^t` (see `Basic.lean`), and `K = 2^k` is written `2 ^ k`.
* `lam k I` is `λ := K + o_I − 1` (so that `λ + 1 = K + o_I`, because `K ≥ 1`).
* `delta k Δ` (the file's deficit `δ`) is `k − |Δ| − min Δ` in `ℤ` for `Δ ≠ ∅`, and
  `δ(∅) := 0`.
* `gamma k I Δ` (the file's gold `γ`) is `Σ_{u ∈ I ∖ Δ, u > min Δ} h_u` for `Δ ≠ ∅`, and
  `γ(∅) := 0`.
* `ruler k I α μ E` (the file's `R_μ(E)`, with the integer `α`) is
  `Σ_{t∈E} (h_t − α 2^t) − κ(μ, o_E)` in `ℤ`; `rulerSharp k I α E` (the file's `R^♯(E)`) is
  `Σ_{t∈E} (h_t − α 2^t) − κ(K − 1, o_E)`.
* `xi k I D` (the file's `ξ_D := λ + 1 − 2 o_D`) is the natural number `lam k I + 1 - 2 * oE D`;
  Lemma 5.0 (`lemma_5_0_xi`) shows that this subtraction does not truncate and that `ξ_D ≥ 1`.
* `clock k I i D` (the file's raw clock `u_i(D) := φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)`) is this
  integer, with `i + o_D − 1` the natural number subtraction; it is only used for
  `(i, D) ≠ (0, ∅)`, where this subtraction does not truncate.
* `xD k I m D` (the file's `x_D := R_m(D) − R_{m+K}(I ∖ D)` with `α = 1`) and
  `xSharp k I D` (the file's `x^♯_D := R^♯(D) − R^♯(I ∖ D)` with `α = 1`).
-/

@[expose] public section

namespace Rulers

open Finset

variable (k : ℕ) (I : Finset ℕ)

/-- `min E`, with the convention `min ∅ := k` of `C3_rulers_gold_clocks.md`. -/
def minOr (E : Finset ℕ) : ℕ := if h : E.Nonempty then E.min' h else k

/-- `next(t) := min{u ∈ I ∪ {k} : u > t}` (*A family*, `C3_rulers_gold_clocks.md`). -/
def next (t : ℕ) : ℕ := minOr k ((insert k I).filter (fun u => t < u))

/-- `h_t := next(t) − t` (*A family*, `C3_rulers_gold_clocks.md`). -/
def h (t : ℕ) : ℕ := next k I t - t

/-- `t₁ := min I`, or `k` if `I = ∅` (*A family*, `C3_rulers_gold_clocks.md`). -/
def t1 : ℕ := minOr k I

/-- `h(E) := Σ_{t∈E} h_t` (*A family*, `C3_rulers_gold_clocks.md`). -/
def hSum (E : Finset ℕ) : ℕ := ∑ t ∈ E, h k I t

/-- `G(E) := Σ_{t∈E} (h_t − 1)` (*A family*, `C3_rulers_gold_clocks.md`), in `ℤ`. -/
def G (E : Finset ℕ) : ℤ := ∑ t ∈ E, ((h k I t : ℤ) - 1)

/-- `λ`, defined by `λ + 1 := K + o_I` with `K = 2^k` (*A family*,
`C3_rulers_gold_clocks.md`). -/
def lam : ℕ := 2 ^ k + oE I - 1

/-- **The deficit** `δ(Δ) := k − |Δ| − min Δ` for `Δ ≠ ∅`, `δ(∅) := 0`
(`C3_rulers_gold_clocks.md`). -/
def delta (Δ : Finset ℕ) : ℤ := if Δ = ∅ then 0 else (k : ℤ) - Δ.card - minOr k Δ

/-- **The gold** `γ(Δ) := Σ_{u ∈ I ∖ Δ, u > min Δ} h_u` for `Δ ≠ ∅`, `γ(∅) := 0`
(`C3_rulers_gold_clocks.md`). -/
def gamma (Δ : Finset ℕ) : ℕ :=
  if Δ = ∅ then 0 else ∑ u ∈ (I \ Δ).filter (fun u => minOr k Δ < u), h k I u

/-- **The rulers**: `R_μ(E) := Σ_{t∈E} (h_t − α 2^t) − κ(μ, o_E)` (`C3_rulers_gold_clocks.md`). -/
def ruler (α : ℤ) (μ : ℕ) (E : Finset ℕ) : ℤ :=
  ∑ t ∈ E, ((h k I t : ℤ) - α * 2 ^ t) - kappa μ (oE E)

/-- **The rulers**: `R^♯(E) := Σ_{t∈E} (h_t − α 2^t) − κ(K − 1, o_E)`
(`C3_rulers_gold_clocks.md`). -/
def rulerSharp (α : ℤ) (E : Finset ℕ) : ℤ :=
  ∑ t ∈ E, ((h k I t : ℤ) - α * 2 ^ t) - kappa (2 ^ k - 1) (oE E)

/-- **The clocks**: `ξ_D := λ + 1 − 2 o_D` (`C3_rulers_gold_clocks.md`). -/
def xi (D : Finset ℕ) : ℕ := lam k I + 1 - 2 * oE D

/-- **The clocks**: the raw clock `u_i(D) := φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)`
(`C3_rulers_gold_clocks.md`), meaningful for `(i, D) ≠ (0, ∅)`. -/
def clock (i : ℕ) (D : Finset ℕ) : ℤ :=
  phi (xi k I D) + kappa (i + oE D - 1) (xi k I D) + hSum k I D

/-- `x_D := R_m(D) − R_{m+K}(I ∖ D)` with `α = 1` (`C3_rulers_gold_clocks.md`). -/
def xD (m : ℕ) (D : Finset ℕ) : ℤ := ruler k I 1 m D - ruler k I 1 (m + 2 ^ k) (I \ D)

/-- `x^♯_D := R^♯(D) − R^♯(I ∖ D)` with `α = 1` (`C3_rulers_gold_clocks.md`). -/
def xSharp (D : Finset ℕ) : ℤ := rulerSharp k I 1 D - rulerSharp k I 1 (I \ D)

/-! ### Basic facts about `minOr` and `next` -/

variable {k I}

lemma minOr_eq_of_mem {S : Finset ℕ} {m : ℕ} (hm : m ∈ S) (hle : ∀ x ∈ S, m ≤ x) :
    minOr k S = m := by
  have hne : S.Nonempty := ⟨m, hm⟩
  rw [minOr, dif_pos hne]
  exact le_antisymm (min'_le _ _ hm) (le_min' _ _ _ hle)

lemma minOr_mem {S : Finset ℕ} (hS : S.Nonempty) : minOr k S ∈ S := by
  rw [minOr, dif_pos hS]; exact min'_mem _ _

lemma minOr_le {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) : minOr k S ≤ x := by
  rw [minOr, dif_pos ⟨x, hx⟩]; exact min'_le _ _ hx

lemma minOr_empty : minOr k ∅ = k := by simp [minOr]

lemma next_spec (hI : ∀ t ∈ I, t < k) {t : ℕ} (ht : t ∈ I) :
    t < next k I t ∧ next k I t ≤ k := by
  have hk : k ∈ (insert k I).filter (fun u => t < u) := by simp [hI t ht]
  have hmem := minOr_mem (k := k) ⟨k, hk⟩
  refine ⟨(mem_filter.1 hmem).2, minOr_le hk⟩

lemma next_le_of_mem {t u : ℕ} (hu : u ∈ I) (htu : t < u) : next k I t ≤ u :=
  minOr_le (by simp [hu, htu])

lemma one_le_h (hI : ∀ t ∈ I, t < k) {t : ℕ} (ht : t ∈ I) : 1 ≤ h k I t := by
  have := next_spec hI ht; unfold h; omega

lemma h_cast (hI : ∀ t ∈ I, t < k) {t : ℕ} (ht : t ∈ I) :
    (h k I t : ℤ) = (next k I t : ℤ) - t := by
  have := next_spec hI ht; unfold h; omega

/-- `firstGe m := min{u ∈ I ∪ {k} : u ≥ m}`, an auxiliary for the telescoping of the gaps. -/
def firstGe (k : ℕ) (I : Finset ℕ) (m : ℕ) : ℕ := minOr k ((insert k I).filter (fun u => m ≤ u))

lemma next_eq_firstGe (t : ℕ) : next k I t = firstGe k I (t + 1) := by
  unfold next firstGe; congr 1

/-- The gaps telescope: `Σ_{t ∈ I, t ≥ m} (f(next t) − f t) = f k − f(firstGe m)`. -/
lemma telescope (hI : ∀ t ∈ I, t < k) (f : ℕ → ℤ) :
    ∀ d m, k - m = d → m ≤ k →
      ∑ t ∈ I.filter (fun t => m ≤ t), (f (next k I t) - f t) = f k - f (firstGe k I m) := by
  intro d
  induction d with
  | zero =>
    intro m hd hm
    have hmk : m = k := by omega
    subst hmk
    have h1 : I.filter (fun t => m ≤ t) = ∅ := by
      ext x; simp only [mem_filter, notMem_empty, iff_false, not_and, not_le]
      exact fun hx => hI x hx
    have h2 : firstGe m I m = m :=
      minOr_eq_of_mem (by simp) (fun x hx => (mem_filter.1 hx).2)
    simp [h1, h2]
  | succ d ih =>
    intro m hd hm
    have ih' := ih (m + 1) (by omega) (by omega)
    by_cases hmI : m ∈ I
    · have hsplit : I.filter (fun t => m ≤ t) = insert m (I.filter (fun t => m + 1 ≤ t)) := by
        ext x; simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨hx, hmx⟩
          rcases eq_or_lt_of_le hmx with h | h
          · left; exact h.symm
          · right; exact ⟨hx, h⟩
        · rintro (rfl | ⟨hx, hmx⟩)
          · exact ⟨hmI, le_refl _⟩
          · exact ⟨hx, by omega⟩
      have hnot : m ∉ I.filter (fun t => m + 1 ≤ t) := by simp
      have hfm : firstGe k I m = m :=
        minOr_eq_of_mem (by simp [hmI]) (fun x hx => (mem_filter.1 hx).2)
      rw [hsplit, sum_insert hnot, ih', next_eq_firstGe, hfm]
      ring
    · have hsplit : I.filter (fun t => m ≤ t) = I.filter (fun t => m + 1 ≤ t) := by
        ext x; simp only [mem_filter]
        constructor
        · rintro ⟨hx, hmx⟩
          refine ⟨hx, ?_⟩
          rcases eq_or_lt_of_le hmx with h | h
          · subst h; exact absurd hx hmI
          · exact h
        · rintro ⟨hx, hmx⟩; exact ⟨hx, by omega⟩
      have hfm : firstGe k I m = firstGe k I (m + 1) := by
        unfold firstGe; congr 1; ext x
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨hx, hmx⟩
          refine ⟨hx, ?_⟩
          rcases eq_or_lt_of_le hmx with h | h
          · subst h
            rcases hx with h' | h'
            · omega
            · exact absurd h' hmI
          · exact h
        · rintro ⟨hx, hmx⟩; exact ⟨hx, by omega⟩
      rw [hsplit, ih', hfm]

lemma telescope_mem (hI : ∀ t ∈ I, t < k) (f : ℕ → ℤ) {m : ℕ} (hm : m ∈ I) :
    ∑ t ∈ I.filter (fun t => m ≤ t), (f (next k I t) - f t) = f k - f m := by
  have hmk := hI m hm
  rw [telescope hI f (k - m) m rfl hmk.le]
  congr 2
  exact minOr_eq_of_mem (by simp [hm]) (fun x hx => (mem_filter.1 hx).2)

lemma telescope_all (hI : ∀ t ∈ I, t < k) (f : ℕ → ℤ) :
    ∑ t ∈ I, (f (next k I t) - f t) = f k - f (t1 k I) := by
  have := telescope hI f k 0 (by omega) (Nat.zero_le _)
  rw [show I.filter (fun t => 0 ≤ t) = I by ext; simp] at this
  rw [this, t1]
  congr 2
  by_cases hne : I.Nonempty
  · apply minOr_eq_of_mem
    · simp only [mem_filter, mem_insert, zero_le, and_true]; exact Or.inr (minOr_mem hne)
    · intro x hx
      simp only [mem_filter, mem_insert] at hx
      rcases hx.1 with rfl | hx'
      · exact (hI _ (minOr_mem hne)).le
      · exact minOr_le hx'
  · rw [not_nonempty_iff_eq_empty] at hne
    subst hne
    rw [minOr_empty]
    exact minOr_eq_of_mem (by simp) (by simp)

/-- `k = t₁ + Σ_{t∈I} h_t`. -/
lemma k_eq_t1_add_sum_h (hI : ∀ t ∈ I, t < k) :
    (k : ℤ) = t1 k I + ∑ t ∈ I, (h k I t : ℤ) := by
  have := telescope_all hI (fun t => (t : ℤ))
  rw [sum_congr rfl (fun t ht => h_cast hI ht), this]; ring

lemma G_eq (E : Finset ℕ) :
    G k I E = (hSum k I E : ℤ) - E.card := by
  simp [G, hSum, sum_sub_distrib]

lemma sum_h_sub (α : ℤ) (E : Finset ℕ) :
    ∑ t ∈ E, ((h k I t : ℤ) - α * 2 ^ t) = (hSum k I E : ℤ) - α * oE E := by
  simp [hSum, oE, sum_sub_distrib, mul_sum]

lemma G_sdiff {a b : Finset ℕ} (hba : b ⊆ a) : G k I (a \ b) = G k I a - G k I b := by
  unfold G; rw [← sum_sdiff hba]; ring

/-! ### Lemma 5.0 -/

/-- **Lemma 5.0** of `C3_rulers_gold_clocks.md`, first part: for every dancer `D ⊆ I`,
`ξ_D = λ + 1 − 2 o_D` is a positive integer: the natural number subtraction in `xi` does not
truncate (`ξ_D = K + o_I − 2 o_D` in `ℤ`) and `ξ_D ≥ 1`. -/
theorem lemma_5_0_xi (hI : ∀ t ∈ I, t < k) {D : Finset ℕ} (hD : D ⊆ I) :
    (xi k I D : ℤ) = 2 ^ k + oE I - 2 * oE D ∧ 1 ≤ xi k I D := by
  have hlt := oE_lt D k (fun t ht => hI t (hD ht))
  have hs := oE_sdiff hD
  have hK : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  unfold xi lam
  constructor
  · push_cast [show 2 * oE D ≤ 2 ^ k + oE I - 1 + 1 by omega, show 1 ≤ 2 ^ k + oE I by omega]
    ring
  · omega

/-- **Lemma 5.0** of `C3_rulers_gold_clocks.md`, second part: for `b ⊆ a ⊆ I`,
`o_{a∖b} = o_a − o_b` and `K − o_{a∖b} ≥ 1` (in `ℤ`, `K = 2^k`). -/
theorem lemma_5_0_sdiff (hI : ∀ t ∈ I, t < k) {a b : Finset ℕ} (hba : b ⊆ a) (ha : a ⊆ I) :
    (oE (a \ b) : ℤ) = oE a - oE b ∧ 1 ≤ (2 : ℤ) ^ k - oE (a \ b) := by
  have hs := oE_sdiff hba
  have hlt := oE_lt (a \ b) k (fun t ht => hI t (ha (mem_sdiff.1 ht).1))
  constructor
  · omega
  · have : ((oE (a \ b) : ℕ) : ℤ) < ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast hlt
    push_cast at this; omega

/-! ### Lemma 5.1 -/

/-- **Lemma 5.1 (a)** of `C3_rulers_gold_clocks.md`: for `Δ ⊆ I`, `δ(Δ) = G(Δ) + γ(Δ)`. -/
theorem lemma_5_1_a (hI : ∀ t ∈ I, t < k) {Δ : Finset ℕ} (hΔ : Δ ⊆ I) :
    delta k Δ = G k I Δ + gamma k I Δ := by
  by_cases he : Δ = ∅
  · subst he; simp [delta, gamma, G]
  · have hne : Δ.Nonempty := nonempty_iff_ne_empty.2 he
    set m := minOr k Δ with hm
    have hmΔ : m ∈ Δ := minOr_mem hne
    have hmI : m ∈ I := hΔ hmΔ
    have htel := telescope_mem hI (fun t => (t : ℤ)) hmI
    have hsplit : I.filter (fun t => m ≤ t) =
        Δ ∪ (I \ Δ).filter (fun u => m < u) := by
      ext x; simp only [mem_filter, mem_union, mem_sdiff]
      constructor
      · rintro ⟨hx, hmx⟩
        by_cases hxΔ : x ∈ Δ
        · exact Or.inl hxΔ
        · refine Or.inr ⟨⟨hx, hxΔ⟩, lt_of_le_of_ne hmx ?_⟩
          rintro rfl; exact hxΔ hmΔ
      · rintro (hx | ⟨⟨hx, _⟩, hmx⟩)
        · exact ⟨hΔ hx, minOr_le hx⟩
        · exact ⟨hx, hmx.le⟩
    have hdisj : Disjoint Δ ((I \ Δ).filter (fun u => m < u)) := by
      rw [disjoint_left]; intro x hx hx'; simp [hx] at hx'
    have hcast : ∀ t ∈ I.filter (fun t => m ≤ t), ((next k I t : ℤ) - t) = (h k I t : ℤ) :=
      fun t ht => (h_cast hI (mem_filter.1 ht).1).symm
    rw [sum_congr rfl hcast, hsplit, sum_union hdisj] at htel
    simp only [delta, gamma, if_neg he, G, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
    rw [← hm]
    push_cast
    linarith

/-- **Lemma 5.1 (b)** of `C3_rulers_gold_clocks.md`: for `Δ ⊆ I`, `γ(Δ) = 0` if and only if
`Δ = ∅` or `Δ = {t ∈ I : t ≥ min Δ}` (a tail of `I`). -/
theorem lemma_5_1_b (hI : ∀ t ∈ I, t < k) {Δ : Finset ℕ} (hΔ : Δ ⊆ I) :
    gamma k I Δ = 0 ↔ Δ = ∅ ∨ Δ = I.filter (fun t => minOr k Δ ≤ t) := by
  by_cases he : Δ = ∅
  · simp [he, gamma]
  · have hne : Δ.Nonempty := nonempty_iff_ne_empty.2 he
    have hmΔ : minOr k Δ ∈ Δ := minOr_mem hne
    rw [gamma, if_neg he]; simp only [he, false_or]
    rw [sum_eq_zero_iff]
    constructor
    · intro h0
      ext x; simp only [mem_filter]
      constructor
      · intro hx; exact ⟨hΔ hx, minOr_le hx⟩
      · rintro ⟨hx, hmx⟩
        by_contra hxΔ
        have hlt : minOr k Δ < x := lt_of_le_of_ne hmx (by rintro rfl; exact hxΔ hmΔ)
        have := h0 x (by simp [hx, hxΔ, hlt])
        have := one_le_h hI hx
        omega
    · intro htail u hu
      simp only [mem_filter, mem_sdiff] at hu
      exfalso
      apply hu.1.2
      rw [htail]; simp [hu.1.1, hu.2.le]

end Rulers
