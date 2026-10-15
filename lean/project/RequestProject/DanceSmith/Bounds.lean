module

public import RequestProject.DanceSmith.SmithForm
public import RequestProject.DanceSmith.Basic

/-!
# The common skeleton of Parts S and Z of `C15_smith_form_of_the_dance_matrix.md`

This file packages the parts of the proof of Theorem 7.10 that do not depend on the dance:

* `floor_minor` — the *floor* (Lemma 6.1 / Theorem 7.4 in the file): if every entry `M p q` on
  an arrow `arr p q` is divisible by `2^{C + c(p, q)}`, the entries off the arrows vanish, and every
  `r`-matching (C2's `SmithBounds.IsRMatching`) along the arrows costs at least `Y`, then every
  `r × r` minor is divisible by `2^{r C + Y}`; this is `SmithBounds.lemma_A1`.
* `smith_of_bounds` — the *conclusion* (Theorem 6.5 in the file): (Q1), (Q2) and
  `Divisors.theorem_B_without_M` turn the floor, the ceiling and a rank bound into the
  determinantal divisors and the Smith form.

Exponents which are integers known to be non-negative are passed to `2 ^ ·` through `Int.toNat`.
-/

@[expose] public section

namespace DanceSmith

open Finset Matrix AntitonicFit

/-- `ifit N x` only depends on the values of `x` at the positions `< N` (used in Parts S and Z of
`C15_smith_form_of_the_dance_matrix.md`). -/
lemma ifit_congr {N : ℕ} {x x' : ℕ → ℤ} (h : ∀ j < N, x j = x' j) : ifit N x = ifit N x' := by
  have hf : fit N (toR x) = fit N (toR x') := fit_congr fun j hj => by simp [toR, h j hj]
  funext j
  unfold ifit
  rw [hf]
  split_ifs
  · congr 1
    refine sum_congr rfl fun i hi => h i ?_
    simp only [levelSet, mem_filter, mem_range] at hi
    exact hi.1
  · rfl

/-- An exact power of `2` dividing `x` is its 2-valuation. -/
lemma padicValInt_eq_of_exact {x : ℤ} {n : ℕ} (h1 : (2 : ℤ) ^ n ∣ x)
    (h2 : ¬ (2 : ℤ) ^ (n + 1) ∣ x) : x ≠ 0 ∧ padicValInt 2 x = n := by
  have hx : x ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  refine ⟨hx, le_antisymm ?_ ?_⟩
  · by_contra hlt
    exact h2 (by exact_mod_cast ((padicValInt_dvd_iff (p := 2) (n + 1) x).2
      (Or.inr (by omega))))
  · rcases (padicValInt_dvd_iff (p := 2) n x).1 (by exact_mod_cast h1) with h | h
    · exact absurd h hx
    · exact h

/-- The **floor** (Lemma 6.1 and Theorem 7.4, as used in Parts S and Z of
`C15_smith_form_of_the_dance_matrix.md`), for a matrix on `Fin N` whose positions are compared with
the positions `ℕ` of an `r`-matching. -/
theorem floor_minor {N : ℕ} (M : Matrix (Fin N) (Fin N) ℤ) (arr : ℕ → ℕ → Prop)
    (c : ℕ → ℕ → ℤ) (C Y : ℤ) {r : ℕ}
    (hsupp : ∀ p q : Fin N, ¬ arr p q → M p q = 0)
    (hdiv : ∀ p q : Fin N, arr p q → 0 ≤ C + c p q ∧ (2 : ℤ) ^ (C + c p q).toNat ∣ M p q)
    (hmatch : ∀ Rows β, SmithBounds.IsRMatching N arr r Rows β → Y ≤ ∑ a ∈ Rows, c a (β a))
    (A B : Finset (Fin N)) (hA : A.card = r) (hB : B.card = r) :
    (2 : ℤ) ^ ((r : ℤ) * C + Y).toNat ∣ Divisors.minor M r A B := by
  classical
  rw [Divisors.minor_of_card _ hA hB]
  set e : Fin r ≃ A := (A.orderIsoOfFin hA).toEquiv
  set f : Fin r ≃ B := (B.orderIsoOfFin hB).toEquiv
  have hmin : M.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB) = SmithBounds.minor M e f := by
    ext i j; simp [SmithBounds.minor, e, f]
  rw [hmin]
  set cn : Fin N → Fin N → ℕ := fun p q => if arr p q then (C + c p q).toNat else 0
  refine SmithBounds.lemma_A1 M 2 (fun p q => arr p q) hsupp cn (fun p q => ?_) e f _ ?_
  · by_cases h : arr p q
    · simp only [cn, if_pos h]; exact (hdiv p q h).2
    · simp [cn, if_neg h]
  · intro β hβ
    -- the matching, as an `r`-matching of positions
    set βn : ℕ → ℕ := fun x => if h : x < N then
      (if hx : (⟨x, h⟩ : Fin N) ∈ A then ((β ⟨⟨x, h⟩, hx⟩ : B) : Fin N).val else 0) else 0
    have hβn : ∀ p : A, βn (p : Fin N) = ((β p : B) : Fin N) := by
      intro p
      simp only [βn, dif_pos (p : Fin N).2, Fin.eta, dif_pos p.2]
    set Rows := A.image (fun p : Fin N => (p : ℕ))
    have hRows : SmithBounds.IsRMatching N arr r Rows βn := by
      refine ⟨fun x hx => ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨p, -, rfl⟩ := mem_image.1 hx; exact mem_range.2 p.2
      · rw [card_image_of_injective _ Fin.val_injective, hA]
      · intro x hx y hy hxy
        obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
        obtain ⟨q, hq, rfl⟩ := mem_image.1 hy
        have h1 := hβn ⟨p, hp⟩
        have h2 := hβn ⟨q, hq⟩
        simp only at h1 h2 hxy
        rw [h1, h2] at hxy
        have := β.injective (Subtype.ext (Fin.ext hxy))
        simp only [Subtype.mk.injEq] at this
        rw [this]
      · obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
        rw [hβn ⟨p, hp⟩]; exact Fin.is_lt _
      · obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
        rw [hβn ⟨p, hp⟩]; exact hβ ⟨p, hp⟩
    have hY := hmatch Rows βn hRows
    have hsum : ∑ a ∈ Rows, c a (βn a) = ∑ p : A, c (p : Fin N) ((β p : B) : Fin N) := by
      rw [sum_image (fun x _ y _ h => Fin.ext h), ← sum_coe_sort A]
      exact sum_congr rfl fun p _ => by rw [hβn p]
    have hcost : ((SmithBounds.cost cn β : ℕ) : ℤ) = r * C + ∑ p : A, c (p : Fin N) ((β p : B) : Fin N) := by
      unfold SmithBounds.cost
      push_cast
      rw [sum_congr rfl fun (p : A) _ => show ((cn p (β p) : ℕ) : ℤ) = C + c (p : Fin N) ((β p : B) : Fin N) by
        simp only [cn, if_pos (hβ p)]; exact Int.toNat_of_nonneg (hdiv _ _ (hβ p)).1]
      rw [sum_add_distrib, sum_const, card_univ, Fintype.card_coe, hA, nsmul_eq_mul]
    rw [Int.toNat_le, hcost]
    linarith

/-- The **conclusion** (Theorem 6.5, as used in Parts S and Z of
`C15_smith_form_of_the_dance_matrix.md`): for an `n × n` integer matrix `A` and `N' ≤ n`, if every
`r × r` minor (`r ≤ N'`) is divisible by `2^{r C + Σ_{[N'−r, N')} ifit_{N'}(x)}` (floor), some
`r × r` minor is non-zero of valuation at most `r C + Σ_{[N'−r, N')} x` (ceiling), and every
`(N' + 1) × (N' + 1)` minor vanishes if `N' < n`, then `dd_r(A) = r C + Σ_{[N'−r, N')} ifit_{N'}(x)`
for `r ≤ N'`, and `A` has the Smith form at 2 with exponents `C + ifit_{N'}(x)(N' − 1 − j)`,
`j < N'`, followed by `n − N'` zeros. -/
theorem smith_of_bounds {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {N' : ℕ} (hN' : N' ≤ n)
    (x : ℕ → ℤ) (C : ℤ)
    (hfloor : ∀ r ≤ N', ∀ B D : Finset (Fin n), B.card = r → D.card = r →
      (2 : ℤ) ^ ((r : ℤ) * C + ∑ j ∈ Ico (N' - r) N', ifit N' x j).toNat ∣ Divisors.minor A r B D)
    (hceil : ∀ r ≤ N', ∃ B D : Finset (Fin n), B.card = r ∧ D.card = r ∧
      Divisors.minor A r B D ≠ 0 ∧
      (padicValInt 2 (Divisors.minor A r B D) : ℤ) ≤ r * C + ∑ j ∈ Ico (N' - r) N', x j)
    (hrank : N' < n → ∀ B D : Finset (Fin n), B.card = N' + 1 → D.card = N' + 1 →
      Divisors.minor A (N' + 1) B D = 0) :
    (∀ r ≤ N', (Divisors.dd A r : ℤ) = r * C + ∑ j ∈ Ico (N' - r) N', ifit N' x j) ∧
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, Odd P.det ∧ Odd Q.det ∧
      ∃ E : ℕ → ℕ, (∀ j < N', (E j : ℤ) = C + ifit N' x (N' - 1 - j)) ∧
        ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧
          P * A * Q = diagonal (fun j : Fin n => if (j : ℕ) < N' then u j * 2 ^ E j else 0) := by
  obtain ⟨P, Q, hP, hQ, ρ, hρ, e, he, u, hu, hD⟩ := Q1 n A
  obtain ⟨hdd, hzero, -⟩ := Q2 A P Q hP hQ hρ he hu hD
  have hρN : ρ = N' := by
    apply le_antisymm
    · by_contra hlt
      push_neg at hlt
      obtain ⟨_, B, D, hB, hD', h0, -⟩ := Q2_nonempty A P Q hρ he hu hD (show N' + 1 ≤ ρ by omega)
      exact h0 (hrank (by omega) B D hB hD')
    · by_contra hlt
      push_neg at hlt
      obtain ⟨B, D, hB, hD', h0, -⟩ := hceil N' le_rfl
      exact h0 (hzero N' hlt B D hB hD')
  subst hρN
  have hlow : ∀ r ≤ ρ, (r : ℤ) * C + ∑ j ∈ Ico (ρ - r) ρ, ifit ρ x j ≤ Divisors.dd A r := by
    intro r hr
    have hne := Q2_nonempty A P Q hρ he hu hD hr
    have := Divisors.le_dd_of_dvd hne (hfloor r hr)
    exact (Int.self_le_toNat _).trans (by exact_mod_cast this)
  have hup : ∀ r ≤ ρ, (Divisors.dd A r : ℤ) ≤ r * C + ∑ j ∈ Ico (ρ - r) ρ, x j := by
    intro r hr
    obtain ⟨B, D, hB, hD', h0, hv⟩ := hceil r hr
    exact (by exact_mod_cast Divisors.dd_le A hB hD' h0 : (Divisors.dd A r : ℤ) ≤ _).trans hv
  have hdHat : ∀ r ≤ ρ, Divisors.dHat C (fun j => (e j : ℤ)) r = (Divisors.dd A r : ℤ) - r * C := by
    intro r hr
    rw [Divisors.dHat, hdd r hr]; push_cast; ring
  obtain ⟨h1, h2⟩ := Divisors.theorem_B_without_M ρ x C (fun j => (e j : ℤ))
    (fun i j hij hj => by simp only; exact_mod_cast he i j hij hj)
    (fun r hr => by rw [hdHat r hr]; linarith [hlow r hr])
    (fun r hr => by rw [hdHat r hr]; linarith [hup r hr])
  refine ⟨fun r hr => ?_, P, Q, hP, hQ, e, fun j hj => h2 j hj, u, hu, hD⟩
  have := h1 r hr
  rw [hdHat r hr] at this
  linarith

end DanceSmith
