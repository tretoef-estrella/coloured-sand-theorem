module

public import RequestProject.OddSmith.Basic

/-!
# The common skeleton of Parts S and Z of `CSI18_theorem_4_4_smith_form_of_Mp.md`, at a prime `p`

C15's `DanceSmith.floor_minor`, `DanceSmith.smith_of_bounds` and `DanceSmith.golden_ceiling` work at
the prime `2`; here they are redone at a prime `p` (C15 is not modified):

* `oddSmith_floor_minor` — the *floor*: `SmithBounds.lemma_A1` with `π = p`.
* `oddSmith_smith_of_bounds` — the *conclusion*: CSI14's (Q1) `Q1_smith`, (Q2) `Q2_smith` and C5's
  `Divisors.theorem_B_without_M` turn floor, ceiling and a rank bound into the `p`-adic
  determinantal divisors `ddP` and a Smith form at `p`.
* `oddSmith_ceiling` — the *ceiling*: CSI14's (C1) `C1_natural_minor`, read on the positions of the
  o-order (rows `[N − r, N)`, columns `[0, r)`).

Exponents which are integers known to be non-negative are passed to `p ^ ·` through `Int.toNat`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset Matrix AntitonicFit TheoremF

variable {p : ℕ}

/-- An exact power of `p` dividing `x` is its `p`-valuation. -/
lemma oddSmith_padicValInt_eq_of_exact [Fact p.Prime] {x : ℤ} {n : ℕ} (h1 : (p : ℤ) ^ n ∣ x)
    (h2 : ¬ (p : ℤ) ^ (n + 1) ∣ x) : x ≠ 0 ∧ padicValInt p x = n := by
  have hx : x ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  refine ⟨hx, le_antisymm ?_ ?_⟩
  · by_contra hlt
    exact h2 (by exact_mod_cast ((padicValInt_dvd_iff (p := p) (n + 1) x).2
      (Or.inr (by omega))))
  · rcases (padicValInt_dvd_iff (p := p) n x).1 (by exact_mod_cast h1) with h | h
    · exact absurd h hx
    · exact h

/-- The **floor** at `p` (as C15's `DanceSmith.floor_minor`; Parts S and Z of
`CSI18_theorem_4_4_smith_form_of_Mp.md`): if every entry `M a b` on an arrow is divisible by
`p^{C + c(a, b)}`, the entries off the arrows vanish, and every `r`-matching along the arrows costs at
least `Y`, then every `r × r` minor is divisible by `p^{r C + Y}`. -/
theorem oddSmith_floor_minor {N : ℕ} (M : Matrix (Fin N) (Fin N) ℤ) (arr : ℕ → ℕ → Prop)
    (c : ℕ → ℕ → ℤ) (C Y : ℤ) {r : ℕ}
    (hsupp : ∀ a b : Fin N, ¬ arr a b → M a b = 0)
    (hdiv : ∀ a b : Fin N, arr a b → 0 ≤ C + c a b ∧ (p : ℤ) ^ (C + c a b).toNat ∣ M a b)
    (hmatch : ∀ Rows β, SmithBounds.IsRMatching N arr r Rows β → Y ≤ ∑ a ∈ Rows, c a (β a))
    (A B : Finset (Fin N)) (hA : A.card = r) (hB : B.card = r) :
    (p : ℤ) ^ ((r : ℤ) * C + Y).toNat ∣ Divisors.minor M r A B := by
  classical
  rw [Divisors.minor_of_card _ hA hB]
  set e : Fin r ≃ A := (A.orderIsoOfFin hA).toEquiv
  set f : Fin r ≃ B := (B.orderIsoOfFin hB).toEquiv
  have hmin : M.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB) = SmithBounds.minor M e f := by
    ext i j; simp [SmithBounds.minor, e, f]
  rw [hmin]
  set cn : Fin N → Fin N → ℕ := fun a b => if arr a b then (C + c a b).toNat else 0
  refine SmithBounds.lemma_A1 M (p : ℤ) (fun a b => arr a b) hsupp cn (fun a b => ?_) e f _ ?_
  · by_cases h : arr a b
    · simp only [cn, if_pos h]; exact (hdiv a b h).2
    · simp [cn, if_neg h]
  · intro β hβ
    set βn : ℕ → ℕ := fun x => if h : x < N then
      (if hx : (⟨x, h⟩ : Fin N) ∈ A then ((β ⟨⟨x, h⟩, hx⟩ : B) : Fin N).val else 0) else 0
    have hβn : ∀ a : A, βn (a : Fin N) = ((β a : B) : Fin N) := by
      intro a
      simp only [βn, dif_pos (a : Fin N).2, Fin.eta, dif_pos a.2]
    set Rows := A.image (fun a : Fin N => (a : ℕ))
    have hRows : SmithBounds.IsRMatching N arr r Rows βn := by
      refine ⟨fun x hx => ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨a, -, rfl⟩ := mem_image.1 hx; exact mem_range.2 a.2
      · rw [card_image_of_injective _ Fin.val_injective, hA]
      · intro x hx y hy hxy
        obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
        obtain ⟨b, hb, rfl⟩ := mem_image.1 hy
        have h1 := hβn ⟨a, ha⟩
        have h2 := hβn ⟨b, hb⟩
        simp only at h1 h2 hxy
        rw [h1, h2] at hxy
        have := β.injective (Subtype.ext (Fin.ext hxy))
        simp only [Subtype.mk.injEq] at this
        rw [this]
      · obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
        rw [hβn ⟨a, ha⟩]; exact Fin.is_lt _
      · obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
        rw [hβn ⟨a, ha⟩]; exact hβ ⟨a, ha⟩
    have hY := hmatch Rows βn hRows
    have hsum : ∑ a ∈ Rows, c a (βn a) = ∑ a : A, c (a : Fin N) ((β a : B) : Fin N) := by
      rw [sum_image (fun x _ y _ h => Fin.ext h), ← sum_coe_sort A]
      exact sum_congr rfl fun a _ => by rw [hβn a]
    have hcost : ((SmithBounds.cost cn β : ℕ) : ℤ) =
        r * C + ∑ a : A, c (a : Fin N) ((β a : B) : Fin N) := by
      unfold SmithBounds.cost
      push_cast
      rw [sum_congr rfl fun (a : A) _ => show ((cn a (β a) : ℕ) : ℤ) =
          C + c (a : Fin N) ((β a : B) : Fin N) by
        simp only [cn, if_pos (hβ a)]; exact Int.toNat_of_nonneg (hdiv _ _ (hβ a)).1]
      rw [sum_add_distrib, sum_const, card_univ, Fintype.card_coe, hA, nsmul_eq_mul]
    rw [Int.toNat_le, hcost]
    linarith

/-- The **conclusion** at `p` (as C15's `DanceSmith.smith_of_bounds`, with CSI14's (Q1), (Q2) and
C5's `Divisors.theorem_B_without_M`; Parts S and Z of `CSI18_theorem_4_4_smith_form_of_Mp.md`): for
an `n × n` integer matrix `A` and `N' ≤ n`, if every `r × r` minor (`r ≤ N'`) is divisible by
`p^{r C + Σ_{[N'−r, N')} ifit_{N'}(x)}` (floor), some `r × r` minor is non-zero of `p`-valuation at most
`r C + Σ_{[N'−r, N')} x` (ceiling), and every `(N' + 1) × (N' + 1)` minor vanishes if `N' < n`, then
`ddP_r(A) = r C + Σ_{[N'−r, N')} ifit_{N'}(x)` for `r ≤ N'`, and `A` has the Smith form at `p` with
exponents `C + ifit_{N'}(x)(N' − 1 − j)`, `j < N'`, followed by `n − N'` zeros. -/
theorem oddSmith_smith_of_bounds (hp : p.Prime) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {N' : ℕ}
    (hN' : N' ≤ n) (x : ℕ → ℤ) (C : ℤ)
    (hfloor : ∀ r ≤ N', ∀ B D : Finset (Fin n), B.card = r → D.card = r →
      (p : ℤ) ^ ((r : ℤ) * C + ∑ j ∈ Ico (N' - r) N', ifit N' x j).toNat ∣ Divisors.minor A r B D)
    (hceil : ∀ r ≤ N', ∃ B D : Finset (Fin n), B.card = r ∧ D.card = r ∧
      Divisors.minor A r B D ≠ 0 ∧
      (padicValInt p (Divisors.minor A r B D) : ℤ) ≤ r * C + ∑ j ∈ Ico (N' - r) N', x j)
    (hrank : N' < n → ∀ B D : Finset (Fin n), B.card = N' + 1 → D.card = N' + 1 →
      Divisors.minor A (N' + 1) B D = 0) :
    (∀ r ≤ N', (ddP p A r : ℤ) = r * C + ∑ j ∈ Ico (N' - r) N', ifit N' x j) ∧
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, ¬ (p : ℤ) ∣ P.det ∧ ¬ (p : ℤ) ∣ Q.det ∧
      ∃ E : ℕ → ℕ, (∀ j < N', (E j : ℤ) = C + ifit N' x (N' - 1 - j)) ∧
        ∃ u : ℕ → ℤ, (∀ j, ¬ (p : ℤ) ∣ u j) ∧
          P * A * Q = diagonal (fun j : Fin n => if (j : ℕ) < N' then u j * (p : ℤ) ^ E j else 0) := by
  haveI := Fact.mk hp
  obtain ⟨P, Q, hP, hQ, ρ, hρ, e, he, u, hu, hD⟩ := Q1_smith hp n A
  obtain ⟨hdd, hzero, -⟩ := Q2_smith hp A P Q hP hQ hρ he hu hD
  have hD' : P * A * Q = diagonal (smithDiagP (n := n) p ρ e u) := hD
  have hne : ∀ r ≤ ρ, (minorValsP p A r).Nonempty := fun r hr =>
    minorValsP_nonempty_of_mul P A Q (by rw [hD']; exact (ddP_smithDiagP hp hρ he hu hr).2)
  have hρN : ρ = N' := by
    apply le_antisymm
    · by_contra hlt
      push_neg at hlt
      obtain ⟨_, B, D, hB, hD'', h0, -⟩ := hne (N' + 1) (by omega)
      exact h0 (hrank (by omega) B D hB hD'')
    · by_contra hlt
      push_neg at hlt
      obtain ⟨B, D, hB, hD'', h0, -⟩ := hceil N' le_rfl
      exact h0 (hzero N' hlt B D hB hD'')
  subst hρN
  have hlow : ∀ r ≤ ρ, (r : ℤ) * C + ∑ j ∈ Ico (ρ - r) ρ, ifit ρ x j ≤ ddP p A r := by
    intro r hr
    have := le_ddP_of_dvd (hne r hr) (hfloor r hr)
    exact (Int.self_le_toNat _).trans (by exact_mod_cast this)
  have hup : ∀ r ≤ ρ, (ddP p A r : ℤ) ≤ r * C + ∑ j ∈ Ico (ρ - r) ρ, x j := by
    intro r hr
    obtain ⟨B, D, hB, hD'', h0, hv⟩ := hceil r hr
    exact (by exact_mod_cast ddP_le A hB hD'' h0 : (ddP p A r : ℤ) ≤ _).trans hv
  have hdHat : ∀ r ≤ ρ, Divisors.dHat C (fun j => (e j : ℤ)) r = (ddP p A r : ℤ) - r * C := by
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

/-- The **ceiling** at `p` (CSI14's (C1) `C1_natural_minor`, read in o-order as C15's
`DanceSmith.golden_ceiling`; Parts S and Z of `CSI18_theorem_4_4_smith_form_of_Mp.md`): under (S) and
(H) of (C1), for every `r ≤ N` the matrix `(M'(dancer(N − r + i), dancer(j)))_{i, j < r}` has
determinant of exact `p`-valuation `r C + Σ_{j ∈ [N − r, N)} x(dancer j)`, `x = xP I R₁ R₂`. -/
theorem oddSmith_ceiling (hp : p.Prime) (k : ℕ) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k)
    (R₁ R₂ : Finset ℕ → ℤ) (C : ℤ) (M' : Finset ℕ → Finset ℕ → ℤ)
    (hS : ∀ a b, a ⊆ I → b ⊆ I → ¬ b ⊆ a → M' a b = 0)
    (hH : ∀ a b, b ⊆ a → a ⊆ I → ∃ n : ℕ, (n : ℤ) = C + cHatP k I R₁ R₂ a b ∧
      (p : ℤ) ^ n ∣ M' a b ∧ ¬ (p : ℤ) ^ (n + 1) ∣ M' a b)
    {r : ℕ} (hr : r ≤ 2 ^ #I) :
    ∃ n : ℕ, (n : ℤ) = r * C + ∑ j ∈ Ico (2 ^ #I - r) (2 ^ #I), xP I R₁ R₂ (dancer I j) ∧
      (p : ℤ) ^ n ∣ (Matrix.of fun i j : Fin r => M' (dancer I (2 ^ #I - r + i)) (dancer I j)).det ∧
      ¬ (p : ℤ) ^ (n + 1) ∣
        (Matrix.of fun i j : Fin r => M' (dancer I (2 ^ #I - r + i)) (dancer I j)).det := by
  set N := 2 ^ #I with hN
  have hL : ∀ i : Fin r, dancer I (N - r + i) ∈ GoldenMatching.Lr I r := fun i => by
    simp only [GoldenMatching.Lr, mem_filter, mem_powerset]
    exact ⟨lemma_0a I _, by rw [lemma_0c_rank (by omega)]; omega⟩
  have hF : ∀ j : Fin r, dancer I j ∈ GoldenMatching.Fr I r := fun j => by
    simp only [GoldenMatching.Fr, mem_filter, mem_powerset]
    exact ⟨lemma_0a I _, by rw [lemma_0c_rank (by omega)]; exact j.2⟩
  set e : Fin r ≃ GoldenMatching.Lr I r := Equiv.ofBijective (fun i => ⟨_, hL i⟩) ⟨fun i i' h => by
      have h' := congrArg Subtype.val h
      have := CellFloor.dancer_inj (I := I) (by omega) (by omega) h'
      exact Fin.ext (by omega),
    fun D => by
      obtain ⟨D, hD⟩ := D
      simp only [GoldenMatching.Lr, mem_filter, mem_powerset] at hD
      have hlt := GoldenMatching.rank_lt hD.1
      refine ⟨⟨GoldenMatching.rank I D - (N - r), by omega⟩, Subtype.ext ?_⟩
      simp only
      rw [show N - r + (GoldenMatching.rank I D - (N - r)) = GoldenMatching.rank I D by omega,
        DanceSmith.dancer_rank hD.1]⟩
  set f : Fin r ≃ GoldenMatching.Fr I r := Equiv.ofBijective (fun j => ⟨_, hF j⟩) ⟨fun j j' h => by
      have h' := congrArg Subtype.val h
      exact Fin.ext (CellFloor.dancer_inj (I := I) (by omega) (by omega) h'),
    fun D => by
      obtain ⟨D, hD⟩ := D
      simp only [GoldenMatching.Fr, mem_filter, mem_powerset] at hD
      exact ⟨⟨GoldenMatching.rank I D, hD.2⟩, Subtype.ext (DanceSmith.dancer_rank hD.1)⟩⟩
  obtain ⟨n, hn, h1, h2, -⟩ := C1_natural_minor k hI R₁ R₂ hp C M' hS hH r hr e f
  refine ⟨n, ?_, h1, h2⟩
  rw [hn, UP, DanceSmith.sum_Lr _ r]

end ColouredSand.OddTwist
