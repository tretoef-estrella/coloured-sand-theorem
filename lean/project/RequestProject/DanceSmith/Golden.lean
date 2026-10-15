module

public import RequestProject.DanceSmith.Bounds

/-!
# The ceiling of Parts S and Z of `C15_smith_form_of_the_dance_matrix.md`

`GoldenMatching.corollary_D` (C4) read on the positions of the o-order: the rows `L_r` are the
dancers at the positions `[N − r, N)` and the columns `F_r` those at the positions `[0, r)`, both
listed increasingly; `U(r) = Σ_{j ∈ [N − r, N)} x_j`.  On a matrix `M` on `Fin N`, the rows of the
positions `[N − r, N)` and the columns of the positions `[0, r)` form the minor
`Divisors.minor M r (lastSet N r) (firstSet N r)`.
-/

@[expose] public section

namespace DanceSmith

open Finset Matrix TheoremF

/-- The positions `[N − r, N)` as a subset of `Fin N` (rows of the ceiling minor, Parts S and Z of
`C15_smith_form_of_the_dance_matrix.md`). -/
def lastSet (N r : ℕ) : Finset (Fin N) := univ.filter (fun p : Fin N => N - r ≤ (p : ℕ))

/-- The positions `[0, r)` as a subset of `Fin N` (columns of the ceiling minor, Parts S and Z of
`C15_smith_form_of_the_dance_matrix.md`). -/
def firstSet (N r : ℕ) : Finset (Fin N) := univ.filter (fun p : Fin N => (p : ℕ) < r)

lemma card_firstSet {N r : ℕ} (hr : r ≤ N) : (firstSet N r).card = r :=
  Divisors.card_filter_lt hr

lemma card_lastSet {N r : ℕ} (hr : r ≤ N) : (lastSet N r).card = r := by
  have : lastSet N r = (firstSet N r).map (Fin.revPerm.toEmbedding) := by
    ext p
    simp only [lastSet, firstSet, mem_filter, mem_univ, true_and, mem_map,
      Equiv.coe_toEmbedding, Fin.revPerm_apply]
    constructor
    · intro h; exact ⟨p.rev, by simp [Fin.val_rev]; omega, by simp⟩
    · rintro ⟨q, hq, rfl⟩; simp [Fin.val_rev]; omega
  rw [this, card_map, card_firstSet hr]

/-- The ceiling minor is `det (M (N − r + i) j)_{i, j < r}`. -/
lemma minor_last_first {N : ℕ} (M : Matrix (Fin N) (Fin N) ℤ) {r : ℕ} (hr : r ≤ N) :
    Divisors.minor M r (lastSet N r) (firstSet N r) =
      (Matrix.of fun i j : Fin r => M ⟨N - r + i, by omega⟩ ⟨j, by omega⟩).det := by
  rw [Divisors.minor_of_card _ (card_lastSet hr) (card_firstSet hr)]
  have h1 : (fun i : Fin r => (⟨N - r + i, by omega⟩ : Fin N)) =
      (lastSet N r).orderEmbOfFin (card_lastSet hr) :=
    orderEmbOfFin_unique _ (fun i => by simp [lastSet]; omega) (fun i j h => by
      simp only [Fin.mk_lt_mk]; exact Nat.add_lt_add_left h _)
  have h2 : (fun j : Fin r => (⟨j, by omega⟩ : Fin N)) =
      (firstSet N r).orderEmbOfFin (card_firstSet hr) :=
    orderEmbOfFin_unique _ (fun j => by simp [firstSet]) (fun i j h => by simpa using h)
  rw [← h1, ← h2]
  rfl

lemma dancer_rank {I D : Finset ℕ} (hD : D ⊆ I) : dancer I (GoldenMatching.rank I D) = D :=
  rank_injOn (lemma_0a I _) hD (lemma_0c_rank (GoldenMatching.rank_lt hD))

/-- `U(r) = Σ_{D ∈ L_r} x_D = Σ_{j ∈ [N − r, N)} x(dancer_I(j))` (proof of Corollary 6.3 as used in
Parts S and Z of `C15_smith_form_of_the_dance_matrix.md`). -/
lemma sum_Lr {I : Finset ℕ} (g : Finset ℕ → ℤ) (r : ℕ) :
    ∑ D ∈ GoldenMatching.Lr I r, g D = ∑ j ∈ Ico (2 ^ #I - r) (2 ^ #I), g (dancer I j) := by
  symm
  refine sum_nbij' (fun j => dancer I j) (fun D => GoldenMatching.rank I D) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_Ico] at hj
    simp only [GoldenMatching.Lr, mem_filter, mem_powerset]
    exact ⟨lemma_0a I j, by rw [lemma_0c_rank hj.2]; exact hj.1⟩
  · intro D hD
    simp only [GoldenMatching.Lr, mem_filter, mem_powerset] at hD
    simp only [mem_Ico]
    exact ⟨hD.2, GoldenMatching.rank_lt hD.1⟩
  · intro j hj
    simp only [mem_Ico] at hj
    exact lemma_0c_rank hj.2
  · intro D hD
    simp only [GoldenMatching.Lr, mem_filter, mem_powerset] at hD
    exact dancer_rank hD.1
  · intros; rfl

/-- **The ceiling** (Corollary 6.3, `GoldenMatching.corollary_D`, read in o-order; Parts S and Z of
`C15_smith_form_of_the_dance_matrix.md`): under (S) and (H) of Corollary D, for every `r ≤ N` the
matrix `(M'(dancer(N − r + i), dancer(j)))_{i, j < r}` has determinant of exact 2-valuation
`r C + Σ_{j ∈ [N − r, N)} x(dancer j)`, `x = GoldenMatching.xVal k I α μ`. -/
theorem golden_ceiling (k : ℕ) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) (α : ℤ) (μ : ℕ) (C : ℤ)
    (M' : Finset ℕ → Finset ℕ → ℤ)
    (hS : ∀ a b, a ⊆ I → b ⊆ I → ¬ b ⊆ a → M' a b = 0)
    (hH : ∀ a b, b ⊆ a → a ⊆ I →
      ∃ n : ℕ, (n : ℤ) = C + GoldenMatching.cHat k I α μ a b ∧ 2 ^ n ∣ M' a b ∧
        ¬ 2 ^ (n + 1) ∣ M' a b)
    {r : ℕ} (hr : r ≤ 2 ^ #I) :
    ∃ n : ℕ, (n : ℤ) = r * C + ∑ j ∈ Ico (2 ^ #I - r) (2 ^ #I),
        GoldenMatching.xVal k I α μ (dancer I j) ∧
      2 ^ n ∣ (Matrix.of fun i j : Fin r => M' (dancer I (2 ^ #I - r + i)) (dancer I j)).det ∧
      ¬ 2 ^ (n + 1) ∣
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
        dancer_rank hD.1]⟩
  set f : Fin r ≃ GoldenMatching.Fr I r := Equiv.ofBijective (fun j => ⟨_, hF j⟩) ⟨fun j j' h => by
      have h' := congrArg Subtype.val h
      exact Fin.ext (CellFloor.dancer_inj (I := I) (by omega) (by omega) h'),
    fun D => by
      obtain ⟨D, hD⟩ := D
      simp only [GoldenMatching.Fr, mem_filter, mem_powerset] at hD
      exact ⟨⟨GoldenMatching.rank I D, hD.2⟩, Subtype.ext (dancer_rank hD.1)⟩⟩
  obtain ⟨n, hn, h1, h2, -⟩ := GoldenMatching.corollary_D k hI α μ C M' hS hH r hr e f
  refine ⟨n, ?_, h1, h2⟩
  rw [hn, GoldenMatching.U, sum_Lr _ r]

end DanceSmith
