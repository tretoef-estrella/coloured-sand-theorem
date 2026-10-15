module

public import RequestProject.Splitting.OneCoordinate
public import RequestProject.Splitting.Tensor

/-!
# The Laplacian of `H(d,q)` as a sum of one-coordinate Laplacians

This file corresponds to **§0 (Objects)** (`deg = d(q−1)`) and to the first bullet of the proof
of **(A2)** in `CS2_theorem_A_splitting.md`:
`L = Σ_{i=1}^d 1 ⊗ ⋯ ⊗ K^{(i)} ⊗ ⋯ ⊗ 1` on `(ℤ^q)^{⊗ d} = (V → ℤ)`, with `K = qI − J`.
The encodings are those of `RequestProject/Splitting/Basic.lean` (Laplacian),
`RequestProject/Splitting/OneCoordinate.lean` (`K = Kmat q`) and
`RequestProject/Splitting/Tensor.lean` (`K^{(i)} = coordOp K i`).
-/

@[expose] public section

open Finset Matrix

namespace ColouredSand.Splitting

variable {d q : ℕ}

lemma hammingDist_update_self (x : Fin d → Fin q) (i : Fin d) {a : Fin q} (ha : a ≠ x i) :
    hammingDist x (Function.update x i a) = 1 := by
  rw [hammingDist, Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  by_cases hj : j = i
  · subst hj; simp [Ne.symm ha]
  · simp [hj]

/-- The neighbours of `x` in `H(d,q)` are the `x[i ↦ a]` with `a ≠ xᵢ`, each obtained once. -/
lemma sum_neighborFinset {M : Type*} [AddCommMonoid M] (g : (Fin d → Fin q) → M)
    (x : Fin d → Fin q) :
    ∑ y ∈ (hammingGraph d q).neighborFinset x, g y =
      ∑ i, ∑ a ∈ univ.erase (x i), g (Function.update x i a) := by
  have hs := Finset.sum_sigma univ (fun i => univ.erase (x i))
    (fun p : (Σ _ : Fin d, Fin q) => g (Function.update x p.1 p.2))
  simp only at hs
  rw [← hs]
  symm
  refine Finset.sum_bij (fun p _ => Function.update x p.1 p.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨i, a⟩ hp
    simp only [mem_sigma, mem_univ, mem_erase, true_and] at hp
    rw [SimpleGraph.mem_neighborFinset]
    exact hammingDist_update_self x i hp.1
  · rintro ⟨i, a⟩ hp ⟨i', a'⟩ hp' h
    simp only [mem_sigma, mem_univ, mem_erase, true_and] at hp hp'
    have hi : i = i' := by
      by_contra hne
      have := congrFun h i
      simp [Function.update_of_ne hne] at this
      exact hp.1 this
    subst hi
    have := congrFun h i
    simp at this
    subst this
    rfl
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    change hammingDist x y = 1 at hy
    rw [hammingDist, Finset.card_eq_one] at hy
    obtain ⟨i, hi⟩ := hy
    have hmem : ∀ j, x j ≠ y j ↔ j = i := fun j => by
      have := congrArg (j ∈ ·) hi
      simpa using this
    refine ⟨⟨i, y i⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_univ, mem_erase, true_and]
      exact ⟨fun h : y i = x i => ((hmem i).mpr rfl) h.symm, trivial⟩
    · funext j
      by_cases hj : j = i
      · subst hj; simp
      · show Function.update x i (y i) j = y j
        rw [Function.update_of_ne hj]
        by_contra h
        exact hj ((hmem j).mp h)

/-- The degree of every vertex of `H(d,q)` is `d (q − 1)`. -/
theorem hammingGraph_degree (x : Fin d → Fin q) : (hammingGraph d q).degree x = d * (q - 1) := by
  rw [SimpleGraph.degree, card_eq_sum_ones, sum_neighborFinset (fun _ => 1) x]
  simp only [← card_eq_sum_ones]
  rw [Finset.sum_congr rfl fun i _ => Finset.card_erase_of_mem (mem_univ (x i))]
  simp

/-- **(A2), proof, first bullet.**  `L = Σᵢ 1 ⊗ ⋯ ⊗ K^{(i)} ⊗ ⋯ ⊗ 1` with `K = qI − J`. -/
theorem laplacian_eq_sum_coordOp (d q : ℕ) :
    laplacian d q = ∑ i : Fin d, coordOp (Kmat q) i := by
  refine LinearMap.ext fun f => funext fun x => ?_
  rw [laplacian_apply, hammingGraph_degree, sum_neighborFinset, LinearMap.sum_apply,
    Finset.sum_apply]
  rcases d with _ | d
  · simp
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Fin.pos (x 0)).ne'
  have hterm : ∀ i : Fin (d + 1), coordOp (Kmat q) i f x =
      ((q : ℤ) - 1) * f x - ∑ a ∈ univ.erase (x i), f (Function.update x i a) := by
    intro i
    rw [coordOp_apply, ← Finset.add_sum_erase _ _ (mem_univ (x i))]
    simp only [Kmat, sub_apply, smul_apply, one_apply, of_apply, Function.update_eq_self,
      if_true, smul_eq_mul]
    rw [Finset.sum_congr rfl fun a ha => by
      rw [if_neg (Ne.symm (ne_of_mem_erase ha))]]
    rw [Finset.sum_congr rfl fun a _ => show ((q : ℤ) * 0 - 1) * f (Function.update x i a) =
      -f (Function.update x i a) by ring, sum_neg_distrib]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast [Nat.cast_sub hq]
  ring

end ColouredSand.Splitting
