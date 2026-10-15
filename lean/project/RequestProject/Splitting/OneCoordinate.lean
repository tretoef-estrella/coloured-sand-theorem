module

public import RequestProject.Splitting.Basic

/-!
# (A1) One coordinate

This file corresponds to **(A1) One coordinate** of `CS2_theorem_A_splitting.md`.

## Encoding

* `ℤ^q` is `Fin q → ℤ`.  The basis vector `e_i` is `ev q i` (`= Pi.single i 1`, see
  `ev_eq_single`); it is indexed by a natural number `i` so that `e_0`, `e_1`, … can be written
  without bound proofs (`ev q i = 0` if `i ≥ q`, which never occurs below).
* `f_i = e_i − e_0` is `fv q i`, and `σ = f_1 + ⋯ + f_{q−1}` is `sigma q`.
* `K = qI − J` is the matrix `Kmat q = (q : ℤ) • 1 − of (fun _ _ => 1)`, acting by `*ᵥ`;
  `completeGraph_lapMatrix` shows that it is the Laplacian matrix of the complete graph `K_q`.
* The family `e_0, σ, f_1, …, f_{q−2}` is `basisVec q : Fin q → (Fin q → ℤ)`, with
  `basisVec q 0 = e_0`, `basisVec q 1 = σ` and `basisVec q k = f_{k−1}` for `2 ≤ k ≤ q − 1`.
  "Is a `ℤ`-basis" means that there is a `Basis (Fin q) ℤ (Fin q → ℤ)` whose vectors are exactly
  this family (`basisVec_isBasis`).
-/

@[expose] public section

open Finset Matrix

namespace ColouredSand.Splitting

/-- `e_i ∈ ℤ^q` (the `i`-th standard basis vector; `0` if `i ≥ q`). -/
def ev (q i : ℕ) : Fin q → ℤ := fun a => if (a : ℕ) = i then 1 else 0

/-- `f_i = e_i − e_0`. -/
def fv (q i : ℕ) : Fin q → ℤ := ev q i - ev q 0

/-- `σ = f_1 + ⋯ + f_{q−1}`. -/
def sigma (q : ℕ) : Fin q → ℤ := ∑ i ∈ Icc 1 (q - 1), fv q i

/-- The family `e_0, σ, f_1, …, f_{q−2}`, indexed by `Fin q`. -/
def basisVec (q : ℕ) (k : Fin q) : Fin q → ℤ :=
  if (k : ℕ) = 0 then ev q 0 else if (k : ℕ) = 1 then sigma q else fv q (k - 1)

/-- The matrix `K = qI − J` (`J` the all-ones matrix). -/
def Kmat (q : ℕ) : Matrix (Fin q) (Fin q) ℤ := (q : ℤ) • 1 - Matrix.of (fun _ _ => 1)

lemma ev_eq_single {q : ℕ} (a : Fin q) : ev q a = Pi.single a 1 := by
  ext b
  simp [ev, Pi.single_apply, Fin.ext_iff]

lemma Kmat_mulVec (q : ℕ) (v : Fin q → ℤ) : Kmat q *ᵥ v = (q : ℤ) • v - fun _ => ∑ a, v a := by
  rw [Kmat, sub_mulVec, smul_mulVec, one_mulVec]
  ext b
  simp [mulVec, dotProduct]

lemma sum_ev {q i : ℕ} (hi : i < q) : ∑ a, ev q i a = 1 := by
  rw [show i = ((⟨i, hi⟩ : Fin q) : ℕ) from rfl, ev_eq_single]
  simp

lemma sum_fv {q i : ℕ} (hi : i < q) : ∑ a, fv q i a = 0 := by
  simp only [fv, Pi.sub_apply, sum_sub_distrib, sum_ev hi, sum_ev (by omega : 0 < q), sub_self]

lemma sum_sigma (q : ℕ) : ∑ a, sigma q a = 0 := by
  simp only [sigma, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => sum_fv ?_
  simp at hi
  omega

/-- The Laplacian matrix of the complete graph `K_q` is `K = qI − J`. -/
theorem completeGraph_lapMatrix (q : ℕ) : (⊤ : SimpleGraph (Fin q)).lapMatrix ℤ = Kmat q := by
  ext a b
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply,
    SimpleGraph.top_adj, sub_apply, diagonal_apply, Kmat, smul_apply, one_apply, of_apply,
    SimpleGraph.complete_graph_degree, Fintype.card_fin]
  by_cases h : a = b
  · subst h
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Fin.pos a).ne'
    simp [Nat.cast_sub this]
  · simp [h]

/-- **(A1)** `K e_0 = −σ`. -/
theorem K_ev_zero {q : ℕ} (hq : 1 ≤ q) : Kmat q *ᵥ ev q 0 = -sigma q := by
  rw [Kmat_mulVec, sum_ev (by omega)]
  ext b
  simp only [sigma, fv, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
    sum_sub_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hsum : ∑ i ∈ Icc 1 (q - 1), ev q i b = 1 - ev q 0 b := by
    have hb := b.isLt
    simp only [ev]
    rw [Finset.sum_ite_eq]
    by_cases h0 : (b : ℕ) = 0
    · simp [h0]
    · rw [if_pos (by simp; omega)]
      simp [h0]
  rw [hsum, show q - 1 + 1 - 1 = q - 1 by omega, Nat.cast_sub hq]
  simp only [Pi.mul_apply, Pi.natCast_apply, Pi.sub_apply]
  push_cast
  ring

/-- **(A1)** `K σ = q σ`. -/
theorem K_sigma (q : ℕ) : Kmat q *ᵥ sigma q = (q : ℤ) • sigma q := by
  rw [Kmat_mulVec, sum_sigma]
  ext b
  simp

/-- **(A1)** `K f_i = q f_i` (for `1 ≤ i ≤ q − 1`; in fact for every `i < q`). -/
theorem K_fv {q i : ℕ} (hi : i < q) : Kmat q *ᵥ fv q i = (q : ℤ) • fv q i := by
  rw [Kmat_mulVec, sum_fv hi]
  ext b
  simp

lemma basisVec_zero {q : ℕ} (k : Fin q) (hk : (k : ℕ) = 0) : basisVec q k = ev q 0 := by
  simp [basisVec, hk]

lemma basisVec_one {q : ℕ} (k : Fin q) (hk : (k : ℕ) = 1) : basisVec q k = sigma q := by
  simp [basisVec, hk]

lemma basisVec_ge_two {q : ℕ} (k : Fin q) (hk : 2 ≤ (k : ℕ)) : basisVec q k = fv q (k - 1) := by
  simp [basisVec, show (k : ℕ) ≠ 0 by omega, show (k : ℕ) ≠ 1 by omega]

lemma span_basisVec {q : ℕ} (hq : 2 ≤ q) :
    Submodule.span ℤ (Set.range (basisVec q)) = ⊤ := by
  set W := Submodule.span ℤ (Set.range (basisVec q))
  have hmem : ∀ k : Fin q, basisVec q k ∈ W := fun k => Submodule.subset_span ⟨k, rfl⟩
  have he0 : ev q 0 ∈ W := by
    have h := hmem ⟨0, by omega⟩
    rwa [basisVec_zero (q := q) _ rfl] at h
  have hsig : sigma q ∈ W := by
    have h := hmem ⟨1, by omega⟩
    rwa [basisVec_one (q := q) _ rfl] at h
  have hf : ∀ i, 1 ≤ i → i ≤ q - 2 → fv q i ∈ W := fun i h1 h2 => by
    have h := hmem ⟨i + 1, by omega⟩
    rwa [basisVec_ge_two (q := q) _ (by simp; omega), show i + 1 - 1 = i by omega] at h
  have hflast : fv q (q - 1) ∈ W := by
    have hs : sigma q = (∑ i ∈ Icc 1 (q - 2), fv q i) + fv q (q - 1) := by
      rw [sigma, show q - 1 = (q - 2) + 1 by omega, Finset.sum_Icc_succ_top (by omega)]
    have : fv q (q - 1) = sigma q - ∑ i ∈ Icc 1 (q - 2), fv q i := by rw [hs]; abel
    rw [this]
    exact W.sub_mem hsig (W.sum_mem fun i hi => by simp at hi; exact hf i hi.1 hi.2)
  have hev : ∀ a : Fin q, ev q a ∈ W := by
    intro a
    by_cases ha : (a : ℕ) = 0
    · rw [ha]; exact he0
    · have : ev q a = fv q a + ev q 0 := by simp [fv]
      rw [this]
      refine W.add_mem ?_ he0
      by_cases ha' : (a : ℕ) = q - 1
      · rw [ha']; exact hflast
      · exact hf a (by omega) (by omega)
  rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin q)).span_eq, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  simpa [ev_eq_single] using hev a

lemma linearIndependent_basisVec {q : ℕ} (hq : 2 ≤ q) : LinearIndependent ℤ (basisVec q) := by
  set F := Fintype.linearCombination ℤ (basisVec q)
  have hsurj : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, span_basisVec hq]
  have hinj := OrzechProperty.injective_of_surjective_endomorphism F hsurj
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have : F g = F 0 := by rw [Fintype.linearCombination_apply, hg, map_zero]
  simp [hinj this]

/-- **(A1)** `e_0, σ, f_1, …, f_{q−2}` is a `ℤ`-basis of `ℤ^q` (for `q ≥ 2`). -/
theorem basisVec_isBasis {q : ℕ} (hq : 2 ≤ q) :
    ∃ b : Module.Basis (Fin q) ℤ (Fin q → ℤ), ⇑b = basisVec q :=
  ⟨Module.Basis.mk (linearIndependent_basisVec hq) (span_basisVec hq).ge,
    Module.Basis.coe_mk _ _⟩

end ColouredSand.Splitting
