module

public import RequestProject.NumberOfFactors.Diagonal

/-!
# (D2) The rank of `U` over `𝔽_p`

This file corresponds to **(D2) The rank of `U` over `F_p`** of
`CS5_theorem_D_number_of_factors.md`.

## Encoding

* `B_m(ZMod p) = Finset (Fin m) → ZMod p` and `U = U m (ZMod p)` are those of
  `RequestProject/Strings/Basic.lean` (`(U f) T = ∑_{x ∈ T} f (T ∖ {x})`, i.e.
  `U e_S = ∑_{x ∉ S} e_{S ∪ {x}}`); the level `B_m(s)` is `level m (ZMod p) s`.
* `rank U` is `Module.finrank (ZMod p) (LinearMap.range (U m (ZMod p)))`.
* `rPart p m s = r_p(m,s) = ∑_{0 ≤ i ≤ t, p ∤ (k − i)} (C(m,i) − C(m,i−1))` with
  `(t,k) = (s, s+1)` if `2s ≤ m − 1` and `(t,k) = (m−1−s, m−s)` otherwise (here `k = t + 1`, so
  `k − i = t + 1 − i ≥ 1`); `rho p m = ρ_p(m) = ∑_{s=0}^{m−1} r_p(m,s)`.

## Proof

As in the file: `U` maps `B_m(s)` to `B_m(s+1)` with matrix `W_{s,s+1}ᵀ`
(`toLin'_inclMat_map_transpose`), the ranks of these blocks add up (`finrank_range_U_eq_sum`),
for `2s ≤ m − 1` (D1) gives the rank of `W_{s,s+1}` mod `p` (`rank_inclMat_zmod`), and otherwise
complementation identifies `W_{s,s+1}ᵀ` with `W_{m−1−s, m−s}` (`inclMat_compl`).
-/

@[expose] public section

open Finset Module

namespace ColouredSand.NumberOfFactors

open ColouredSand.Strings

/-- `r_p(m,s)` of (D2). -/
def rPart (p m s : ℕ) : ℕ :=
  let t := if 2 * s ≤ m - 1 then s else m - 1 - s
  ∑ i ∈ (range (t + 1)).filter (fun i => ¬ p ∣ (t + 1 - i)), strMult m i

/-- `ρ_p(m) = ∑_{s=0}^{m−1} r_p(m,s)` of (D2). -/
def rho (p m : ℕ) : ℕ := ∑ s ∈ range m, rPart p m s

/-! ### The blocks of `U` -/

section ring

variable {m : ℕ} {R : Type*} [CommRing R]

/-- `U` restricted to `B_m(s)` is the matrix `W_{s,s+1}ᵀ`. -/
lemma toLin'_inclMat_map_transpose {s : ℕ} (f : level m R s) :
    Matrix.toLin' ((inclMat m s).map (Int.cast : ℤ → R)).transpose (levelEquivFun m R s f) =
      levelEquivFun m R (s + 1) ⟨U m R f, U_mem_level f.2⟩ := by
  funext T
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, inclMat,
    Matrix.map_apply, Matrix.of_apply, levelEquivFun, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, U_apply]
  rw [sum_erase_eq_sum_powersetCard _ T.2]
  have h1 : ∀ S : {S : Finset (Fin m) // S.card = s},
      ((if (S : Finset (Fin m)) ⊆ T then (1 : ℤ) else 0 : ℤ) : R) * (f : B m R) S =
        if (S : Finset (Fin m)) ⊆ T then (f : B m R) S else 0 := by
    intro S; split_ifs <;> simp
  simp_rw [h1]
  rw [← Finset.sum_subtype (univ.filter fun S : Finset (Fin m) => S.card = s)
    (by simp) (fun S => if S ⊆ (T : Finset (Fin m)) then (f : B m R) S else 0), ← sum_filter]
  congr 1
  ext S
  simp [mem_powersetCard, and_comm]

end ring

section field

variable {m : ℕ} (K : Type*) [Field K]

/-- Vectors supported on sets of size `< n`. -/
def lowLev (m : ℕ) (n : ℕ) : Submodule K (B m K) where
  carrier := {f | ∀ S : Finset (Fin m), n ≤ S.card → f S = 0}
  add_mem' hf hg S hS := by simp [hf S hS, hg S hS]
  zero_mem' _ _ := rfl
  smul_mem' a f hf S hS := by simp [hf S hS]

lemma lowLev_succ (n : ℕ) : lowLev K m (n + 1) = lowLev K m n ⊔ level m K n := by
  apply le_antisymm
  · intro f hf
    let g : B m K := fun S => if S.card = n then f S else 0
    have h1 : f - g ∈ lowLev K m n := by
      intro S hS
      simp only [g, Pi.sub_apply]
      split_ifs with h
      · ring
      · rw [hf S (by omega)]; ring
    have h2 : g ∈ level m K n := fun S hS => by simp [g, hS]
    have : f = (f - g) + g := by abel
    rw [this]
    exact Submodule.add_mem_sup h1 h2
  · refine sup_le (fun f hf S hS => hf S (by omega)) (fun f hf S hS => hf S (by omega))

lemma map_U_lowLev_le (n : ℕ) : (lowLev K m n).map (U m K) ≤ lowLev K m (n + 1) := by
  rintro _ ⟨f, hf, rfl⟩ T hT
  simp only [U_apply]
  refine sum_eq_zero fun x hx => hf _ ?_
  rw [card_erase_of_mem hx]
  omega

lemma lowLev_top : lowLev K m (m + 1) = ⊤ := by
  rw [eq_top_iff]
  intro f _ S hS
  have := (card_le_univ S).trans_eq (Fintype.card_fin m)
  omega

/-- The ranks of the blocks `B_m(s) → B_m(s+1)` of `U` add up to the rank of `U`. -/
lemma finrank_range_U_eq_sum :
    finrank K (LinearMap.range (U m K)) =
      ∑ s ∈ range m, finrank K ((level m K s).map (U m K)) := by
  have key : ∀ n, finrank K ((lowLev K m n).map (U m K)) =
      ∑ s ∈ range n, finrank K ((level m K s).map (U m K)) := by
    intro n
    induction n with
    | zero =>
      have : lowLev K m 0 = ⊥ := by
        rw [eq_bot_iff]; intro f hf; rw [Submodule.mem_bot]; funext S; exact hf S (Nat.zero_le _)
      simp [this]
    | succ n ih =>
      rw [lowLev_succ, Submodule.map_sup, sum_range_succ, ← ih]
      have hdisj : (lowLev K m n).map (U m K) ⊓ (level m K n).map (U m K) = ⊥ := by
        rw [eq_bot_iff]
        intro f ⟨hf1, hf2⟩
        have h1 := map_U_lowLev_le K n hf1
        obtain ⟨g, hg, rfl⟩ := hf2
        have h2 := U_mem_level hg
        rw [Submodule.mem_bot]
        funext S
        by_cases hS : S.card = n + 1
        · exact h1 S (by omega)
        · exact h2 S hS
      have := Submodule.finrank_sup_add_finrank_inf_eq ((lowLev K m n).map (U m K))
        ((level m K n).map (U m K))
      rw [hdisj, finrank_bot, add_zero] at this
      exact this
  have hm : finrank K ((level m K m).map (U m K)) = 0 := by
    have : (level m K m).map (U m K) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨g, hg, rfl⟩
      rw [Submodule.mem_bot]
      exact eq_zero_of_mem_level_of_lt (U_mem_level hg) (Nat.lt_succ_self m)
    rw [this, finrank_bot]
  rw [← Submodule.map_top, ← lowLev_top K, key, sum_range_succ, hm, add_zero]

/-- The rank of the block `B_m(s) → B_m(s+1)` of `U` is the rank of `W_{s,s+1}` over `K`. -/
lemma finrank_map_U_level (s : ℕ) :
    finrank K ((level m K s).map (U m K)) = ((inclMat m s).map (Int.cast : ℤ → K)).rank := by
  rw [← Matrix.rank_transpose, Matrix.rank]
  set V := ((inclMat m s).map (Int.cast : ℤ → K)).transpose.mulVecLin
  have hcomp : (U m K).comp (level m K s).subtype =
      ((level m K (s + 1)).subtype.comp (levelEquivFun m K (s + 1)).symm.toLinearMap).comp
        (V.comp (levelEquivFun m K s).toLinearMap) := by
    apply LinearMap.ext
    intro f
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, V,
      Matrix.mulVecLin_apply]
    have := toLin'_inclMat_map_transpose (R := K) f
    rw [Matrix.toLin'_apply] at this
    rw [this, LinearEquiv.symm_apply_apply]
  have h1 : (level m K s).map (U m K) = LinearMap.range ((U m K).comp (level m K s).subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [h1, hcomp, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  have hinj : Function.Injective
      ((level m K (s + 1)).subtype.comp (levelEquivFun m K (s + 1)).symm.toLinearMap) :=
    (level m K (s + 1)).injective_subtype.comp (levelEquivFun m K (s + 1)).symm.injective
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm

/-- The rank of a rectangular "diagonal" matrix (entry `d a` at `(a, φ a)`, zero elsewhere) is the
number of nonzero `d a`. -/
lemma rank_rect_diag [DecidableEq K] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (φ : ι ↪ κ)
    (d : ι → K) :
    (Matrix.of fun a b => if b = φ a then d a else 0).rank = Fintype.card {a // d a ≠ 0} := by
  classical
  rw [Matrix.rank_eq_finrank_span_row]
  let w : {a // d a ≠ 0} → (κ → K) := fun a => Pi.single (φ a.1) 1
  have hrow : ∀ a, (Matrix.of fun a b => if b = φ a then d a else 0).row a =
      d a • (Pi.single (φ a) (1 : K) : κ → K) := by
    intro a; funext b
    simp only [Matrix.row, Matrix.of_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
  have hspan : Submodule.span K (Set.range (Matrix.of fun a b => if b = φ a then d a else 0).row) =
      Submodule.span K (Set.range w) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [hrow]
      by_cases ha : d a = 0
      · rw [ha, zero_smul]; exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have : w a = (d a.1)⁻¹ • (Matrix.of fun a b => if b = φ a then d a else 0).row a.1 := by
        rw [hrow, smul_smul, inv_mul_cancel₀ a.2, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a.1, rfl⟩)
  rw [hspan, finrank_span_eq_card]
  have : w = (Pi.basisFun K κ) ∘ (φ ∘ Subtype.val) := by
    funext a; simp [w, Pi.basisFun_apply]
  rw [this]
  exact (Pi.basisFun K κ).linearIndependent.comp _ (φ.injective.comp Subtype.val_injective)

end field

/-! ### The rank of `W_{t,t+1}` modulo `p` -/

/-- For `2t + 1 ≤ m`: `rank_{𝔽_p} W_{t,t+1} = ∑_{0 ≤ i ≤ t, p ∤ t+1−i} (C(m,i) − C(m,i−1))`,
from (D1). -/
lemma rank_inclMat_zmod (p : ℕ) [Fact p.Prime] {m t : ℕ} (ht : 2 * t + 1 ≤ m) :
    ((inclMat m t).map (Int.cast : ℤ → ZMod p)).rank =
      ∑ i ∈ (range (t + 1)).filter (fun i => ¬ p ∣ (t + 1 - i)), strMult m i := by
  classical
  obtain ⟨P, Q, φ, lab, hP, hQ, hlab, hPWQ, hcard⟩ := wilson_diagonal_form m t ht
  let f := Int.castRingHom (ZMod p)
  have hPQ := congrArg (fun A => A.map f) hPWQ
  simp only [Matrix.map_mul] at hPQ
  have hPu : IsUnit (P.map f).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hP.map _
  have hQu : IsUnit (Q.map f).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hQ.map _
  have h1 : ((inclMat m t).map (Int.cast : ℤ → ZMod p)).rank =
      (P.map f * (inclMat m t).map f * Q.map f).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQu,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPu]
    rfl
  rw [h1, hPQ]
  have h2 : (Matrix.of fun a b => if b = φ a then (t : ℤ) + 1 - lab a else 0).map f =
      Matrix.of fun a b => if b = φ a then (((t + 1 - lab a : ℕ) : ℤ) : ZMod p) else 0 := by
    ext a b
    simp only [f, Matrix.map_apply, Matrix.of_apply]
    split_ifs
    · rw [Nat.cast_sub (by have := hlab a; omega)]; push_cast; simp
    · simp
  rw [h2, rank_rect_diag]
  -- count
  have h3 : ∀ a, ((((t + 1 - lab a : ℕ) : ℤ) : ZMod p) ≠ 0 ↔ ¬ p ∣ (t + 1 - lab a)) := by
    intro a
    rw [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff]
  rw [Fintype.card_subtype, Finset.card_eq_sum_card_fiberwise (f := lab)
    (t := (range (t + 1)).filter (fun i => ¬ p ∣ (t + 1 - i)))]
  · refine sum_congr rfl fun i hi => ?_
    rw [mem_filter, mem_range] at hi
    rw [← hcard i (by omega), Fintype.card_subtype]
    congr 1
    ext a
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl
    exact (h3 a).mpr hi.2
  · intro a ha
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha
    simp only [coe_filter, mem_range, Set.mem_setOf_eq]
    exact ⟨by have := hlab a; omega, (h3 a).mp ha⟩

/-! ### Complementation -/

/-- Complementation `S ↦ Sᶜ` between `a`-subsets and `b`-subsets of `Fin m`, `a + b = m`. -/
def complEquiv (m a b : ℕ) (hab : a + b = m) :
    {S : Finset (Fin m) // S.card = a} ≃ {S : Finset (Fin m) // S.card = b} where
  toFun S := ⟨(S : Finset (Fin m))ᶜ, by rw [card_compl, Fintype.card_fin, S.2]; omega⟩
  invFun S := ⟨(S : Finset (Fin m))ᶜ, by rw [card_compl, Fintype.card_fin, S.2]; omega⟩
  left_inv S := by ext1; simp
  right_inv S := by ext1; simp

/-- `W_{m−1−s, m−s}` is `W_{s,s+1}ᵀ` up to complementation of rows and columns. -/
lemma inclMat_compl {m s : ℕ} (hs : s + 1 ≤ m) :
    inclMat m (m - 1 - s) = (inclMat m s).transpose.submatrix
      (complEquiv m (m - 1 - s) (s + 1) (by omega))
      (complEquiv m (m - 1 - s + 1) s (by omega)) := by
  ext S T
  simp only [inclMat, Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, complEquiv,
    Equiv.coe_fn_mk, compl_subset_compl]

/-! ### (D2) -/

lemma rank_block_zmod (p : ℕ) [Fact p.Prime] {m s : ℕ} (hs : s < m) :
    ((inclMat m s).map (Int.cast : ℤ → ZMod p)).rank = rPart p m s := by
  unfold rPart
  split_ifs with h
  · exact rank_inclMat_zmod p (by omega)
  · rw [← rank_inclMat_zmod p (by omega), inclMat_compl (by omega), ← Matrix.submatrix_map,
      Matrix.rank_submatrix, Matrix.transpose_map, Matrix.rank_transpose]

/-- **(D2) The rank of `U` over `𝔽_p`.**  For a prime `p`, the up operator `U` on
`B_m(ZMod p) = Finset (Fin m) → ZMod p` has rank `ρ_p(m) = ∑_{s=0}^{m−1} r_p(m,s)`. -/
theorem rank_U_zmod (p : ℕ) [Fact p.Prime] (m : ℕ) :
    finrank (ZMod p) (LinearMap.range (U m (ZMod p))) = rho p m := by
  rw [finrank_range_U_eq_sum, rho]
  refine sum_congr rfl fun s hs => ?_
  rw [finrank_map_U_level, rank_block_zmod p (mem_range.mp hs)]

end ColouredSand.NumberOfFactors
