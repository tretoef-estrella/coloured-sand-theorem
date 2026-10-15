module

public import RequestProject.Strings.Decomposition

/-!
# Strings of the Boolean lattice: global decomposition and ranks

This file corresponds to the closing remark of **(S3)** in `CS1_strings_and_theorem_E.md`
("If `R` is a principal ideal domain, or local, `Λ_k` is free of rank `C(m,k) − C(m,k−1)`"):
see `Lam_free_finrank` (PID case) and `Lam_free_finrank_of_isLocalRing` (local case).
It also contains the global form of the string decomposition used in the proof of **(S5)**:
`B_m(R) = ⨁_{k ≤ m/2} ⨁_{0 ≤ i ≤ m−2k} U^i Λ_k`.
Encodings are those of `RequestProject/Strings/Basic.lean` and
`RequestProject/Strings/Decomposition.lean`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Strings

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### Reindexing the strings -/

lemma sum_strings_reindex {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) :
    ∑ k ∈ range (m / 2 + 1), ∑ i ∈ range (m - 2 * k + 1), f k i =
      ∑ r ∈ range (m + 1), ∑ k ∈ strIdx m r, f k (r - k) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.1 + x.2, x.1⟩) (fun y _ => ⟨y.2, y.1 - y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨k, i⟩ h; simp only [mem_sigma, mem_range, mem_strIdx] at h ⊢; omega
  · rintro ⟨r, k⟩ h; simp only [mem_sigma, mem_range, mem_strIdx] at h ⊢; omega
  · rintro ⟨k, i⟩ _; simp
  · rintro ⟨r, k⟩ h
    simp only [mem_sigma, mem_range, mem_strIdx] at h
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    omega
  · rintro ⟨k, i⟩ _; simp

/-! ### Level projections -/

variable (m R) in
/-- The projection of `B_m(R)` onto the level `B_m(r)`. -/
def lproj (r : ℕ) : B m R →ₗ[R] B m R where
  toFun f S := if S.card = r then f S else 0
  map_add' f g := by ext S; by_cases h : S.card = r <;> simp [h]
  map_smul' a f := by ext S; by_cases h : S.card = r <;> simp [h]

lemma lproj_apply (r : ℕ) (f : B m R) (S : Finset (Fin m)) :
    lproj m R r f S = if S.card = r then f S else 0 := rfl

lemma lproj_of_mem_level {s r : ℕ} {f : B m R} (hf : f ∈ level m R s) :
    lproj m R r f = if s = r then f else 0 := by
  ext S
  rw [lproj_apply]
  by_cases hsr : s = r
  · subst hsr
    by_cases hS : S.card = s
    · simp [hS]
    · simp [hS, hf S hS]
  · by_cases hS : S.card = r
    · simp [hS, hsr, hf S (by omega)]
    · simp [hS, hsr]

lemma sum_lproj (f : B m R) : ∑ r ∈ range (m + 1), lproj m R r f = f := by
  ext S
  rw [Finset.sum_apply]
  simp only [lproj_apply]
  rw [Finset.sum_ite_eq]
  have := (Finset.card_le_univ S).trans_eq (Fintype.card_fin m)
  rw [if_pos (by simp; omega)]

lemma lproj_mem_level (r : ℕ) (f : B m R) : lproj m R r f ∈ level m R r := by
  intro S hS
  rw [lproj_apply, if_neg hS]

/-! ### The global string decomposition -/

/-- Every vector is a sum of strings: `x = ∑_{k ≤ m/2} ∑_{i ≤ m−2k} U^i v_{k,i}`, `v_{k,i} ∈ Λ_k`. -/
lemma global_span (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) (x : B m R) :
    ∃ v : ℕ → ℕ → B m R, (∀ k i, v k i ∈ Lam m R k) ∧
      x = ∑ k ∈ range (m / 2 + 1), ∑ i ∈ range (m - 2 * k + 1), (U m R ^ i) (v k i) := by
  have h := fun r => strings_span hR r (lproj m R r x) (lproj_mem_level r x)
  choose w hw hwx using h
  refine ⟨fun k i => w (k + i) k, fun k i => hw _ _, ?_⟩
  rw [sum_strings_reindex (fun k i => (U m R ^ i) (w (k + i) k))]
  conv_lhs => rw [← sum_lproj x]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [hwx r]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have := mem_strIdx.mp hk
  rw [show k + (r - k) = r by omega]

/-- The strings are independent. -/
lemma global_indep (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) (v : ℕ → ℕ → B m R)
    (hv : ∀ k i, v k i ∈ Lam m R k)
    (h0 : ∑ k ∈ range (m / 2 + 1), ∑ i ∈ range (m - 2 * k + 1), (U m R ^ i) (v k i) = 0) :
    ∀ k i, k ≤ m / 2 → i ≤ m - 2 * k → v k i = 0 := by
  intro k i hk hi
  rw [sum_strings_reindex (fun k i => (U m R ^ i) (v k i))] at h0
  have h1 := congrArg (lproj m R (k + i)) h0
  rw [map_sum, map_zero, Finset.sum_eq_single (k + i)] at h1
  · rw [map_sum] at h1
    have h2 : ∑ k' ∈ strIdx m (k + i), (U m R ^ (k + i - k')) (v k' (k + i - k')) = 0 := by
      rw [← h1]
      refine Finset.sum_congr rfl (fun k' hk' => ?_)
      have := mem_strIdx.mp hk'
      have hl := U_pow_mem_level (mem_Lam.mp (hv k' (k + i - k'))).2 (k + i - k')
      rw [show k' + (k + i - k') = k + i by omega] at hl
      rw [lproj_of_mem_level hl, if_pos rfl]
    have := strings_indep hR (k + i) (fun k' => v k' (k + i - k')) (fun k' => hv _ _) h2 k
      (mem_strIdx.mpr (by omega))
    simpa using this
  · intro r _ hr
    rw [map_sum]
    refine Finset.sum_eq_zero (fun k' hk' => ?_)
    have := mem_strIdx.mp hk'
    have hl := U_pow_mem_level (mem_Lam.mp (hv k' (r - k'))).2 (r - k')
    rw [show k' + (r - k') = r by omega] at hl
    rw [lproj_of_mem_level hl, if_neg hr]
  · intro h; exfalso; exact h (by simp; omega)

/-! ### Ranks over a principal ideal domain -/

/-- The multiplicity `C(m,k) − C(m,k−1)` (with `C(m,−1) = 0`) of the strings starting in level
`k`. -/
def strMult (m k : ℕ) : ℕ := m.choose k - if k = 0 then 0 else m.choose (k - 1)

variable (m R) in
/-- `B_m(r) ≃ (subsets of size r → R)`. -/
def levelEquivFun (r : ℕ) : level m R r ≃ₗ[R] ({S : Finset (Fin m) // S.card = r} → R) where
  toFun f S := (f : B m R) S
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨fun S => if h : S.card = r then g ⟨S, h⟩ else 0, by
    intro S hS; simp [hS]⟩
  left_inv f := by
    ext S
    simp only
    split_ifs with h
    · rfl
    · exact (f.2 S h).symm
  right_inv g := by
    ext S
    simp [S.2]

lemma finrank_level [Nontrivial R] (r : ℕ) : Module.finrank R (level m R r) = m.choose r := by
  rw [(levelEquivFun m R r).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_finset_len, Fintype.card_fin]

/-! ### `Λ_k` is a direct summand of `B_m(k)` -/

lemma stringEquiv_single (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {k : ℕ}
    (hk : k ∈ strIdx m k) (v : Lam m R k) :
    ((stringEquiv hR k (Pi.single (⟨k, hk⟩ : strIdx m k) v) : level m R k) : B m R) = v := by
  simp only [stringEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]
  rw [stringMap_apply, Finset.sum_eq_single k]
  · rw [dif_pos hk, Pi.single_eq_same, Nat.sub_self, pow_zero, Module.End.one_apply]
  · intro j hj hjk
    rw [dif_pos hj, Pi.single_eq_of_ne (fun h => hjk (congrArg Subtype.val h)),
      ZeroMemClass.coe_zero, map_zero]
  · intro h; exact absurd hk h

variable (m R) in
/-- The inclusion `Λ_k → B_m(k)`. -/
def lamIncl (k : ℕ) : Lam m R k →ₗ[R] level m R k := Submodule.inclusion inf_le_right

/-- The retraction `B_m(k) → Λ_k` coming from (S3)(b). -/
noncomputable def lamRetr (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {k : ℕ}
    (hk : k ∈ strIdx m k) : level m R k →ₗ[R] Lam m R k :=
  (LinearMap.proj (⟨k, hk⟩ : strIdx m k)) ∘ₗ (stringEquiv hR k).symm.toLinearMap

lemma lamRetr_comp_lamIncl (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {k : ℕ}
    (hk : k ∈ strIdx m k) : lamRetr hR hk ∘ₗ lamIncl m R k = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  have h : (stringEquiv hR k).symm (lamIncl m R k v) = Pi.single (⟨k, hk⟩ : strIdx m k) v := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (stringEquiv_single hR hk v).symm
  simp only [lamRetr, LinearMap.comp_apply, LinearEquiv.coe_coe, h, LinearMap.proj_apply,
    Pi.single_eq_same, LinearMap.id_apply]

instance (k : ℕ) : Module.Free R (level m R k) :=
  Module.Free.of_equiv (levelEquivFun m R k).symm

instance (k : ℕ) : Module.Finite R (level m R k) :=
  Module.Finite.equiv (levelEquivFun m R k).symm

lemma Lam_projective (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {k : ℕ} (hk : 2 * k ≤ m) :
    Module.Projective R (Lam m R k) :=
  Module.Projective.of_split (lamIncl m R k) (lamRetr hR (mem_strIdx.mpr ⟨le_rfl, by omega⟩))
    (lamRetr_comp_lamIncl hR _)

lemma Lam_finite (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {k : ℕ} (hk : 2 * k ≤ m) :
    Module.Finite R (Lam m R k) := by
  refine Module.Finite.of_surjective (lamRetr hR (mem_strIdx.mpr ⟨le_rfl, by omega⟩)) ?_
  intro v
  exact ⟨lamIncl m R k v, by
    rw [← LinearMap.comp_apply, lamRetr_comp_lamIncl, LinearMap.id_apply]⟩

/-! ### Ranks -/

lemma finrank_level_eq_sum [Nontrivial R] (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R))
    (hfree : ∀ j, 2 * j ≤ m → Module.Free R (Lam m R j)) (r : ℕ) :
    m.choose r = ∑ k ∈ strIdx m r, Module.finrank R (Lam m R k) := by
  haveI : ∀ k : strIdx m r, Module.Free R (Lam m R k) := fun k => by
    have := mem_strIdx.mp k.2; exact hfree k (by omega)
  haveI : ∀ k : strIdx m r, Module.Finite R (Lam m R k) := fun k => by
    have := mem_strIdx.mp k.2; exact Lam_finite hR (by omega)
  rw [← finrank_level (R := R), ← (stringEquiv hR r).finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_coe_sort (strIdx m r) (fun k => Module.finrank R (Lam m R k))]

/-- If `1, …, m` are units of the nontrivial ring `R` and the `Λ_j` (`2j ≤ m`) are free, then
`rank Λ_k = C(m,k) − C(m,k−1)` for `k ≤ m/2`. -/
lemma finrank_Lam [Nontrivial R] (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R))
    (hfree : ∀ j, 2 * j ≤ m → Module.Free R (Lam m R j)) {k : ℕ} (hk : k ≤ m / 2) :
    Module.finrank R (Lam m R k) = strMult m k := by
  have hI : ∀ r, r ≤ m / 2 → strIdx m r = range (r + 1) := by
    intro r hr; ext j; simp only [mem_strIdx, mem_range]; omega
  have h1 := finrank_level_eq_sum hR hfree k
  rw [hI k hk, sum_range_succ] at h1
  rcases k with _ | k
  · simp [strMult] at h1 ⊢; omega
  · have h0 := finrank_level_eq_sum hR hfree k
    rw [hI k (by omega)] at h0
    simp only [strMult, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
    omega

/-- **(S3), closing remark, PID case.**  If `R` is a principal ideal domain in which every
`n ∈ [1, m]` is a unit, then for `k ≤ m/2` the module `Λ_k` is free of rank
`C(m,k) − C(m,k−1)` (`strMult m k`, with `C(m,−1) = 0`). -/
theorem Lam_free_finrank [IsDomain R] [IsPrincipalIdealRing R]
    (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {k : ℕ} (hk : k ≤ m / 2) :
    Module.Free R (Lam m R k) ∧ Module.finrank R (Lam m R k) = strMult m k :=
  ⟨inferInstance, finrank_Lam hR (fun _ _ => inferInstance) hk⟩

/-- **(S3), closing remark, local case.**  If `R` is a local ring in which every
`n ∈ [1, m]` is a unit, then for `k ≤ m/2` the module `Λ_k` is free of rank
`C(m,k) − C(m,k−1)` (`strMult m k`, with `C(m,−1) = 0`). -/
theorem Lam_free_finrank_of_isLocalRing [IsLocalRing R]
    (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {k : ℕ} (hk : k ≤ m / 2) :
    Module.Free R (Lam m R k) ∧ Module.finrank R (Lam m R k) = strMult m k := by
  have hfree : ∀ j, 2 * j ≤ m → Module.Free R (Lam m R j) := fun j hj => by
    haveI := Lam_projective hR hj
    haveI := Lam_finite hR hj
    exact Module.free_of_flat_of_isLocalRing
  exact ⟨hfree k (by omega), finrank_Lam hR hfree hk⟩

end ColouredSand.Strings
