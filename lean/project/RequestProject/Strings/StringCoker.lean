module

public import RequestProject.Strings.Global
public import RequestProject.Strings.Bidiagonal

/-!
# The cokernel of `q (c + H) + U` via strings (general ring)

This file contains the ring-independent part of the proof of **(S5) Theorem E** of
`CS1_strings_and_theorem_E.md`: over any commutative ring in which `1, …, m` are units and in
which each `Λ_k` (`k ≤ m/2`) has a basis, the operator `M = q (c + H) + U` is, in a basis adapted
to the strings, block diagonal with lower bidiagonal blocks, so that by (S4)
`coker M ≅ ∏_{strings} R ⧸ (∏_{i=0}^{m−2k} q (c + k + i))`.
-/

@[expose] public section

open Finset Matrix

namespace ColouredSand.Strings

variable {m : ℕ} {R : Type*} [CommRing R]

variable (m R) in
/-- The operator `M = q (c + H) + U` on `B_m(R)`, i.e. `M e_S = q (c + |S|) e_S + U e_S`. -/
def opM (q c : R) : B m R →ₗ[R] B m R := q • (c • LinearMap.id + H m R) + U m R

/-- The matrix of `M` on one string `v, U v, …, U^{n−1} v` with `v ∈ Λ_k`: lower bidiagonal with
diagonal `q (c + k + i)` and subdiagonal `1`. -/
def strMat (q c : R) (k n : ℕ) : Matrix (Fin n) (Fin n) R := fun i j =>
  if i = j then q * (c + ((k + i : ℕ) : R)) else if (i : ℕ) = j + 1 then 1 else 0

lemma opM_U_pow (q c : R) {k : ℕ} {b : B m R} (hb : b ∈ level m R k) (i : ℕ) :
    opM m R q c ((U m R ^ i) b) =
      (q * (c + ((k + i : ℕ) : R))) • (U m R ^ i) b + (U m R ^ (i + 1)) b := by
  simp only [opM, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [H_of_mem_level (U_pow_mem_level hb i), pow_succ', Module.End.mul_apply]
  rw [smul_add, smul_smul, smul_smul, ← add_smul, mul_add]

lemma opM_column (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) (q c : R) {k : ℕ}
    (hk : k ≤ m / 2) {b : B m R} (hb : b ∈ Lam m R k) (j : Fin (m - 2 * k + 1)) :
    opM m R q c ((U m R ^ (j : ℕ)) b) =
      ∑ i : Fin (m - 2 * k + 1), strMat q c k (m - 2 * k + 1) i j • (U m R ^ (i : ℕ)) b := by
  rw [opM_U_pow q c (mem_Lam.mp hb).2]
  have hsplit : ∀ i : Fin (m - 2 * k + 1), strMat q c k (m - 2 * k + 1) i j • (U m R ^ (i : ℕ)) b =
      (if i = j then (q * (c + ((k + j : ℕ) : R))) • (U m R ^ (j : ℕ)) b else 0) +
      (if (i : ℕ) = j + 1 then (U m R ^ (i : ℕ)) b else 0) := by
    intro i
    by_cases h1 : i = j
    · subst h1; simp [strMat]
    · by_cases h2 : (i : ℕ) = j + 1
      · simp [strMat, h1, h2]
      · simp [strMat, h1, h2]
  rw [sum_congr rfl (fun i _ => hsplit i), sum_add_distrib, sum_ite_eq', if_pos (mem_univ _)]
  congr 1
  by_cases hj : (j : ℕ) + 1 < m - 2 * k + 1
  · rw [sum_eq_single ⟨j + 1, hj⟩]
    · simp
    · intro i _ hi
      rw [if_neg]
      intro h; exact hi (Fin.ext h)
    · intro h; exact absurd (mem_univ _) h
  · rw [sum_eq_zero]
    · rw [show (j : ℕ) + 1 = m - 2 * k + 1 by omega]
      exact U_pow_eq_zero_of_mem_Lam hR hk hb
    · intro i _
      rw [if_neg]
      have := i.2
      omega

section Psi

variable (β : Fin (m / 2 + 1) → ℕ) (bas : (k : Fin (m / 2 + 1)) → Module.Basis (Fin (β k)) R (Lam m R k))

/-- The index type of the strings: pairs `(k, j)` with `k ≤ m/2` and `j < β k`. -/
abbrev StrIdx := Σ k : Fin (m / 2 + 1), Fin (β k)

/-- The string coordinates: `x ↦ ∑_{(k,j)} ∑_{i ≤ m−2k} x_{(k,j),i} U^i b_{k,j}`. -/
noncomputable def Psi : ((t : StrIdx β) → (Fin (m - 2 * (t.1 : ℕ) + 1) → R)) →ₗ[R] B m R where
  toFun x := ∑ t : StrIdx β, ∑ i : Fin (m - 2 * (t.1 : ℕ) + 1),
    x t i • (U m R ^ (i : ℕ)) (bas t.1 t.2 : B m R)
  map_add' x y := by simp [add_smul, sum_add_distrib]
  map_smul' a x := by simp [smul_sum, smul_smul]

lemma Psi_apply (x : (t : StrIdx β) → (Fin (m - 2 * (t.1 : ℕ) + 1) → R)) :
    Psi β bas x = ∑ t : StrIdx β, ∑ i : Fin (m - 2 * (t.1 : ℕ) + 1),
      x t i • (U m R ^ (i : ℕ)) (bas t.1 t.2 : B m R) := rfl

/-- The `ℕ`-indexed family of string generators attached to coordinates `x`. -/
noncomputable def vOf (x : (t : StrIdx β) → (Fin (m - 2 * (t.1 : ℕ) + 1) → R)) (k i : ℕ) :
    B m R :=
  if h : k < m / 2 + 1 ∧ i < m - 2 * k + 1 then
    ∑ j : Fin (β ⟨k, h.1⟩), x ⟨⟨k, h.1⟩, j⟩ ⟨i, h.2⟩ • (bas ⟨k, h.1⟩ j : B m R)
  else 0

lemma vOf_mem (x : (t : StrIdx β) → (Fin (m - 2 * (t.1 : ℕ) + 1) → R)) (k i : ℕ) :
    vOf β bas x k i ∈ Lam m R k := by
  unfold vOf
  split_ifs with h
  · exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (bas ⟨k, h.1⟩ j).2)
  · exact Submodule.zero_mem _

lemma Psi_apply_eq (x : (t : StrIdx β) → (Fin (m - 2 * (t.1 : ℕ) + 1) → R)) :
    Psi β bas x = ∑ k ∈ range (m / 2 + 1), ∑ i ∈ range (m - 2 * k + 1),
      (U m R ^ i) (vOf β bas x k i) := by
  rw [Psi_apply, Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl (fun k _ => ?_)
  dsimp only
  rw [sum_comm, ← Fin.sum_univ_eq_sum_range (fun i => (U m R ^ i) (vOf β bas x k i))]
  refine sum_congr rfl (fun i _ => ?_)
  rw [vOf, dif_pos ⟨k.2, i.2⟩, map_sum]
  refine sum_congr rfl (fun j _ => ?_)
  rw [map_smul]

lemma Psi_bijective (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) :
    Function.Bijective (Psi β bas) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, Psi_apply_eq] at hx
    have h0 := global_indep hR _ (vOf_mem β bas x) hx
    rw [Submodule.mem_bot]
    funext t i
    have h1 := h0 t.1 i (by have := t.1.2; omega) (by have := i.2; omega)
    rw [vOf, dif_pos ⟨t.1.2, i.2⟩] at h1
    have h2 : ∑ j : Fin (β t.1), x ⟨t.1, j⟩ i • bas t.1 j = 0 := by
      apply Subtype.ext
      simpa using h1
    have h3 := (Fintype.linearIndependent_iff.mp (bas t.1).linearIndependent) _ h2 t.2
    simpa using h3
  · intro y
    obtain ⟨v, hv, rfl⟩ := global_span hR y
    refine ⟨fun t i => (bas t.1).repr ⟨v t.1 i, hv _ _⟩ t.2, ?_⟩
    rw [Psi_apply_eq]
    refine sum_congr rfl (fun k hk => sum_congr rfl (fun i hi => ?_))
    rw [mem_range] at hk hi
    rw [vOf, dif_pos ⟨hk, hi⟩]
    congr 1
    have := (bas ⟨k, hk⟩).sum_repr ⟨v k i, hv _ _⟩
    dsimp only
    have h3 : ((∑ j, ((bas ⟨k, hk⟩).repr ⟨v k i, hv _ _⟩) j • (bas ⟨k, hk⟩) j :
        Lam m R k) : B m R) = v k i := by rw [this]
    rw [Submodule.coe_sum] at h3
    simpa only [Submodule.coe_smul] using h3

/-- The block diagonal operator `(x_t)_t ↦ (N_t x_t)_t`. -/
noncomputable def Nblock (q c : R) :
    ((t : StrIdx β) → (Fin (m - 2 * (t.1 : ℕ) + 1) → R)) →ₗ[R]
      ((t : StrIdx β) → (Fin (m - 2 * (t.1 : ℕ) + 1) → R)) :=
  LinearMap.pi (fun t => (strMat q c t.1 (m - 2 * (t.1 : ℕ) + 1)).mulVecLin ∘ₗ LinearMap.proj t)

lemma opM_comp_Psi (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) (q c : R) :
    opM m R q c ∘ₗ Psi β bas = Psi β bas ∘ₗ Nblock β q c := by
  refine LinearMap.ext (fun x => ?_)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Psi_apply, Psi_apply, map_sum]
  refine sum_congr rfl (fun t _ => ?_)
  rw [map_sum]
  simp_rw [map_smul, opM_column hR q c (by have := t.1.2; omega) (bas t.1 t.2).2, smul_sum,
    smul_smul]
  rw [sum_comm]
  refine sum_congr rfl (fun i _ => ?_)
  simp only [Nblock, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, sum_smul]
  refine sum_congr rfl (fun j _ => ?_)
  rw [mul_comm]

lemma range_Nblock (q c : R) :
    LinearMap.range (Nblock β q c) = Submodule.pi Set.univ
      (fun t => LinearMap.range (strMat q c t.1 (m - 2 * (t.1 : ℕ) + 1)).mulVecLin) := by
  ext x
  simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨y, rfl⟩ t
    exact ⟨y t, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext fun t => hy t⟩

include bas in
/-- Ring-independent form of Theorem E: the cokernel of `M` is the product, over the strings, of
`R ⧸ (∏_{i ≤ m−2k} q (c + k + i))`. -/
theorem coker_opM_equiv (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) (q c : R) :
    Nonempty ((B m R ⧸ LinearMap.range (opM m R q c)) ≃ₗ[R]
      ((t : StrIdx β) → R ⧸ Ideal.span
        {∏ i : Fin (m - 2 * (t.1 : ℕ) + 1), q * (c + ((t.1 + i : ℕ) : R))})) := by
  classical
  let e := LinearEquiv.ofBijective (Psi β bas) (Psi_bijective β bas hR)
  have hrange : (LinearMap.range (Nblock β q c)).map (e : _ →ₗ[R] B m R) =
      LinearMap.range (opM m R q c) := by
    have he : (e : _ →ₗ[R] B m R) = Psi β bas := LinearMap.ext (fun x => by simp [e])
    rw [← LinearMap.range_comp, he, ← opM_comp_Psi β bas hR,
      LinearMap.range_comp_of_range_eq_top]
    exact LinearMap.range_eq_top.mpr (Psi_bijective β bas hR).2
  have e1 := (Submodule.Quotient.equiv _ _ e hrange).symm
  rw [range_Nblock] at e1
  have e2 := Submodule.quotientPi
    (fun t : StrIdx β => LinearMap.range (strMat q c t.1 (m - 2 * (t.1 : ℕ) + 1)).mulVecLin)
  have e3 : ∀ t : StrIdx β,
      Nonempty (((Fin (m - 2 * (t.1 : ℕ) + 1) → R) ⧸
        LinearMap.range (strMat q c t.1 (m - 2 * (t.1 : ℕ) + 1)).mulVecLin) ≃ₗ[R]
        R ⧸ Ideal.span {∏ i : Fin (m - 2 * (t.1 : ℕ) + 1), q * (c + ((t.1 + i : ℕ) : R))}) := by
    intro t
    refine bidiagonal_coker _ (by omega) _ (fun i => q * (c + ((t.1 + i : ℕ) : R)))
      (fun i => by simp [strMat]) (fun i j h => ?_) (fun i j h1 h2 => by simp [strMat, h1, h2])
    have : i ≠ j := fun h' => by rw [h'] at h; omega
    simp [strMat, this, h]
  exact ⟨e1.trans (e2.trans (LinearEquiv.piCongrRight (fun t => (e3 t).some)))⟩

end Psi

end ColouredSand.Strings
