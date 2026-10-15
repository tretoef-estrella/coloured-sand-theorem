module

public import RequestProject.Strings.Basic

/-!
# Strings of the Boolean lattice: (S3)

This file corresponds to **(S3) Strings over a ring where `1, …, m` are units** of
`CS1_strings_and_theorem_E.md`.  The encodings of `B_m(R)`, `U`, `D`, `H` and of the levels
`B_m(s)` are those of `RequestProject/Strings/Basic.lean`.

The hypothesis "every integer `n` with `1 ≤ n ≤ m` is a unit of `R`" is
`hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)`.

The key technical input is that `D U` acts invertibly on each level `B_m(s)` with `2s < m`; we
prove this by showing that `D U` is killed on `B_m(s)` by the polynomial
`∏_{k ≤ s} (X − (s−k+1)(m−s−k))`, whose constant term is a unit.
-/

@[expose] public section

open Finset Polynomial

namespace ColouredSand.Strings

variable {m : ℕ} {R : Type*} [CommRing R]

/-! ### Generalities on polynomials of endomorphisms -/

section aeval

variable {M : Type*} [AddCommGroup M] [Module R M]

lemma pow_mul_mul_intertwine (a b : Module.End R M) (n : ℕ) :
    (a * b) ^ n * a = a * (b * a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (a * b) ^ (n + 1) * a = (a * b) ^ n * a * (b * a) := by
          rw [pow_succ]; simp only [mul_assoc]
      _ = a * (b * a) ^ n * (b * a) := by rw [ih]
      _ = _ := by rw [pow_succ, mul_assoc]

lemma aeval_mul_mul_intertwine (a b : Module.End R M) (p : R[X]) :
    aeval (a * b) p * a = a * aeval (b * a) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_mul, mul_add, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, mul_assoc, pow_mul_mul_intertwine, ← mul_assoc,
      Algebra.commutes, mul_assoc]

lemma pow_apply_mem_of_invariant (T : Module.End R M) (N : Submodule R M)
    (hT : ∀ x ∈ N, T x ∈ N) (n : ℕ) : ∀ x ∈ N, (T ^ n) x ∈ N := by
  induction n with
  | zero => simp
  | succ n ih => intro x hx; rw [pow_succ', Module.End.mul_apply]; exact hT _ (ih x hx)

lemma aeval_mem_of_invariant (T : Module.End R M) (N : Submodule R M)
    (hT : ∀ x ∈ N, T x ∈ N) (p : R[X]) : ∀ x ∈ N, aeval T p x ∈ N := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => intro x hx; simpa using N.add_mem (hp x hx) (hq x hx)
  | monomial n c =>
    intro x hx
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact N.smul_mem _ (pow_apply_mem_of_invariant T N hT n x hx)

lemma pow_apply_eq_of_eqOn (T₁ T₂ : Module.End R M) (N : Submodule R M)
    (hT : ∀ x ∈ N, T₁ x ∈ N) (h : ∀ x ∈ N, T₁ x = T₂ x) (n : ℕ) :
    ∀ x ∈ N, (T₁ ^ n) x = (T₂ ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro x hx
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih x hx,
      h _ (pow_apply_mem_of_invariant T₁ N hT n x hx)]

lemma aeval_eq_of_eqOn (T₁ T₂ : Module.End R M) (N : Submodule R M)
    (hT : ∀ x ∈ N, T₁ x ∈ N) (h : ∀ x ∈ N, T₁ x = T₂ x) (p : R[X]) :
    ∀ x ∈ N, aeval T₁ p x = aeval T₂ p x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => intro x hx; simp [hp x hx, hq x hx]
  | monomial n c =>
    intro x hx
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      pow_apply_eq_of_eqOn T₁ T₂ N hT h n x hx]

end aeval

/-! ### The annihilating polynomial of `D U` on a level -/

variable (m) in
/-- The eigenvalue `(s−k+1)(m−s−k)` of `D U` on `U^{s−k} Λ_k ⊆ B_m(s)`. -/
def lam (s k : ℕ) : ℤ := ((s : ℤ) - k + 1) * ((m : ℤ) - s - k)

variable (m R) in
/-- `∏_{k ≤ s} (X − (s−k+1)(m−s−k))`. -/
noncomputable def annPoly (s : ℕ) : R[X] :=
  ∏ k ∈ range (s + 1), (X - C ((lam m s k : ℤ) : R))

lemma DU_mem_level {s : ℕ} {f : B m R} (hf : f ∈ level m R s) :
    (D m R * U m R) f ∈ level m R s :=
  D_mem_level (U_mem_level hf)

lemma UD_mem_level {s : ℕ} {f : B m R} (hf : f ∈ level m R s) :
    (U m R * D m R) f ∈ level m R s := by
  rcases s with _ | s
  · simp [Module.End.mul_apply, D_of_mem_level_zero hf]
  · exact U_mem_level (D_mem_level hf)

lemma aeval_annPoly (s : ℕ) : ∀ x ∈ level m R s, aeval (D m R * U m R) (annPoly m R s) x = 0 := by
  induction s with
  | zero =>
    intro x hx
    simp only [annPoly, zero_add, range_one, prod_singleton, lam]
    simp [Module.End.mul_apply, DU_apply_of_mem_level hx, D_of_mem_level_zero hx]
  | succ s ih =>
    intro x hx
    set c : ℤ := (m : ℤ) - 2 * (s + 1 : ℕ) with hc
    have hsplit : annPoly m R (s + 1) =
        (annPoly m R s).comp (X - C (c : R)) * (X - C (c : R)) := by
      rw [annPoly, prod_range_succ, annPoly, Polynomial.prod_comp]
      congr 1
      · refine prod_congr rfl (fun k _ => ?_)
        simp only [sub_comp, X_comp, C_comp]
        rw [sub_sub, ← C_add]
        congr 3
        simp only [lam, hc]
        push_cast
        ring
      · congr 3
        simp only [lam, hc]
        push_cast
        ring
    have hy : (D m R * U m R - algebraMap R _ (c : R)) x = (U m R * D m R) x := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
        DU_apply_of_mem_level hx, hc, ← Int.cast_smul_eq_zsmul R]
      abel
    have hyl : (U m R * D m R) x ∈ level m R (s + 1) := UD_mem_level hx
    rw [hsplit, aeval_mul, Module.End.mul_apply, aeval_comp]
    simp only [map_sub, aeval_X, aeval_C]
    rw [hy, aeval_eq_of_eqOn _ (U m R * D m R) (level m R (s + 1)) _ _ _ _ hyl]
    · rw [Module.End.mul_apply, ← Module.End.mul_apply _ (U m R),
        aeval_mul_mul_intertwine, Module.End.mul_apply, ih _ (D_mem_level hx), map_zero]
    · intro y hy'
      exact Submodule.sub_mem _ (DU_mem_level hy') (Submodule.smul_mem _ _ hy')
    · intro y hy'
      simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
        DU_apply_of_mem_level hy', hc, ← Int.cast_smul_eq_zsmul R]
      abel

/-- Under `hR`, the integer `n ∈ [1, m]` is a unit (as an integer cast). -/
lemma isUnit_intCast_of_mem (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {z : ℤ}
    (h1 : 1 ≤ z) (h2 : z ≤ m) : IsUnit (z : R) := by
  lift z to ℕ using (by omega)
  exact_mod_cast hR z (by omega) (by omega)

lemma isUnit_lam (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {s k : ℕ} (hs : 2 * s < m)
    (hk : k ≤ s) : IsUnit ((lam m s k : ℤ) : R) := by
  rw [lam, Int.cast_mul]
  exact (isUnit_intCast_of_mem hR (by omega) (by omega)).mul
    (isUnit_intCast_of_mem hR (by omega) (by omega))

/-- `D U` is bijective on `B_m(s)` when `2s < m` (given `hR`). -/
lemma DU_bijOn (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {s : ℕ} (hs : 2 * s < m) :
    (∀ x ∈ level m R s, ∃ y ∈ level m R s, D m R (U m R y) = x) ∧
    (∀ y ∈ level m R s, D m R (U m R y) = 0 → y = 0) := by
  obtain ⟨Q, hQ⟩ := X_dvd_sub_C (p := annPoly m R s)
  have hu : IsUnit ((annPoly m R s).coeff 0) := by
    rw [coeff_zero_eq_eval_zero, annPoly, eval_prod]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro k hk
    simpa using (isUnit_lam hR hs (by simpa [Nat.lt_succ_iff] using hk)).neg
  have hP : annPoly m R s = Q * X + C ((annPoly m R s).coeff 0) := by
    rw [mul_comm, ← hQ]; ring
  have key : ∀ x ∈ level m R s,
      aeval (D m R * U m R) Q (D m R (U m R x)) + (annPoly m R s).coeff 0 • x = 0 := by
    intro x hx
    have := aeval_annPoly s x hx
    rw [hP, aeval_add, aeval_mul, aeval_X, aeval_C] at this
    simpa [Module.End.mul_apply, Module.algebraMap_end_apply] using this
  have key' : ∀ x ∈ level m R s,
      D m R (U m R (aeval (D m R * U m R) Q x)) + (annPoly m R s).coeff 0 • x = 0 := by
    intro x hx
    have := aeval_annPoly s x hx
    rw [hP, mul_comm, aeval_add, aeval_mul, aeval_X, aeval_C] at this
    simpa [Module.End.mul_apply, Module.algebraMap_end_apply] using this
  refine ⟨fun x hx => ?_, fun y hy h0 => ?_⟩
  · refine ⟨-((hu.unit⁻¹ : Rˣ) : R) • aeval (D m R * U m R) Q x,
      Submodule.smul_mem _ _ (aeval_mem_of_invariant _ _ (fun y hy => DU_mem_level hy) Q x hx), ?_⟩
    rw [map_smul, map_smul]
    have h := key' x hx
    rw [add_eq_zero_iff_eq_neg] at h
    rw [h, smul_neg, smul_smul, neg_mul, neg_smul, neg_neg, hu.val_inv_mul, one_smul]
  · have h := key y hy
    rw [h0, map_zero, zero_add] at h
    exact (hu.smul_eq_zero).mp h

/-! ### `Λ_k` and (S3)(a) -/

variable (m R) in
/-- `Λ_k := ker D ∩ B_m(k)` (S3). -/
def Lam (k : ℕ) : Submodule R (B m R) := LinearMap.ker (D m R) ⊓ level m R k

lemma mem_Lam {k : ℕ} {v : B m R} : v ∈ Lam m R k ↔ D m R v = 0 ∧ v ∈ level m R k := by
  simp [Lam]

/-- **(S3)(a), case `r = 0`.**  `Λ_0 = B_m(0)`. (No hypothesis on `R` is needed.) -/
theorem Lam_zero : Lam m R 0 = level m R 0 := by
  ext v
  rw [mem_Lam]
  exact ⟨fun h => h.2, fun h => ⟨D_of_mem_level_zero h, h⟩⟩

/-- **(S3)(a).**  Assume every `n ∈ [1, m]` is a unit of `R`.  For `1 ≤ r ≤ m/2`,
`B_m(r) = U(B_m(r−1)) ⊕ Λ_r` as an internal direct sum of submodules of `B_m(R)`: the two
submodules are disjoint and their sum is `B_m(r)`.  (The case `r = 0` is `Lam_zero`.) -/
theorem strings_a (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : r ≤ m / 2) :
    Disjoint ((level m R (r - 1)).map (U m R)) (Lam m R r) ∧
      (level m R (r - 1)).map (U m R) ⊔ Lam m R r = level m R r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hs : 2 * s < m := by omega
  obtain ⟨hsurj, hinj⟩ := DU_bijOn hR hs
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x ⟨y, hy, rfl⟩ hx
    rw [mem_Lam] at hx
    rw [hinj y hy hx.1, map_zero]
  · refine sup_le ?_ inf_le_right
    rintro _ ⟨y, hy, rfl⟩
    exact U_mem_level hy
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hsurj _ (D_mem_level hx)
    rw [Submodule.mem_sup]
    refine ⟨U m R y, ⟨y, hy, rfl⟩, x - U m R y, ?_, by abel⟩
    rw [mem_Lam]
    exact ⟨by rw [map_sub, hxy, sub_self], Submodule.sub_mem _ hx (U_mem_level hy)⟩

/-! ### The upper half: `U` is onto `B_m(r)` when `2r > m` -/

variable (m R) in
/-- The complement involution `e_S ↦ e_{Sᶜ}`. -/
def cpl : B m R →ₗ[R] B m R where
  toFun f T := f Tᶜ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma cpl_apply (f : B m R) (T : Finset (Fin m)) : cpl m R f T = f Tᶜ := rfl

lemma cpl_cpl (f : B m R) : cpl m R (cpl m R f) = f := by
  ext T; simp

lemma cpl_mem_level {s : ℕ} {f : B m R} (hf : f ∈ level m R s) :
    cpl m R f ∈ level m R (m - s) := by
  intro T hT
  apply hf
  have h1 := Finset.card_compl T
  have h2 := (Finset.card_le_univ T)
  simp only [Fintype.card_fin] at h1 h2
  omega

lemma cpl_D (f : B m R) : cpl m R (D m R f) = U m R (cpl m R f) := by
  ext T
  simp only [cpl_apply, D_apply, compl_compl, U_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.compl_erase]

/-- For `2r > m`, `B_m(r) ⊆ U(B_m(r−1))` (given `hR`). -/
lemma level_le_map_U (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {r : ℕ} (hr : m < 2 * r) :
    level m R r ≤ (level m R (r - 1)).map (U m R) := by
  intro x hx
  by_cases hrm : m < r
  · rw [eq_zero_of_mem_level_of_lt hx hrm]; exact Submodule.zero_mem _
  push_neg at hrm
  obtain ⟨hsurj, -⟩ := DU_bijOn (R := R) hR (s := m - r) (by omega)
  obtain ⟨z, hz, hzx⟩ := hsurj _ (cpl_mem_level hx)
  refine ⟨cpl m R (U m R z), ?_, ?_⟩
  · have := cpl_mem_level (U_mem_level hz)
    rwa [show m - (m - r + 1) = r - 1 by omega] at this
  · rw [← cpl_D, hzx, cpl_cpl]

/-! ### (S3)(c) -/

/-- A vector of a level `B_m(r)` with `2r > m` that is killed by `D` is zero (given `hR`). -/
lemma eq_zero_of_D_eq_zero_of_high (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {r : ℕ}
    (hr : m < 2 * r) {y : B m R} (hy : y ∈ level m R r) (hD : D m R y = 0) : y = 0 := by
  by_cases hrm : m < r
  · exact eq_zero_of_mem_level_of_lt hy hrm
  push_neg at hrm
  have key : ∀ j, j ≤ m - r + 1 → (U m R ^ (m - r + 1 - j)) y = 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      exact eq_zero_of_mem_level_of_lt (U_pow_mem_level hy _) (by omega)
    | succ j ih =>
      intro hj
      have h := string_relation_succ hy hD (m - r + 1 - (j + 1))
      rw [show m - r + 1 - (j + 1) + 1 = m - r + 1 - j by omega, ih (by omega),
        map_zero, ← Int.cast_smul_eq_zsmul R] at h
      refine ((IsUnit.smul_eq_zero ?_).mp h.symm)
      rw [Int.cast_mul]
      refine (isUnit_intCast_of_mem hR (by omega) (by omega)).mul ?_
      have := (isUnit_intCast_of_mem hR (R := R)
        (z := 2 * r + (m - r + 1 - (j + 1) : ℕ) - m) (by omega) (by omega)).neg
      convert this using 1
      push_cast
      ring
  simpa using key (m - r + 1) le_rfl

lemma U_pow_eq_zero_of_mem_Lam (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {k : ℕ}
    (hk : k ≤ m / 2) {v : B m R} (hv : v ∈ Lam m R k) : (U m R ^ (m - 2 * k + 1)) v = 0 := by
  rw [mem_Lam] at hv
  refine eq_zero_of_D_eq_zero_of_high hR (r := k + (m - 2 * k + 1)) (by omega)
    (U_pow_mem_level hv.2 _) ?_
  rw [string_relation_succ hv.2 hv.1]
  have : ((m : ℤ) - 2 * k - (m - 2 * k : ℕ)) = 0 := by push_cast [show 2 * k ≤ m by omega]; ring
  rw [this, mul_zero, zero_smul]

/-- **(S3)(c).**  Assume every `n ∈ [1, m]` is a unit of `R`.  For `k ≤ m/2`,
`U^{m−2k+1} Λ_k = 0`.  This holds over every commutative ring in which `1, …, m` are units;
no "domain of characteristic `0`" hypothesis is needed (a more general statement than the
file's). -/
theorem strings_c (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) {k : ℕ} (hk : k ≤ m / 2) :
    (Lam m R k).map (U m R ^ (m - 2 * k + 1)) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨v, hv, rfl⟩
  exact (Submodule.mem_bot R).mpr (U_pow_eq_zero_of_mem_Lam hR hk hv)

/-! ### (S3)(b) -/

variable (m) in
/-- The index set `{k : 0 ≤ k ≤ min(r, m − r)}` of (S3)(b), as `{k : k ≤ r ∧ k + r ≤ m}`
(this is also correct, i.e. empty, when `r > m`). -/
def strIdx (r : ℕ) : Finset ℕ := (range (r + 1)).filter (fun k => k + r ≤ m)

lemma mem_strIdx {r k : ℕ} : k ∈ strIdx m r ↔ k ≤ r ∧ k + r ≤ m := by
  simp [strIdx]

lemma D_pow_U_pow {k : ℕ} {v : B m R} (hv : v ∈ Lam m R k) {j n : ℕ} (hjn : j ≤ n) :
    ∃ c : R, (D m R ^ j) ((U m R ^ n) v) = c • (U m R ^ (n - j)) v ∧
      (n + 2 * k ≤ m → (∀ i : ℕ, 1 ≤ i → i ≤ m → IsUnit (i : R)) → IsUnit c) := by
  rw [mem_Lam] at hv
  induction j with
  | zero => exact ⟨1, by simp, fun _ _ => isUnit_one⟩
  | succ j ih =>
    obtain ⟨c, hc, hcu⟩ := ih (by omega)
    obtain ⟨t, ht⟩ : ∃ t, n - j = t + 1 := ⟨n - j - 1, by omega⟩
    refine ⟨c * (((t + 1 : ℕ) * ((m : ℤ) - 2 * k - t) : ℤ) : R), ?_, ?_⟩
    · rw [pow_succ', Module.End.mul_apply, hc, map_smul, ht, string_relation_succ hv.2 hv.1,
        ← Int.cast_smul_eq_zsmul R, smul_smul, show n - (j + 1) = t by omega]
      push_cast
      ring_nf
    · intro hn hR
      refine (hcu hn hR).mul ?_
      rw [Int.cast_mul]
      exact (isUnit_intCast_of_mem hR (by omega) (by omega)).mul
        (isUnit_intCast_of_mem hR (by omega) (by omega))

lemma D_pow_U_pow_eq_zero {k : ℕ} {v : B m R} (hv : v ∈ Lam m R k) {j n : ℕ} (hjn : n < j) :
    (D m R ^ j) ((U m R ^ n) v) = 0 := by
  obtain ⟨c, hc, -⟩ := D_pow_U_pow hv (le_refl n)
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 + n := ⟨j - n - 1, by omega⟩
  rw [pow_add, Module.End.mul_apply, hc, Nat.sub_self, pow_zero, Module.End.one_apply,
    map_smul, pow_succ, Module.End.mul_apply, (mem_Lam.mp hv).1, map_zero, smul_zero]

/-- Linear independence of the strings at level `r`. -/
lemma strings_indep (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) (r : ℕ) (v : ℕ → B m R)
    (hv : ∀ k, v k ∈ Lam m R k) (h0 : ∑ k ∈ strIdx m r, (U m R ^ (r - k)) (v k) = 0) :
    ∀ k ∈ strIdx m r, v k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hk' := mem_strIdx.mp hk
    have h1 := congrArg (D m R ^ (r - k)) h0
    rw [map_sum, map_zero, Finset.sum_eq_single k] at h1
    · obtain ⟨c, hc, hcu⟩ := D_pow_U_pow (hv k) (le_refl (r - k))
      rw [hc, Nat.sub_self, pow_zero, Module.End.one_apply] at h1
      exact ((hcu (by omega) hR).smul_eq_zero).mp h1
    · intro k' hk'' hne
      have := mem_strIdx.mp hk''
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [ih k' hlt hk'', map_zero, map_zero]
      · exact D_pow_U_pow_eq_zero (hv k') (by omega)
    · intro h; exact absurd hk h

/-- Spanning of the strings at level `r`. -/
lemma strings_span (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) (r : ℕ) :
    ∀ x ∈ level m R r, ∃ v : ℕ → B m R, (∀ k, v k ∈ Lam m R k) ∧
      x = ∑ k ∈ strIdx m r, (U m R ^ (r - k)) (v k) := by
  induction r with
  | zero =>
    intro x hx
    refine ⟨fun k => if k = 0 then x else 0, fun k => ?_, ?_⟩
    · dsimp only
      split_ifs with h
      · subst h; rw [Lam_zero]; exact hx
      · exact Submodule.zero_mem _
    · have : strIdx m 0 = {0} := by ext k; simp only [mem_strIdx, mem_singleton]; omega
      simp [this]
  | succ r ih =>
    intro x hx
    by_cases hrm : m < r + 1
    · refine ⟨0, fun k => Submodule.zero_mem _, ?_⟩
      rw [eq_zero_of_mem_level_of_lt hx hrm]
      simp
    push_neg at hrm
    by_cases hlow : 2 * (r + 1) ≤ m
    · obtain ⟨-, hsup⟩ := strings_a hR (r := r + 1) (by omega) (by omega)
      rw [← hsup, Submodule.mem_sup] at hx
      obtain ⟨_, ⟨y, hy, rfl⟩, l, hl, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := ih y (by simpa using hy)
      refine ⟨fun k => if k = r + 1 then l else v k, fun k => ?_, ?_⟩
      · dsimp only
        split_ifs with h
        · subst h; exact hl
        · exact hv k
      · have hI : strIdx m (r + 1) = insert (r + 1) (strIdx m r) := by
          ext k; simp only [mem_insert, mem_strIdx]; omega
        have hnot : r + 1 ∉ strIdx m r := by simp [mem_strIdx]
        rw [hI, Finset.sum_insert hnot]
        dsimp only
        rw [if_pos rfl, Nat.sub_self, pow_zero, Module.End.one_apply,
          map_sum, add_comm]
        congr 1
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have := mem_strIdx.mp hk
        rw [if_neg (by omega), ← Module.End.mul_apply, ← pow_succ',
          show r - k + 1 = r + 1 - k by omega]
    · push_neg at hlow
      obtain ⟨y, hy, rfl⟩ := level_le_map_U hR (r := r + 1) (by omega) hx
      obtain ⟨v, hv, rfl⟩ := ih y (by simpa using hy)
      refine ⟨v, hv, ?_⟩
      rw [map_sum]
      symm
      refine Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_) |>.trans
        (Finset.sum_congr rfl (fun k hk => ?_))
      · have := mem_strIdx.mp hk; rw [mem_strIdx]; omega
      · have h1 := mem_strIdx.mp hk
        have h2 : ¬ (k ≤ r + 1 ∧ k + (r + 1) ≤ m) := fun h => hk' (mem_strIdx.mpr h)
        rw [show r + 1 - k = m - 2 * k + 1 by omega]
        exact U_pow_eq_zero_of_mem_Lam hR (by omega) (hv k)
      · have := mem_strIdx.mp hk
        rw [← Module.End.mul_apply, ← pow_succ', show r - k + 1 = r + 1 - k by omega]

variable (m R) in
/-- The string map of (S3)(b): `Φ_r : ⊕_{0 ≤ k ≤ min(r, m−r)} Λ_k → B_m(R)`,
`(v_k) ↦ ∑_k U^{r−k} v_k`.  The direct sum is the (finite) product
`(k : strIdx m r) → Lam m R k`. -/
noncomputable def stringMap (r : ℕ) : ((k : strIdx m r) → Lam m R k) →ₗ[R] B m R :=
  ∑ k : strIdx m r, (U m R ^ (r - (k : ℕ))) ∘ₗ (Lam m R k).subtype ∘ₗ LinearMap.proj k

lemma stringMap_apply (r : ℕ) (v : (k : strIdx m r) → Lam m R k) :
    stringMap m R r v = ∑ k ∈ strIdx m r,
      (U m R ^ (r - k)) (if h : k ∈ strIdx m r then (v ⟨k, h⟩ : B m R) else 0) := by
  simp only [stringMap, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.subtype_apply]
  rw [← Finset.sum_coe_sort (strIdx m r)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [dif_pos k.2]

/-- **(S3)(b).**  Assume every `n ∈ [1, m]` is a unit of `R`.  For every `r`, the map
`⊕_{k ≤ min(r, m−r)} Λ_k → B_m(r)`, `(v_k) ↦ ∑_k U^{r−k} v_k` is an isomorphism: the map
`stringMap m R r` is injective and its range is exactly `B_m(r)`.  The isomorphism itself is
`stringEquiv`. -/
theorem strings_b (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) (r : ℕ) :
    Function.Injective (stringMap m R r) ∧ LinearMap.range (stringMap m R r) = level m R r := by
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, stringMap_apply] at hv
    rw [Submodule.mem_bot]
    funext k
    have := strings_indep hR r _ (fun k => ?_) hv k k.2
    · rw [dif_pos k.2] at this
      exact Subtype.ext this
    · split_ifs with h
      · exact (v ⟨k, h⟩).2
      · exact Submodule.zero_mem _
  · rintro _ ⟨v, rfl⟩
    rw [stringMap_apply]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    have := mem_strIdx.mp hk
    have hmem : (if h : k ∈ strIdx m r then (v ⟨k, h⟩ : B m R) else 0) ∈ level m R k := by
      rw [dif_pos hk]; exact (mem_Lam.mp (v ⟨k, hk⟩).2).2
    have h := U_pow_mem_level hmem (r - k)
    rwa [show k + (r - k) = r by omega] at h
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := strings_span hR r x hx
    refine ⟨fun k => ⟨v k, hv k⟩, ?_⟩
    rw [stringMap_apply]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [dif_pos hk]

/-- The isomorphism `⊕_{k ≤ min(r, m−r)} Λ_k ≃ B_m(r)` of (S3)(b). -/
noncomputable def stringEquiv (hR : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsUnit (n : R)) (r : ℕ) :
    ((k : strIdx m r) → Lam m R k) ≃ₗ[R] level m R r :=
  (LinearEquiv.ofInjective _ (strings_b hR r).1).trans
    (LinearEquiv.ofEq _ _ (strings_b hR r).2)

end ColouredSand.Strings
