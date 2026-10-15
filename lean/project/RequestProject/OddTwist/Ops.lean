module

public import RequestProject.OddTwist.Twist

/-!
# `CSI1_the_odd_twist.md`: computations with the closed formulas (Parts A, B)

Auxiliary computations for the proof sketch of (A1): the closed formulas in terms of an explicit
Euclidean division (`twFdL_eq`, `twEdL_eq`), the closed formulas on arbitrary vectors (for `F`)
and on weight vectors (for `E`), the single operators (`F1_lt`, `F1_last`, `E1_pos`, `E1_zero`),
the commutation `X E^{(c)} = E^{(c)} (X − c(w + c + 1))` on `N`, and the recursion of the sets
`S(j, r)`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset Polynomial

open scoped Nat

variable (p : ℕ) [Fact p.Prime] (N : DPLattice ℤ_[p])

lemma one_le_p : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
lemma two_le_p : 2 ≤ p := (Fact.out : p.Prime).two_le

/-! ### Small values of `q(c, r)` -/

lemma qc_zero_zero : qc p 0 0 = 1 := by
  have := qc_spec p (c := 0) (r := 0) (by simp); simpa using this

lemma qc_zero_one : qc p 0 1 = 1 := by
  have h : 1 / p ≤ 0 := by rw [Nat.div_eq_of_lt (by have := two_le_p p; omega)]
  have := qc_spec p h; simpa using this

lemma qc_one_one : qc p 1 1 = p := by
  have h : 1 / p ≤ 1 := Nat.div_le_self 1 p
  have := qc_spec p h; simpa using this

/-! ### The closed formulas through an explicit Euclidean division -/

lemma twFdL_eq {r j c m : ℕ} (h : j + r = p * c + m) (hm : m < p) :
    twFdL p N r j = ((-1 : ℤ_[p]) ^ c * qc p c r) • (bv p m ∘ₗ N.Fd c) := by
  obtain ⟨h1, h2⟩ := div_mod_unique h hm
  rw [twFdL, cFr, h1, h2]

lemma twEdL_eq {r j c m : ℕ} (w : ℤ) (h : r + m = j + p * c) (hm : m < p) (hj : j < p) :
    twEdL p N r j w =
      ((-1 : ℤ_[p]) ^ c * qc p c r) • (bv p m ∘ₗ N.Ed c ∘ₗ PP p N w (Sset p j r)) := by
  have ht : r + p - 1 - j = p * c + (p - 1 - m) := by omega
  obtain ⟨h1, -⟩ := div_mod_unique ht (by omega)
  have h3 : j + p * c - r = m := by omega
  rw [twEdL, cEr, h1, h3]

lemma twFd_comp_bv (r : ℕ) {j : ℕ} (hj : j < p) : twFd p N r ∘ₗ bv p j = twFdL p N r j := by
  refine ext_single fun i => ?_
  rw [LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl, ← single_eq_bv,
    twFd_pi_single]
  rfl

/-- `F^{(r)}(b_j n)` is given by the closed formula for every vector `n`. -/
lemma twFd_bv (r : ℕ) {j : ℕ} (hj : j < p) (n : N.ι → ℤ_[p]) :
    twFd p N r (bv p j n) = twFdL p N r j n :=
  LinearMap.congr_fun (twFd_comp_bv p N r hj) n

/-- `E^{(r)}(b_j x)` is given by the closed formula for every vector `x` of weight `w`. -/
lemma twEd_bv (r : ℕ) {j : ℕ} (hj : j < p) {w : ℤ} {x : N.ι → ℤ_[p]} (hx : InWt N.wt w x) :
    twEd p N r (bv p j x) = twEdL p N r j w x :=
  Doubling.eq_on_inWt (twEd p N r ∘ₗ bv p j) (twEdL p N r j w)
    (fun i hi => by
      rw [LinearMap.comp_apply, show j = ((⟨j, hj⟩ : Fin p) : ℕ) from rfl, ← single_eq_bv,
        twEd_pi_single, twEdB]
      simp only [hi]) hx

/-! ### The sets `S(j, r)` -/

lemma Sset_zero (j : ℕ) : Sset p j 0 = ∅ := by
  ext ⟨a, k⟩
  simp only [mem_Sset p (one_le_p p), Finset.notMem_empty, iff_false]
  rintro ⟨h1, h2, h3, h4⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; have := h3 rfl; omega
  · have : p ≤ p * a := Nat.le_mul_of_pos_right p ha
    omega

lemma Sset_one_pos {j : ℕ} (h1 : 1 ≤ j) (hj : j < p) : Sset p j 1 = {(0, j)} := by
  ext ⟨a, k⟩
  simp only [mem_Sset p (one_le_p p), Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; have := h3 rfl; omega
    · have : p ≤ p * a := Nat.le_mul_of_pos_right p ha
      omega
  · rintro ⟨rfl, rfl⟩
    refine ⟨h1, by omega, fun _ => le_rfl, by omega⟩

lemma Sset_one_zero : Sset p 0 1 = ∅ := by
  ext ⟨a, k⟩
  simp only [mem_Sset p (one_le_p p), Finset.notMem_empty, iff_false]
  rintro ⟨h1, h2, h3, h4⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; have := h3 rfl; omega
  · have : p ≤ p * a := Nat.le_mul_of_pos_right p ha
    omega

/-- `S(j, r+1) = S(j, r) ∪ {(c, m)}` when the step from slot `m ≥ 1` (at position `r`) is not a
wrap. -/
lemma Sset_succ_pos {j r c m : ℕ} (h : r + m = j + p * c) (hm1 : 1 ≤ m) (hm : m < p) :
    Sset p j (r + 1) = insert (c, m) (Sset p j r) ∧ (c, m) ∉ Sset p j r := by
  constructor
  · ext ⟨a, k⟩
    simp only [Finset.mem_insert, mem_Sset p (one_le_p p), Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hlt : j + p * a < r + k
      · exact Or.inr ⟨h1, h2, h3, hlt⟩
      · have e : k + p * c = m + p * a := by omega
        obtain ⟨hk, ha⟩ := eq_of_add_mul_eq (by omega) hm e
        exact Or.inl ⟨ha, hk⟩
    · rintro (⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4⟩)
      · refine ⟨hm1, by omega, fun hc => ?_, by omega⟩
        subst hc; simp at h; omega
      · exact ⟨h1, h2, h3, by omega⟩
  · simp only [mem_Sset p (one_le_p p)]
    omega

/-- `S(j, r+1) = S(j, r)` when the step at position `r` is the wrap from slot `0`. -/
lemma Sset_succ_zero {j r c : ℕ} (h : r = j + p * c) : Sset p j (r + 1) = Sset p j r := by
  ext ⟨a, k⟩
  simp only [mem_Sset p (one_le_p p)]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    by_contra hlt
    have e : k + p * c = 0 + p * a := by omega
    obtain ⟨hk, -⟩ := eq_of_add_mul_eq (by omega) (by have := one_le_p p; omega) e
    omega
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, by omega⟩

/-! ### The polynomial factors -/

lemma aeval_lin (a b : ℤ_[p]) (x : N.ι → ℤ_[p]) :
    aeval (N.Fd 1 * N.Ed 1) (C a * X + C b) x = a • N.Fd 1 (N.Ed 1 x) + b • x := by
  simp only [map_add, map_mul, aeval_C, aeval_X, LinearMap.add_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply]

lemma aeval_pFactor (w : ℤ) (ak : ℕ × ℕ) (x : N.ι → ℤ_[p]) :
    aeval (N.Fd 1 * N.Ed 1) (pFactor p w ak) x =
      (p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 x) +
        (((((ak.2 : ℕ) : ℤ) - p * (ak.1 : ℕ)) * (p * (w + 1 + (ak.1 : ℕ)) - (ak.2 : ℕ)) : ℤ) :
          ℤ_[p]) • x := by
  rw [pFactor, aeval_lin]

lemma PP_empty (w : ℤ) : PP p N w ∅ = 1 := by simp [PP]

lemma PP_insert (w : ℤ) {S : Finset (ℕ × ℕ)} {ak : ℕ × ℕ} (h : ak ∉ S) (x : N.ι → ℤ_[p]) :
    PP p N w (insert ak S) x = aeval (N.Fd 1 * N.Ed 1) (pFactor p w ak) (PP p N w S x) := by
  rw [PP, prod_insert h, map_mul, Module.End.mul_apply]; rfl

lemma inWt_PP (w : ℤ) (S : Finset (ℕ × ℕ)) {μ : ℤ} {x : N.ι → ℤ_[p]} (hx : InWt N.wt μ x) :
    InWt N.wt μ (PP p N w S x) := Doubling.inWt_aeval N _ hx

/-! ### Weights on `Φ_p(N)` -/

lemma inWt_tw (k : ℕ) {μ : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt μ n) :
    InWt (twWt p N) (p * μ + p - 1 - 2 * (k : ℤ)) (bv p k n) :=
  inWt_bv p k (fun j i hj hi => by simp [twWt, hj, hi]) hn

/-! ### `X E^{(c)} = E^{(c)} (X − c(w + c + 1))` on `N` -/

lemma FE_Ed1 {μ : ℤ} {y : N.ι → ℤ_[p]} (hy : InWt N.wt μ y) :
    N.Fd 1 (N.Ed 1 (N.Ed 1 y)) =
      N.Ed 1 (N.Fd 1 (N.Ed 1 y)) - ((μ + 2 : ℤ) : ℤ_[p]) • N.Ed 1 y := by
  have h := Doubling.Ed_FE N hy
  simp only [LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply] at h
  rw [h]; abel

/-- `F E E^{(c)} z = E^{(c)} F E z − c(w + c + 1) E^{(c)} z` for `z` of weight `w`. -/
lemma FE_Ed (c : ℕ) {w : ℤ} {z : N.ι → ℤ_[p]} (hz : InWt N.wt w z) :
    N.Fd 1 (N.Ed 1 (N.Ed c z)) =
      N.Ed c (N.Fd 1 (N.Ed 1 z)) - (((c : ℤ) * (w + c + 1) : ℤ) : ℤ_[p]) • N.Ed c z := by
  induction c with
  | zero => simp [N.isDP.P0_E]
  | succ c ih =>
    apply Doubling.cancel_smul (Doubling.natCast_succ_ne_zero (A := ℤ_[p]) c)
    have hy := N.isDP.inWt_Ed c hz
    have e1 : ((c : ℤ_[p]) + 1) • N.Fd 1 (N.Ed 1 (N.Ed (c + 1) z)) =
        N.Fd 1 (N.Ed 1 (N.Ed 1 (N.Ed c z))) := by
      rw [Doubling.dp_rec_E N c z, map_smul, map_smul]
    rw [e1, FE_Ed1 p N hy, ih, map_sub, map_smul, Doubling.dp_rec_E, Doubling.dp_rec_E]
    push_cast
    module

/-! ### The single operators -/

/-- (B1) `F(b_j n) = b_{j+1} n` for `j ≤ p − 2`. -/
lemma F1_lt {j : ℕ} (hj : j + 1 < p) (n : N.ι → ℤ_[p]) :
    twFd p N 1 (bv p j n) = bv p (j + 1) n := by
  rw [twFd_bv p N 1 (by omega), twFdL_eq p N (c := 0) (m := j + 1) (by ring) hj]
  simp [qc_zero_one, N.isDP.P0_F]

/-- (B1) `F(b_{p−1} n) = −p · b_0 (F n)`. -/
lemma F1_last (n : N.ι → ℤ_[p]) :
    twFd p N 1 (bv p (p - 1) n) = (-(p : ℤ_[p])) • bv p 0 (N.Fd 1 n) := by
  have := one_le_p p
  rw [twFd_bv p N 1 (by omega), twFdL_eq p N (c := 1) (m := 0) (by omega) (by omega)]
  simp [qc_one_one]

/-- (B1) `E(b_j n) = b_{j−1}(g_j n)`, `g_j = p²X + j(pw + p − j)`, for `1 ≤ j ≤ p − 1` and `n` of
weight `w`. -/
lemma E1_pos {j : ℕ} (h1 : 1 ≤ j) (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    twEd p N 1 (bv p j n) = bv p (j - 1)
      ((p : ℤ_[p]) ^ 2 • N.Fd 1 (N.Ed 1 n) + (((j : ℤ) * (p * w + p - j) : ℤ) : ℤ_[p]) • n) := by
  rw [twEd_bv p N 1 hj hn, twEdL_eq p N w (c := 0) (m := j - 1) (by omega) (by omega) hj,
    Sset_one_pos p h1 hj, ← insert_empty_eq, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, PP_insert p N w (Finset.notMem_empty _), PP_empty, aeval_pFactor]
  simp only [pow_zero, qc_zero_one, mul_one, one_smul, N.isDP.P0_E, Module.End.one_apply]
  congr 3
  push_cast; ring

/-- (B1) `E(b_0 n) = −p · b_{p−1}(E n)` for every vector `n`. -/
lemma E1_zero (n : N.ι → ℤ_[p]) :
    twEd p N 1 (bv p 0 n) = (-(p : ℤ_[p])) • bv p (p - 1) (N.Ed 1 n) := by
  have hp := one_le_p p
  have : twEd p N 1 ∘ₗ bv p 0 = (-(p : ℤ_[p])) • (bv p (p - 1) ∘ₗ N.Ed 1) := by
    refine ext_single fun i => ?_
    rw [LinearMap.comp_apply, show (0 : ℕ) = ((⟨0, by omega⟩ : Fin p) : ℕ) from rfl,
      ← single_eq_bv, twEd_pi_single, twEdB]
    simp only
    rw [twEdL_eq p N _ (c := 1) (m := p - 1) (by omega) (by omega) (by omega), Sset_one_zero,
      PP_empty]
    simp [qc_one_one]
  exact LinearMap.congr_fun this n

end ColouredSand.OddTwist
