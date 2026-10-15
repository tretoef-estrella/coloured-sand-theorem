module

public import RequestProject.OddSES.ModP

/-!
# `CSI4_the_short_exact_sequences.md`: Part C, (C2) — the Casimir on `Ψ_s(N)` modulo `p`

Encodings (CSI3's, see `RequestProject/OddSplit/Basic.lean`): the basis of `Ψ_s(N)` is
`Bool × Fin p × N.ι`, `aV p j n = A_j n`, `cV p j n = C_j n`; the single operators are CSI3's
`psiF p N s`, `psiE p N s` and the weights `psiWt p N s`.

* `ASpan p N` is `span{A_k n'}`: the span of the basis vectors `A_k δ_i`.
* `casPsi p N s = 4 • (psiF ∘ psiE) + (Hop (psiWt) + 1)²` is the Casimir written with the operators
  of Definition 1.3; for every `L : PsiData p N s` (in particular for `psi p N s h1 h2`) it is
  `casimir L.lat` (`casimir_lat`).
* `Dcas M c = Ω_M − c • 1`, so `D = Dcas (psi p N s h1 h2) (s²)` is the `D := Ω − s²` of (C2).
* "`D x ∈ p • (ι → ℤ_[p])`" is `D x ∈ pSub p _`, and "`D x ∈ span{A_k n'} + p • (ι → ℤ_[p])`" is
  `D x ∈ ASpan p N ⊔ pSub p _`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

variable (p N) in
/-- (C2) `span{A_k n'}`: the span of the basis vectors `A_k δ_i` of `Ψ_s(N)`. -/
def ASpan : Submodule ℤ_[p] (Bool × Fin p × N.ι → ℤ_[p]) :=
  Submodule.span ℤ_[p] (Set.range fun x : Fin p × N.ι => aV p x.1 (Pi.single x.2 1))

lemma aV_mem_ASpan (k : ℕ) (n : N.ι → ℤ_[p]) : aV p k n ∈ ASpan p N := by
  rcases Nat.lt_or_ge k p with hk | hk
  · have hn : n = ∑ i, n i • (Pi.single i 1 : N.ι → ℤ_[p]) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hn, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨k, hk⟩, i), rfl⟩)
  · rw [aV_of_ge p hk]; exact Submodule.zero_mem _

variable (p N) in
/-- (C2) The Casimir of `Ψ_s(N)` written with the operators of Definition 1.3:
`4 • (psiF ∘ psiE) + (H + 1)²`, `H = Hop (psiWt p N s)`. -/
def casPsi (s : ℕ) : Module.End ℤ_[p] (Bool × Fin p × N.ι → ℤ_[p]) :=
  (4 : ℤ_[p]) • (psiF p N s ∘ₗ psiE p N s) + (Hop (psiWt p N s) + 1) ^ 2

/-- (C2) For every `L : PsiData p N s` (e.g. `psiD p N s h1 h2`, whose lattice is
`psi p N s h1 h2`), the Casimir of `L.lat` is `casPsi p N s`. -/
lemma casimir_lat {s : ℕ} (L : PsiData p N s) : casimir L.lat = casPsi p N s := by
  unfold casimir casPsi
  rw [lat_Fd1, lat_Ed1]
  rfl

lemma casPsi_apply (s : ℕ) (x : Bool × Fin p × N.ι → ℤ_[p]) :
    casPsi p N s x = (4 : ℤ_[p]) • psiF p N s (psiE p N s x) + Hop (psiWt p N s)
      (Hop (psiWt p N s) x) + (2 : ℤ_[p]) • Hop (psiWt p N s) x + x := by
  simp only [casPsi, pow_two, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Module.End.mul_apply, Module.End.one_apply, map_add]
  module

/-- (C2) `Dcas M c = Ω_M − c • 1`. -/
def Dcas {A : Type*} [CommRing A] (M : DPLattice A) (c : A) : Module.End A (M.ι → A) :=
  casimir M - c • LinearMap.id

/-! ### `E`, `F E` and `Ω` on `A_j n` modulo `p` -/

section A

variable (s : ℕ)

lemma modP_psiE_aV {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    ModP p (psiE p N s (aV p j n)) (((j : ℤ_[p]) * (p * w + p + s - j)) • aV p (j - 1) n) := by
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · rw [psiE_A_zero s hn]
    exact ⟨-aV p (p - 1) (N.Ed 1 n) + ((p : ℤ_[p]) - s) • cV p (p - 1 - s) (N.Ed 1 n), by
      simp only [Nat.cast_zero, zero_mul, zero_smul, sub_zero, smul_add, smul_neg]; module⟩
  · rcases le_or_gt j s with h2 | h2
    · rw [psiE_A_low s h1 h2 hj hn]
      exact ⟨aV p (j - 1) ((p : ℤ_[p]) • N.Fd 1 (N.Ed 1 n)) -
          (s : ℤ_[p]) • cV p (p + j - 1 - s) (N.Ed 1 n), by
        simp only [map_add, map_smul, map_sub, smul_sub]; module⟩
    · rw [psiE_A_high s h2 hj hn]
      exact ⟨aV p (j - 1) ((p : ℤ_[p]) • N.Fd 1 (N.Ed 1 n)) +
          ((s : ℤ_[p]) * p) • cV p (j - 1 - s) (N.Fd 1 (N.Ed 1 n)), by
        simp only [map_add, map_smul, map_sub, smul_add]; module⟩

lemma modP_psiFE_aV {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    ModP p (psiF p N s (psiE p N s (aV p j n)))
      (((j : ℤ_[p]) * (p * w + p + s - j)) • aV p j n) := by
  refine ((modP_psiE_aV s hj hn).map (psiF p N s)).trans (ModP.of_eq ?_)
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · simp
  · rw [map_smul, psiF_A_lt s (by omega), Nat.sub_add_cancel h1]

/-- (C2) `Ω(A_j n) ≡ s² A_j n` modulo `p`: `4 g^A_j + (pw + p + s − 2j)² = (p(w+1) + s)²`. -/
lemma modP_casPsi_aV {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    ModP p (casPsi p N s (aV p j n)) (((s : ℤ_[p]) ^ 2) • aV p j n) := by
  obtain ⟨z, hz⟩ := modP_psiFE_aV s hj hn
  have hz' : psiF p N s (psiE p N s (aV p j n)) =
      ((j : ℤ_[p]) * (p * w + p + s - j)) • aV p j n + (p : ℤ_[p]) • z := by
    rw [← hz]; abel
  refine ⟨(4 : ℤ_[p]) • z + (((w : ℤ_[p]) + 1) * (p * (w + 1) + 2 * s)) • aV p j n, ?_⟩
  rw [casPsi_apply, H_aV s j hn, map_smul, H_aV s j hn, hz']
  push_cast
  module

end A

/-! ### `E`, `F E` and `Ω` on `C_j n` modulo `p` -/

section C

variable (s : ℕ) (hs1 : 1 ≤ s) (hsp : s ≤ p - 1)
include hs1 hsp

lemma modP_psiE_cV {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    ModP p (psiE p N s (cV p j n)) (((j : ℤ_[p]) * (p * w + p - s - j)) • cV p (j - 1) n +
      (if j ≤ p - s then (s : ℤ_[p]) • aV p (j + s - 1) n else 0)) := by
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · rw [psiE_C_zero s hn, if_pos (Nat.zero_le _), zero_add]
    exact ⟨-cV p (p - 1) (N.Ed 1 n), by
      simp only [Nat.cast_zero, zero_mul, zero_smul, zero_add, smul_neg]; module⟩
  · rcases le_or_gt j (p - s) with h2 | h2
    · rw [psiE_C_low s h1 h2 hj hn, if_pos h2]
      exact ⟨cV p (j - 1) ((p : ℤ_[p]) • N.Fd 1 (N.Ed 1 n)), by
        simp only [map_add, map_smul]; module⟩
    · rw [psiE_C_high s (by omega) hj hn, if_neg (by omega), add_zero]
      exact ⟨cV p (j - 1) ((p : ℤ_[p]) • N.Fd 1 (N.Ed 1 n) + (s : ℤ_[p]) • n) -
          (s : ℤ_[p]) • aV p (j + s - 1 - p) (N.Fd 1 n), by
        simp only [map_add, map_smul, map_sub, smul_sub, smul_add]; module⟩

lemma modP_psiFE_cV {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    ModP p (psiF p N s (psiE p N s (cV p j n))) (((j : ℤ_[p]) * (p * w + p - s - j)) • cV p j n +
      (if j ≤ p - s then (s : ℤ_[p]) • psiF p N s (aV p (j + s - 1) n) else 0)) := by
  refine ((modP_psiE_cV s hs1 hsp hj hn).map (psiF p N s)).trans (ModP.of_eq ?_)
  rw [map_add]
  congr 1
  · rcases Nat.eq_zero_or_pos j with rfl | h1
    · simp
    · rw [map_smul, psiF_C_lt s (by omega), Nat.sub_add_cancel h1]
  · split_ifs <;> simp

/-- (C2) `Ω(C_j n) ≡ s² C_j n + 4s·F(A_{j+s−1} n)` modulo `p` (the last term only for
`j ≤ p − s`): the diagonal part is `(p(w+1) − s)² ≡ s²`. -/
lemma modP_casPsi_cV {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]} (hn : InWt N.wt w n) :
    ModP p (casPsi p N s (cV p j n)) (((s : ℤ_[p]) ^ 2) • cV p j n +
      (if j ≤ p - s then (4 * s : ℤ_[p]) • psiF p N s (aV p (j + s - 1) n) else 0)) := by
  obtain ⟨z, hz⟩ := modP_psiFE_cV s hs1 hsp hj hn
  have hz' : psiF p N s (psiE p N s (cV p j n)) =
      ((j : ℤ_[p]) * (p * w + p - s - j)) • cV p j n +
      (if j ≤ p - s then (s : ℤ_[p]) • psiF p N s (aV p (j + s - 1) n) else 0) +
      (p : ℤ_[p]) • z := by
    rw [← hz]; abel
  refine ⟨(4 : ℤ_[p]) • z + (((w : ℤ_[p]) + 1) * (p * (w + 1) - 2 * s)) • cV p j n, ?_⟩
  rw [casPsi_apply, H_cV s j hn, map_smul, H_cV s j hn, hz']
  split_ifs
  · push_cast; module
  · push_cast; module

end C

/-! ### (C2) -/

section C2

variable (s : ℕ) (hs1 : 1 ≤ s) (hsp : s ≤ p - 1)

lemma Dcas_lat_apply (L : PsiData p N s) (x : Bool × Fin p × N.ι → ℤ_[p]) :
    Dcas L.lat ((s : ℤ_[p]) ^ 2) x = casPsi p N s x - ((s : ℤ_[p]) ^ 2) • x := by
  rw [Dcas, casimir_lat]; rfl

/-- (C2) `D` kills the `A`-part modulo `p`. -/
lemma Dcas_aV_mem (L : PsiData p N s) {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]}
    (hn : InWt N.wt w n) : Dcas L.lat ((s : ℤ_[p]) ^ 2) (aV p j n) ∈ pSub p _ := by
  rw [Dcas_lat_apply]
  exact modP_iff.1 (modP_casPsi_aV s hj hn)

include hs1 hsp in
/-- (C2) `D` maps the `C`-part into the `A`-part modulo `p`. -/
lemma Dcas_cV_mem (L : PsiData p N s) {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]}
    (hn : InWt N.wt w n) :
    Dcas L.lat ((s : ℤ_[p]) ^ 2) (cV p j n) ∈ ASpan p N ⊔ pSub p _ := by
  rw [Dcas_lat_apply]
  have h := (modP_casPsi_cV s hs1 hsp hj hn).sub (ModP.refl (((s : ℤ_[p]) ^ 2) • cV p j n))
  rw [add_sub_cancel_left] at h
  refine h.mem_sup ?_
  split_ifs
  · refine (ModP.smul _ (modP_psiF_aV (N := N) s (j + s - 1) n)).mem_sup ?_
    exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (aV_mem_ASpan _ _))
  · exact Submodule.zero_mem _

include hs1 hsp in
/-- (C2) `D ∘ D = p • R` for some endomorphism `R` (for every `L : PsiData p N s`). -/
lemma Dcas_sq_lat (L : PsiData p N s) :
    ∃ R, Dcas L.lat ((s : ℤ_[p]) ^ 2) ∘ₗ Dcas L.lat ((s : ℤ_[p]) ^ 2) = (p : ℤ_[p]) • R := by
  set D := Dcas L.lat ((s : ℤ_[p]) ^ 2) with hD
  have hA : ASpan p N ≤ (pSub p _).comap D := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨j, i⟩, rfl⟩
    exact Dcas_aV_mem s L j.isLt (inWt_single N.wt i)
  have hP : pSub p (Bool × Fin p × N.ι → ℤ_[p]) ≤ (pSub p _).comap D := by
    intro x hx
    obtain ⟨z, rfl⟩ := mem_pSub.1 hx
    rw [Submodule.mem_comap, map_smul]; exact p_smul_mem_pSub _
  have hsup : ASpan p N ⊔ pSub p _ ≤ (pSub p _).comap D := sup_le hA hP
  refine exists_eq_p_smul (D ∘ₗ D) fun x => ?_
  obtain ⟨b, j, i⟩ := x
  rw [LinearMap.comp_apply]
  cases b
  · rw [single_false]
    exact hP (Dcas_aV_mem s L j.isLt (inWt_single N.wt i))
  · rw [single_true]
    exact hsup (Dcas_cV_mem s hs1 hsp L j.isLt (inWt_single N.wt i))

/-- (C2) **The Casimir on `Ψ_s(N)` modulo `p`.** For `1 ≤ s ≤ p − 1`, let
`D := Ω − s²` on `psi p N s` (`D = Dcas (psi p N s h1 h2) (s²)`). Then for every basis vector
`A_j δ_i`, `D (A_j δ_i) ∈ p • (ι → ℤ_[p])` (`D` kills the `A`-part modulo `p`); for every basis
vector `C_j δ_i`, `D (C_j δ_i) ∈ span{A_k n'} + p • (ι → ℤ_[p])` (`D` maps the `C`-part into
the `A`-part modulo `p`); hence `D ∘ D = p • R` for some endomorphism `R`. -/
theorem C2 :
    (∀ (j : ℕ) (i : N.ι), j < p →
      Dcas (psi p N s hs1 hsp) ((s : ℤ_[p]) ^ 2) (aV p j (Pi.single i 1)) ∈ pSub p _) ∧
    (∀ (j : ℕ) (i : N.ι), j < p →
      Dcas (psi p N s hs1 hsp) ((s : ℤ_[p]) ^ 2) (cV p j (Pi.single i 1)) ∈
        ASpan p N ⊔ pSub p _) ∧
    ∃ R, Dcas (psi p N s hs1 hsp) ((s : ℤ_[p]) ^ 2) ∘ₗ
      Dcas (psi p N s hs1 hsp) ((s : ℤ_[p]) ^ 2) = (p : ℤ_[p]) • R :=
  ⟨fun _ i hj => Dcas_aV_mem s (psiD p N s hs1 hsp) hj (inWt_single N.wt i),
    fun _ i hj => Dcas_cV_mem s hs1 hsp (psiD p N s hs1 hsp) hj (inWt_single N.wt i),
    Dcas_sq_lat s hs1 hsp (psiD p N s hs1 hsp)⟩

end C2

end ColouredSand.OddTwist
