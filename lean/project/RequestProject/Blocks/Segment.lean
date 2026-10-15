module

public import RequestProject.Blocks.Tools

/-!
# Contracting the unit links of a bidiagonal chain (CSG1, §3 "Elimination", first step)

This file formalizes the first step of the elimination of §3 of
`CSG1_lemma_8_the_blocks.md`: "solving the unit subdiagonal entries, the cokernel is generated
by the first vector of each segment between non-unit entries, with one relation at the end of
each segment".

## Encoding

* A lower bidiagonal chain matrix on `R^{n+1} = Fin (n+1) → R` with diagonal `d` and
  subdiagonal `s` (both `ℕ → R`) is encoded by its columns
  `chainCol n d s i = d i • e_i + s i • e_{i+1}` (`e_{n+1} = 0`), and its range (the relation
  module) is `chainRel n d s = span {chainCol n d s i | i ≤ n}`.
* The chain is cut into segments of length `L`: the links `i → i+1` with `L ∣ i+1` are the
  "broken" ones, all other subdiagonal entries are assumed to be units.
* `segPi` sends `e_i` to `c_i e_{⌊i/L⌋}` (`c_i` = `segCoef`, the product of the
  `−d_u / s_u` along the segment), `segSig` sends `e_t` to `e_{tL}`.
* The reduced chain has diagonal `segD` (the end-of-segment relation coefficient) and
  subdiagonal `segS` (the broken link).
-/

@[expose] public section

open Submodule

namespace ColouredSand.Blocks

variable {R : Type*} [CommRing R]

/-- Column `i` of the lower bidiagonal chain matrix: `d i • e_i + s i • e_{i+1}`. -/
def chainCol (n : ℕ) (d s : ℕ → R) (i : ℕ) : Fin (n + 1) → R := d i • ev i + s i • ev (i + 1)

/-- The relation module (range) of the lower bidiagonal chain matrix on `R^{n+1}`. -/
def chainRel (n : ℕ) (d s : ℕ → R) : Submodule R (Fin (n + 1) → R) :=
  Submodule.span R (Set.range fun i : Fin (n + 1) => chainCol n d s i)

/-- The coefficients `c_i` with `[e_i] = c_i [e_{L ⌊i/L⌋}]` in the cokernel. -/
noncomputable def segCoef (L : ℕ) (d s : ℕ → R) : ℕ → R
  | 0 => 1
  | i + 1 => if (i + 1) % L = 0 then 1 else -(d i) * Ring.inverse (s i) * segCoef L d s i

/-- The reduction map `e_i ↦ c_i e_{⌊i/L⌋}`. -/
noncomputable def segPi (n L : ℕ) (d s : ℕ → R) : (Fin (n + 1) → R) →ₗ[R] (Fin (n / L + 1) → R) :=
  linOfFun (fun i => segCoef L d s i • (ev (i / L) : Fin (n / L + 1) → R))

/-- The section `e_t ↦ e_{tL}`. -/
noncomputable def segSig (n L : ℕ) : (Fin (n / L + 1) → R) →ₗ[R] (Fin (n + 1) → R) :=
  linOfFun (fun t => (ev (t * L) : Fin (n + 1) → R))

/-- The diagonal of the reduced chain: the coefficient of the end-of-segment relation. -/
noncomputable def segD (n L : ℕ) (d s : ℕ → R) (t : ℕ) : R :=
  d (min (t * L + L - 1) n) * segCoef L d s (min (t * L + L - 1) n)

/-- The subdiagonal of the reduced chain: the broken link. -/
def segS (L : ℕ) (s : ℕ → R) (t : ℕ) : R := s (t * L + L - 1)

lemma chainCol_mem {n : ℕ} {d s : ℕ → R} {i : ℕ} (hi : i ≤ n) :
    chainCol n d s i ∈ chainRel n d s :=
  subset_span ⟨⟨i, by omega⟩, rfl⟩

section lemmas

variable {n L : ℕ} {d s : ℕ → R}

lemma segCoef_mul (hL : 0 < L) (t : ℕ) : segCoef L d s (t * L) = 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [segCoef]
  · obtain ⟨i, hi⟩ : ∃ i, t * L = i + 1 := ⟨t * L - 1, by
      have := Nat.mul_le_mul ht hL; omega⟩
    rw [hi, segCoef, if_pos]
    rw [← hi]; simp

lemma segPi_ev {j : ℕ} (hj : j ≤ n) :
    segPi n L d s (ev j) = segCoef L d s j • (ev (j / L) : Fin (n / L + 1) → R) := by
  unfold segPi; rw [linOfFun_ev _ (by omega)]

lemma mul_le_of_le_div {t : ℕ} (ht : t ≤ n / L) : t * L ≤ n :=
  le_trans (Nat.mul_le_mul_right L ht) (Nat.div_mul_le_self n L)

lemma segSig_ev {t : ℕ} (ht : t ≤ n / L) :
    segSig (R := R) n L (ev t) = (ev (t * L) : Fin (n + 1) → R) := by
  unfold segSig; rw [linOfFun_ev _ (by omega)]

lemma segPi_segSig (hL : 0 < L) (w : Fin (n / L + 1) → R) :
    segPi n L d s (segSig n L w) = w := by
  have : (segPi n L d s).comp (segSig n L) = LinearMap.id := by
    apply ext_ev
    intro t ht
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply]
    rw [segSig_ev (by omega), segPi_ev (mul_le_of_le_div (by omega)), segCoef_mul hL, one_smul,
      Nat.mul_div_cancel _ hL]
  exact congrArg (fun f => f w) this

/-- The basic reduction: `e_j ≡ c_j e_{L⌊j/L⌋}` modulo the unit links. -/
lemma ev_sub_mem (hs : ∀ i < n, (i + 1) % L ≠ 0 → IsUnit (s i))
    (N : Submodule R (Fin (n + 1) → R))
    (hN : ∀ i < n, (i + 1) % L ≠ 0 → chainCol n d s i ∈ N) :
    ∀ j ≤ n, (ev j : Fin (n + 1) → R) - segCoef L d s j • ev (j / L * L) ∈ N := by
  intro j
  induction j with
  | zero => intro _; simp [segCoef]
  | succ j ih =>
    intro hj
    by_cases hmod : (j + 1) % L = 0
    · have h1 : (j + 1) / L * L = j + 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
      rw [h1, segCoef, if_pos hmod, one_smul, sub_self]; exact N.zero_mem
    · have hdiv : (j + 1) / L = j / L :=
        Nat.succ_div_of_not_dvd (fun h => hmod (Nat.mod_eq_zero_of_dvd h))
      have hu := hs j (by omega) hmod
      have hc := hN j (by omega) hmod
      have hih := ih (by omega)
      have h1 : Ring.inverse (s j) * s j = 1 := Ring.inverse_mul_cancel _ hu
      have key : (ev (j + 1) : Fin (n + 1) → R) - segCoef L d s (j + 1) • ev ((j + 1) / L * L) =
          Ring.inverse (s j) • chainCol n d s j - (Ring.inverse (s j) * d j) •
            ((ev j : Fin (n + 1) → R) - segCoef L d s j • ev (j / L * L)) := by
        rw [hdiv, segCoef, if_neg hmod, chainCol]
        linear_combination (norm := module) (-h1) • (ev (j + 1) : Fin (n + 1) → R)
      rw [key]
      exact N.sub_mem (N.smul_mem _ hc) (N.smul_mem _ hih)

lemma nat_of_mod_eq_zero {i : ℕ} (h : (i + 1) % L = 0) :
    (i + 1) / L = i / L + 1 ∧ i / L * L + L - 1 = i := by
  have h1 : (i + 1) / L = i / L + 1 := Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero h)
  refine ⟨h1, ?_⟩
  have h2 : (i + 1) / L * L = i + 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
  rw [h1, Nat.add_mul, one_mul] at h2
  omega

lemma segPi_chainCol (hL : 0 < L) (hs : ∀ i < n, (i + 1) % L ≠ 0 → IsUnit (s i)) {i : ℕ}
    (hi : i ≤ n) : segPi n L d s (chainCol n d s i) =
      if i < n ∧ (i + 1) % L ≠ 0 then 0 else chainCol (n / L) (segD n L d s) (segS L s) (i / L) := by
  rw [chainCol, map_add, map_smul, map_smul, segPi_ev hi]
  split_ifs with h
  · obtain ⟨hin, hmod⟩ := h
    have hdiv : (i + 1) / L = i / L :=
      Nat.succ_div_of_not_dvd (fun h => hmod (Nat.mod_eq_zero_of_dvd h))
    rw [segPi_ev (by omega), hdiv, segCoef, if_neg hmod]
    have h1 : Ring.inverse (s i) * s i = 1 := Ring.inverse_mul_cancel _ (hs i hin hmod)
    linear_combination (norm := module)
      (-(segCoef L d s i * d i) * h1) • (ev (i / L) : Fin (n / L + 1) → R)
  · rw [chainCol, segD, segS]
    by_cases hin : i < n
    · have hmod : (i + 1) % L = 0 := by tauto
      obtain ⟨h1, h2⟩ := nat_of_mod_eq_zero hmod
      rw [segPi_ev (by omega), h1, segCoef, if_pos hmod, h2, min_eq_left (by omega)]
      simp [smul_smul]
    · have hin' : i = n := by omega
      subst hin'
      have hlt : i < i / L * L + L := Nat.lt_div_mul_add hL
      rw [ev_eq_zero (show i + 1 ≤ i + 1 from le_rfl), map_zero, smul_zero, add_zero,
        ev_eq_zero (m := i / L + 1) (show i / L + 1 ≤ i / L + 1 from le_rfl), smul_zero, add_zero,
        min_eq_right (by omega), smul_smul]

lemma exists_chainCol_eq (hL : 0 < L) {t : ℕ} (ht : t ≤ n / L) :
    ∃ i ≤ n, ¬(i < n ∧ (i + 1) % L ≠ 0) ∧ i / L = t := by
  by_cases h : t * L + L - 1 < n
  · refine ⟨t * L + L - 1, by omega, ?_, ?_⟩
    · intro ⟨_, h2⟩; apply h2
      rw [show t * L + L - 1 + 1 = (t + 1) * L by rw [Nat.add_mul]; omega]; simp
    · rw [show t * L + L - 1 = (L - 1) + L * t by rw [mul_comm]; omega, Nat.add_mul_div_left _ _ hL,
        Nat.div_eq_of_lt (by omega)]; simp
  · refine ⟨n, le_rfl, by omega, ?_⟩
    have h1 : n / L * L ≤ n := Nat.div_mul_le_self n L
    have h2 : n / L < t + 1 := by
      by_contra h3
      have : (t + 1) * L ≤ n / L * L := Nat.mul_le_mul_right L (by omega)
      rw [Nat.add_mul] at this; omega
    omega

lemma segSig_segPi_sub_mem (hs : ∀ i < n, (i + 1) % L ≠ 0 → IsUnit (s i))
    (N : Submodule R (Fin (n + 1) → R))
    (hN : ∀ i < n, (i + 1) % L ≠ 0 → chainCol n d s i ∈ N) (v : Fin (n + 1) → R) :
    v - segSig n L (segPi n L d s v) ∈ N := by
  have := mem_of_forall_ev (LinearMap.id - (segSig n L).comp (segPi n L d s)) N ?_ v
  · simpa using this
  intro j hj
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp, Function.comp_apply]
  rw [segPi_ev (by omega), map_smul, segSig_ev (Nat.div_le_div_right (by omega))]
  exact ev_sub_mem hs _ hN j (by omega)

lemma not_within_iff {j : ℕ} (hL : 0 < L) (hj : j ≤ n) (hw : ¬(j < n ∧ (j + 1) % L ≠ 0)) :
    j = n ↔ j / L = n / L := by
  constructor
  · rintro rfl; rfl
  · intro h
    by_contra hne
    have hmod : (j + 1) % L = 0 := by omega
    obtain ⟨h1, _⟩ := nat_of_mod_eq_zero hmod
    have h3 : (j + 1) / L ≤ n / L := Nat.div_le_div_right (by omega)
    omega

/-- **Segment reduction.**  Contracting all unit links of a lower bidiagonal chain:
the cokernel of the chain on `R^{n+1}` is the cokernel of the reduced chain on `R^{⌊n/L⌋+1}`. -/
noncomputable def segRedEquiv (hL : 0 < L) (hs : ∀ i < n, (i + 1) % L ≠ 0 → IsUnit (s i)) :
    ((Fin (n + 1) → R) ⧸ chainRel n d s) ≃ₗ[R]
      ((Fin (n / L + 1) → R) ⧸ chainRel (n / L) (segD n L d s) (segS L s)) := by
  refine quotEquivOfSection _ _ (segPi n L d s) (segSig n L) (segPi_segSig hL) ?_ ?_
  · exact segSig_segPi_sub_mem hs _ (fun i hi _ => chainCol_mem (by omega))
  · rw [chainRel, map_span_range]
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      simp only [Function.comp_apply]
      rw [segPi_chainCol hL hs (by omega)]
      split_ifs
      · exact zero_mem _
      · exact subset_span ⟨⟨(i : ℕ) / L, by
          have := Nat.div_le_div_right (c := L) (show (i : ℕ) ≤ n by omega); omega⟩, rfl⟩
    · rw [chainRel, span_le]
      rintro _ ⟨t, rfl⟩
      obtain ⟨i, hi, hni, hit⟩ := exists_chainCol_eq hL (show (t : ℕ) ≤ n / L by omega)
      refine subset_span ⟨⟨i, by omega⟩, ?_⟩
      simp only [Function.comp_apply]
      rw [segPi_chainCol hL hs hi, if_neg hni, hit]

end lemmas

end ColouredSand.Blocks
