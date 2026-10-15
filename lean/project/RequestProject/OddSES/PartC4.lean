module

public import RequestProject.OddSES.PartS5
public import RequestProject.OddSES.CasimirPsi
public import RequestProject.OddSES.CasimirTwist

/-!
# `CSI4_the_short_exact_sequences.md`: Part C, (C4) — the ambient

On `Z_r = tensor V (psi p N r _ _)`, `1 ≤ r ≤ p − 1`:
`(Ω − (r+1)²)² ∘ (Ω − (r−1)²)² = p • R` for some endomorphism `R` (`C4`), where
`Dcas M c = Ω_M − c • id` (`CasimirPsi.lean`).

Proof, from (C2), (C3) and Part S: for a short exact sequence `0 → X → Y → Z → 0` of
DP-lattices, if `(Ω − a)² = p • R` on `X` and `(Ω − b)² = p • R'` on `Z`, then
`(Ω − a)² ∘ (Ω − b)² = p • R''` on `Y` (`ses_casimir`), since morphisms commute with `Ω` ((C1)).
The three cases are the sequences of (S5); for `r = 1` the quotient is
`dsum (twist p N) (twist p N)`, on which `Ω = p • R` by (C3) (`casimir_dsum_twist`), and for
`r = p − 1` the subobject is `twist p (tensor V N)`, on which `Ω = p • R` by (C3).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

variable {p : ℕ} [Fact p.Prime]

/-- Morphisms commute with `Ω − c`. -/
lemma Dcas_hom {X Y : DPLattice ℤ_[p]} (f : Hom X Y) (c : ℤ_[p]) (x : X.ι → ℤ_[p]) :
    f.toLin (Dcas X c x) = Dcas Y c (f.toLin x) := by
  have h := LinearMap.congr_fun (casimir_hom f) x
  simp only [LinearMap.comp_apply] at h
  simp only [Dcas, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
    map_smul, h]

/-- (C4) **Casimir classes along a short exact sequence.** -/
theorem ses_casimir {X Y Z : DPLattice ℤ_[p]} {f : Hom X Y} {g : Hom Y Z}
    (hse : WeylFilt.ShortExact f g) (a b : ℤ_[p])
    (hX : ∃ R, Dcas X a ∘ₗ Dcas X a = (p : ℤ_[p]) • R)
    (hZ : ∃ R, Dcas Z b ∘ₗ Dcas Z b = (p : ℤ_[p]) • R) :
    ∃ R, (Dcas Y a ∘ₗ Dcas Y a) ∘ₗ (Dcas Y b ∘ₗ Dcas Y b) = (p : ℤ_[p]) • R := by
  obtain ⟨RX, hRX⟩ := hX
  obtain ⟨RZ, hRZ⟩ := hZ
  refine exists_eq_p_smul _ fun i => ?_
  set y : Y.ι → ℤ_[p] := Pi.single i 1
  obtain ⟨y', hy'⟩ := hse.surj (RZ (g.toLin y))
  have hker : Dcas Y b (Dcas Y b y) - (p : ℤ_[p]) • y' ∈ LinearMap.ker g.toLin := by
    rw [LinearMap.mem_ker, map_sub, map_smul, Dcas_hom g, Dcas_hom g, hy']
    have := LinearMap.congr_fun hRZ (g.toLin y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
    rw [this, sub_self]
  rw [← hse.exact] at hker
  obtain ⟨x, hx⟩ := hker
  have hy : Dcas Y b (Dcas Y b y) = f.toLin x + (p : ℤ_[p]) • y' := by
    rw [hx, sub_add_cancel]
  simp only [LinearMap.comp_apply]
  rw [hy, map_add, map_add, ← Dcas_hom, ← Dcas_hom, map_smul, map_smul]
  have := LinearMap.congr_fun hRX x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at this
  rw [this, map_smul, ← smul_add]
  exact p_smul_mem_pSub _

/-- If `Ω = p • R` then `(Ω − p²)² = p • R'`. -/
lemma Dcas_sq_of_casimir {X : DPLattice ℤ_[p]} (h : ∃ R, casimir X = (p : ℤ_[p]) • R) :
    ∃ R, Dcas X ((p : ℤ_[p]) ^ 2) ∘ₗ Dcas X ((p : ℤ_[p]) ^ 2) = (p : ℤ_[p]) • R := by
  obtain ⟨R, hR⟩ := h
  have hD : Dcas X ((p : ℤ_[p]) ^ 2) = (p : ℤ_[p]) • (R - (p : ℤ_[p]) • LinearMap.id) := by
    rw [Dcas, hR, smul_sub, smul_smul, sq]
  refine ⟨(R - (p : ℤ_[p]) • LinearMap.id) ∘ₗ Dcas X ((p : ℤ_[p]) ^ 2), ?_⟩
  rw [hD, LinearMap.smul_comp]

/-- (C3) on `dsum (twist p N) (twist p N)`: `Ω = p • R`. -/
lemma casimir_dsum_twist (N : DPLattice ℤ_[p]) :
    ∃ R, casimir (Lemma35.dsum (twist p N) (twist p N)) = (p : ℤ_[p]) • R := by
  obtain ⟨R, hR⟩ := C3 (p := p) (N := N)
  refine exists_eq_p_smul _ fun k => ?_
  have hsplit : ∀ z : (Lemma35.dsum (twist p N) (twist p N)).ι → ℤ_[p],
      z = (Lemma35.inlHom (M := twist p N) (N := twist p N)).toLin (z ∘ Sum.inl) +
        (Lemma35.inrHom (M := twist p N) (N := twist p N)).toLin (z ∘ Sum.inr) := by
    intro z; funext x
    cases x with
    | inl v => exact (add_zero _).symm
    | inr v => exact (zero_add _).symm
  rw [hsplit (Pi.single k 1), map_add]
  have h1 := LinearMap.congr_fun (casimir_hom (Lemma35.inlHom (M := twist p N)
    (N := twist p N))) ((Pi.single k 1 : (Lemma35.dsum (twist p N) (twist p N)).ι → ℤ_[p]) ∘
      Sum.inl)
  have h2 := LinearMap.congr_fun (casimir_hom (Lemma35.inrHom (M := twist p N)
    (N := twist p N))) ((Pi.single k 1 : (Lemma35.dsum (twist p N) (twist p N)).ι → ℤ_[p]) ∘
      Sum.inr)
  simp only [LinearMap.comp_apply] at h1 h2
  rw [← h1, ← h2, hR, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, ← smul_add]
  exact p_smul_mem_pSub _

lemma Dcas_zero (X : DPLattice ℤ_[p]) : Dcas X 0 = casimir X := by
  rw [Dcas, zero_smul, sub_zero]

variable {N : DPLattice ℤ_[p]}

/-- (C4) **The ambient.** For `p` an odd prime (`3 ≤ p`) and `1 ≤ r ≤ p − 1`, on
`tensor V (psi p N r _ _)`: `(Ω − (r+1)²)² ∘ (Ω − (r−1)²)² = p • R` for some endomorphism `R`. -/
theorem C4 (hp3 : 3 ≤ p) (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    ∃ R, (Dcas (Tensor2.tensor (V ℤ_[p]) (psi p N r h1 h2)) (((r : ℤ_[p]) + 1) ^ 2) ∘ₗ
        Dcas (Tensor2.tensor (V ℤ_[p]) (psi p N r h1 h2)) (((r : ℤ_[p]) + 1) ^ 2)) ∘ₗ
      (Dcas (Tensor2.tensor (V ℤ_[p]) (psi p N r h1 h2)) (((r : ℤ_[p]) - 1) ^ 2) ∘ₗ
        Dcas (Tensor2.tensor (V ℤ_[p]) (psi p N r h1 h2)) (((r : ℤ_[p]) - 1) ^ 2)) =
      (p : ℤ_[p]) • R := by
  rcases Nat.lt_or_ge r 2 with hr | hr
  · -- r = 1
    obtain rfl : r = 1 := by omega
    refine ses_casimir (S5_one hp3 h1 h2) _ _ ?_ ?_
    · have := (C2 (N := N) 2 (by omega) (by omega)).2.2
      simpa [one_add_one_eq_two] using this
    · obtain ⟨R, hR⟩ := casimir_dsum_twist (p := p) N
      refine ⟨R ∘ₗ casimir _, ?_⟩
      simp only [Nat.cast_one, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Dcas_zero, hR, LinearMap.smul_comp]
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rcases Nat.lt_or_ge (s + 2) p with hsp | hsp
    · -- 2 ≤ r ≤ p − 2
      refine ses_casimir (S5_mid s (by omega) (by omega)) _ _ ?_ ?_
      · have := (C2 (N := N) (s + 2) (by omega) (by omega)).2.2
        simpa [add_assoc, one_add_one_eq_two] using this
      · have := (C2 (N := N) s (by omega) (by omega)).2.2
        simpa using this
    · -- r = p − 1
      refine ses_casimir (S5_last s (by omega) (by omega)) _ _ ?_ ?_
      · have := Dcas_sq_of_casimir (C3 (p := p) (N := Tensor2.tensor (V ℤ_[p]) N))
        have hc : ((s + 1 : ℕ) : ℤ_[p]) + 1 = (p : ℤ_[p]) := by
          have hp' : (p : ℤ_[p]) = ((s + 1 + 1 : ℕ) : ℤ_[p]) := by
            congr 1; omega
          rw [hp']; push_cast; ring
        rw [hc]
        exact this
      · have := (C2 (N := N) s (by omega) (by omega)).2.2
        simpa using this

end ColouredSand.OddTwist
