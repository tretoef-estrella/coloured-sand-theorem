module

public import RequestProject.Divisors.Basic

/-!
# Lemma A1 of `C5_divisors_theorem_65.md` (invariance of `dd_r`)

Encodings as in `RequestProject/Divisors/Basic.lean`: `minor M r A B = det M[A, B]` and
`dd M r = dd_r(M)`.  The proof is the one of the file: by Cauchy–Binet (`minor_mul`, proved in
`CauchyBinet.lean` since Mathlib does not have it) every `r × r` minor of `P M Q` is an integer
combination of `r × r` minors of `M`; then `adj(P) (P M Q) adj(Q) = (det P)(det Q) M` and
multiplication by an odd integer does not change `dd_r`.
-/

@[expose] public section

namespace Divisors

open Finset Matrix

/-- Every `r × r` minor of `P M Q` is an integer combination of `r × r` minors of `M`; in
particular a common divisor of the `r × r` minors of `M` divides those of `P M Q`. (Proof of
Lemma A1 of `C5_divisors_theorem_65.md`.) -/
theorem dvd_minor_mul_mul {n : ℕ} (P M Q : Matrix (Fin n) (Fin n) ℤ) {r : ℕ} {d : ℤ}
    (hd : ∀ A B : Finset (Fin n), A.card = r → B.card = r → d ∣ minor M r A B)
    (I J : Finset (Fin n)) : d ∣ minor (P * M * Q) r I J := by
  by_cases h : I.card = r ∧ J.card = r
  · rw [minor_mul _ _ h.1 h.2]
    refine dvd_sum fun S _ => Dvd.dvd.mul_right ?_ _
    rw [minor_mul _ _ h.1 S.2]
    exact dvd_sum fun T _ => Dvd.dvd.mul_left (hd _ _ T.2 S.2) _
  · rw [minor_of_not_card _ h]; exact dvd_zero _

/-- If `P M Q` has a non-zero `r × r` minor, so does `M`. (Proof of Lemma A1 of
`C5_divisors_theorem_65.md`.) -/
theorem minorVals_nonempty_of_mul {n : ℕ} (P M Q : Matrix (Fin n) (Fin n) ℤ) {r : ℕ}
    (h : (minorVals (P * M * Q) r).Nonempty) : (minorVals M r).Nonempty := by
  obtain ⟨_, I, J, _, _, h0, _⟩ := h
  by_contra hne
  apply h0
  refine zero_dvd_iff.1 (dvd_minor_mul_mul P M Q (fun A B hA hB => ?_) I J)
  by_contra hm
  exact hne ⟨_, A, B, hA, hB, by rwa [zero_dvd_iff] at hm, rfl⟩

/-- `dd_r(M) ≤ dd_r(P M Q)` as soon as `P M Q` has a non-zero `r × r` minor. (Proof of
Lemma A1 of `C5_divisors_theorem_65.md`.) -/
theorem dd_le_dd_mul {n : ℕ} (P M Q : Matrix (Fin n) (Fin n) ℤ) {r : ℕ}
    (h : (minorVals (P * M * Q) r).Nonempty) : dd M r ≤ dd (P * M * Q) r :=
  le_dd_of_dvd h fun A B _ _ =>
    dvd_minor_mul_mul P M Q (fun A B _ _ => pow_dd_dvd_minor M r A B) A B

/-- `adj(P) (P M Q) adj(Q) = (det P)(det Q) M`. (Proof of Lemma A1 of
`C5_divisors_theorem_65.md`.) -/
theorem adjugate_mul_mul_adjugate {n : ℕ} (P M Q : Matrix (Fin n) (Fin n) ℤ) :
    adjugate P * (P * M * Q) * adjugate Q = (det P * det Q) • M := by
  calc adjugate P * (P * M * Q) * adjugate Q = (adjugate P * P) * M * (Q * adjugate Q) := by
        simp only [Matrix.mul_assoc]
    _ = (det P * det Q) • M := by
        rw [adjugate_mul, mul_adjugate, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
          Matrix.mul_one, smul_smul, mul_comm]

/-- **Lemma A1** (invariance) of `C5_divisors_theorem_65.md`: if `P`, `Q` are `n × n` integer
matrices with `det P` and `det Q` odd, then `dd_r(P M Q) = dd_r(M)` for every `0 ≤ r ≤ n`.

More general than stated in the file: the hypothesis `det M ≠ 0` of the setting is not needed,
and the identity holds for every `r` (for `r > n` both sides are `0`). -/
theorem lemma_A1 {n : ℕ} (M P Q : Matrix (Fin n) (Fin n) ℤ) (hP : Odd (det P))
    (hQ : Odd (det Q)) (r : ℕ) : dd (P * M * Q) r = dd M r := by
  have hc : Odd (det P * det Q) := hP.mul hQ
  have hY := adjugate_mul_mul_adjugate P M Q
  by_cases h : (minorVals (P * M * Q) r).Nonempty
  · have h1 := dd_le_dd_mul P M Q h
    have hM := minorVals_nonempty_of_mul P M Q h
    have hcM : (minorVals (adjugate P * (P * M * Q) * adjugate Q) r).Nonempty := by
      rwa [hY, minorVals_smul_odd hc]
    have h2 := dd_le_dd_mul (adjugate P) (P * M * Q) (adjugate Q) hcM
    rw [hY, dd_smul_odd hc] at h2
    omega
  · have hM : ¬ (minorVals M r).Nonempty := by
      intro hM
      apply h
      apply minorVals_nonempty_of_mul (adjugate P) _ (adjugate Q)
      rwa [hY, minorVals_smul_odd hc]
    rw [Set.not_nonempty_iff_eq_empty] at h hM
    rw [dd, dd, h, hM]

end Divisors
