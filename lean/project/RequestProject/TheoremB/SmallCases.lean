module

public import RequestProject.TheoremB.TheoremB

/-!
# (B4) The small cases `d = 2, 3, 4`

This file corresponds to **(B4) The small cases, as checks** of `CS3_theorem_B.md`.

* `nCount_two`, `nCount_three`, `nCount_four`: the values of `n_v` (`nCount d q v`, see
  `RequestProject/TheoremB/Count.lean`) for `d = 2, 3, 4`, with `u = q − 2`, computed from the
  formula of (B3).  They hold for every `q` (with `u = q − 2` the truncated subtraction on `ℕ`).
* `theorem_B_two`, `theorem_B_three`, `theorem_B_four`: the resulting explicit forms of Theorem B.
  The direct sum `⨁_{v=1}^{d} (ℤ/p^{ev})^{n_v}` is written as the product over `v : Fin d`
  (standing for `v + 1`) of `Fin (n_{v+1}) → ZMod (p ^ (e * (v + 1)))`, the multiplicities being
  given by the vector `![n_1, …, n_d]`.
-/

@[expose] public section

open Finset

namespace ColouredSand.TheoremB

/-- **(B4), `d = 2`**: `n_1 = u² + 1`, `n_2 = 2u`, with `u = q − 2`. -/
theorem nCount_two (q : ℕ) :
    nCount 2 q 1 = (q - 2) ^ 2 + 1 ∧ nCount 2 q 2 = 2 * (q - 2) := by
  refine ⟨?_, ?_⟩ <;>
  simp [nCount, Finset.sum_range_succ, ballot, Nat.choose]
  ring

/-- **(B4), `d = 3`**: `n_1 = u³ + 3u`, `n_2 = 3u² + 2`, `n_3 = 3u`, with `u = q − 2`. -/
theorem nCount_three (q : ℕ) :
    nCount 3 q 1 = (q - 2) ^ 3 + 3 * (q - 2) ∧ nCount 3 q 2 = 3 * (q - 2) ^ 2 + 2 ∧
      nCount 3 q 3 = 3 * (q - 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [nCount, Finset.sum_range_succ, ballot, Nat.choose] <;> ring

/-- **(B4), `d = 4`**: `n_1 = u⁴ + 6u² + 2`, `n_2 = 4u³ + 8u`, `n_3 = 6u² + 3`, `n_4 = 4u`, with
`u = q − 2`. -/
theorem nCount_four (q : ℕ) :
    nCount 4 q 1 = (q - 2) ^ 4 + 6 * (q - 2) ^ 2 + 2 ∧
      nCount 4 q 2 = 4 * (q - 2) ^ 3 + 8 * (q - 2) ∧
      nCount 4 q 3 = 6 * (q - 2) ^ 2 + 3 ∧ nCount 4 q 4 = 4 * (q - 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp [nCount, Finset.sum_range_succ, ballot, Nat.choose] <;> ring

/-- Regrouping the direct sum of Theorem B by `v`, with prescribed multiplicities `n'`. -/
lemma theorem_B_regroup {d q p : ℕ} [Fact p.Prime] (hd : 1 ≤ d) (hpd : d < p) (hpq : p ∣ q)
    (hq : 2 ≤ q) (n' : Fin d → ℕ) (hn : ∀ v : Fin d, nCount d q (v + 1) = n' v) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((v : Fin d) → Fin (n' v) → ZMod (p ^ (padicValNat p q * (v + 1))))) := by
  obtain ⟨E⟩ := theorem_B d q p hd hpd hpq hq
  let E1 := (LinearEquiv.piCurry ℤ
    (fun (v : Fin d) (_ : Fin (nCount d q (v + 1))) =>
      ZMod (p ^ (padicValNat p q * (v + 1))))).toAddEquiv
  let E2 : ((v : Fin d) → Fin (nCount d q (v + 1)) → ZMod (p ^ (padicValNat p q * (v + 1)))) ≃+
      ((v : Fin d) → Fin (n' v) → ZMod (p ^ (padicValNat p q * (v + 1)))) :=
    AddEquiv.piCongrRight fun v =>
      (LinearEquiv.funCongrLeft ℤ (ZMod (p ^ (padicValNat p q * (v + 1))))
        (finCongr (hn v)).symm).toAddEquiv
  exact ⟨E.trans (E1.trans E2)⟩

/-- **(B4), `d = 2`, as an isomorphism**: for a prime `p > 2` dividing `q ≥ 2`, `e = v_p(q)`,
`u = q − 2`: `Syl_p K(H(2,q)) ≅ (ℤ/p^e)^{u²+1} ⊕ (ℤ/p^{2e})^{2u}`. -/
theorem theorem_B_two {q p : ℕ} [Fact p.Prime] (hpd : 2 < p) (hpq : p ∣ q) (hq : 2 ≤ q) :
    Nonempty (AddCommGroup.primaryComponent (sandpile 2 q) p ≃+
      ((v : Fin 2) → Fin (![(q - 2) ^ 2 + 1, 2 * (q - 2)] v) →
        ZMod (p ^ (padicValNat p q * (v + 1))))) :=
  theorem_B_regroup (by norm_num) hpd hpq hq _ fun v => by
    fin_cases v
    · exact (nCount_two q).1
    · exact (nCount_two q).2

/-- **(B4), `d = 3`, as an isomorphism**: for a prime `p > 3` dividing `q ≥ 2`, `e = v_p(q)`,
`u = q − 2`: `Syl_p K(H(3,q)) ≅ (ℤ/p^e)^{u³+3u} ⊕ (ℤ/p^{2e})^{3u²+2} ⊕ (ℤ/p^{3e})^{3u}`. -/
theorem theorem_B_three {q p : ℕ} [Fact p.Prime] (hpd : 3 < p) (hpq : p ∣ q) (hq : 2 ≤ q) :
    Nonempty (AddCommGroup.primaryComponent (sandpile 3 q) p ≃+
      ((v : Fin 3) → Fin (![(q - 2) ^ 3 + 3 * (q - 2), 3 * (q - 2) ^ 2 + 2, 3 * (q - 2)] v) →
        ZMod (p ^ (padicValNat p q * (v + 1))))) :=
  theorem_B_regroup (by norm_num) hpd hpq hq _ fun v => by
    fin_cases v
    · exact (nCount_three q).1
    · exact (nCount_three q).2.1
    · exact (nCount_three q).2.2

/-- **(B4), `d = 4`, as an isomorphism**: for a prime `p > 4` dividing `q ≥ 2`, `e = v_p(q)`,
`u = q − 2`: `Syl_p K(H(4,q)) ≅ (ℤ/p^e)^{u⁴+6u²+2} ⊕ (ℤ/p^{2e})^{4u³+8u} ⊕ (ℤ/p^{3e})^{6u²+3} ⊕
(ℤ/p^{4e})^{4u}`. -/
theorem theorem_B_four {q p : ℕ} [Fact p.Prime] (hpd : 4 < p) (hpq : p ∣ q) (hq : 2 ≤ q) :
    Nonempty (AddCommGroup.primaryComponent (sandpile 4 q) p ≃+
      ((v : Fin 4) → Fin (![(q - 2) ^ 4 + 6 * (q - 2) ^ 2 + 2, 4 * (q - 2) ^ 3 + 8 * (q - 2),
          6 * (q - 2) ^ 2 + 3, 4 * (q - 2)] v) →
        ZMod (p ^ (padicValNat p q * (v + 1))))) :=
  theorem_B_regroup (by norm_num) hpd hpq hq _ fun v => by
    fin_cases v
    · exact (nCount_four q).1
    · exact (nCount_four q).2.1
    · exact (nCount_four q).2.2.1
    · exact (nCount_four q).2.2.2

end ColouredSand.TheoremB
