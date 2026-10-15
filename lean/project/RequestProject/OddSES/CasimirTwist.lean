module

public import RequestProject.OddSES.CasimirPsi

/-!
# `CSI4_the_short_exact_sequences.md`: Part C, (C3) — the Casimir on `Φ_p(N)` is `≡ 0` mod `p`

Encodings: `twist p N` is CSI1's `Φ_p(N)` (basis `Fin p × N.ι`, `bv p j n = b_j n`), whose single
operators are given by CSI1's `B1`. "`Ω = p • R` for some endomorphism `R`" is
`∃ R, casimir (twist p N) = (p : ℤ_[p]) • R`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

/-- (C3) `Ω(b_j n) ≡ 0` modulo `p`: on `b_j n` (`j ≥ 1`),
`4j(pw + p − j) + (pw + p − 2j)² = (pw + p)²`, and `E(b_0 n) = −p·b_{p−1}(En)`. -/
lemma modP_casimir_twist_bv {j : ℕ} (hj : j < p) {w : ℤ} {n : N.ι → ℤ_[p]}
    (hn : InWt N.wt w n) : ModP p (casimir (twist p N) (bv p j n)) 0 := by
  have hH : H (twist p N) (bv p j n) = ((p * w + p - 1 - 2 * j : ℤ) : ℤ_[p]) • bv p j n :=
    (B1 p N).2.2.2.2 j w n hn
  rw [casimir_apply, hH, map_smul, hH]
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · rw [(B1 p N).2.2.2.1 n, map_smul, show (twist p N).Fd 1 = twFd p N 1 from rfl]
    refine ⟨(-4 : ℤ_[p]) • twFd p N 1 (bv p (p - 1) (N.Ed 1 n)) +
      ((p : ℤ_[p]) * ((w : ℤ_[p]) + 1) ^ 2) • bv p 0 n, ?_⟩
    push_cast; module
  · rw [(B1 p N).2.2.1 j w _ h1 hj hn, (B1 p N).1 (j - 1) _ (by omega), Nat.sub_add_cancel h1]
    refine ⟨((4 : ℤ_[p]) * p) • bv p j (N.Fd 1 (N.Ed 1 n)) +
      ((p : ℤ_[p]) * ((w : ℤ_[p]) + 1) ^ 2) • bv p j n, ?_⟩
    simp only [map_add, map_smul]
    push_cast; module

/-- (C3) **The Casimir on `Φ_p(N)`.** On `twist p N`, `Ω = p • R` for some endomorphism `R`. -/
theorem C3 : ∃ R, casimir (twist p N) = (p : ℤ_[p]) • R :=
  exists_eq_p_smul _ fun x => by
    obtain ⟨j, i⟩ := x
    change casimir (twist p N) (Pi.single (j, i) 1) ∈ _
    rw [single_eq_bv]
    exact (modP_casimir_twist_bv j.isLt (inWt_single N.wt i)).mem_pSub

end ColouredSand.OddTwist
