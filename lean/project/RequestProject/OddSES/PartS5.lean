module

public import RequestProject.OddSES.PartS5b

/-!
# `CSI4_the_short_exact_sequences.md`: Part S, (S5) — the short exact sequences

`0 → Ψ_{r+1}(N) → V ⊗ Ψ_r(N) → Q_{r−1}(N) → 0`, as `WeylFilt.ShortExact` (C19: `f.toLin`
injective, `g.toLin` surjective, `range f.toLin = ker g.toLin`):

* `S5_one` — `r = 1`: `ShortExact (ι_2) (π_1)`, `ι_2 = iotaHom p N 1 _ _`, `π_1 = pi1Hom p N _ _`
  into `dsum (twist p N) (twist p N)`;
* `S5_mid` — `2 ≤ r ≤ p − 2` (`r = s + 1`): `ShortExact (ι_{r+1}) (π_r)`,
  `ι_{r+1} = iotaHom p N (s+1) _ _`, `π_r = piHom p N s _ _`;
* `S5_last` — `r = p − 1` (`r = s + 1`, `s + 2 = p`): `ShortExact (ι_p) (π_{p−1})`,
  `ι_p = iotaPHom p N (s+1) _ _ _` (Part P), `π_{p−1} = piHom p N s _ _`.

The hypothesis `3 ≤ p` is "`p` is an odd prime". The proof is the rank argument
`shortExact_of_rank`: `π ∘ ι = 0` (`pi_comp_iota`, `pi1_comp_iota`, `pi_comp_iotaL`), `ι` has a
left inverse (CSI3 `I6`, (P3)), `π` is surjective ((S4)), and
`rank Z_r = 4p·|N.ι| = rank Ψ_{r+1} + rank Q_{r−1}` (`card_psi`, ...).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

/-! ### Ranks -/

lemma card_psi (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    Fintype.card (psi p N r h1 h2).ι = 2 * (p * Fintype.card N.ι) := by
  rw [show Fintype.card (psi p N r h1 h2).ι = Fintype.card (Bool × Fin p × N.ι) from
    Fintype.card_congr (Equiv.refl _)]
  simp [Fintype.card_prod]

lemma card_tensorV (M : DPLattice ℤ_[p]) :
    Fintype.card (Tensor2.tensor (V ℤ_[p]) M).ι = 2 * Fintype.card M.ι := by
  rw [show Fintype.card (Tensor2.tensor (V ℤ_[p]) M).ι = Fintype.card (Fin 2 × M.ι) from
    Fintype.card_congr (Equiv.refl _)]
  simp [Fintype.card_prod]

lemma card_twist (M : DPLattice ℤ_[p]) :
    Fintype.card (twist p M).ι = p * Fintype.card M.ι := by
  rw [show Fintype.card (twist p M).ι = Fintype.card (Fin p × M.ι) from
    Fintype.card_congr (Equiv.refl _)]
  simp [Fintype.card_prod]

lemma card_dsum (X Y : DPLattice ℤ_[p]) :
    Fintype.card (Lemma35.dsum X Y).ι = Fintype.card X.ι + Fintype.card Y.ι := by
  rw [show Fintype.card (Lemma35.dsum X Y).ι = Fintype.card (X.ι ⊕ Y.ι) from
    Fintype.card_congr (Equiv.refl _)]
  simp

/-! ### The three short exact sequences -/

/-- (S5) **`r = 1`**: `0 → Ψ_2(N) → V ⊗ Ψ_1(N) → Φ_p(N) ⊕ Φ_p(N) → 0` is short exact, with
`ι_2 = iotaHom p N 1 _ _` (CSI3) and `π_1 = pi1Hom p N _ _` ((S3)); `3 ≤ p` (`p` odd). -/
theorem S5_one (hp3 : 3 ≤ p) (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) :
    WeylFilt.ShortExact (iotaHom p N 1 le_rfl hp3) (pi1Hom p N h1 h2) := by
  refine shortExact_of_rank _ _ _ (I6 p N 1 le_rfl hp3).2.2
    (S4_pi1 h1 h2 (by omega)) (pi1_comp_iota h1 h2 hp3) ?_
  rw [card_psi, card_dsum, card_twist, card_tensorV, card_psi]
  ring

/-- (S5) **`2 ≤ r ≤ p − 2`** (`r = s + 1`): `0 → Ψ_{r+1}(N) → V ⊗ Ψ_r(N) → Ψ_{r−1}(N) → 0` is
short exact, with `ι_{r+1} = iotaHom p N (s+1) _ _` (CSI3) and `π_r = piHom p N s _ _` ((S2)). -/
theorem S5_mid (s : ℕ) (hs1 : 1 ≤ s) (hsp3 : s + 3 ≤ p) :
    WeylFilt.ShortExact (iotaHom p N (s + 1) (by omega) hsp3) (piHom p N s hs1 (by omega)) := by
  refine shortExact_of_rank _ _ _ (I6 p N (s + 1) (by omega) hsp3).2.2
    (S4_pi s hs1 (by omega)) (pi_comp_iota s hs1 (by omega) hsp3) ?_
  rw [card_psi, card_psi, card_tensorV, card_psi]
  ring

/-- (S5) **`r = p − 1`** (`r = s + 1`, `s + 2 = p`): `0 → Ψ_p(N) → V ⊗ Ψ_{p−1}(N) → Ψ_{p−2}(N) → 0`
is short exact, with `Ψ_p(N) = Φ_p(V ⊗ N)` (`Psip`), `ι_p = iotaPHom p N (s+1) _ _ _` ((P2), (P3))
and `π_{p−1} = piHom p N s _ _` ((S2)). -/
theorem S5_last (s : ℕ) (hs1 : 1 ≤ s) (hsp : s + 2 = p) :
    WeylFilt.ShortExact (iotaPHom p N (s + 1) (by omega) (by omega) (by omega))
      (piHom p N s hs1 (by omega)) := by
  refine shortExact_of_rank _ _ _ (P3 (N := N) (s + 1) (by omega) (by omega) (by omega)).2.2.1
    (S4_pi s hs1 (by omega)) ?_ ?_
  · rw [(P3 (N := N) (s + 1) (by omega) (by omega) (by omega)).1, iotaP, ← LinearMap.comp_assoc,
      pi_comp_iotaL s hs1 (by omega), LinearMap.zero_comp]
  · rw [Psip, card_twist, card_tensorV, card_psi, card_tensorV, card_psi]
    ring

end ColouredSand.OddTwist
