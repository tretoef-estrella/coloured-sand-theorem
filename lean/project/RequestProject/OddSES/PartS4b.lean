module

public import RequestProject.OddSES.PartS4

/-!
# `CSI4_the_short_exact_sequences.md`: Part S, (S4) — `π_1` is surjective (`p ≠ 2`)

A vector of `dsum (twist p N) (twist p N)` is `Sum.elim (first) (second)`. With
`n = δ_i`, `b_j n = bv p j n` (CSI1) and `κ` of CSI3 (B1) (`kappa_aV`, `kappa_cV`):

* `π_1(b̂_1 ⊗ C_{k−1} n) = (0, −2 b_k n)` for `k ≥ 1`;
* `π_1(b̂_0 ⊗ C_0 n) + π_1(b̂_1 ⊗ A_0 n) = (0, −2H b_0 n) ≡ (0, 2 b_0 n)` modulo `p`;
* `π_1(b̂_0 ⊗ C_j n) = (b_j n, −H b_j n)`;

and `2` is a unit since `p ≠ 2`; Nakayama (`surj_of_modP`) concludes.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

section elim

variable {A : Type*} [CommRing A] {ι κ : Type*}

lemma elim_add (a b : ι → A) (c d : κ → A) :
    Sum.elim a c + Sum.elim b d = Sum.elim (a + b) (c + d) := by
  funext x; cases x <;> rfl

lemma elim_smul (t : A) (a : ι → A) (c : κ → A) :
    t • Sum.elim a c = Sum.elim (t • a) (t • c) := by
  funext x; cases x <;> rfl

lemma elim_neg (a : ι → A) (c : κ → A) : -Sum.elim a c = Sum.elim (-a) (-c) := by
  funext x; cases x <;> rfl

lemma single_inl_eq [DecidableEq ι] [DecidableEq κ] (k : ι) :
    (Pi.single (Sum.inl k) 1 : ι ⊕ κ → A) = Sum.elim (Pi.single k 1) (0 : κ → A) := by
  funext x; cases x <;> simp [Pi.single_apply]

lemma single_inr_eq [DecidableEq ι] [DecidableEq κ] (k : κ) :
    (Pi.single (Sum.inr k) 1 : ι ⊕ κ → A) = Sum.elim (0 : ι → A) (Pi.single k 1) := by
  funext x; cases x <;> simp [Pi.single_apply]

end elim

variable (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1)

lemma isUnit_two_padic (hp2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by
  have := isUnit_natCast_of_not_dvd p (n := 2) fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 hd)
  simpa using this

/-- (S4) **`π_1` is surjective** (for `p` an odd prime). -/
theorem S4_pi1 (hp2 : p ≠ 2) : Function.Surjective (pi1Hom p N h1 h2).toLin := by
  apply surj_of_modP
  have hu2 := isUnit_two_padic hp2
  have hpos := (Fact.out : p.Prime).pos
  -- the three computations
  have hC : ∀ j : ℕ, j < p → ∀ n : N.ι → ℤ_[p],
      (pi1Hom p N h1 h2).toLin (tv 0 (cV p j n)) = Sum.elim (bv p j n)
        ((2 : ℤ_[p]) • (twist p N).Ed 1 0 - H (twist p N) (bv p j n)) ∧
      (pi1Hom p N h1 h2).toLin (tv 1 (cV p j n)) = Sum.elim (-0)
        (-H (twist p N) 0 - (2 : ℤ_[p]) • (twist p N).Fd 1 (bv p j n)) := by
    intro j hj n
    exact S3 p N h1 h2 (cV p j n) 0 (bv p j n) (by rw [kappa_cV hj, map_zero, zero_add]; rfl)
  have hA0 : ∀ n : N.ι → ℤ_[p],
      (pi1Hom p N h1 h2).toLin (tv 1 (aV p 0 n)) = Sum.elim (-bv p 0 n)
        (-H (twist p N) (bv p 0 n) - (2 : ℤ_[p]) • (twist p N).Fd 1 0) := by
    intro n
    exact (S3 p N h1 h2 (aV p 0 n) (bv p 0 n) 0 (by
      rw [kappa_aV hpos, Nat.cast_zero, zero_smul, map_zero, add_zero]
      exact (add_zero _).symm)).2
  rintro (⟨j, i⟩ | ⟨j, i⟩)
  all_goals
    have hn := inWt_single (A := ℤ_[p]) N.wt i
    have HB : ∀ j : ℕ, H (twist p N) (bv p j (Pi.single i 1)) =
        ((p * N.wt i + p - 1 - 2 * j : ℤ) : ℤ_[p]) • bv p j (Pi.single i 1) :=
      fun j => (B1 p N).2.2.2.2 j _ _ hn
    have hinr : ∀ j : ℕ, j < p → Sum.elim (0 : Fin p × N.ι → ℤ_[p]) (bv p j (Pi.single i 1)) ∈
        LinearMap.range (pi1Hom p N h1 h2).toLin ⊔
          pSub p ((Lemma35.dsum (twist p N) (twist p N)).ι → ℤ_[p]) := by
      intro j hj
      rcases j with _ | k
      · have hm : ModP p ((pi1Hom p N h1 h2).toLin
            (tv (ι := (psi p N 1 h1 h2).ι) 0 (cV p 0 (Pi.single i 1)) +
              tv (ι := (psi p N 1 h1 h2).ι) 1 (aV p 0 (Pi.single i 1))))
            ((2 : ℤ_[p]) • Sum.elim (0 : Fin p × N.ι → ℤ_[p]) (bv p 0 (Pi.single i 1))) := by
          rw [map_add, (hC 0 hpos _).1, hA0, HB]
          refine ⟨Sum.elim 0 (((-2 : ℤ_[p]) * ((N.wt i : ℤ_[p]) + 1)) •
            bv p 0 (Pi.single i 1)), ?_⟩
          funext x
          cases x with
          | inl x => simp
          | inr x =>
            simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Sum.elim_inr, map_zero,
              smul_zero, smul_eq_mul, Pi.neg_apply, Pi.zero_apply]
            push_cast; ring
        exact mem_of_unit_smul_mem hu2 (mem_range_sup_of_modP _ _ hm)
      · have he : (pi1Hom p N h1 h2).toLin (tv 1 (cV p k (Pi.single i 1))) =
            (-2 : ℤ_[p]) • Sum.elim (0 : Fin p × N.ι → ℤ_[p]) (bv p (k + 1) (Pi.single i 1)) := by
          rw [(hC k (by omega) _).2, (B1 p N).1 k _ hj, elim_smul]
          congr 1
          · simp
          · simp [neg_smul]
        refine mem_of_unit_smul_mem hu2.neg ?_
        rw [← he]
        exact Submodule.mem_sup_left ⟨_, rfl⟩
  · rw [single_inl_eq, single_eq_bv]
    have he : (pi1Hom p N h1 h2).toLin (tv 0 (cV p j (Pi.single i 1))) =
        Sum.elim (bv p j (Pi.single i 1)) (0 : Fin p × N.ι → ℤ_[p]) -
          ((p * N.wt i + p - 1 - 2 * j : ℤ) : ℤ_[p]) •
            Sum.elim (0 : Fin p × N.ι → ℤ_[p]) (bv p j (Pi.single i 1)) := by
      rw [(hC j j.isLt _).1, HB, elim_smul]
      funext x
      cases x <;> simp
    have he' := eq_add_of_sub_eq he.symm
    rw [he']
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨_, rfl⟩)
      (Submodule.smul_mem _ _ (hinr j j.isLt))
  · rw [single_inr_eq, single_eq_bv]
    exact hinr j j.isLt

end ColouredSand.OddTwist
