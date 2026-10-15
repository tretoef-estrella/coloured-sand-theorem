module

public import RequestProject.Glue.Stability

/-!
# (G2) The glue is forced (CSG2, §1 (G2) and §2 "*(G2)*")

* `glue_forced`: for general `λ = μ + 2r`: a stable `ℤ_[p]`-submodule `Λ` of `V` satisfying
  (i) (an `inl`-supported vector lies in `Λ` iff it lies in `Dλ`) and (ii) (the projection of `Λ`
  onto the `inr` coordinates is `Dμ`) is `Lx x` for some `x`.
* `G2_glue_forced`: the statement of §1 (with `λ = lam p r a`, `μ = mu p r a`), together with
  `‖x‖ ≤ p^ν` from (G1).

Encoding of the hypotheses: "`v` is supported on the `inl` indices" is `∀ j, v (inr j) = 0`;
(ii) is the conjunction of "`‖v (inr j)‖ ≤ 1` for all `v ∈ Λ` and all `j`" (integral `inr`
coordinates) and "for every `j` there is `v ∈ Λ` whose `inr`-part is that of `s_j`".

Proof.  The argument is shorter than the paper's: take `v₀ ∈ Λ` with `inr`-part `s₀`; its weight
`μ` component is `w = P μ v₀ = s₀ + x ℓ_r` (only `s₀` and `ℓ_r` have weight `μ`).  Then
`F j w = s̃ x j` (`C(r + j, j) = C(j + r, j)`), so every `s̃ x j` lies in `Λ` by stability under
`F j` (`j ≥ 1`); together with (i) this gives `Lx x ≤ Λ`.  Conversely, for `v ∈ Λ`,
`v − Σ_j v(inr j) • s̃ x j` lies in `Λ` and is `inl`-supported, hence in `Dλ ⊆ Lx x` by (i).
(So the recursion on the `x_j` of the paper, with stability under `F 1` and `F p`, is not needed:
stability under all `F j` already forces `x_j ≡ C(j + r, j) x_0`.)
-/

@[expose] public section

open Finset

namespace ColouredSand.Glue

open ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime] {L M : ℕ}

lemma Fop_zero_apply (v : V p L M) : Fop p L M 0 v = v := by
  ext (i | j)
  · rw [Fop_inl, if_pos (Nat.zero_le _), Nat.choose_zero_right, Nat.sub_zero, cL_fin]; simp
  · rw [Fop_inr, if_pos (Nat.zero_le _), Nat.choose_zero_right, Nat.sub_zero, cR_fin]; simp

/-- **(G2), general form** (`λ = μ + 2r`). -/
theorem glue_forced (r : ℕ) (hLM : L = M + 2 * r) (Λ : Submodule ℤ_[p] (V p L M))
    (hS : IsStable p L M Λ)
    (hi : ∀ v : V p L M, (∀ j, v (.inr j) = 0) → (v ∈ Λ ↔ v ∈ Dlam p L M))
    (hii1 : ∀ v ∈ Λ, ∀ j, ‖v (.inr j)‖ ≤ 1)
    (hii2 : ∀ j : Fin (M + 1), ∃ v ∈ Λ, ∀ j', v (.inr j') = ess p L M j (.inr j')) :
    ∃ x : ℚ_[p], Λ = Lx p L M r x := by
  -- `ℓ_i ∈ Λ`
  have hell : ∀ i, ell p L M i ∈ Λ := by
    intro i
    by_cases hiL : i ≤ L
    · apply (hi _ (fun j => ell_inr i j)).2
      exact Submodule.subset_span ⟨⟨i, Nat.lt_succ_of_le hiL⟩, rfl⟩
    · rw [ell, dif_neg hiL]; exact Λ.zero_mem
  obtain ⟨v₀, hv₀, hv₀s⟩ := hii2 ⟨0, Nat.succ_pos _⟩
  set w := Pop p L M (M : ℤ) v₀ with hw_def
  have hwΛ : w ∈ Λ := hS.2 _ _ hv₀
  set x := cL v₀ r with hx
  have hw : w = ess p L M 0 + x • ell p L M r := by
    ext (i | j)
    · rw [hw_def, Pop_apply, Pi.add_apply, ess_inl, Pi.smul_apply, ell_inl, smul_eq_mul, zero_add]
      simp only [wt]
      by_cases h : (i : ℕ) = r
      · rw [if_pos (by rw [h, hLM]; push_cast; ring), if_pos h, hx, ← h, cL_fin]; ring
      · rw [if_neg (by intro h'; apply h; omega), if_neg h]; ring
    · rw [hw_def, Pop_apply, Pi.add_apply, ess_inr, Pi.smul_apply, ell_inr, smul_eq_mul,
        mul_zero, add_zero, hv₀s, ess_inr]
      simp only [wt]
      by_cases h : (j : ℕ) = 0
      · rw [if_pos (by rw [h]; ring), if_pos h]
      · rw [if_neg (by intro h'; apply h; omega), if_neg h]
  have hF : ∀ j, j ≤ M → Fop p L M j w = stilde p L M r x j := by
    intro j hj
    rw [hw, map_add, LinearMap.map_smul, F_ess j 0 (Nat.zero_le _),
      F_ell j r (by omega), stilde, if_pos hj, zero_add, Nat.choose_self, Nat.cast_one, one_smul,
      smul_smul, add_comm r j, mul_comm x]
  have hst : ∀ j, stilde p L M r x j ∈ Λ := by
    intro j
    by_cases hj : j ≤ M
    · rw [← hF j hj]
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, Fop_zero_apply]; exact hwΛ
      · exact (hS.1 j hpos w hwΛ).1
    · rw [stilde, if_neg hj]; exact Λ.zero_mem
  refine ⟨x, le_antisymm ?_ ?_⟩
  · intro v hv
    set c : Fin (M + 1) → ℤ_[p] := fun j => ⟨v (.inr j), hii1 v hv j⟩ with hc
    set s := ∑ j : Fin (M + 1), c j • stilde p L M r x j with hs
    have hsΛ : s ∈ Λ := Λ.sum_mem (fun j _ => Λ.smul_mem _ (hst j))
    have hsL : s ∈ Lx p L M r x :=
      Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (stilde_mem_Lx r x j))
    have hu : ∀ j', (v - s) (.inr j') = 0 := by
      intro j'
      rw [Pi.sub_apply, hs, Finset.sum_apply]
      simp only [padic_smul_apply, stilde_inr, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single j']
      · rw [if_pos rfl, hc]; simp
      · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h).symm)]
      · simp
    have huD : v - s ∈ Dlam p L M := (hi _ hu).1 (Λ.sub_mem hv hsΛ)
    have : v = (v - s) + s := by abel
    rw [this]
    exact Submodule.add_mem _ (Dlam_le_Lx r x huD) hsL
  · rw [Lx, Submodule.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact hell i
    · exact hst j

/-- **(G2) The glue is forced.**  Let `Λ` be a stable `ℤ_[p]`-submodule of `V` such that
(i) an `inl`-supported `v ∈ V` lies in `Λ` iff it lies in `Dλ`, and (ii) the projection of `Λ` onto
the `inr` coordinates is exactly `Dμ`.  Then `Λ = Lx x` for some `x : ℚ_[p]`, and `‖x‖ ≤ p^ν`. -/
theorem G2_glue_forced {r a : ℕ} (hr1 : 1 ≤ r) (hrp : r ≤ p) (ha : a ≤ p - 1)
    (hra : r = p → a = p - 1)
    (Λ : Submodule ℤ_[p] (V p (lam p r a) (mu p r a)))
    (hS : IsStable p (lam p r a) (mu p r a) Λ)
    (hi : ∀ v : V p (lam p r a) (mu p r a), (∀ j, v (.inr j) = 0) →
      (v ∈ Λ ↔ v ∈ Dlam p (lam p r a) (mu p r a)))
    (hii1 : ∀ v ∈ Λ, ∀ j, ‖v (.inr j)‖ ≤ 1)
    (hii2 : ∀ j : Fin (mu p r a + 1), ∃ v ∈ Λ,
      ∀ j', v (.inr j') = ess p (lam p r a) (mu p r a) j (.inr j')) :
    ∃ x : ℚ_[p], Λ = Lx p (lam p r a) (mu p r a) r x ∧ ‖x‖ ≤ (p : ℝ) ^ nu p r a := by
  obtain ⟨x, hx⟩ := glue_forced r (lam_eq_mu_add (p := p) r a hrp hra) Λ hS hi hii1 hii2
  refine ⟨x, hx, ?_⟩
  rw [← G1_stability_threshold hr1 hrp ha hra, ← hx]
  exact hS

end ColouredSand.Glue
