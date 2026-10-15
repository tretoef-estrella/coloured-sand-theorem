module

public import RequestProject.TiltP.GlueDP

/-!
# (T1)–(T2) The glued lattice `Tglue p r a` of Lemma 7 (CSG3, Part T)

## Encoding

* `GlueHyp p r a` is the standing hypothesis of the file: `1 ≤ r ≤ p`, `a ≤ p − 1`,
  `r = p → a = p − 1`.
* `Tglue p r a : DPLattice ℤ_[p]` is `glueDP` (see `RequestProject/TiltP/GlueDP.lean`) for
  `L = λ = lam p r a`, `M = μ = mu p r a`, shift `r`, and glue parameter `xT p r a`, where
  `xT p r a = xzero p r a = p^(−ν)` under `GlueHyp p r a` (and `0` otherwise, so that `Tglue` is a
  total function; then `Tglue p r a = Δ(λ) ⊕ Δ(μ)` coordinatewise).  Thus, under `GlueHyp`:
  - the basis is `ι = Fin (λ + 1) ⊕ Fin (μ + 1)` (`Tglue_ι`);
  - `wt (inl i) = λ − 2i`, `wt (inr j) = μ − 2j` (`Tglue_wt_inl`, `Tglue_wt_inr`);
  - `Fd t v` is the coordinate vector, in `glueBasis p λ μ r (xzero p r a)`, of
    `Fop p λ μ t (Σ_y v y • b y)`, and similarly for `Ed t` (`T1_Fd`, `T1_Ed`); these make sense
    because `Lx x₀` is stable (`T1_stable`, from `G1_stability_threshold` and `‖x₀‖ = p^ν`, and
    `Fop 0 = Eop 0 = id`);
  - (W), (P0), (P1), (K) hold (`T1_isDP`).
* (T2): `Tf p r a : Hom (delta ℤ_[p] λ) (Tglue p r a)` (`e_i ↦ δ_{inl i}`) and
  `Tg p r a : Hom (Tglue p r a) (delta ℤ_[p] μ)` (`δ_{inl i} ↦ 0`, `δ_{inr j} ↦ e_j`); `T2` states
  `ShortExact (Tf p r a) (Tg p r a)` and that `Tf`, `Tg` are weight-preserving.  (T2) holds for all
  `r, a` (more general than the file).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltP

open DPLattice WeylFilt LemmaW Lemma35 ColouredSand.Glue ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime]

/-- The standing hypothesis of CSG3: `1 ≤ r ≤ p`, `a ≤ p − 1`, `r = p → a = p − 1`. -/
def GlueHyp (p r a : ℕ) : Prop := 1 ≤ r ∧ r ≤ p ∧ a ≤ p - 1 ∧ (r = p → a = p - 1)

open Classical in
variable (p) in
/-- The glue parameter of `Tglue`: `x₀ = p^(−ν)` under `GlueHyp`, `0` otherwise. -/
def xT (r a : ℕ) : ℚ_[p] := if GlueHyp p r a then xzero p r a else 0

lemma xT_of_hyp {r a : ℕ} (h : GlueHyp p r a) : xT p r a = xzero p r a := by
  classical
  unfold xT; rw [if_pos h]

/-- (T1) Under `GlueHyp`, `Lx x₀` is stable under every `F t`, `E t` (`t ≥ 1` by
`G1_stability_threshold`, since `‖x₀‖ = p^ν`; `t = 0` since `F 0 = E 0 = id`). -/
theorem T1_stable {r a : ℕ} (h : GlueHyp p r a) (t : ℕ) (v : V p (lam p r a) (mu p r a))
    (hv : v ∈ Lx p (lam p r a) (mu p r a) r (xzero p r a)) :
    Fop p (lam p r a) (mu p r a) t v ∈ Lx p (lam p r a) (mu p r a) r (xzero p r a) ∧
      Eop p (lam p r a) (mu p r a) t v ∈ Lx p (lam p r a) (mu p r a) r (xzero p r a) := by
  obtain ⟨hr1, hrp, ha, hra⟩ := h
  have hS := (G1_stability_threshold hr1 hrp ha hra (xzero p r a)).2 (norm_xzero r a).le
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [Fop_zero, Eop_zero]; exact ⟨hv, hv⟩
  · exact hS.1 t ht v hv

lemma glueOK_xT (r a : ℕ) : GlueOK p (lam p r a) (mu p r a) r (xT p r a) := by
  by_cases h : GlueHyp p r a
  · rw [xT_of_hyp h]
    exact ⟨Or.inr (lam_eq_mu_add r a h.2.1 h.2.2.2), fun t v hv => T1_stable h t v hv⟩
  · classical
    have : xT p r a = 0 := by unfold xT; rw [if_neg h]
    rw [this]; exact glueOK_zero r

variable (p) in
/-- **(T1) The glued lattice of Lemma 7 as a DP-lattice over `ℤ_[p]`.** -/
def Tglue (r a : ℕ) : DPLattice ℤ_[p] :=
  glueDP p (lam p r a) (mu p r a) r (xT p r a) (glueOK_xT r a)

/-- (T1) The basis of `Tglue p r a` is `Fin (λ + 1) ⊕ Fin (μ + 1)`. -/
theorem Tglue_ι (r a : ℕ) : (Tglue p r a).ι = (Fin (lam p r a + 1) ⊕ Fin (mu p r a + 1)) := rfl

/-- (T1) `wt (inl i) = λ − 2i`. -/
theorem Tglue_wt_inl (r a : ℕ) (i : Fin (lam p r a + 1)) :
    (Tglue p r a).wt (Sum.inl i) = (lam p r a : ℤ) - 2 * (i : ℤ) := rfl

/-- (T1) `wt (inr j) = μ − 2j`. -/
theorem Tglue_wt_inr (r a : ℕ) (j : Fin (mu p r a + 1)) :
    (Tglue p r a).wt (Sum.inr j) = (mu p r a : ℤ) - 2 * (j : ℤ) := rfl

lemma glueDP_Fd_spec' {L M : ℕ} (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) (x' : ℚ_[p])
    (hx : x = x') (t : ℕ) (v : Idx L M → ℤ_[p]) :
    ∑ y, (glueDP p L M r x h).Fd t v y • (glueBasis p L M r x' y : V p L M) =
      Fop p L M t (∑ y, v y • (glueBasis p L M r x' y : V p L M)) := by
  subst hx; exact glueDP_Fd_spec r x h t v

lemma glueDP_Ed_spec' {L M : ℕ} (r : ℕ) (x : ℚ_[p]) (h : GlueOK p L M r x) (x' : ℚ_[p])
    (hx : x = x') (t : ℕ) (v : Idx L M → ℤ_[p]) :
    ∑ y, (glueDP p L M r x h).Ed t v y • (glueBasis p L M r x' y : V p L M) =
      Eop p L M t (∑ y, v y • (glueBasis p L M r x' y : V p L M)) := by
  subst hx; exact glueDP_Ed_spec r x h t v

/-- **(T1), `F`**: under `GlueHyp`, `Fd t v` is the coordinate vector, in the basis
`b = glueBasis p λ μ r (xzero p r a)` of `Lx x₀`, of `Fop p λ μ t (Σ_y v y • b y)`. -/
theorem T1_Fd {r a : ℕ} (h : GlueHyp p r a) (t : ℕ) (v : Idx (lam p r a) (mu p r a) → ℤ_[p]) :
    ∑ y, (Tglue p r a).Fd t v y •
        (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) y : V p (lam p r a) (mu p r a)) =
      Fop p (lam p r a) (mu p r a) t (∑ y, v y •
        (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) y : V p (lam p r a) (mu p r a))) :=
  glueDP_Fd_spec' r _ (glueOK_xT r a) _ (xT_of_hyp h) t v

/-- **(T1), `E`**: under `GlueHyp`, `Ed t v` is the coordinate vector, in the basis
`b = glueBasis p λ μ r (xzero p r a)` of `Lx x₀`, of `Eop p λ μ t (Σ_y v y • b y)`. -/
theorem T1_Ed {r a : ℕ} (h : GlueHyp p r a) (t : ℕ) (v : Idx (lam p r a) (mu p r a) → ℤ_[p]) :
    ∑ y, (Tglue p r a).Ed t v y •
        (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) y : V p (lam p r a) (mu p r a)) =
      Eop p (lam p r a) (mu p r a) t (∑ y, v y •
        (glueBasis p (lam p r a) (mu p r a) r (xzero p r a) y : V p (lam p r a) (mu p r a))) :=
  glueDP_Ed_spec' r _ (glueOK_xT r a) _ (xT_of_hyp h) t v

/-- **(T1)** `Tglue p r a` satisfies (W), (P0), (P1), (K). -/
theorem T1_isDP (r a : ℕ) : IsDP (Tglue p r a).wt (Tglue p r a).Fd (Tglue p r a).Ed :=
  (Tglue p r a).isDP

variable (p) in
/-- (T2) `f : Δ(λ) → Tglue`, `e_i ↦ δ_{inl i}`. -/
def Tf (r a : ℕ) : Hom (delta ℤ_[p] (lam p r a)) (Tglue p r a) :=
  glueF p (lam p r a) (mu p r a) r (xT p r a) (glueOK_xT r a)

variable (p) in
/-- (T2) `g : Tglue → Δ(μ)`, `δ_{inl i} ↦ 0`, `δ_{inr j} ↦ e_j`. -/
def Tg (r a : ℕ) : Hom (Tglue p r a) (delta ℤ_[p] (mu p r a)) :=
  glueG p (lam p r a) (mu p r a) r (xT p r a) (glueOK_xT r a)

/-- (T2) `f (e_i) = δ_{inl i}`. -/
theorem Tf_single (r a : ℕ) (i : Fin (lam p r a + 1)) :
    (Tf p r a).toLin (Pi.single i 1) =
      (Pi.single (Sum.inl i : Idx (lam p r a) (mu p r a)) (1 : ℤ_[p]) :
        Idx (lam p r a) (mu p r a) → ℤ_[p]) := by
  funext y; rcases y with i' | j'
  · show (Pi.single i (1 : ℤ_[p]) : Fin (lam p r a + 1) → ℤ_[p]) i' = _
    by_cases hi : i' = i
    · subst hi; simp
    · rw [Pi.single_apply, if_neg hi, Pi.single_apply, if_neg (by simpa using hi)]
  · show (0 : ℤ_[p]) = _
    rw [Pi.single_apply, if_neg (by simp)]

/-- (T2) `g (δ_{inl i}) = 0`. -/
theorem Tg_single_inl (r a : ℕ) (i : Fin (lam p r a + 1)) :
    (Tg p r a).toLin (Pi.single (Sum.inl i : Idx (lam p r a) (mu p r a)) 1) = 0 := by
  funext j
  show (Pi.single (Sum.inl i : Idx (lam p r a) (mu p r a)) (1 : ℤ_[p]) :
    Idx (lam p r a) (mu p r a) → ℤ_[p]) (Sum.inr j) = 0
  rw [Pi.single_apply, if_neg (by simp)]

/-- (T2) `g (δ_{inr j}) = e_j`. -/
theorem Tg_single_inr (r a : ℕ) (j : Fin (mu p r a + 1)) :
    (Tg p r a).toLin (Pi.single (Sum.inr j : Idx (lam p r a) (mu p r a)) 1) =
      (Pi.single j (1 : ℤ_[p]) : Fin (mu p r a + 1) → ℤ_[p]) := by
  funext j'
  show (Pi.single (Sum.inr j : Idx (lam p r a) (mu p r a)) (1 : ℤ_[p]) :
    Idx (lam p r a) (mu p r a) → ℤ_[p]) (Sum.inr j') = _
  by_cases hj : j' = j
  · subst hj; simp
  · rw [Pi.single_apply, if_neg (by simpa using hj), Pi.single_apply, if_neg hj]

/-- **(T2)** `Δ(λ) —f→ Tglue p r a —g→ Δ(μ)` is short exact, and `f`, `g` are weight-preserving.
(This holds for every `r, a`.) -/
theorem T2 (r a : ℕ) :
    ShortExact (Tf p r a) (Tg p r a) ∧ IsWtPres (Tf p r a).toLin ∧ IsWtPres (Tg p r a).toLin :=
  ⟨glue_shortExact r _ _, glue_wtPres r _ _⟩

end ColouredSand.TiltP
