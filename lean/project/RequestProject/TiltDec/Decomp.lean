module

public import RequestProject.TiltDec.Weyl
public import RequestProject.TiltRules.All
public import RequestProject.FamDec.All

/-!
# `CSG5_the_induction.md`, Part D — the decomposition `V^{⊗n} ⊗ ℤ_p ≅ ⊕ T(λ)^{m_λ(n)}`

## Encoding (namespace `ColouredSand.TiltDec`)

* DP-lattices over `ℤ_[p]` are the cube's `DPLattice ℤ_[p]`; `tensorV M` is `V ⊗ M`,
  `Filt.tpow ℤ_[p] n` is `V^{⊗n} ⊗ ℤ_p` (`tpow A 0 = one A`, `tpow A (n+1) = tensorV (tpow A n)`),
  finite direct sums are `Step36.dsumList` (`dsumList [] = 0`, `dsumList (X :: L) = X ⊕ dsumList L`),
  and "`X ≅ Y`" is `Nonempty (Doubling.Iso X Y)`.
* `Ttilt p l` is the tilting lattice of CSG3 (`RequestProject/TiltP/Tilt.lean`): `Δ(l)` if `l` is
  simple, `Tglue p (rT p l) (aT p l)` otherwise.
* `VdotP`, `LP`, `mP` are those of Part M (`RequestProject/TiltDec/Rule.lean`).
* Throughout `p` is a prime (`[Fact p.Prime]`) with `hp2 : p ≠ 2`.

## Contents

* **(D1)** `D1`: `V ⊗ Ttilt p l ≅ dsumList ((VdotP p l).map (Ttilt p))` for `l ≤ p² + p − 2`,
  case by case from the CSG4 rules `S0`, `S1`, `S2`, `R1`, `R2`, `R3_pos`, `R3_zero`, `R4`.
* **(D2)** `D2`: `tpow ℤ_[p] n ≅ dsumList ((LP p n).map (Ttilt p))` for `n ≤ p² + p − 1`
  (induction on `n` as `FamDec.D2`, with (M3) to stay in the range of (D1), and `FamDec.P2`).
* **(D3)** `D3`: the multiplicity form, from (D2), `LP_perm_replicate` and `FamDec.P1`.
* `card_Ttilt`: the rank of `Ttilt p l` is `rankT p l` (for `l ≤ p² + p − 1`), the rank used in
  (W5); `W5_card`: (W5) with the actual ranks `Fintype.card (Ttilt p λ).ι`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TiltDec

open DPLattice WeylFilt Doubling Lemma35 Tensor2 Lemma35b Filt Step36
  ColouredSand.TiltP ColouredSand.TiltRules ColouredSand.Blocks

variable {p : ℕ} [Fact p.Prime]

/-! ### `Ttilt` at the weights occurring in (D1) -/

/-- `Ttilt p (lam p r a) = Tglue p r a` for `1 ≤ r ≤ p − 1`. -/
lemma Ttilt_lam {r : ℕ} (a : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ p - 1) :
    Ttilt p (lam p r a) = Tglue p r a := by
  rw [Ttilt_of_not_simple p (not_simple_lam a hr1 hr), rT_lam a hr1 (by omega),
    aT_lam a hr1 (by omega)]

/-- `Ttilt p (lam p p (p − 1)) = Tglue p p (p − 1)`. -/
lemma Ttilt_lam_top : Ttilt p (lam p p (p - 1)) = Tglue p p (p - 1) := by
  have hp := (Fact.out : p.Prime).two_le
  rw [Ttilt_of_not_simple p (not_simple_lam_top (by omega)), rT_lam _ (by omega) le_rfl,
    aT_lam _ (by omega) le_rfl]

/-- `3 ≤ p` for a prime `p ≠ 2`. -/
lemma three_le (hp2 : p ≠ 2) : 3 ≤ p := by
  have := (Fact.out : p.Prime).two_le; omega

omit [Fact p.Prime] in
/-- `GlueHyp p r a` for `1 ≤ r ≤ p − 1`, `a ≤ p − 1`. -/
lemma glueHyp_of {r a : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ p - 1) (ha : a ≤ p - 1) : GlueHyp p r a :=
  ⟨hr1, by omega, ha, by omega⟩

/-- `X ≅ dsumList [X]`. -/
def isoSingle (X : DPLattice ℤ_[p]) : Doubling.Iso X (dsumList [X]) :=
  (dsumListSingletonIso X).symm

/-- `X ⊕ Y ≅ dsumList [X, Y]`. -/
def isoPair (X Y : DPLattice ℤ_[p]) : Doubling.Iso (dsum X Y) (dsumList [X, Y]) :=
  dsumIso (Iso.refl X) (isoSingle Y)

/-- `X ⊕ (Y ⊕ Z) ≅ dsumList [X, Y, Z]`. -/
def isoTriple (X Y Z : DPLattice ℤ_[p]) : Doubling.Iso (dsum X (dsum Y Z)) (dsumList [X, Y, Z]) :=
  dsumIso (Iso.refl X) (isoPair Y Z)

/-! ### (D1) -/

/-- **(D1)** (`CSG5_the_induction.md`, Part D, (D1)): for a prime `p ≠ 2` and every
`l ≤ p² + p − 2`, `V ⊗ Ttilt p l ≅ dsumList ((VdotP p l).map (Ttilt p))`. -/
theorem D1 (hp2 : p ≠ 2) {l : ℕ} (hl : l ≤ p ^ 2 + p - 2) :
    Nonempty (Doubling.Iso (tensorV (Ttilt p l)) (dsumList ((VdotP p l).map (Ttilt p)))) := by
  have hp3 := three_le (p := p) hp2
  rcases cases_weight hp3 hl with rfl | ⟨h1, h2⟩ | ⟨b, hb, hlb⟩ | ⟨r, a, hr1, hr, ha, rfl⟩
  · -- `l = 0`: (S0)
    rw [VdotP_zero, List.map_singleton, Ttilt_of_simple p (simple_of_le (Nat.zero_le _)),
      Ttilt_of_simple p (simple_of_le (by omega) : IsSimpleWt p 1)]
    obtain ⟨u⟩ := S0 (p := p)
    exact ⟨u.trans (isoSingle _)⟩
  · -- `1 ≤ l ≤ p − 2`: (S1)
    rw [VdotP_simple_small (simple_of_le (by omega)) h1 h2, List.map_cons, List.map_singleton,
      Ttilt_of_simple p (simple_of_le (by omega) : IsSimpleWt p l),
      Ttilt_of_simple p (simple_of_le (by omega) : IsSimpleWt p (l + 1)),
      Ttilt_of_simple p (simple_of_le (by omega) : IsSimpleWt p (l - 1))]
    obtain ⟨u⟩ := S1 (p := p) h1 h2
    exact ⟨u.trans (isoPair _ _)⟩
  · -- `l = (b + 1) p − 1`: (S2)
    obtain ⟨e1, -⟩ := lam_one_of_simple (by omega) hlb
    have hs : IsSimpleWt p l := by
      have := simple_mul_sub_one (p := p) (b := b + 1) (by omega) (by omega)
      rwa [← hlb, Nat.add_sub_cancel] at this
    have hbp : p ≤ (b + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
    rw [VdotP_simple_large (by omega) hs (by omega), List.map_singleton, Ttilt_of_simple p hs, e1,
      Ttilt_lam b le_rfl (by omega)]
    obtain ⟨u⟩ := S2 (p := p) hb (show l = (b + 1) * p - 1 by omega)
    exact ⟨u.trans (isoSingle _)⟩
  · -- `l = lam p r a`, not simple
    rw [Ttilt_lam a hr1 hr]
    rcases (show r = 1 ∨ (2 ≤ r ∧ r ≤ p - 2) ∨ r = p - 1 by omega) with rfl | ⟨hr2, hr3⟩ | rfl
    · -- (R1)
      rw [VdotP_lam_one hp3 a, List.map_cons, List.map_cons, List.map_singleton,
        lam_add_one_eq, Ttilt_lam a (by omega) (by omega),
        Ttilt_of_simple p (simple_lam_one_pred ha (by omega))]
      obtain ⟨u⟩ := R1 hp2 (glueHyp_of (p := p) le_rfl hr ha)
      exact ⟨u.trans (isoTriple _ _ _)⟩
    · -- (R2)
      rw [VdotP_lam_mid a hr2 hr3, List.map_cons, List.map_singleton,
        lam_add_one_eq, Ttilt_lam a (by omega) (by omega),
        lam_sub_one_eq a hr2, Ttilt_lam a (by omega) (by omega)]
      obtain ⟨u⟩ := R2 (glueHyp_of (p := p) hr1 hr ha) hr2 hr3
      exact ⟨u.trans (isoPair _ _)⟩
    · rcases (show (1 ≤ a ∧ a ≤ p - 2) ∨ a = 0 ∨ a = p - 1 by omega) with ⟨ha1, ha2⟩ | rfl | rfl
      · -- (R3), `a ≥ 1`
        rw [VdotP_lam_top_pos hp3 ha1 ha2, List.map_cons, List.map_cons, List.map_singleton,
          Ttilt_of_simple p (simple_lam_top_succ (by omega) ha2),
          lam_sub_one_eq a (by omega), Ttilt_lam a (by omega) (by omega),
          Ttilt_of_simple p (simple_mu_top_pred (by omega) ha1 ha),
          show p - 1 - 1 = p - 2 by omega]
        obtain ⟨u⟩ := R3_pos (p := p) ha1 ha2
        exact ⟨u.trans (isoTriple _ _ _)⟩
      · -- (R3), `a = 0`
        rw [VdotP_lam_top_ext hp3 (Or.inl rfl), List.map_cons, List.map_singleton,
          Ttilt_of_simple p (simple_lam_top_succ (by omega) (by omega)),
          lam_sub_one_eq 0 (by omega), Ttilt_lam 0 (by omega) (by omega),
          show p - 1 - 1 = p - 2 by omega]
        obtain ⟨u⟩ := R3_zero (p := p) hp2
        exact ⟨u.trans (isoPair _ _)⟩
      · -- (R4)
        rw [VdotP_lam_top_ext hp3 (Or.inr rfl), List.map_cons, List.map_singleton,
          lam_top_add_one p (by omega), Ttilt_lam_top,
          lam_sub_one_eq (p - 1) (by omega), Ttilt_lam (p - 1) (by omega) (by omega),
          show p - 1 - 1 = p - 2 by omega]
        obtain ⟨u⟩ := R4 (p := p) hp2
        exact ⟨u.trans (isoPair _ _)⟩

/-! ### (D2), (D3) -/

/-- **(D2)** (`CSG5_the_induction.md`, Part D, (D2)): for a prime `p ≠ 2` and every
`n ≤ p² + p − 1`, `tpow ℤ_[p] n ≅ dsumList ((LP p n).map (Ttilt p))`.  Induction on `n` as in
`FamDec.D2`: `tpow_succ`, `tensorVIso`, `tensorVDsumListIso`, (D1) (applicable by (M3), since every
`λ ∈ LP p n` has `λ ≤ n ≤ p² + p − 2`) and `FamDec.P2`. -/
theorem D2 (hp2 : p ≠ 2) {n : ℕ} (hn : n ≤ p ^ 2 + p - 1) :
    Nonempty (Doubling.Iso (tpow ℤ_[p] n) (dsumList ((LP p n).map (Ttilt p)))) := by
  have hp3 := three_le (p := p) hp2
  induction n with
  | zero =>
    rw [tpow_zero, LP_zero, List.map_singleton,
      Ttilt_of_simple p (simple_of_le (Nat.zero_le _) : IsSimpleWt p 0)]
    exact ⟨(Iso.ofDataEquiv finOneEquivUnit T5_delta_zero).symm.trans (isoSingle _)⟩
  | succ n ih =>
    obtain ⟨u⟩ := ih (by omega)
    obtain ⟨w⟩ := FamDec.P2 (fun lam => tensorV (Ttilt p lam))
      (fun lam => (VdotP p lam).map (Ttilt p)) (LP p n)
      (fun lam hlam => D1 hp2 (by have := (M3 (by omega) n lam hlam).1; omega))
    have hmap : (LP p n).flatMap (fun lam => (VdotP p lam).map (Ttilt p)) =
        (LP p (n + 1)).map (Ttilt p) := by
      rw [LP_succ, List.map_flatMap]
    have hmap' : ((LP p n).map (Ttilt p)).map tensorV =
        (LP p n).map (fun lam => tensorV (Ttilt p lam)) := by
      rw [List.map_map]; rfl
    rw [tpow_succ, ← hmap]
    refine ⟨((tensorVIso u).trans (tensorVDsumListIso _)).trans ?_⟩
    rw [hmap']
    exact w

/-- **(D3)** (`CSG5_the_induction.md`, Part D, (D3)), multiplicity form: for a prime `p ≠ 2` and
`n ≤ p² + p − 1`, `tpow ℤ_[p] n ≅
dsumList ((List.range (n + 1)).flatMap (fun λ => List.replicate (mP p λ n) (Ttilt p λ)))`,
i.e. `V^{⊗n} ⊗ ℤ_p ≅ ⊕_{λ ≤ n} T(λ)^{m_λ(n)}`.  From (D2), `LP_perm_replicate` and `FamDec.P1`. -/
theorem D3 (hp2 : p ≠ 2) {n : ℕ} (hn : n ≤ p ^ 2 + p - 1) :
    Nonempty (Doubling.Iso (tpow ℤ_[p] n)
      (dsumList ((List.range (n + 1)).flatMap
        (fun lam => List.replicate (mP p lam n) (Ttilt p lam))))) := by
  have hp3 := three_le (p := p) hp2
  obtain ⟨u⟩ := D2 hp2 hn
  have hperm := (LP_perm_replicate (p := p) (by omega) n).map (Ttilt p)
  have heq : ((List.range (n + 1)).flatMap
      (fun lam => List.replicate (mP p lam n) lam)).map (Ttilt p) =
      (List.range (n + 1)).flatMap (fun lam => List.replicate (mP p lam n) (Ttilt p lam)) := by
    rw [List.map_flatMap]
    simp only [List.map_replicate]
  rw [heq] at hperm
  obtain ⟨v⟩ := FamDec.P1 hperm
  exact ⟨u.trans v⟩

/-! ### The rank of `Ttilt p l` (for (W5)) -/

/-- (W5) the rank of `Ttilt p l` (the cardinality of its basis) is `rankT p l`, i.e. `l + 1` if
`l` is simple and `l + μ + 2` (`μ = l − 2 rT p l`) otherwise, for `l ≤ p² + p − 1`. -/
theorem card_Ttilt {l : ℕ} (hl : l ≤ p ^ 2 + p - 1) : Fintype.card (Ttilt p l).ι = rankT p l := by
  classical
  have hp := (Fact.out : p.Prime).two_le
  unfold rankT
  by_cases hs : IsSimpleWt p l
  · rw [if_pos hs]
    have : (Ttilt p l).ι = Fin (l + 1) := by rw [Ttilt_of_simple p hs]; rfl
    rw [Fintype.card_congr (Equiv.cast this), Fintype.card_fin]
  · rw [if_neg hs]
    obtain ⟨-, -, -, -, -, hlam⟩ := T3 hp hs hl
    have : (Ttilt p l).ι = (Fin (lam p (rT p l) (aT p l) + 1) ⊕ Fin (mu p (rT p l) (aT p l) + 1)) :=
      by rw [Ttilt_of_not_simple p hs]; rfl
    rw [Fintype.card_congr (Equiv.cast this), Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    unfold mu; rw [hlam]; omega

/-- **(W5)**, rank form (`CSG5_the_induction.md`, Part W, (W5)): for a prime `p ≠ 2` and
`n ≤ p² + p − 1`, the ranks of the summands `Ttilt p λ`, `λ ∈ LP p n`, of (D2) add up to `2^n`:
`Σ_{λ ∈ LP p n} card (Ttilt p λ).ι = 2^n`. -/
theorem W5_card (hp2 : p ≠ 2) {n : ℕ} (hn : n ≤ p ^ 2 + p - 1) :
    ((LP p n).map (fun lam => Fintype.card (Ttilt p lam).ι)).sum = 2 ^ n := by
  have hp3 := three_le (p := p) hp2
  rw [← W5 hp3 hn]
  congr 1
  exact List.map_congr_left (fun lam hlam =>
    card_Ttilt (by have := (M3 (by omega) n lam hlam).1; omega))

end ColouredSand.TiltDec
