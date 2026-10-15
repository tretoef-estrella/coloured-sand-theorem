module

public import RequestProject.Blocks.Valuation

/-!
# The simple blocks (CSG1, §2, (S1) and (S2))

This file proves **(S1)** and **(S2)** of `CSG1_lemma_8_the_blocks.md` (§2 "The simple blocks"):
the cokernel of the chain matrix `Mch` (defined in `RequestProject/Blocks/Defs.lean`).

## Encoding

* `R = ℤ_[p]`, `Mch p q c k lam : Matrix (Fin (λ+1)) (Fin (λ+1)) ℤ_[p]` literally as in §2;
  the cokernel is `(Fin (λ+1) → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin (Mch …))`, and the
  isomorphisms are `≃+` (additive group isomorphisms), wrapped in `Nonempty`.
* `chA p q c k lam = A = Σ_{t ∈ range (λ+1)} v t`.
* The hypotheses are those of the preamble: `[Fact p.Prime]`, `1 ≤ padicValNat p q`; the case
  `c + k ≥ 1` is the hypothesis `1 ≤ c + k`, the case `c = k = 0` is `c = 0` and `k = 0`.

## Proof

The range of `Mch` is the chain relation module `chainRel λ N (i ↦ i + 1)`.  For (S1) all links
are units and contracting them (`segRedEquiv` with segment length `λ + 1`) leaves `R ⧸ (D)` with
`D = ∏ N t` up to a unit.  For (S2) the links `i + 1 = t p` are `p · unit`; contracting the unit
links (segment length `p`) and then applying the `ϖ`-chain lemma `pchainEquiv` with `ϖ = p`
gives `(R ⧸ p)^a × R ⧸ (X)` where `p^a X = ∏ N t` up to a unit.
-/

@[expose] public section

open Finset Submodule

namespace ColouredSand.Blocks

variable {p : ℕ} [hp : Fact p.Prime] {q c k : ℕ}

/-- The range of `Mch` is the chain relation module with diagonal `N` and subdiagonal `i + 1`. -/
lemma range_Mch (lam : ℕ) :
    LinearMap.range (Matrix.mulVecLin (Mch p q c k lam)) =
      chainRel lam (Nt p q c k) (fun i => ((i : ℕ) : ℤ_[p]) + 1) := by
  rw [Matrix.range_mulVecLin, chainRel]
  congr 1
  ext x
  simp only [Set.mem_range]
  have hcol : ∀ i : Fin (lam + 1), (Mch p q c k lam).col i =
      chainCol lam (Nt p q c k) (fun i => ((i : ℕ) : ℤ_[p]) + 1) i := by
    intro i
    ext i'
    simp only [Matrix.col_apply, Mch, Matrix.of_apply, chainCol, Pi.add_apply, Pi.smul_apply,
      ev_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases h : i' = i
    · subst h; simp
    · have h' : (i' : ℕ) ≠ i := fun h'' => h (Fin.ext h'')
      simp [h, h']
  simp only [hcol]

/-- A chain on `R^1`: its cokernel is `R ⧸ (D 0)`. -/
noncomputable def chainZeroEquiv {R : Type*} [CommRing R] {n : ℕ} (hn : n = 0) (D S : ℕ → R) :
    ((Fin (n + 1) → R) ⧸ chainRel n D S) ≃ₗ[R] (R ⧸ (Ideal.span {D 0} : Submodule R R)) := by
  subst hn
  refine Submodule.Quotient.equiv _ _ (LinearEquiv.funUnique (Fin 1) R R) ?_
  rw [chainRel, Submodule.map_span, ← Set.range_comp, Ideal.span]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i = 0 := Fin.ext (by have := i.2; omega)
    subst hi
    simp [chainCol, LinearEquiv.funUnique]
  · rintro rfl
    refine ⟨0, ?_⟩
    simp [chainCol, LinearEquiv.funUnique]

/-- The cokernel of `Mch` as the quotient by the chain relations. -/
noncomputable def mchCokerEquiv (lam : ℕ) :
    ((Fin (lam + 1) → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin (Mch p q c k lam))) ≃ₗ[ℤ_[p]]
      ((Fin (lam + 1) → ℤ_[p]) ⧸ chainRel lam (Nt p q c k) (fun i => ((i : ℕ) : ℤ_[p]) + 1)) :=
  Submodule.quotEquivOfEq _ _ (range_Mch lam)

lemma isUnit_link_of_not_dvd (i : ℕ) (h : (i + 1) % p ≠ 0) :
    IsUnit (((i : ℕ) : ℤ_[p]) + 1) := by
  have := isUnit_natCast_of_not_dvd (p := p) (n := i + 1)
    (fun hd => h (Nat.mod_eq_zero_of_dvd hd))
  simpa using this

omit hp in
lemma one_le_vt (hq : 1 ≤ padicValNat p q) (t : ℕ) : 1 ≤ vt p q c k t := by
  unfold vt; omega

omit hp in
lemma card_le_sum_vt (hq : 1 ≤ padicValNat p q) (s : Finset ℕ) :
    s.card ≤ ∑ t ∈ s, vt p q c k t := by
  have := Finset.sum_le_sum (s := s) (f := fun _ => 1) (g := vt p q c k)
    (fun t _ => one_le_vt hq t)
  simpa using this

/-- Common core of (S1): the cokernel is `R ⧸ (D)` with `D = ∏_{t ≤ λ} N t` up to a unit. -/
lemma S1_core {lam : ℕ} (hlam : lam ≤ p - 1) :
    ∃ D : ℤ_[p], Associated D (∏ t ∈ range (lam + 1), Nt p q c k t) ∧
      Nonempty (((Fin (lam + 1) → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin (Mch p q c k lam)))
        ≃ₗ[ℤ_[p]] (ℤ_[p] ⧸ (Ideal.span {D} : Submodule ℤ_[p] ℤ_[p]))) := by
  have hp2 := hp.out.two_le
  have hs : ∀ i < lam, (i + 1) % (lam + 1) ≠ 0 → IsUnit (((i : ℕ) : ℤ_[p]) + 1) :=
    fun i hi _ => isUnit_succ_of_lt (by omega)
  have hdiv : lam / (lam + 1) = 0 := Nat.div_eq_of_lt (by omega)
  refine ⟨segD lam (lam + 1) (Nt p q c k) (fun i => ((i : ℕ) : ℤ_[p]) + 1) 0, ?_,
    ⟨(mchCokerEquiv lam).trans ((segRedEquiv (Nat.succ_pos lam) hs).trans
      (chainZeroEquiv hdiv _ _))⟩⟩
  have := segD_associated (Nat.succ_pos lam) (d := Nt p q c k) hs (t := 0) (Nat.zero_le _)
  simpa [min_eq_left (show lam + 1 - 1 ≤ lam by omega)] using this

/-- **(S1), case `c + k ≥ 1`.**  If `λ ≤ p − 1`, `coker Mch ≃+ ZMod (p^A)`. -/
theorem S1_pos (hq : 1 ≤ padicValNat p q) (hck : 1 ≤ c + k) {lam : ℕ} (hlam : lam ≤ p - 1) :
    Nonempty (((Fin (lam + 1) → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin (Mch p q c k lam)))
      ≃+ ZMod (p ^ chA p q c k lam)) := by
  obtain ⟨D, hD, ⟨E⟩⟩ := S1_core (c := c) (k := k) hlam
  exact ⟨E.toAddEquiv.trans (quotAssocEquiv (hD.trans (prod_Nt_associated hq hck _)))⟩

/-- **(S1), case `c = k = 0`.**  If `λ ≤ p − 1`, `coker Mch ≃+ ℤ_[p]`.
(More general than stated: the hypothesis `1 ≤ padicValNat p q` is not needed here.) -/
theorem S1_zero (hc : c = 0) (hk : k = 0) {lam : ℕ}
    (hlam : lam ≤ p - 1) :
    Nonempty (((Fin (lam + 1) → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin (Mch p q c k lam)))
      ≃+ ℤ_[p]) := by
  obtain ⟨D, hD, ⟨E⟩⟩ := S1_core (c := c) (k := k) hlam
  have h0 : ∏ t ∈ range (lam + 1), Nt p q c k t = 0 :=
    Finset.prod_eq_zero (i := 0) (by simp) (Nt_zero_of hc hk)
  rw [h0, associated_zero_iff_eq_zero] at hD
  subst hD
  exact ⟨E.toAddEquiv.trans quotZeroEquiv⟩

/-- **(S1)** of §2, both cases. -/
theorem S1 (hq : 1 ≤ padicValNat p q) {lam : ℕ} (hlam : lam ≤ p - 1) :
    (1 ≤ c + k → Nonempty (((Fin (lam + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (Mch p q c k lam))) ≃+ ZMod (p ^ chA p q c k lam))) ∧
    (c = 0 → k = 0 → Nonempty (((Fin (lam + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (Mch p q c k lam))) ≃+ ℤ_[p])) :=
  ⟨fun hck => S1_pos hq hck hlam, fun hc hk => S1_zero hc hk hlam⟩

lemma p_dvd_segD (hq : 1 ≤ padicValNat p q) (n L t : ℕ) (s : ℕ → ℤ_[p]) :
    (p : ℤ_[p]) ∣ segD n L (Nt p q c k) s t :=
  Dvd.dvd.mul_right (p_dvd_Nt hq _) _

/-- Common core of (S2): the cokernel is `(R ⧸ p)^a × R ⧸ (X)` with `p^a X = ∏_{t ≤ λ} N t`
up to a unit. -/
lemma S2_core (hq : 1 ≤ padicValNat p q) {lam a : ℕ} (hlam : lam + 1 = (a + 1) * p)
    (ha : a ≤ p - 1) :
    ∃ X : ℤ_[p], Associated ((p : ℤ_[p]) ^ a * X) (∏ t ∈ range (lam + 1), Nt p q c k t) ∧
      Nonempty (((Fin (lam + 1) → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin (Mch p q c k lam)))
        ≃ₗ[ℤ_[p]] ((Fin a → ℤ_[p]) ⧸ piSpan a (p : ℤ_[p])) ×
          (ℤ_[p] ⧸ (Ideal.span {X} : Submodule ℤ_[p] ℤ_[p]))) := by
  have hp2 := hp.out.two_le
  have hp0 : 0 < p := by omega
  have hring : (a + 1) * p = a * p + p := by ring
  have hs : ∀ i < lam, (i + 1) % p ≠ 0 → IsUnit (((i : ℕ) : ℤ_[p]) + 1) :=
    fun i _ h => isUnit_link_of_not_dvd i h
  have hdiv : lam / p = a := Nat.div_eq_of_lt_le (by omega) (by omega)
  set d := Nt p q c k
  set s : ℕ → ℤ_[p] := fun i => ((i : ℕ) : ℤ_[p]) + 1
  set D := segD lam p d s
  set S := segS p s
  obtain ⟨E1⟩ : Nonempty (((Fin (lam + 1) → ℤ_[p]) ⧸
      LinearMap.range (Matrix.mulVecLin (Mch p q c k lam))) ≃ₗ[ℤ_[p]]
      ((Fin (lam / p + 1) → ℤ_[p]) ⧸ chainRel (lam / p) D S)) :=
    ⟨(mchCokerEquiv lam).trans (segRedEquiv hp0 hs)⟩
  rw [hdiv] at E1
  have hDv : ∀ t, (p : ℤ_[p]) ∣ D t := fun t => p_dvd_segD hq lam p t s
  set P : ℕ → ℤ_[p] := fun t => (hDv t).choose
  set w : ℕ → ℤ_[p] := fun t => ((t : ℕ) : ℤ_[p]) + 1
  have hD : ∀ t < a, D t = p * P t := fun t _ => (hDv t).choose_spec
  have hw : ∀ t < a, IsUnit (w t) := fun t ht => isUnit_succ_of_lt (by omega)
  have hS : ∀ t < a, S t = p * w t := by
    intro t _
    simp only [S, segS, s, w]
    have h1 : t * p + p - 1 + 1 = t * p + p := by omega
    have h2 : (((t * p + p - 1 : ℕ) : ℤ_[p]) + 1) = ((t * p + p - 1 + 1 : ℕ) : ℤ_[p]) := by
      push_cast; ring
    rw [h2, h1]; push_cast; ring
  refine ⟨D a * pcCoef P w a, ?_, ⟨E1.trans (pchainEquiv (p : ℤ_[p]) D S hD hS hw (hDv a))⟩⟩
  have h1 : (p : ℤ_[p]) ^ a * (D a * pcCoef P w a) = D a * ((p : ℤ_[p]) ^ a * pcCoef P w a) := by
    ring
  rw [h1]
  refine ((pcCoef_associated (p : ℤ_[p]) a hD hw).mul_left (D a)).trans ?_
  rw [mul_comm, ← prod_range_succ]
  have h2 : ∀ t ∈ range (a + 1), Associated (D t) (∏ i ∈ Ico (t * p) (t * p + p), d i) := by
    intro t ht
    have ht' : t ≤ a := by simp at ht; omega
    have h3 := Nat.mul_le_mul_right p ht'
    have h4 : min (t * p + p - 1) lam + 1 = t * p + p := by omega
    have := segD_associated hp0 (d := d) hs (t := t) (by omega)
    rwa [h4] at this
  refine (Associated.prod _ _ _ h2).trans ?_
  rw [prod_segments d p (a + 1), ← hlam]
  exact Associated.refl _

/-- **(S2), case `c + k ≥ 1`.**  If `λ + 1 = (a + 1) p` with `a ≤ p − 1`, then `a + 1 ≤ A` and
`coker Mch ≃+ (ZMod p)^a × ZMod (p^(A − a))`. -/
theorem S2_pos (hq : 1 ≤ padicValNat p q) (hck : 1 ≤ c + k) {lam a : ℕ}
    (hlam : lam + 1 = (a + 1) * p) (ha : a ≤ p - 1) :
    a + 1 ≤ chA p q c k lam ∧
    Nonempty (((Fin (lam + 1) → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin (Mch p q c k lam)))
      ≃+ (Fin a → ZMod p) × ZMod (p ^ (chA p q c k lam - a))) := by
  have hp0 := hp.out.pos
  have hA : a + 1 ≤ chA p q c k lam := by
    have h4 := card_le_sum_vt (c := c) (k := k) hq (range (lam + 1))
    rw [card_range] at h4
    have h5 : a + 1 ≤ (a + 1) * p := Nat.le_mul_of_pos_right _ hp0
    have h6 : chA p q c k lam = ∑ t ∈ range (lam + 1), vt p q c k t := rfl
    omega
  refine ⟨hA, ?_⟩
  obtain ⟨X, hX, ⟨E⟩⟩ := S2_core (c := c) (k := k) hq hlam ha
  have h1 := hX.trans (prod_Nt_associated hq hck _)
  have h2 : (p : ℤ_[p]) ^ (∑ t ∈ range (lam + 1), vt p q c k t) =
      (p : ℤ_[p]) ^ a * (p : ℤ_[p]) ^ (chA p q c k lam - a) := by
    have h6 : chA p q c k lam = ∑ t ∈ range (lam + 1), vt p q c k t := rfl
    rw [← pow_add]; congr 1; omega
  rw [h2] at h1
  have hpne : (p : ℤ_[p]) ^ a ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have h3 := Associated.of_mul_left h1 (Associated.refl _) hpne
  exact ⟨E.toAddEquiv.trans ((piSpanEquiv a).prodCongr (quotAssocEquiv h3))⟩

/-- **(S2), case `c = k = 0`.**  If `λ + 1 = (a + 1) p` with `a ≤ p − 1`, then
`coker Mch ≃+ ℤ_[p] × (ZMod p)^a`. -/
theorem S2_zero (hq : 1 ≤ padicValNat p q) (hc : c = 0) (hk : k = 0) {lam a : ℕ}
    (hlam : lam + 1 = (a + 1) * p) (ha : a ≤ p - 1) :
    Nonempty (((Fin (lam + 1) → ℤ_[p]) ⧸ LinearMap.range (Matrix.mulVecLin (Mch p q c k lam)))
      ≃+ ℤ_[p] × (Fin a → ZMod p)) := by
  obtain ⟨X, hX, ⟨E⟩⟩ := S2_core (c := c) (k := k) hq hlam ha
  have h0 : ∏ t ∈ range (lam + 1), Nt p q c k t = 0 :=
    Finset.prod_eq_zero (i := 0) (by simp) (Nt_zero_of hc hk)
  rw [h0, associated_zero_iff_eq_zero] at hX
  have hpne : (p : ℤ_[p]) ^ a ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hX0 : X = 0 := (mul_eq_zero.1 hX).resolve_left hpne
  subst hX0
  exact ⟨E.toAddEquiv.trans (((piSpanEquiv a).prodCongr quotZeroEquiv).trans
    (AddEquiv.prodComm))⟩

/-- **(S2)** of §2, both cases. -/
theorem S2 (hq : 1 ≤ padicValNat p q) {lam a : ℕ} (hlam : lam + 1 = (a + 1) * p)
    (ha : a ≤ p - 1) :
    (1 ≤ c + k → a + 1 ≤ chA p q c k lam ∧ Nonempty (((Fin (lam + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (Mch p q c k lam))) ≃+
          (Fin a → ZMod p) × ZMod (p ^ (chA p q c k lam - a)))) ∧
    (c = 0 → k = 0 → Nonempty (((Fin (lam + 1) → ℤ_[p]) ⧸
        LinearMap.range (Matrix.mulVecLin (Mch p q c k lam))) ≃+ ℤ_[p] × (Fin a → ZMod p))) :=
  ⟨fun hck => S2_pos hq hck hlam ha, fun hc hk => S2_zero hq hc hk hlam ha⟩

end ColouredSand.Blocks
