module

public import RequestProject.OddSplitting.Tools
public import RequestProject.OddSES.CasimirPsi
public import RequestProject.OddSES.PartS1b

/-!
# `CSI5_the_splitting.md`: Part H — a splitting lemma over `ℤ_[p]`

Namespace `ColouredSand.OddTwist`. We reuse C18 (`DPLattice`, `Hom`, `H`), C19
(`WeylFilt.ShortExact`, `WeylFilt.Hom.comp`), C20 (`Doubling.Iso`, `Doubling.Iso.ofInverse`),
C22 (`Lemma35.dsum`, `Lemma35.fstHom`, `Lemma35.sndHom`) and CSI4 (`casimir`, `Dcas`,
`casimir_hom`, `casimir_comm_Fd`, `casimir_comm_Ed`, `casimir_comm_H`, `pairHom`).

**Setting and encoding.** `p` is a prime (`[Fact p.Prime]`), the ring is `ℤ_[p]`.
`ι : Hom Y M`, `π : Hom M Q` with `hSE : WeylFilt.ShortExact ι π` is the short exact sequence
`Y →ι M →π Q`; `a b : ℤ_[p]` with `hab : IsUnit (a − b)`. `Ω` is CSI4's `casimir`, and
`Dcas X c = Ω_X − c • 1`, so the hypotheses of the file are

* `hY : ∃ R, Dcas Y a ∘ₗ Dcas Y a = (p : ℤ_[p]) • R` (`(Ω_Y − a)² = p • R_Y`),
* `hQ : ∃ R, Dcas Q b ∘ₗ Dcas Q b = (p : ℤ_[p]) • R` (`(Ω_Q − b)² = p • R_Q`).

**Results.**

* `exists_retraction`: there is a morphism `E : Hom M Y` with `E ∘ ι = id` (the heart of the
  proof; `e = ι ∘ E`).
* **(H1)** `splitting_H1`: there is `e : Hom M M` with `e ∘ e = e`, `e ∘ ι = ι` (both as equalities of
  morphisms, `WeylFilt.Hom.comp`) and `π ∘ e = 0` (as linear maps).
* **(H2)** `splitting_H2`: `Nonempty (Doubling.Iso M (Lemma35.dsum Y Q))`.

**Proof (finite, following the outline).** By Cayley–Hamilton applied to `R_Q`
(`exists_annihilating_poly`) there is `G = X^{2k} + p·h` with `G(Ω_Q − b) = 0`. Put
`P := G(Ω_M − b)`. Then `π ∘ P = G(Ω_Q − b) ∘ π = 0`, so `P` maps `M` into `range ι = ker π`:
`P = ι ∘ P'`. On `Y`, `P' ∘ ι = P_Y := G(Ω_Y − b)`, and modulo `p`,
`P_Y ≡ (Ω_Y − b)^{2k} = ((Ω_Y − a) + (a − b))^{2k}` is a unit (`(Ω_Y − a)` is nilpotent modulo
`p`, `a − b` is a unit), so `P_Y` is invertible (`isUnit_of_isUnit_modP`). Then
`E := P_Y⁻¹ ∘ P'` is a retraction of `ι`; it commutes with every `F^{(r)}`, `E^{(r)}` and `H`
because `Ω` does (CSI4 (C1)). The isomorphism of (H2) is `x ↦ (E x, π x)`, with inverse
`(y, q) ↦ ι y + (s q − ι E s q)` for a linear section `s` of `π`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Polynomial

variable {p : ℕ} [Fact p.Prime]

section commute

variable {M M' : DPLattice ℤ_[p]}

/-- Part H (auxiliary): a morphism intertwines `Ω − c`. -/
lemma Dcas_homL (f : Hom M M') (c : ℤ_[p]) : f.toLin ∘ₗ Dcas M c = Dcas M' c ∘ₗ f.toLin := by
  simp only [Dcas, LinearMap.comp_sub, LinearMap.sub_comp, casimir_hom f, LinearMap.comp_smul,
    LinearMap.smul_comp, LinearMap.id_comp, LinearMap.comp_id]

/-- Part H (auxiliary): `F^{(r)}` commutes with `Ω − c` (CSI4 (C1)). -/
lemma Fd_Dcas (M : DPLattice ℤ_[p]) (r : ℕ) (c : ℤ_[p]) :
    M.Fd r ∘ₗ Dcas M c = Dcas M c ∘ₗ M.Fd r := by
  simp only [Dcas, LinearMap.comp_sub, LinearMap.sub_comp, (casimir_comm_Fd M r).symm,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp, LinearMap.comp_id]

/-- Part H (auxiliary): `E^{(r)}` commutes with `Ω − c` (CSI4 (C1)). -/
lemma Ed_Dcas (M : DPLattice ℤ_[p]) (r : ℕ) (c : ℤ_[p]) :
    M.Ed r ∘ₗ Dcas M c = Dcas M c ∘ₗ M.Ed r := by
  simp only [Dcas, LinearMap.comp_sub, LinearMap.sub_comp, (casimir_comm_Ed M r).symm,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp, LinearMap.comp_id]

/-- Part H (auxiliary): `H` commutes with `Ω − c` (CSI4 (C1)). -/
lemma H_Dcas (M : DPLattice ℤ_[p]) (c : ℤ_[p]) :
    H M ∘ₗ Dcas M c = Dcas M c ∘ₗ H M := by
  simp only [Dcas, LinearMap.comp_sub, LinearMap.sub_comp, (casimir_comm_H M).symm,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp, LinearMap.comp_id]

end commute

section split

variable {Y M Q : DPLattice ℤ_[p]} {ι : Hom Y M} {π : Hom M Q}

/-- Part H, steps 1–5: under the hypotheses of Part H, `ι` has a retraction which is a morphism:
`E : Hom M Y` with `E ∘ ι = id`. -/
theorem exists_retraction (hSE : WeylFilt.ShortExact ι π) {a b : ℤ_[p]} (hab : IsUnit (a - b))
    (hY : ∃ R, Dcas Y a ∘ₗ Dcas Y a = (p : ℤ_[p]) • R)
    (hQ : ∃ R, Dcas Q b ∘ₗ Dcas Q b = (p : ℤ_[p]) • R) :
    ∃ E : Hom M Y, E.toLin ∘ₗ ι.toLin = LinearMap.id := by
  obtain ⟨RY, hRY⟩ := hY
  obtain ⟨RQ, hRQ⟩ := hQ
  obtain ⟨k, h, hkh⟩ := exists_annihilating_poly (p : ℤ_[p]) (Dcas Q b) RQ hRQ
  set G : ℤ_[p][X] := X ^ (2 * k) + C (p : ℤ_[p]) * h with hGdef
  have hG : ∀ {X : DPLattice ℤ_[p]} (A : Module.End ℤ_[p] (X.ι → ℤ_[p])),
      aeval A G = A ^ (2 * k) + (p : ℤ_[p]) • aeval A h := by
    intro X A
    simp only [hGdef, map_add, map_pow, aeval_X, map_mul, aeval_C, Algebra.smul_def]
  have hGQ : aeval (Dcas Q b) G = 0 := by rw [hG]; exact hkh
  set P := aeval (Dcas M b) G with hP
  set PY := aeval (Dcas Y b) G with hPY
  have hπP : π.toLin ∘ₗ P = 0 := by
    rw [hP, intertwine_aeval _ _ _ (Dcas_homL π b), hGQ, LinearMap.zero_comp]
  have hιP : ι.toLin ∘ₗ PY = P ∘ₗ ι.toLin := intertwine_aeval _ _ _ (Dcas_homL ι b) G
  have hPmem : ∀ x, P x ∈ LinearMap.range ι.toLin := by
    intro x
    rw [hSE.exact, LinearMap.mem_ker]
    exact LinearMap.congr_fun hπP x
  -- cancellation by the injective `ι`
  have cancel : ∀ {Z : Type} [AddCommGroup Z] [Module ℤ_[p] Z]
      (u v : Z →ₗ[ℤ_[p]] (Y.ι → ℤ_[p])), ι.toLin ∘ₗ u = ι.toLin ∘ₗ v → u = v :=
    fun u v huv => LinearMap.ext fun x => hSE.inj (LinearMap.congr_fun huv x)
  obtain ⟨P', hιP'⟩ : ∃ P' : (M.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Y.ι → ℤ_[p]), ι.toLin ∘ₗ P' = P := by
    refine ⟨(LinearEquiv.ofInjective ι.toLin hSE.inj).symm.toLinearMap ∘ₗ
      P.codRestrict _ hPmem, LinearMap.ext fun x => ?_⟩
    change ι.toLin ((LinearEquiv.ofInjective ι.toLin hSE.inj).symm ⟨P x, hPmem x⟩) = P x
    exact congrArg Subtype.val
      ((LinearEquiv.ofInjective ι.toLin hSE.inj).apply_symm_apply ⟨P x, hPmem x⟩)
  have hP'ι : P' ∘ₗ ι.toLin = PY := cancel _ _ (by
    rw [← LinearMap.comp_assoc, hιP', hιP])
  -- `P_Y` is invertible: modulo `p` it is `((Ω_Y − a) + (a − b))^{2k}`
  have hU : IsUnit PY := by
    apply isUnit_of_isUnit_modP
    rw [hPY, hG, map_add, modP_p_smul, add_zero, map_pow]
    apply IsUnit.pow
    have hsplit : Dcas Y b = Dcas Y a + algebraMap ℤ_[p] (Module.End ℤ_[p] (Y.ι → ℤ_[p])) (a - b) := by
      simp only [Dcas, Algebra.algebraMap_eq_smul_one, sub_smul]
      rw [Module.End.one_eq_id]
      abel
    rw [hsplit, map_add]
    refine IsNilpotent.isUnit_add_right_of_commute ⟨2, ?_⟩ ((hab.map _).map _)
      ((Algebra.commute_algebraMap_left (a - b) (Dcas Y a)).symm.map _)
    rw [sq, ← map_mul, Module.End.mul_eq_comp, hRY, modP_p_smul]
  set U := hU.unit with hUdef
  have hUval : (U : Module.End ℤ_[p] (Y.ι → ℤ_[p])) = PY := hU.unit_spec
  -- a common commutation argument for `F^{(r)}`, `E^{(r)}`, `H`
  have key : ∀ (TM : Module.End ℤ_[p] (M.ι → ℤ_[p])) (TY : Module.End ℤ_[p] (Y.ι → ℤ_[p])),
      ι.toLin ∘ₗ TY = TM ∘ₗ ι.toLin → TM ∘ₗ Dcas M b = Dcas M b ∘ₗ TM →
      TY ∘ₗ Dcas Y b = Dcas Y b ∘ₗ TY →
      (((U⁻¹ : (Module.End ℤ_[p] (Y.ι → ℤ_[p]))ˣ) : Module.End ℤ_[p] _) ∘ₗ P') ∘ₗ TM =
        TY ∘ₗ (((U⁻¹ : (Module.End ℤ_[p] (Y.ι → ℤ_[p]))ˣ) : Module.End ℤ_[p] _) ∘ₗ P') := by
    intro TM TY hι hM hYc
    have h1 : P' ∘ₗ TM = TY ∘ₗ P' := cancel _ _ (by
      rw [← LinearMap.comp_assoc, hιP', ← LinearMap.comp_assoc, hι, LinearMap.comp_assoc, hιP',
        hP, intertwine_aeval _ _ _ hM G])
    have h2 : Commute (U : Module.End ℤ_[p] (Y.ι → ℤ_[p])) TY := by
      rw [hUval]
      exact (intertwine_aeval _ _ _ hYc G).symm
    have h3 := h2.units_inv_left
    rw [LinearMap.comp_assoc, h1, ← LinearMap.comp_assoc, ← Module.End.mul_eq_comp _ TY, h3.eq,
      Module.End.mul_eq_comp, LinearMap.comp_assoc]
  refine ⟨⟨((U⁻¹ : (Module.End ℤ_[p] (Y.ι → ℤ_[p]))ˣ) : Module.End ℤ_[p] _) ∘ₗ P',
    fun r => key _ _ (ι.comm_F r) (Fd_Dcas M r b) (Fd_Dcas Y r b),
    fun r => key _ _ (ι.comm_E r) (Ed_Dcas M r b) (Ed_Dcas Y r b),
    key _ _ ι.comm_H (H_Dcas M b) (H_Dcas Y b)⟩, ?_⟩
  change ((U⁻¹ : (Module.End ℤ_[p] (Y.ι → ℤ_[p]))ˣ) : Module.End ℤ_[p] _) ∘ₗ P' ∘ₗ ι.toLin = _
  rw [hP'ι, ← hUval, ← Module.End.mul_eq_comp, Units.inv_mul]
  rfl

/-- **(H1)** (Part H of `CSI5_the_splitting.md`). For a short exact sequence `Y →ι M →π Q` of
DP-lattices over `ℤ_[p]` and `a, b` with `a − b` a unit, if `(Ω_Y − a)² = p • R_Y` and
`(Ω_Q − b)² = p • R_Q`, there is a morphism `e : Hom M M` with `e ∘ e = e`, `e ∘ ι = ι` and
`π ∘ e = 0`. -/
theorem splitting_H1 (hSE : WeylFilt.ShortExact ι π) {a b : ℤ_[p]} (hab : IsUnit (a - b))
    (hY : ∃ R, Dcas Y a ∘ₗ Dcas Y a = (p : ℤ_[p]) • R)
    (hQ : ∃ R, Dcas Q b ∘ₗ Dcas Q b = (p : ℤ_[p]) • R) :
    ∃ e : Hom M M, WeylFilt.Hom.comp e e = e ∧ WeylFilt.Hom.comp e ι = ι ∧
      (WeylFilt.Hom.comp π e).toLin = 0 := by
  obtain ⟨E, hE⟩ := exists_retraction hSE hab hY hQ
  have hπι : π.toLin ∘ₗ ι.toLin = 0 := by
    refine LinearMap.ext fun y => ?_
    have : ι.toLin y ∈ LinearMap.ker π.toLin := hSE.exact ▸ LinearMap.mem_range_self _ y
    exact this
  refine ⟨WeylFilt.Hom.comp ι E, WeylFilt.Hom.ext' ?_, WeylFilt.Hom.ext' ?_, ?_⟩
  · change (ι.toLin ∘ₗ E.toLin) ∘ₗ (ι.toLin ∘ₗ E.toLin) = ι.toLin ∘ₗ E.toLin
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc E.toLin, hE, LinearMap.id_comp]
  · change (ι.toLin ∘ₗ E.toLin) ∘ₗ ι.toLin = ι.toLin
    rw [LinearMap.comp_assoc, hE, LinearMap.comp_id]
  · change π.toLin ∘ₗ (ι.toLin ∘ₗ E.toLin) = 0
    rw [← LinearMap.comp_assoc, hπι, LinearMap.zero_comp]

/-- **(H2)** (Part H of `CSI5_the_splitting.md`). Under the hypotheses of Part H,
`M ≅ Y ⊕ Q`: `Nonempty (Doubling.Iso M (Lemma35.dsum Y Q))`. The isomorphism is
`x ↦ (E x, π x)` for the retraction `E` of `exists_retraction`. -/
theorem splitting_H2 (hSE : WeylFilt.ShortExact ι π) {a b : ℤ_[p]} (hab : IsUnit (a - b))
    (hY : ∃ R, Dcas Y a ∘ₗ Dcas Y a = (p : ℤ_[p]) • R)
    (hQ : ∃ R, Dcas Q b ∘ₗ Dcas Q b = (p : ℤ_[p]) • R) :
    Nonempty (Doubling.Iso M (Lemma35.dsum Y Q)) := by
  obtain ⟨E, hE⟩ := exists_retraction hSE hab hY hQ
  have hE' : ∀ y, E.toLin (ι.toLin y) = y := fun y => LinearMap.congr_fun hE y
  have hπι : ∀ y, π.toLin (ι.toLin y) = 0 := fun y => by
    have : ι.toLin y ∈ LinearMap.ker π.toLin := hSE.exact ▸ LinearMap.mem_range_self _ y
    exact this
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π.toLin LinearMap.id hSE.surj
  have hs' : ∀ q, π.toLin (s q) = q := fun q => LinearMap.congr_fun hs q
  obtain ⟨g, hg⟩ : ∃ g : ((Lemma35.dsum Y Q).ι → ℤ_[p]) →ₗ[ℤ_[p]] (M.ι → ℤ_[p]),
      ∀ z : (Lemma35.dsum Y Q).ι → ℤ_[p], g z = ι.toLin (z ∘ Sum.inl) + (s (z ∘ Sum.inr) -
        ι.toLin (E.toLin (s (z ∘ Sum.inr)))) :=
    ⟨ι.toLin ∘ₗ (Lemma35.fstHom Y Q).toLin +
      (s - ι.toLin ∘ₗ E.toLin ∘ₗ s) ∘ₗ (Lemma35.sndHom Y Q).toLin, fun z => rfl⟩
  refine ⟨Doubling.Iso.ofInverse (pairHom E π) g ?_ ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, pairHom_apply, hg]
    change ι.toLin (E.toLin x) + (s (π.toLin x) - ι.toLin (E.toLin (s (π.toLin x)))) = x
    have hd : x - s (π.toLin x) ∈ LinearMap.ker π.toLin := by
      rw [LinearMap.mem_ker, map_sub, hs', sub_self]
    rw [← hSE.exact] at hd
    obtain ⟨y, hy⟩ := hd
    have h1 : ι.toLin (E.toLin (x - s (π.toLin x))) = x - s (π.toLin x) := by
      rw [← hy, hE']
    rw [map_sub, map_sub] at h1
    rw [← sub_eq_zero]
    rw [show ι.toLin (E.toLin x) + (s (π.toLin x) - ι.toLin (E.toLin (s (π.toLin x)))) - x =
      (ι.toLin (E.toLin x) - ι.toLin (E.toLin (s (π.toLin x)))) - (x - s (π.toLin x)) by abel,
      h1, sub_self]
  · refine LinearMap.ext fun z => funext fun i => ?_
    cases i with
    | inl i =>
      rw [LinearMap.comp_apply, LinearMap.id_apply, pairHom_apply, hg]
      simp only [Sum.elim_inl, map_add, map_sub, hE', sub_self, add_zero]
      rfl
    | inr i =>
      rw [LinearMap.comp_apply, LinearMap.id_apply, pairHom_apply, hg]
      simp only [Sum.elim_inr, map_add, map_sub, hπι, hs', sub_zero, zero_add]
      rfl

end split

end ColouredSand.OddTwist
