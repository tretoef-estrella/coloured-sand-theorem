module

public import RequestProject.ThmH.Dictionary
public import RequestProject.ThmH.FreeTorsion
public import RequestProject.Families.All
public import RequestProject.Splitting.All
public import RequestProject.Corollaries.Valuation

/-!
# `CSH1_theorem_H_the_prime_two.md`, Part T — Theorem H (the prime 2, every `d`, every even `q`)

Namespace `ColouredSand.ThmH`.

Encodings:

* `ℤ_[2]` is Mathlib's `PadicInt 2`; `v_2(q)` is `padicValNat 2 q`.
* The cokernel of an endomorphism `f` of `M` is `M ⧸ LinearMap.range f`; `B m R` and
  `ColouredSand.Strings.opM m R q c = q • (c • id + H) + U` are the Coloured Sand objects, and
  `X_q(m,c) = ColouredSand.Splitting.Xq q m c`, `K(H(d,q)) = ColouredSand.TheoremB.sandpile d q`.
* `X^{(α)}(λ, i)` is this project's `FamilyGroup.X (Families.ds λ) α i`, the cokernel over `ℤ_[2]`
  of `σ^{(α)}_i` on `T(λ)` (identified with the cokernel of `Families.sigL ℤ_[2] λ α i` by
  `Families.B2Z`).  The multiplicities `m_λ(m)` are encoded by the list `FamDec.L m`: the direct
  sum `⊕_λ X(λ, ·)^{m_λ(m)}` is the product over the positions `j : Fin (FamDec.L m).length`.
* `Syl_2 G` is `AddCommGroup.primaryComponent G 2`, `tors X` is `Submodule.torsion ℤ X`,
  `ℤ_2^{[c=0]}` is `Fin (if c = 0 then 1 else 0) → ℤ_[2]`; "`≅`" of abelian groups is `≃+`.
* The direct sum over `j ≤ d` with multiplicities `C(d,j)(q−2)^j` in (T4) is the product over
  `σ : Σ j : Fin (d + 1), Fin (d.choose j * (q − 2) ^ j)`, as in Corollary 1
  (`ColouredSand.Corollaries.corollary1_whole`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmH

open ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB ColouredSand.Corollaries
open FamDec Families

/-! ### (T1) -/

/-- On a summand `T(λ)` of `V^{⊗m}`, `F + 2^{e−1}((m + 2c) − H) = sigL λ e (c + (m − λ)/2)`
(auxiliary for (T1) of `CSH1_theorem_H_the_prime_two.md`; uses `m − λ` even, C31 (M3)). -/
lemma opT_eq_sigL (m e c lam : ℕ) (h : lam ∈ L m) :
    (Filt.T ℤ_[2] lam).Fd 1 + ((2 : ℤ_[2]) ^ (e - 1)) •
        (((m : ℤ_[2]) + 2 * c) • LinearMap.id - DPLattice.H (Filt.T ℤ_[2] lam)) =
      sigL ℤ_[2] lam e (c + (m - lam) / 2) := by
  have hm : ((m : ℤ_[2]) + 2 * c) = (lam : ℤ_[2]) + 2 * ((c + (m - lam) / 2 : ℕ) : ℤ_[2]) := by
    have := congrArg (fun z : ℕ => (z : ℤ_[2])) (add_two_mul_half m lam h)
    push_cast at this ⊢
    rw [← this]
    ring
  rw [sigL, hm]

/-- **(T1)** of `CSH1_theorem_H_the_prime_two.md` (explicit equivalence, from an isomorphism
`u : V^{⊗m} ≅ ⊕_j T(λ_j)` as given by C31 `FamDec.D2`): for `e ≥ 1`,
`coker (opM m ℤ_[2] (2^e) c) ≃ₗ[ℤ_[2]] Π_j X^{(e)}(λ_j, c + (m − λ_j)/2)`, `λ_j = (L m).get j`.
Built from (D3), `Families.Q1` (`dsumMap_exists`), `Families.Q2` (`isoEquiv`) and
`Families.B2Z` (`sigEquivZ`). -/
def T1equiv (e m c : ℕ) (he : 1 ≤ e)
    (u : Doubling.Iso (Filt.tpow ℤ_[2] m) (Step36.dsumList ((L m).map (Filt.T ℤ_[2])))) :
    (B m ℤ_[2] ⧸ LinearMap.range (opM m ℤ_[2] ((2 : ℤ_[2]) ^ e) (c : ℤ_[2]))) ≃ₗ[ℤ_[2]]
      ((j : Fin (L m).length) →
        FamilyGroup.X (ds ((L m).get j)) e (c + (m - (L m).get j) / 2)) :=
  let Θ2 := Classical.choose (dsumMap_exists (Filt.T ℤ_[2]) (L m))
  have hΘ2 := Classical.choose_spec (dsumMap_exists (Filt.T ℤ_[2]) (L m))
  let Θ := (Psi ℤ_[2] m).trans ((isoEquiv u).trans Θ2)
  let s : ℤ_[2] := (2 : ℤ_[2]) ^ (e - 1)
  let a : ℤ_[2] := (m : ℤ_[2]) + 2 * c
  let Gj : ∀ j : Fin (L m).length, Module.End ℤ_[2] ((Filt.T ℤ_[2] ((L m).get j)).ι → ℤ_[2]) :=
    fun j => sigL ℤ_[2] ((L m).get j) e (c + (m - (L m).get j) / 2)
  have hD3 : ∀ f, Psi ℤ_[2] m (opM m ℤ_[2] ((2 : ℤ_[2]) ^ e) (c : ℤ_[2]) f) =
      (Filt.tpow ℤ_[2] m).Fd 1 (Psi ℤ_[2] m f) +
        s • (a • Psi ℤ_[2] m f - DPLattice.H (Filt.tpow ℤ_[2] m) (Psi ℤ_[2] m f)) := fun f => by
    have := LinearMap.congr_fun (D3 ℤ_[2] m e c he) f
    simpa using this
  have hu : ∀ y, isoEquiv u ((Filt.tpow ℤ_[2] m).Fd 1 y +
        s • (a • y - DPLattice.H (Filt.tpow ℤ_[2] m) y)) =
      (Step36.dsumList ((L m).map (Filt.T ℤ_[2]))).Fd 1 (isoEquiv u y) +
        s • (a • isoEquiv u y -
          DPLattice.H (Step36.dsumList ((L m).map (Filt.T ℤ_[2]))) (isoEquiv u y)) := fun y => by
    have hF := LinearMap.congr_fun (u.hom.comm_F 1) y
    have hH := LinearMap.congr_fun u.hom.comm_H y
    simp only [LinearMap.comp_apply] at hF hH
    change u.hom.toLin _ = _
    rw [map_add, map_smul, map_sub, map_smul, hF, hH]
    rfl
  have hΘ : ∀ f, (LinearMap.pi fun j => Gj j ∘ₗ LinearMap.proj j) (Θ f) =
      Θ (opM m ℤ_[2] ((2 : ℤ_[2]) ^ e) (c : ℤ_[2]) f) := fun f => by
    simp only [Θ, LinearEquiv.trans_apply, hD3, hu]
    rw [map_add, map_smul, map_sub, map_smul, hΘ2.1, hΘ2.2]
    funext j
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Gj]
    rw [← opT_eq_sigL m e c _ (List.get_mem _ _)]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, s, a]
    rfl
  (cokerEquivOfConj _ _ Θ Θ hΘ).trans
    ((Submodule.quotEquivOfEq _ _ (range_pi_comp_proj Gj)).trans
      ((Submodule.quotientPi _).trans
        (LinearEquiv.piCongrRight fun j =>
          sigEquivZ ((L m).get j) e (c + (m - (L m).get j) / 2))))

/-- **(T1)** of `CSH1_theorem_H_the_prime_two.md` (the `ℤ_2`-form, `q = 2^e`): for `e ≥ 1`, `m`,
`c : ℕ`,
`coker (opM m ℤ_[2] (2^e) c) ≃ₗ[ℤ_[2]] Π_{j : Fin (L m).length} X^{(e)}(λ_j, c + (m − λ_j)/2)`,
`λ_j = (FamDec.L m).get j`.  From (D3), C31 `FamDec.D2` (instantiated at
`ℤ_[2] → ZMod 2` as in `Families.T2`), `Families.Q1`, `Families.Q2` and `Families.B2Z`. -/
theorem T1 (e m c : ℕ) (he : 1 ≤ e) :
    Nonempty ((B m ℤ_[2] ⧸ LinearMap.range (opM m ℤ_[2] ((2 : ℤ_[2]) ^ e) (c : ℤ_[2]))) ≃ₗ[ℤ_[2]]
      ((j : Fin (L m).length) →
        FamilyGroup.X (ds ((L m).get j)) e (c + (m - (L m).get j) / 2))) := by
  obtain ⟨u⟩ := FamDec.D2 (φ := (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)) Lift2.Z1.1 Lift2.Z1.2.1
    Lift2.Z1.2.2.1 Lift2.Z1.2.2.2 Twist.C3_hyp.2.2.2.2.1 m
  exact ⟨T1equiv e m c he u⟩

/-! ### (T2) -/

/-- **(T2)** of `CSH1_theorem_H_the_prime_two.md` (any even `q`): for `q` with
`1 ≤ v_2(q)`, and `m`, `c : ℕ`,
`coker (opM m ℤ_[2] q c) ≃ₗ[ℤ_[2]] Π_j X^{(v_2 q)}(λ_j, c + (m − λ_j)/2)`.
The hypothesis `q ≥ 1` of the file is omitted: it follows from `1 ≤ v_2(q)` (as
`v_2(0) = 0`), so the statement is the same.  From the rescaling lemma
`ColouredSand.Splitting.opM_coker_depends_only_on_valuations` (`p = 2`, `q' = 2^e`, `c' = c`)
and (T1). -/
theorem T2 (q m c : ℕ) (hv : 1 ≤ padicValNat 2 q) :
    Nonempty ((B m ℤ_[2] ⧸
        LinearMap.range (opM m ℤ_[2] ((q : ℤ) : ℤ_[2]) ((c : ℤ) : ℤ_[2]))) ≃ₗ[ℤ_[2]]
      ((j : Fin (L m).length) →
        FamilyGroup.X (ds ((L m).get j)) (padicValNat 2 q) (c + (m - (L m).get j) / 2))) := by
  set e := padicValNat 2 q with he
  have hq0 : q ≠ 0 := by rintro rfl; simp [he] at hv
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq0
  obtain ⟨E⟩ := opM_coker_depends_only_on_valuations (p := 2) m (q : ℤ) (c : ℤ)
    ((2 : ℤ) ^ e) (c : ℤ)
    (fun s _ => by simp [mul_eq_zero, hq0])
    (fun s _ => by
      by_cases hcs : (c : ℤ) + s = 0
      · rw [hcs, mul_zero, mul_zero]
      · rw [padicValInt.mul hqz hcs, padicValInt.mul (pow_ne_zero _ two_ne_zero) hcs,
          padicValInt.of_nat, show (2 : ℤ) ^ e = ((2 ^ e : ℕ) : ℤ) by push_cast; rfl,
          padicValInt.of_nat, padicValNat.prime_pow])
  obtain ⟨E1⟩ := T1 e m c hv
  have hcast : opM m ℤ_[2] (((2 : ℤ) ^ e : ℤ) : ℤ_[2]) ((c : ℤ) : ℤ_[2]) =
      opM m ℤ_[2] ((2 : ℤ_[2]) ^ e) (c : ℤ_[2]) := by push_cast; rfl
  rw [hcast] at E
  exact ⟨E.trans E1⟩

/-! ### (T3) -/

/-- **(T3)** of `CSH1_theorem_H_the_prime_two.md` (Theorem H, first statement): for `q ≥ 1` even,
`m`, `c : ℕ`,
`ℤ_2^{[c=0]} ⊕ Syl_2 (tors X_q(m,c)) ≅ ⊕_j X^{(v_2 q)}(λ_j, c + (m − λ_j)/2)`.
From `ColouredSand.Corollaries.sylTorsXq_equiv` (`Syl_2 (tors X_q(m,c))` is the `ℤ_[2]`-torsion
of the cokernel of (T2)), the splitting `freeTorsionEquiv` of that cokernel as
`ℤ_[2]^{[c=0]} ⊕ torsion`, and (T2). -/
theorem T3 (q m c : ℕ) (hq : 1 ≤ q) (heven : Even q) :
    Nonempty (((Fin (if c = 0 then 1 else 0) → ℤ_[2]) ×
        AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq q m c)) 2) ≃+
      ((j : Fin (L m).length) →
        FamilyGroup.X (ds ((L m).get j)) (padicValNat 2 q) (c + (m - (L m).get j) / 2))) := by
  have hv : 1 ≤ padicValNat 2 q :=
    one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.1 heven)
  have h1 := sylTorsXq_equiv 2 q m c
  have h2 := T2 q m c hv
  obtain ⟨e1⟩ := h1
  obtain ⟨e2⟩ := h2
  have hq0 : (q : ℤ_[2]) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  exact ⟨((AddEquiv.refl _).prodCongr e1).trans
    ((freeTorsionEquiv m hq0 c).toAddEquiv.trans e2.toAddEquiv)⟩

/-! ### (T4) -/

/-- `Π σ, (F σ × S σ) ≃+ (Π σ, F σ) × (Π σ, S σ)` (auxiliary for (T4)). -/
def piProdAddEquiv {ι : Type*} (F S : ι → Type*) [∀ i, AddCommGroup (F i)]
    [∀ i, AddCommGroup (S i)] :
    ((i : ι) → F i × S i) ≃+ (((i : ι) → F i) × ((i : ι) → S i)) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun g i := (g.1 i, g.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The index set of Corollary 1 with the multiplicity `[j = 0]` has exactly one element
(auxiliary for (T4)). -/
lemma card_sigma_free (d q : ℕ) :
    Fintype.card (Σ σ : (Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))),
      Fin (if (σ.1 : ℕ) = 0 then 1 else 0)) = 1 := by
  rw [Fintype.card_sigma, Fintype.sum_sigma, Fin.sum_univ_succ]
  simp

set_option synthInstance.maxHeartbeats 200000 in
/-- **(T4)** of `CSH1_theorem_H_the_prime_two.md` (Theorem H, second statement): for `q ≥ 2` even,
`ℤ_2 ⊕ Syl_2 K(H(d,q)) ≅ ⊕_{j=0}^{d} ⊕_λ X^{(v_2 q)}(λ, j + (d − j − λ)/2)^{C(d,j)(q−2)^j m_λ(d−j)}`,
the multiplicities being encoded by the product over
`σ : Σ j : Fin (d+1), Fin (C(d,j)(q−2)^j)` and over the positions of `FamDec.L (d − j)`.
More general than the file: the hypothesis `d ≥ 1` is not needed (the case `d = 0` holds too).
From `ColouredSand.Corollaries.corollary1_whole` at `p = 2` and (T3) (with `2^{v_2 q}`) on each
factor; only the factor with `j = 0` has `c = 0`, and its `ℤ_[2]` is the `ℤ_[2]` on the left. -/
theorem T4 (d q : ℕ) (hq : 2 ≤ q) (heven : Even q) :
    Nonempty ((ℤ_[2] × AddCommGroup.primaryComponent (sandpile d q) 2) ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (t : Fin (L (d - σ.1)).length) →
          FamilyGroup.X (ds ((L (d - σ.1)).get t)) (padicValNat 2 q)
            (σ.1 + (d - σ.1 - (L (d - σ.1)).get t) / 2))) := by
  set e := padicValNat 2 q with he
  have hv : 1 ≤ e := one_le_padicValNat_of_dvd (by omega) (even_iff_two_dvd.1 heven)
  obtain ⟨EA⟩ := corollary1_whole 2 d q hq
  rw [← he] at EA
  let ι := Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))
  let F : ι → Type := fun σ => Fin (if (σ.1 : ℕ) = 0 then 1 else 0) → ℤ_[2]
  let S : ι → Type := fun σ =>
    AddCommGroup.primaryComponent (Submodule.torsion ℤ (Xq (2 ^ e) (d - σ.1) σ.1)) 2
  have hfac : ∀ σ : ι, Nonempty ((F σ × S σ) ≃+
      ((t : Fin (L (d - σ.1)).length) →
        FamilyGroup.X (ds ((L (d - σ.1)).get t)) e
          (σ.1 + (d - σ.1 - (L (d - σ.1)).get t) / 2))) := fun σ => by
    have h := T3 (2 ^ e) (d - σ.1) σ.1 (Nat.one_le_two_pow)
      ((Nat.even_pow' (by omega)).2 even_two)
    rw [padicValNat.prime_pow] at h
    exact h
  obtain ⟨hU⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 (card_sigma_free d q)
  let eF : ((σ : ι) → F σ) ≃+ ℤ_[2] :=
    (LinearEquiv.piCurry ℤ_[2] (fun (σ : ι) (_ : Fin (if (σ.1 : ℕ) = 0 then 1 else 0)) =>
      ℤ_[2])).symm.toAddEquiv.trans
      (@LinearEquiv.funUnique _ ℤ_[2] ℤ_[2] hU _ _ _).toAddEquiv
  exact ⟨((eF.symm.prodCongr EA).trans (piProdAddEquiv F S).symm).trans
    (AddEquiv.piCongrRight fun σ => (hfac σ).some)⟩

/-! ### (T5) -/

/-- Transport of `X^{(α)}(λ, i)` along an equality of `i` (auxiliary for (T5)). -/
def castXAdd {ds : List Bool} {α a b : ℕ} (h : a = b) :
    FamilyGroup.X ds α a ≃+ FamilyGroup.X ds α b := by
  subst h; exact AddEquiv.refl _

/-- **(T5)** of `CSH1_theorem_H_the_prime_two.md`, the exponent: for `q = 2`, `v_2(q) = 1`. -/
theorem T5_exponent : padicValNat 2 2 = 1 := padicValNat_self

/-- **(T5)** of `CSH1_theorem_H_the_prime_two.md` (the case `q = 2`, the cube `Q_d = H(d,2)`):
(T4) has only the term `j = 0` (since `(q − 2)^j = 0^j`) and the exponent is `v_2(2) = 1`, so
`ℤ_2 ⊕ Syl_2 K(H(d,2)) ≅ Π_{t : Fin (L d).length} X^{(1)}(λ_t, (d − λ_t)/2)`, as in this project's
`Families.T2` for `K(Q_d)`.  Proved from (T4) (for every `d`, including `d = 0`). -/
theorem T5 (d : ℕ) :
    Nonempty ((ℤ_[2] × AddCommGroup.primaryComponent (sandpile d 2) 2) ≃+
      ((t : Fin (L d).length) →
        FamilyGroup.X (ds ((L d).get t)) 1 ((d - (L d).get t) / 2))) := by
  obtain ⟨E⟩ := T4 d 2 le_rfl even_two
  rw [T5_exponent] at E
  let ι := Σ j : Fin (d + 1), Fin (d.choose j * (2 - 2) ^ (j : ℕ))
  have hcard : Fintype.card ι = 1 := by
    rw [Fintype.card_sigma, Fin.sum_univ_succ]
    simp
  obtain ⟨hU⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 hcard
  have h0 : ∀ σ : ι, (σ.1 : ℕ) = 0 := fun σ => by
    obtain ⟨⟨j, hj⟩, r⟩ := σ
    rcases Nat.eq_zero_or_pos j with h | h
    · exact h
    · exfalso
      have := r.2
      simp [Nat.zero_pow h] at this
  have key : ∀ k : ℕ, k = 0 → Nonempty (((t : Fin (L (d - k)).length) →
      FamilyGroup.X (ds ((L (d - k)).get t)) 1 (k + (d - k - (L (d - k)).get t) / 2)) ≃+
      ((t : Fin (L d).length) → FamilyGroup.X (ds ((L d).get t)) 1 ((d - (L d).get t) / 2))) :=
    fun k hk => by
      subst hk
      simp only [Nat.sub_zero]
      exact ⟨AddEquiv.piCongrRight fun t => castXAdd (zero_add _)⟩
  exact ⟨E.trans ((@AddEquiv.piUnique ι _ _ hU).trans (key _ (h0 _)).some)⟩

end ColouredSand.ThmH
