module

public import RequestProject.TheoremB.TorsionTensor
public import RequestProject.TheoremB.Count

/-!
# (B3) Theorem B: the Sylow `p`-subgroup of the sandpile group of `H(d,q)` for `p > d`

This file corresponds to **(B3) Theorem B** of `CS3_theorem_B.md`.

## Encoding

* The sandpile group `K(H(d,q))` is `sandpile d q = Submodule.torsion ℤ (coker L)`, the torsion
  subgroup of `coker L = ((Fin d → Fin q) → ℤ) ⧸ range L` (`RequestProject/TheoremB/Basic.lean`).
* `Syl_p K` is `AddCommGroup.primaryComponent (sandpile d q) p` (elements of `p`-power order).
* `e = v_p(q)` is `padicValNat p q`.
* The direct sum `⨁_{v=1}^{d} (ℤ/p^{ev})^{n_v}` is the finite product over
  `s : Σ v : Fin d, Fin (n_{v+1})` of `ZMod (p ^ (e * (s.1 + 1)))`: the element `v : Fin d`
  stands for `v + 1 ∈ {1, …, d}`, and `n_v = nCount d q v` (`RequestProject/TheoremB/Count.lean`).
* "`≅`" is an additive group isomorphism `≃+`.

## Proof

As in the file, but cancelling the free summand by taking torsion:
`Syl_p K ≅ Syl_p (coker L) ≅ torsion (ℤ_[p] ⊗ coker L)` (`torsion_tensor_equiv_syl`, from (B1));
Theorem A (`ColouredSand.Splitting.theorem_A`) splits `coker L`; (B1) (`cokerBaseChangePi`)
identifies `ℤ_[p] ⊗ X_q(d−j, j)` with the `ℤ_[p]`-cokernel of `q (j + H) + U`; Theorem E
(`ColouredSand.Strings.theorem_E`) computes it; `expA_eq` shows `A_k = e (m − 2k + 1)`; and
`bigIdxEquiv` (with the count `card_fiber_gIdx`, which uses (B2)) collects the factors.
-/

@[expose] public section

open Finset TensorProduct

namespace ColouredSand.TheoremB

open ColouredSand.Strings ColouredSand.Splitting

variable {p : ℕ} [hp : Fact p.Prime]

/-- `ℤ_[p] ⧸ (p^n) ≅ ℤ/p^n`. -/
noncomputable def padicQuotZMod (n : ℕ) :
    (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ n}) ≃+* ZMod (p ^ n) :=
  (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := PadicInt.toZModPow n) fun z =>
      ⟨(z.val : ℤ_[p]), by simp⟩)

omit hp in
/-- `A_k = e (m − 2k + 1)` when `1 ≤ c + r ≤ d < p` for all `r ∈ [k, m − k]`. -/
lemma expA_eq {q c m k d : ℕ} (hcm : c + m ≤ d) (hpd : d < p) (hk : 2 * k ≤ m)
    (hck : (c, k) ≠ (0, 0)) :
    expA p (q : ℤ) c m k = padicValNat p q * (m - 2 * k + 1) := by
  have hc : c ≠ 0 ∨ k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hck (by rw [h.1, h.2])
  unfold expA
  have hterm : ∀ r ∈ Icc k (m - k), padicValInt p (q : ℤ) + padicValNat p (c + r) =
      padicValNat p q := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    rw [padicValInt.of_nat, padicValNat.eq_zero_of_not_dvd (n := c + r) (fun h =>
      absurd (Nat.le_of_dvd (by omega) h) (by omega)), add_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_comm]
  congr 1
  omega

/-- A product of cyclic modules `∏ ℤ_[p] ⧸ (p^{Aₜ})` is torsion. -/
lemma torsion_pi_quot_eq_top {T : Type*} [Fintype T] (A : T → ℕ) :
    Submodule.torsion ℤ_[p] ((t : T) → ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ A t}) = ⊤ := by
  classical
  refine torsion_eq_top_of_smul (∏ t, (p : ℤ_[p]) ^ A t)
    (mem_nonZeroDivisors_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun t _ =>
      pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))) fun x => funext fun t => ?_
  simp only [Pi.smul_apply, Pi.zero_apply]
  rw [← Finset.mul_prod_erase _ _ (mem_univ t), mul_comm, mul_smul]
  have : ((p : ℤ_[p]) ^ A t) • x t = 0 := by
    induction x t using Submodule.Quotient.induction_on with
    | H z =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  rw [this, smul_zero]

/-- (B1) for the pieces: `ℤ_[p] ⊗ X_q(m, c) ≅ coker (q (c + H) + U)` over `ℤ_[p]`. -/
noncomputable def pieceBaseChange (q m c : ℕ) :
    (ℤ_[p] ⊗[ℤ] Xq q m c) ≃ₗ[ℤ_[p]] B m ℤ_[p] ⧸ LinearMap.range
      (((q : ℤ) : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p]) :=
  cokerBaseChangePi (Mq q m c) _ (fun f => by
    funext S
    simp [opM])

/-- **(B3) Theorem B.**  Let `d ≥ 1`, let `p > d` be a prime dividing `q`, `q ≥ 2`, and
`e = v_p(q)`.  Then `Syl_p K(H(d,q)) ≅ ⨁_{v=1}^{d} (ℤ/p^{ev})^{n_v}` with
`n_v = Σ_{j + 2k = d + 1 − v, (j,k) ≠ (0,0)} C(d,j) (q−2)^j b(k,v)`.

Encoding: `K(H(d,q)) = sandpile d q` is the torsion subgroup of `coker L`; `Syl_p` is
`AddCommGroup.primaryComponent`; the direct sum is the product over
`s : Σ v : Fin d, Fin (n_{v+1})` of `ZMod (p ^ (e * (s.1 + 1)))` (`v : Fin d` stands for
`v + 1`); `n_v = nCount d q v`. -/
theorem theorem_B (d q p : ℕ) [Fact p.Prime] (hd : 1 ≤ d) (hpd : d < p) (hpq : p ∣ q)
    (hq : 2 ≤ q) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((s : Σ v : Fin d, Fin (nCount d q (v + 1))) → ZMod (p ^ (padicValNat p q * (s.1 + 1))))) := by
  classical
  set e := padicValNat p q with he
  have he1 : 1 ≤ padicValInt p (q : ℤ) := by
    rw [padicValInt.of_nat]
    exact one_le_padicValNat_of_dvd (by omega) hpq
  -- Step 1: `Syl_p K ≅ torsion (ℤ_[p] ⊗ coker L)`
  let E1 : sylSub p (sandpile d q) ≃+ Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] cokerL d q) :=
    (sylTorsion (p := p) (cokerL d q)).toAddEquiv.trans
      (torsion_tensor_equiv_syl (p := p) (cokerL d q)).some.symm
  -- Step 2: Theorem A, base change, and torsion of a product
  obtain ⟨EA⟩ := theorem_A d q hq
  let X : PieceIdx d q → Type := fun σ => Xq q (d - σ.1) σ.1
  let E2 : Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] cokerL d q) ≃ₗ[ℤ_[p]]
      ∀ σ : PieceIdx d q, Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] X σ) :=
    (torsionEquiv ((LinearEquiv.baseChange ℤ ℤ_[p] _ _ EA).trans
      (TensorProduct.piRight ℤ ℤ_[p] ℤ_[p] X))).trans (torsionPi _)
  -- Step 3: each piece, by (B1) and Theorem E
  let Q : (σ : PieceIdx d q) → StrIdxE σ.1 (d - σ.1) → Type := fun σ t =>
    ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ expA p (q : ℤ) σ.1 (d - σ.1) t.1}
  have hE : ∀ σ : PieceIdx d q, Nonempty ((ℤ_[p] ⊗[ℤ] X σ) ≃ₗ[ℤ_[p]]
      ((Fin (if (σ.1 : ℕ) = 0 then 1 else 0) → ℤ_[p]) × ((t : StrIdxE σ.1 (d - σ.1)) → Q σ t))) :=
    fun σ => by
      obtain ⟨EE⟩ := theorem_E p (q : ℤ) he1 σ.1 (d - σ.1) (by omega)
      exact ⟨(pieceBaseChange q (d - σ.1) σ.1).trans EE⟩
  let E3 : (∀ σ : PieceIdx d q, Submodule.torsion ℤ_[p] (ℤ_[p] ⊗[ℤ] X σ)) ≃ₗ[ℤ_[p]]
      ∀ σ : PieceIdx d q, (t : StrIdxE σ.1 (d - σ.1)) → Q σ t :=
    LinearEquiv.piCongrRight fun σ => (torsionEquiv (hE σ).some).trans
      (torsionProdFree (torsion_pi_eq_bot _) (torsion_pi_quot_eq_top _))
  -- Step 4: `A_k = e (m − 2k + 1)` and `ℤ_[p] ⧸ (p^n) ≅ ℤ/p^n`
  let Z : (σ : PieceIdx d q) → StrIdxE σ.1 (d - σ.1) → Type := fun σ t =>
    ZMod (p ^ (e * (d - σ.1 - 2 * t.1.1.1 + 1)))
  have hA : ∀ (σ : PieceIdx d q) (t : StrIdxE σ.1 (d - σ.1)),
      p ^ expA p (q : ℤ) σ.1 (d - σ.1) t.1 = p ^ (e * (d - σ.1 - 2 * t.1.1.1 + 1)) := by
    intro σ t
    have h1 := t.1.1.2
    rw [expA_eq (d := d) (by omega) hpd (by omega) t.1.2]
  let E4 : (∀ σ : PieceIdx d q, (t : StrIdxE σ.1 (d - σ.1)) → Q σ t) ≃+
      ∀ σ : PieceIdx d q, (t : StrIdxE σ.1 (d - σ.1)) → Z σ t :=
    AddEquiv.piCongrRight fun σ => AddEquiv.piCongrRight fun t =>
      ((padicQuotZMod _).trans (ZMod.ringEquivCongr (hA σ t))).toAddEquiv
  -- Step 5: collect the factors
  let E5 : (∀ σ : PieceIdx d q, (t : StrIdxE σ.1 (d - σ.1)) → Z σ t) ≃+
      ((x : BigIdx d q) → Z x.1 x.2) :=
    (LinearEquiv.piCurry ℤ Z).symm.toAddEquiv
  let φ : (Σ v : Fin d, Fin (nCount d q (v + 1))) → Type := fun s =>
    ZMod (p ^ (e * (s.1 + 1)))
  let E6 : ((x : BigIdx d q) → Z x.1 x.2) ≃+ ((s : Σ v : Fin d, Fin (nCount d q (v + 1))) → φ s) :=
    (LinearEquiv.piCongrLeft ℤ φ (bigIdxEquiv hd)).toAddEquiv
  exact ⟨E1.trans ((E2.trans E3).toAddEquiv.trans (E4.trans (E5.trans E6)))⟩

end ColouredSand.TheoremB
