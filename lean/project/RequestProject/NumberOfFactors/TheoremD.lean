module

public import RequestProject.NumberOfFactors.RankModP
public import RequestProject.TheoremB.All

/-!
# (D3) Theorem D: the number of cyclic factors

This file corresponds to **(D3) Theorem D** of `CS5_theorem_D_number_of_factors.md`.

## Encoding

* `H(d,q)`, its Laplacian `L`, `coker L = cokerL d q` and the sandpile group
  `K(H(d,q)) = sandpile d q` (the torsion subgroup of `coker L`) are those of
  `RequestProject/Splitting/Basic.lean` and `RequestProject/TheoremB/Basic.lean`.
* `Syl_p K(H(d,q))` is Mathlib's `AddCommGroup.primaryComponent (sandpile d q) p` (the elements
  of `p`-power order), as in `RequestProject/TheoremB`.
* **Number of cyclic factors.**  For a finite abelian `p`-group `G ≅ ⨁ ℤ/p^{e_i}` (`e_i ≥ 1`) the
  number of cyclic factors is `dim_{𝔽_p} (G ⊗ 𝔽_p)`, since `ℤ/p^e ⊗ 𝔽_p ≅ 𝔽_p`.  The file asks
  for `Module.finrank (ZMod p) (G ⊗[ℤ] ZMod p)`; Mathlib puts the `ZMod p`-module structure on
  the base change `ZMod p ⊗[ℤ] G` (scalars on the left), not on `G ⊗[ℤ] ZMod p`, so the main
  statement `theorem_D` is about `Module.finrank (ZMod p) (ZMod p ⊗[ℤ] G)`, and `theorem_D'`
  states the same for `G ⊗[ℤ] ZMod p` in the form `G ⊗[ℤ] ZMod p ≅ (ZMod p)^N` (as groups).
* `N = ∑_{j=0}^{d} C(d,j) (q−2)^j (2^{d−j} − ρ_p(d−j)) − 1` is written in `ℕ`; the inner
  subtraction is harmless since `ρ_p(m) = rank U ≤ 2^m`, and the outer one since the sum is the
  dimension of `coker L ⊗ 𝔽_p ≅ 𝔽_p ⊕ (K ⊗ 𝔽_p)`, which is at least `1`.

## Proof

As in the file: `coker L ≅ ℤ ⊕ K` (`cokerL_equiv_int_prod_sandpile`), Theorem A
(`theorem_A`), right exactness (`cokerBaseChangePi`), `q(j+H)+U ≡ U` mod `p`, and (D2)
(`rank_U_zmod`).  Finally `K ⊗ 𝔽_p ≅ Syl_p K ⊗ 𝔽_p` (`tensor_primaryComponent_equiv`).
The hypothesis `d ≥ 1` of the file is not needed.
-/

@[expose] public section

open Finset Module TensorProduct

namespace ColouredSand.NumberOfFactors

open ColouredSand.Strings ColouredSand.Splitting ColouredSand.TheoremB

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### `𝔽_p ⊗ G ≅ 𝔽_p ⊗ Syl_p G` for finite `G` -/

/-- For a finite abelian group `G`, the inclusion `Syl_p G → G` induces an isomorphism
`𝔽_p ⊗ Syl_p G ≅ 𝔽_p ⊗ G`. -/
noncomputable def tensorPrimaryEquiv (G : Type) [AddCommGroup G] [Finite G] :
    (ZMod p ⊗[ℤ] AddCommGroup.primaryComponent G p) ≃ₗ[ZMod p] (ZMod p ⊗[ℤ] G) := by
  let D : SylData p G := sylData G
  let i : AddCommGroup.primaryComponent G p →ₗ[ℤ] G :=
    (AddCommGroup.primaryComponent G p).subtype.toIntLinearMap
  have hmem : ∀ x : G, (D.u * D.r) • x ∈ AddCommGroup.primaryComponent G p := by
    intro x
    rw [mem_primaryComponent_iff]
    refine ⟨D.a, ?_⟩
    have := proj_mem D x
    rw [← natCast_zsmul]
    exact_mod_cast this
  let π : G →ₗ[ℤ] AddCommGroup.primaryComponent G p :=
    { toFun := fun x => ⟨(D.u * D.r) • x, hmem x⟩
      map_add' := fun x y => by ext; simp [smul_add]
      map_smul' := fun n x => by ext; simp [smul_comm n] }
  have hπi : ∀ x, π (i x) = x := by
    intro x
    ext
    exact proj_id D x.2
  have hr : ((D.r : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]; exact D.hr
  have hip : ∀ (c : ZMod p) (x : G), c ⊗ₜ[ℤ] i (π x) = c ⊗ₜ[ℤ] x := by
    intro c x
    have hy : (D.r : ℤ) • ((1 - D.u * D.r) • x) = 0 := by
      have h1 : 1 - D.u * D.r = D.s * (p : ℤ) ^ D.a := by linarith [D.hsu]
      rw [h1, smul_smul, show (D.r : ℤ) * (D.s * (p : ℤ) ^ D.a) = D.s * ((p : ℤ) ^ D.a * D.r) by
        ring, mul_smul, card_smul_eq_zero, smul_zero]
    have hc : c = (D.r : ℤ) • (c * ((D.r : ℕ) : ZMod p)⁻¹) := by
      rw [zsmul_eq_mul, Int.cast_natCast, ← mul_assoc, mul_comm _ c, mul_assoc,
        mul_inv_cancel₀ hr, mul_one]
    have h2 : c ⊗ₜ[ℤ] ((1 - D.u * D.r) • x) = 0 := by
      rw [hc, TensorProduct.smul_tmul, hy, TensorProduct.tmul_zero]
    have h3 : x = (D.u * D.r) • x + (1 - D.u * D.r) • x := by
      rw [← add_smul]; simp
    conv_rhs => rw [h3]
    rw [TensorProduct.tmul_add, h2, add_zero]
    rfl
  refine LinearEquiv.ofLinear (i.baseChange (ZMod p)) (π.baseChange (ZMod p)) ?_ ?_
  · apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.id_apply]
      exact hip c x
    | add x y hx hy => simp only [map_add, hx, hy]
  · apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.id_apply, hπi]
    | add x y hx hy => simp only [map_add, hx, hy]

/-! ### `𝔽_p ⊗ X_q(m,c) ≅ B_m(𝔽_p) ⧸ range U` -/

/-- For `p ∣ q`: `𝔽_p ⊗ coker (q (c+H) + U) ≅ coker U` on `B_m(𝔽_p)`. -/
noncomputable def tensorXqEquiv {q : ℕ} (hpq : p ∣ q) (m c : ℕ) :
    (ZMod p ⊗[ℤ] Xq q m c) ≃ₗ[ZMod p] B m (ZMod p) ⧸ LinearMap.range (U m (ZMod p)) :=
  cokerBaseChangePi (Mq q m c) (U m (ZMod p)) (fun f => by
    funext S
    have hq : ((q : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff]; exact hpq
    simp only [U_apply, Mq_apply, algebraMap_int_eq, eq_intCast, Int.cast_add, Int.cast_mul,
      Int.cast_sum, hq, zero_mul, zero_add])

lemma finrank_coker_U (m : ℕ) :
    finrank (ZMod p) (B m (ZMod p) ⧸ LinearMap.range (U m (ZMod p))) = 2 ^ m - rho p m := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (U m (ZMod p)))
  rw [rank_U_zmod, Module.finrank_fintype_fun_eq_card, Fintype.card_finset,
    Fintype.card_fin] at h
  omega

/-! ### The dimension of `𝔽_p ⊗ coker L` -/

/-- `dim_{𝔽_p} (𝔽_p ⊗ coker L) = ∑_{j=0}^{d} C(d,j) (q−2)^j (2^{d−j} − ρ_p(d−j))`. -/
lemma finrank_tensor_cokerL {d q : ℕ} (hq : 2 ≤ q) (hpq : p ∣ q) :
    finrank (ZMod p) (ZMod p ⊗[ℤ] cokerL d q) =
      ∑ j ∈ range (d + 1), d.choose j * (q - 2) ^ j * (2 ^ (d - j) - rho p (d - j)) := by
  obtain ⟨E⟩ := theorem_A d q hq
  let E1 := LinearEquiv.baseChange ℤ (ZMod p) _ _ E
  let E2 := TensorProduct.piRight ℤ (ZMod p) (ZMod p)
    (fun σ : (Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) => Xq q (d - σ.1) σ.1)
  let E3 := LinearEquiv.piCongrRight fun σ : (Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) =>
    tensorXqEquiv p hpq (d - σ.1) σ.1
  rw [((E1.trans E2).trans E3).finrank_eq, Module.finrank_pi_fintype]
  simp only [finrank_coker_U]
  rw [Fintype.sum_sigma]
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j => d.choose j * (q - 2) ^ j * (2 ^ (d - j) - rho p (d - j)))]

/-! ### Theorem D -/

/-- The number `N` of cyclic factors in Theorem D. -/
def nFactors (p d q : ℕ) : ℕ :=
  (∑ j ∈ range (d + 1), d.choose j * (q - 2) ^ j * (2 ^ (d - j) - rho p (d - j))) - 1

/-- **(D3) Theorem D.**  Let `q ≥ 2` and `p` a prime with `p ∣ q`.  The number of cyclic factors
of the `p`-primary component `Syl_p K(H(d,q))` of the sandpile group of the Hamming graph
`H(d,q)` — i.e. `dim_{𝔽_p}` of `𝔽_p ⊗ Syl_p K(H(d,q))` — is
`N = ∑_{j=0}^{d} C(d,j) (q−2)^j (2^{d−j} − ρ_p(d−j)) − 1`.
(The file assumes `d ≥ 1`; the statement holds for all `d`.) -/
theorem theorem_D (d q : ℕ) (hq : 2 ≤ q) (hpq : p ∣ q) :
    finrank (ZMod p) (ZMod p ⊗[ℤ] AddCommGroup.primaryComponent (sandpile d q) p) =
      (∑ j ∈ range (d + 1), d.choose j * (q - 2) ^ j * (2 ^ (d - j) - rho p (d - j))) - 1 := by
  obtain ⟨⟨E⟩, hfin⟩ := cokerL_equiv_int_prod_sandpile d q (by omega)
  haveI := hfin
  rw [(tensorPrimaryEquiv p (sandpile d q)).finrank_eq, ← finrank_tensor_cokerL p hq hpq]
  let E1 := LinearEquiv.baseChange ℤ (ZMod p) _ _ E
  let E2 := TensorProduct.prodRight ℤ (ZMod p) (ZMod p) ℤ (sandpile d q)
  haveI : Module.Finite ℤ (sandpile d q) := Module.Finite.of_finite
  have h1 : finrank (ZMod p) (ZMod p ⊗[ℤ] ℤ) = 1 := by
    rw [Module.finrank_baseChange, Module.finrank_self]
  haveI : Module.Free (ZMod p) (ZMod p ⊗[ℤ] sandpile d q) := Module.Free.of_divisionRing _ _
  haveI : Module.Free (ZMod p) (ZMod p ⊗[ℤ] ℤ) := Module.Free.of_divisionRing _ _
  rw [(E1.trans E2).finrank_eq, Module.finrank_prod, h1]
  omega

/-- **(D3) Theorem D, with `G ⊗[ℤ] ZMod p`.**  Under the hypotheses of `theorem_D`,
`Syl_p K(H(d,q)) ⊗[ℤ] ZMod p ≅ (ZMod p)^N` as abelian groups, with
`N = ∑_{j=0}^{d} C(d,j) (q−2)^j (2^{d−j} − ρ_p(d−j)) − 1`. -/
theorem theorem_D' (d q : ℕ) (hq : 2 ≤ q) (hpq : p ∣ q) :
    Nonempty ((AddCommGroup.primaryComponent (sandpile d q) p ⊗[ℤ] ZMod p) ≃ₗ[ℤ]
      (Fin (nFactors p d q) → ZMod p)) := by
  obtain ⟨-, hfin⟩ := cokerL_equiv_int_prod_sandpile d q (by omega)
  haveI := hfin
  have h := theorem_D p d q hq hpq
  let b := Module.finBasisOfFinrankEq (ZMod p)
    (ZMod p ⊗[ℤ] AddCommGroup.primaryComponent (sandpile d q) p) h
  exact ⟨(TensorProduct.comm ℤ _ _).trans (b.equivFun.restrictScalars ℤ)⟩

end ColouredSand.NumberOfFactors
