module

public import RequestProject.OddSplitMove.Layers
public import RequestProject.OddPayment.TheoremA

/-!
# Part M of `CSI8_the_split_move.md`: the odd split move (Proposition 2.2 of «the odd dance»)

Notation (see `Basic.lean`): `M^S = Payment.Sys N S` (C11's module of a system), the system of the
split `G_S = Gp p (flS p r fl) (FS p r hr F) Q` on `M_S^S = Payment.Sys (NS p N) S`, and the system
with the new data `Gp p fl F (QS p r Q)` on `Payment.Sys N (S × Bool)`. As in C11's
`Payment.theorem_A` and CSI7's `theorem_Ap`, «`X ≅ Y`» is `Nonempty (X ≃ₗ[A] Y)`, `c • G` is the
scalar multiple of the operator, and `c • ⊤` is the submodule `c · M^S`.

* **(M1)** `theorem_M1`: for odd `p`, a digit `0 < r < p`, every graded family, every `Q` and every
  `c : A`,
  `M_S^S ⧸ range (c • G_S) ≃ (Fin (2 (p − 1)) → M^S ⧸ c • ⊤) ×
    (Sys N (S × Bool) ⧸ range ((c * p) • Gp p fl F (QS p r Q)))`.
  **Sign convention** (the file's "state the sign convention you choose"): `theorem_M1` uses the
  file's `QS` (with `−p^{p−2}` on the diagonal blocks) and needs `p` odd; `theorem_M1_sign` holds
  for **every** `p` (also even `p`) with `QSsign` (diagonal blocks `((−1)^p p^{p−2}) • Π(…)`, the
  coupling `K` unchanged), and `theorem_M1` is its odd case (`QSsign_of_odd`). Primality is never
  used.
* **(M2)** `corollary_M2` (`c = p^h`, as C11's `corollary_A2`).

The proof follows the report: `layer_comp_GpS` (step 1: the system in the layers is two of CSI7's
chains coupled by `p · C_{p−r}`), `coupledCokerEquiv` (steps 1–3: CSI7's row/column operations on
each chain plus one column operation for the coupling), `chainProd_layerD_gen` (the products
`Π_p`), `smul_blockGp` (the scalar bookkeeping: `c_{p−r} = (−1)^{p−r} c_0 Π_p(pf+r, pf+p)` gives
the coupling block `K`).
-/

@[expose] public section

namespace ColouredSand.OddTwist

open DirectSum
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The composite of the first `m + 1` layer operators (*Proof* of (M1) of
`CSI8_the_split_move.md`, generalizing CSI7's `chainProd_layerD` to any length):
`D 0 ⋯ D m = p^(m+1) • DSm (Q (p fl i) ⋯ Q (p fl i + m))`. -/
lemma chainProd_layerD_gen (p : ℕ) (fl : ι → ℕ) (Q : ℕ → Matrix S S A) (m : ℕ) :
    chainProd (layerD (N := N) p fl Q) m =
      (p : A) ^ (m + 1) • DSm (N := N)
        (fun i => ((List.range (m + 1)).map (fun j => Q (p * fl i + j))).prod) := by
  rw [chainProd]
  have hD : layerD (N := N) p fl Q = fun j => DSmHom A N S (fun i => (p : A) • Q (p * fl i + j)) :=
    rfl
  have hm : (List.range (m + 1)).map
      (fun j => DSmHom A N S (fun i => (p : A) • Q (p * fl i + j))) =
      ((List.range (m + 1)).map (fun j i => (p : A) • Q (p * fl i + j))).map (DSmHom A N S) := by
    rw [List.map_map]; rfl
  rw [hD, hm, ← map_list_prod, ← DSm_smul]
  change DSm _ = DSm _
  congr 1
  funext i
  have he := map_list_prod (Pi.evalMonoidHom (fun _ : ι => Matrix S S A) i)
    ((List.range (m + 1)).map (fun j i => (p : A) • Q (p * fl i + j)))
  simp only [Pi.evalMonoidHom_apply, List.map_map, Function.comp_def] at he
  rw [Pi.smul_apply, he, list_prod_map_smul, List.length_range]

/-- The scalar bookkeeping of the coupling (steps 2–3 of the *Proof* of (M1) of
`CSI8_the_split_move.md`): with `m = p − r`,
`(c p) • DSm (p • K) = −(c • ((−1)^m • D^C 0 ⋯ D^C (m−1)) ∘ (p • id))`. -/
lemma smul_DSm_KS (p r : ℕ) (hrp : r < p) (fl : ι → ℕ) (Q : ℕ → Matrix S S A)
    (c : A) :
    (c * p) • DSm (N := N) (fun i => (p : A) • KS p r Q (fl i)) =
      -(c • (((-1 : A) ^ (p - r) • chainProd (layerD (N := N) p fl (fun φ => Q (φ + r)))
        (p - r - 1)) ∘ₗ ((p : A) • LinearMap.id))) := by
  obtain ⟨k, hk⟩ : ∃ k, p - r = k + 1 := ⟨p - r - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, chainProd_layerD_gen]
  have hprod : (fun i => (p : A) • KS p r Q (fl i)) =
      ((p : A) * ((-1 : A) ^ (k + 1 + 1) * (p : A) ^ k)) •
        (fun i => ((List.range (k + 1)).map (fun j => Q (p * fl i + j + r))).prod) := by
    funext i
    simp only [KS, prodQ, hk, Nat.add_sub_cancel, Pi.smul_apply, smul_smul]
    rw [Nat.add_sub_add_left, hk]
    congr 2
    exact List.map_congr_left fun j _ => by rw [add_right_comm]
  rw [hprod, DSm_smul]
  generalize DSm (N := N) (S := S)
    (fun i => ((List.range (k + 1)).map (fun j => Q (p * fl i + j + r))).prod) = P
  rw [LinearMap.comp_smul, LinearMap.comp_id]
  module

/-- The scalar bookkeeping of the *Proof* of (M1) of `CSI8_the_split_move.md`: the block
operator of the new data (with the sign built in), multiplied by `c p`, is minus `c` times the
reduced operator of the coupled chains. -/
lemma smul_blockGp (p r : ℕ) (hr : 0 < r) (hrp : r < p) (fl : ι → ℕ)
    (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) (c : A) :
    (c * p) • blockGp p fl F (QAsign p Q) (QCsign p r Q) (KS p r Q) =
      -(c • coupledRed p (p - r) (layerD (N := N) p fl Q)
        (layerD (N := N) p fl (fun φ => Q (φ + r))) (-(p : A) • FSo F) (-(p : A) • FSo F)
        ((p : A) • LinearMap.id)) := by
  have hp : 0 < p := by omega
  have hA := smul_Gp_QTsign (N := N) p hp fl F Q c
  have hC := smul_Gp_QTsign (N := N) p hp fl F (fun φ => Q (φ + r)) c
  have hK := smul_DSm_KS (N := N) p r hrp fl Q c
  rw [← QAsign_eq_QTsign] at hA
  rw [← QCsign_eq_QTsign] at hC
  apply LinearMap.ext
  rintro ⟨u, v⟩
  have hAu := LinearMap.congr_fun hA u
  have hCv := LinearMap.congr_fun hC v
  have hKu := LinearMap.congr_fun hK u
  simp only [LinearMap.smul_apply, LinearMap.neg_apply] at hAu hCv hKu
  simp only [blockGp, coupledRed, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.prodMap_apply, LinearMap.comp_apply, LinearMap.coe_inr, LinearMap.fst_apply,
    LinearMap.neg_apply, Prod.smul_mk, Prod.neg_mk, Prod.mk_add_mk,
    add_zero]
  rw [hAu, smul_add, hCv, hKu]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_add, neg_add]

/-- Two copies of `Fin m → Y` are `Fin (2 m) → Y` (*Part M* of `CSI8_the_split_move.md`: the
`2 (p − 1)` copies of `M^S ⧸ c`). -/
noncomputable def pairPiEquiv (Y : Type*) [AddCommGroup Y] [Module A Y] (m : ℕ) :
    ((Fin m → Y) × (Fin m → Y)) ≃ₗ[A] (Fin (2 * m) → Y) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin m) A Y).symm.trans
    (LinearEquiv.funCongrLeft A Y (finSumFinEquiv.trans (finCongr (two_mul m).symm)).symm)

/-- A linear equivalence maps `c • ⊤` onto `c • ⊤` (*Part M* of `CSI8_the_split_move.md`). -/
lemma map_smul_top_equiv {Y Z : Type*} [AddCommGroup Y] [Module A Y] [AddCommGroup Z]
    [Module A Z] (e : Y ≃ₗ[A] Z) (c : A) :
    (c • (⊤ : Submodule A Y)).map (e : Y →ₗ[A] Z) = c • (⊤ : Submodule A Z) := by
  ext z
  simp only [Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
    true_and]
  constructor
  · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
    exact ⟨e w, by simp⟩
  · rintro ⟨w, rfl⟩
    exact ⟨c • e.symm w, ⟨e.symm w, rfl⟩, by simp⟩

/-- The `2 (p − 1)` copies of `X ⧸ c` (*Part M* of `CSI8_the_split_move.md`):
`((Fin m → X) × (Fin m → X)) ⧸ c • ⊤ ≃ (Fin (2 m) → X ⧸ c • ⊤)`. -/
noncomputable def pairQuotEquiv (Y : Type*) [AddCommGroup Y] [Module A Y] (m : ℕ) (c : A) :
    (((Fin m → Y) × (Fin m → Y)) ⧸ c • (⊤ : Submodule A ((Fin m → Y) × (Fin m → Y)))) ≃ₗ[A]
      (Fin (2 * m) → Y ⧸ c • (⊤ : Submodule A Y)) :=
  (Submodule.Quotient.equiv _ _ (pairPiEquiv Y m) (map_smul_top_equiv _ c)).trans
    ((Submodule.quotEquivOfEq _ _ (smul_top_pi_eq c)).trans (Submodule.quotientPi _))

/-- **(M1) The odd split move, with the sign `(−1)^p` built into the diagonal blocks** (*Part M*
of `CSI8_the_split_move.md`, valid for **every** `p`, also even `p`): for a digit `0 < r < p`,
every graded family `(ι, fl, N, F)`, every slot type `S`, all data `Q` and every `c : A`,
`M_S^S ⧸ range (c • G_S) ≃ (Fin (2 (p − 1)) → M^S ⧸ c • ⊤) ×
  (Sys N (S × Bool) ⧸ range ((c * p) • Gp p fl F (QSsign p r Q)))`,
with `G_S = Gp p (flS p r fl) (FS p r hr F) Q`. -/
theorem theorem_M1_sign (p r : ℕ) (hr : 0 < r) (hrp : r < p) (fl : ι → ℕ)
    (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NS p N) S ⧸
        LinearMap.range (c • Gp p (flS p r fl) (FS p r hr F) Q)) ≃ₗ[A]
      ((Fin (2 * (p - 1)) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N (S × Bool) ⧸
          LinearMap.range ((c * p) • Gp p fl F (QSsign p r Q))))) := by
  have hp : 0 < p := by omega
  have hm : p - r < p := by omega
  have hm0 : 0 < p - r := by omega
  set DA := layerD (N := N) (S := S) p fl Q
  set DC := layerD (N := N) (S := S) p fl (fun φ => Q (φ + r))
  set E : Module.End A (Payment.Sys N S) := -(p : A) • FSo F
  set L : Module.End A (Payment.Sys N S) := (p : A) • LinearMap.id
  have hmap : (LinearMap.range (c • Gp p (flS p r fl) (FS p r hr F) Q)).map
      (splitEquiv (A := A) (N := N) (S := S) p : Payment.Sys (NS p N) S →ₗ[A] _) =
      LinearMap.range (c • coupledOp p (p - r) hm DA DC E E L) := by
    have hsurj : LinearMap.range (splitProj (A := A) (N := N) (S := S) p) = ⊤ :=
      LinearMap.range_eq_top.2 (splitEquiv (A := A) (N := N) (S := S) p).surjective
    rw [splitEquiv_toLinearMap, ← LinearMap.range_comp, LinearMap.comp_smul,
      layer_comp_GpS p r hr hrp, ← LinearMap.smul_comp,
      LinearMap.range_comp_of_range_eq_top _ hsurj]
  have hslot : (LinearMap.range ((c * p) • Gp p fl F (QSsign p r Q))).map
      (slotEquiv (A := A) (N := N) (S := S) : Payment.Sys N (S × Bool) →ₗ[A] _) =
      LinearMap.range (c • coupledRed p (p - r) DA DC E E L) := by
    have hsurj : LinearMap.range (slotProj (A := A) (N := N) (S := S)) = ⊤ :=
      LinearMap.range_eq_top.2 (slotEquiv (A := A) (N := N) (S := S)).surjective
    rw [slotEquiv_toLinearMap, ← LinearMap.range_comp, LinearMap.comp_smul, QSsign,
      slot_comp_Gp_blockS, ← LinearMap.smul_comp, LinearMap.range_comp_of_range_eq_top _ hsurj,
      smul_blockGp p r hr hrp, LinearMap.range_neg]
  let e1 := Submodule.Quotient.equiv _ _ (splitEquiv (A := A) (N := N) (S := S) p) hmap
  let e2 := coupledCokerEquiv p (p - r) hp hm0 hm DA DC E E L c
  let e3 := pairQuotEquiv (A := A) (Payment.Sys N S) (p - 1) c
  let e4 := (Submodule.Quotient.equiv _ _ (slotEquiv (A := A) (N := N) (S := S)) hslot).symm
  exact ⟨(e1.trans e2).trans (LinearEquiv.prodCongr e3 e4)⟩

/-- **(M1) Theorem: the odd split move** (*Part M* of `CSI8_the_split_move.md`; Proposition 2.2
of «the odd dance»): for odd `p`, a digit `0 < r < p` (the file's `1 ≤ r ≤ p − 1`), every graded
family `(ι, fl, N, F)`, every slot type `S`, all data `Q : ℕ → Matrix S S A` and every `c : A`,
`Sys (NS N) S ⧸ range (c • Gp (flS fl) (FS F) Q) ≃
  (Fin (2 (p − 1)) → Sys N S ⧸ c • ⊤) × (Sys N (S × Bool) ⧸ range ((c * p) • Gp fl F (QS Q)))`.
(`p` need not be prime.) -/
theorem theorem_M1 (p r : ℕ) (hp : Odd p) (hr : 0 < r) (hrp : r < p) (fl : ι → ℕ)
    (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) (c : A) :
    Nonempty ((Payment.Sys (NS p N) S ⧸
        LinearMap.range (c • Gp p (flS p r fl) (FS p r hr F) Q)) ≃ₗ[A]
      ((Fin (2 * (p - 1)) → Payment.Sys N S ⧸ c • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N (S × Bool) ⧸ LinearMap.range ((c * p) • Gp p fl F (QS p r Q))))) := by
  rw [← QSsign_of_odd hp]
  exact theorem_M1_sign p r hr hrp fl F Q c

/-- **(M2) Corollary (powers)** (*Part M* of `CSI8_the_split_move.md`, as C11's
`corollary_A2`): for odd `p`, `0 < r < p` and `c = p^h`,
`Sys (NS N) S ⧸ range (p^h • G_S) ≃
  (Fin (2 (p − 1)) → Sys N S ⧸ p^h • ⊤) × (Sys N (S × Bool) ⧸ range (p^(h+1) • Gp fl F (QS Q)))`. -/
theorem corollary_M2 (p r : ℕ) (hp : Odd p) (hr : 0 < r) (hrp : r < p) (fl : ι → ℕ)
    (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (Q : ℕ → Matrix S S A) (h : ℕ) :
    Nonempty ((Payment.Sys (NS p N) S ⧸
        LinearMap.range ((p : A) ^ h • Gp p (flS p r fl) (FS p r hr F) Q)) ≃ₗ[A]
      ((Fin (2 * (p - 1)) → Payment.Sys N S ⧸ (p : A) ^ h • (⊤ : Submodule A (Payment.Sys N S))) ×
        (Payment.Sys N (S × Bool) ⧸
          LinearMap.range ((p : A) ^ (h + 1) • Gp p fl F (QS p r Q))))) := by
  rw [pow_succ]
  exact theorem_M1 p r hp hr hrp fl F Q ((p : A) ^ h)

end ColouredSand.OddTwist
