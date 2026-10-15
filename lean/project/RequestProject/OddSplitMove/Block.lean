module

public import RequestProject.OddPayment.Chain

/-!
# The row/column reduction of the *Proof* of (M1) of `CSI8_the_split_move.md`

Pure linear algebra: two of CSI7's chains (`chainOp`, `RequestProject/OddPayment/Chain.lean`)
coupled by one term. CSI7's row operation `chainRow` and column operation `chainCol` are reused
on each chain, and the coupling is absorbed by one extra (surjective) column operation.

## Encoding

* `X` is an `A`-module (later `X = M^S`); `(Fin p → X) × (Fin p → X)` is the direct sum of the
  `p` layers `A_0, …, A_{p−1}` (first factor) and the `p` layers `C_0, …, C_{p−1}` (second factor).
* `coupledOp p m hm DA DC EA EC L` is the operator
  `(wA, wC) ↦ (chainOp p DA EA wA, chainOp p DC EC wC + Pi.single m (L (wA (p−1))))`:
  the two chains, plus the coupling sending layer `A_{p−1}` to layer `C_m` by `L`
  (later `m = p − r` and `L = p • id`).
* `coupledRed p m DA DC EA EC L : X × X → X × X` is the reduced operator
  `(u, v) ↦ (HA u, HC v + (−1)^m • (DC 0 ⋯ DC (m−1)) (L u))`, with
  `HA = EA + (−1)^(p−1) • DA 0 ⋯ DA (p−1)` and `HC = EC + (−1)^(p−1) • DC 0 ⋯ DC (p−1)`.

## Main result

`coupledCokerEquiv`: for `0 < m < p` and every `c`,
`((Fin p → X) × (Fin p → X)) ⧸ range (c • coupledOp) ≃
  (((Fin (p−1) → X) × (Fin (p−1) → X)) ⧸ c • ⊤) × ((X × X) ⧸ range (c • coupledRed))`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open scoped Pointwise

variable {A X : Type*} [CommRing A] [AddCommGroup X] [Module A X]

/-- The two chains coupled by one term (steps 1–3 of the *Proof* of (M1) of
`CSI8_the_split_move.md`): `(wA, wC) ↦ (chainOp DA EA wA, chainOp DC EC wC + b_m (L (wA_{p−1})))`. -/
def coupledOp (p m : ℕ) (hm : m < p) (DA DC : ℕ → Module.End A X) (EA EC L : Module.End A X) :
    (Fin p → X) × (Fin p → X) →ₗ[A] (Fin p → X) × (Fin p → X) :=
  (chainOp p DA EA).prodMap (chainOp p DC EC) +
    LinearMap.inr A _ _ ∘ₗ LinearMap.single A (fun _ : Fin p => X) (⟨m, hm⟩ : Fin p) ∘ₗ L ∘ₗ
      lproj (⟨p - 1, by omega⟩ : Fin p) ∘ₗ LinearMap.fst A _ _

/-- The value of `coupledOp` (*Proof* of (M1) of `CSI8_the_split_move.md`). -/
lemma coupledOp_apply (p m : ℕ) (hm : m < p) (DA DC : ℕ → Module.End A X)
    (EA EC L : Module.End A X) (w : (Fin p → X) × (Fin p → X)) :
    coupledOp p m hm DA DC EA EC L w = (chainOp p DA EA w.1,
      chainOp p DC EC w.2 + Pi.single (⟨m, hm⟩ : Fin p) (L (w.1 ⟨p - 1, by omega⟩))) := by
  simp [coupledOp]

/-- The reduced operator (step 2–3 of the *Proof* of (M1) of `CSI8_the_split_move.md`):
`(u, v) ↦ (HA u, HC v + (−1)^m • (DC 0 ⋯ DC (m−1)) (L u))`. -/
def coupledRed (p m : ℕ) (DA DC : ℕ → Module.End A X) (EA EC L : Module.End A X) :
    X × X →ₗ[A] X × X :=
  (EA + (-1 : A) ^ (p - 1) • chainProd DA (p - 1)).prodMap
      (EC + (-1 : A) ^ (p - 1) • chainProd DC (p - 1)) +
    LinearMap.inr A X X ∘ₗ ((-1 : A) ^ m • chainProd DC (m - 1)) ∘ₗ L ∘ₗ LinearMap.fst A X X

/-- The row operation on the two chains: CSI7's `chainRow` on each chain, the results
rearranged as `(X × X) × ((Fin (p−1) → X) × (Fin (p−1) → X))` (*Proof* of (M1) of
`CSI8_the_split_move.md`). -/
noncomputable def coupledRowEquiv (p : ℕ) (hp : 0 < p) (DA DC : ℕ → Module.End A X) :
    ((Fin p → X) × (Fin p → X)) ≃ₗ[A] (X × X) × ((Fin (p - 1) → X) × (Fin (p - 1) → X)) :=
  (LinearEquiv.prodCongr (LinearEquiv.ofBijective _ (chainRow_bijective p hp DA))
    (LinearEquiv.ofBijective _ (chainRow_bijective p hp DC))).trans
    (LinearEquiv.prodProdProdComm A _ _ _ _)

/-- The value of `coupledRowEquiv` (*Proof* of (M1) of `CSI8_the_split_move.md`). -/
lemma coupledRowEquiv_apply (p : ℕ) (hp : 0 < p) (DA DC : ℕ → Module.End A X)
    (y : (Fin p → X) × (Fin p → X)) :
    coupledRowEquiv p hp DA DC y =
      (((chainRow p hp DA y.1).1, (chainRow p hp DC y.2).1),
        ((chainRow p hp DA y.1).2, (chainRow p hp DC y.2).2)) := rfl

/-- The column operation on the two chains: CSI7's `chainCol` on each chain, plus the
coupling `b_{m−1} (L (wA_{p−1}))` added to the `C` part (*Proof* of (M1) of
`CSI8_the_split_move.md`). -/
def coupledCol (p m : ℕ) (hp : 0 < p) (hm0 : 0 < m) (hm : m < p) (DA DC : ℕ → Module.End A X)
    (L : Module.End A X) :
    (Fin p → X) × (Fin p → X) →ₗ[A] (X × X) × ((Fin (p - 1) → X) × (Fin (p - 1) → X)) :=
  (LinearEquiv.prodProdProdComm A X (Fin (p - 1) → X) X (Fin (p - 1) → X)).toLinearMap ∘ₗ
      (chainCol p hp DA).prodMap (chainCol p hp DC) +
    LinearMap.inr A _ _ ∘ₗ LinearMap.inr A _ _ ∘ₗ
      LinearMap.single A (fun _ : Fin (p - 1) => X) (⟨m - 1, by omega⟩ : Fin (p - 1)) ∘ₗ L ∘ₗ
      lproj (⟨p - 1, by omega⟩ : Fin p) ∘ₗ LinearMap.fst A _ _

/-- The value of `coupledCol` (*Proof* of (M1) of `CSI8_the_split_move.md`). -/
lemma coupledCol_apply (p m : ℕ) (hp : 0 < p) (hm0 : 0 < m) (hm : m < p)
    (DA DC : ℕ → Module.End A X) (L : Module.End A X) (w : (Fin p → X) × (Fin p → X)) :
    coupledCol p m hp hm0 hm DA DC L w =
      (((chainCol p hp DA w.1).1, (chainCol p hp DC w.2).1),
        ((chainCol p hp DA w.1).2, (chainCol p hp DC w.2).2 +
          Pi.single (⟨m - 1, by omega⟩ : Fin (p - 1)) (L (w.1 ⟨p - 1, by omega⟩)))) := by
  simp [coupledCol]

/-- The column operation is surjective (*Proof* of (M1) of `CSI8_the_split_move.md`). -/
lemma coupledCol_surjective (p m : ℕ) (hp : 0 < p) (hm0 : 0 < m) (hm : m < p)
    (DA DC : ℕ → Module.End A X) (L : Module.End A X) :
    Function.Surjective (coupledCol p m hp hm0 hm DA DC L) := by
  rintro ⟨⟨u, v⟩, ⟨a, b⟩⟩
  obtain ⟨wA, hA⟩ := chainCol_surjective p hp DA (u, a)
  obtain ⟨wC, hC⟩ := chainCol_surjective p hp DC
    (v, b - Pi.single (⟨m - 1, by omega⟩ : Fin (p - 1)) (L (wA ⟨p - 1, by omega⟩)))
  refine ⟨(wA, wC), ?_⟩
  rw [coupledCol_apply]
  simp only [hA, hC, sub_add_cancel]

/-- CSI7's row operation on a single layer `m ≥ 1`: the first component is
`(−1)^m (D 0 ⋯ D (m−1)) z` and the second is `b_{m−1} z` (*Proof* of (M1) of
`CSI8_the_split_move.md`: step 2, the coupling term `c_{p−r} = (−1)^{p−r} c_0 Π_p(…)`). -/
lemma chainRow_single (p m : ℕ) (hp : 0 < p) (hm0 : 0 < m) (hm : m < p)
    (D : ℕ → Module.End A X) (z : X) :
    chainRow p hp D (Pi.single (⟨m, hm⟩ : Fin p) z) =
      ((-1 : A) ^ m • chainProd D (m - 1) z,
        Pi.single (⟨m - 1, by omega⟩ : Fin (p - 1)) z) := by
  rw [chainRow_apply]
  refine Prod.ext ?_ ?_
  · simp only
    have h0 : (⟨0, hp⟩ : Fin p) ≠ ⟨m, hm⟩ := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    rw [Pi.single_eq_of_ne h0, zero_sub]
    rw [Finset.sum_eq_single (⟨m - 1, by omega⟩ : Fin (p - 1))]
    · rw [Pi.single_apply, if_pos (Fin.ext (by simp; omega))]
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp [pow_succ]
    · intro k _ hk
      have : (⟨k.val + 1, by omega⟩ : Fin p) ≠ ⟨m, hm⟩ := fun h => by
        apply hk; ext; have := congrArg Fin.val h; simp at this ⊢; omega
      rw [Pi.single_eq_of_ne this, map_zero, smul_zero]
    · simp
  · funext j
    simp only
    by_cases hj : j = ⟨m - 1, by omega⟩
    · subst hj
      rw [Pi.single_apply, if_pos (Fin.ext (by simp; omega)), Pi.single_eq_same]
    · have : (⟨j.val + 1, by omega⟩ : Fin p) ≠ ⟨m, hm⟩ := fun h => by
        apply hj; ext; have := congrArg Fin.val h; simp at this ⊢; omega
      rw [Pi.single_eq_of_ne this, Pi.single_eq_of_ne hj]

/-- The key identity of the *Proof* of (M1) of `CSI8_the_split_move.md`:
`row ∘ coupledOp = (coupledRed × id) ∘ col`. -/
lemma coupledRow_coupledOp (p m : ℕ) (hp : 0 < p) (hm0 : 0 < m) (hm : m < p)
    (DA DC : ℕ → Module.End A X) (EA EC L : Module.End A X) (w : (Fin p → X) × (Fin p → X)) :
    coupledRowEquiv p hp DA DC (coupledOp p m hm DA DC EA EC L w) =
      ((coupledRed p m DA DC EA EC L).prodMap LinearMap.id)
        (coupledCol p m hp hm0 hm DA DC L w) := by
  rw [coupledRowEquiv_apply, coupledOp_apply, coupledCol_apply]
  simp only [map_add]
  rw [chainRow_single p m hp hm0 hm, chainRow_chainOp, chainRow_chainOp]
  have hu : (chainCol p hp DA w.1).1 = w.1 ⟨p - 1, by omega⟩ := by rw [chainCol_apply]
  simp [coupledRed, hu]

/-- The row operation sends the relations `range (c • coupledOp)` onto
`range (c • coupledRed) × c • ⊤` (*Proof* of (M1) of `CSI8_the_split_move.md`). -/
lemma map_coupledRow_range (p m : ℕ) (hp : 0 < p) (hm0 : 0 < m) (hm : m < p)
    (DA DC : ℕ → Module.End A X) (EA EC L : Module.End A X) (c : A) :
    (LinearMap.range (c • coupledOp p m hm DA DC EA EC L)).map
        (coupledRowEquiv p hp DA DC : _ →ₗ[A] _) =
      (LinearMap.range (c • coupledRed p m DA DC EA EC L)).prod
        (c • (⊤ : Submodule A ((Fin (p - 1) → X) × (Fin (p - 1) → X)))) := by
  rw [← LinearMap.range_comp, LinearMap.comp_smul]
  have hc : (coupledRowEquiv p hp DA DC : _ →ₗ[A] _) ∘ₗ coupledOp p m hm DA DC EA EC L =
      ((coupledRed p m DA DC EA EC L).prodMap LinearMap.id) ∘ₗ
        coupledCol p m hp hm0 hm DA DC L :=
    LinearMap.ext (coupledRow_coupledOp p m hp hm0 hm DA DC EA EC L)
  rw [hc, ← LinearMap.smul_comp,
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 (coupledCol_surjective p m hp hm0 hm DA DC L))]
  ext ⟨y, z⟩
  simp only [LinearMap.mem_range, Submodule.mem_prod,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    simp only [LinearMap.smul_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      Prod.smul_mk, Prod.mk.injEq] at h
    exact ⟨⟨a, by simpa using h.1⟩, ⟨b, h.2⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(a, b), ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      Prod.smul_mk, Prod.mk.injEq]
    exact ⟨by simpa using ha, hb⟩

/-- **The coupled chain reduction** (steps 1–3 of the *Proof* of (M1) of
`CSI8_the_split_move.md`): for `0 < m < p` and every `c`,
`((Fin p → X) × (Fin p → X)) ⧸ range (c • coupledOp) ≃
  (((Fin (p−1) → X) × (Fin (p−1) → X)) ⧸ c • ⊤) × ((X × X) ⧸ range (c • coupledRed))`. -/
noncomputable def coupledCokerEquiv (p m : ℕ) (hp : 0 < p) (hm0 : 0 < m) (hm : m < p)
    (DA DC : ℕ → Module.End A X) (EA EC L : Module.End A X) (c : A) :
    (((Fin p → X) × (Fin p → X)) ⧸ LinearMap.range (c • coupledOp p m hm DA DC EA EC L)) ≃ₗ[A]
      (((Fin (p - 1) → X) × (Fin (p - 1) → X)) ⧸
          c • (⊤ : Submodule A ((Fin (p - 1) → X) × (Fin (p - 1) → X)))) ×
        ((X × X) ⧸ LinearMap.range (c • coupledRed p m DA DC EA EC L)) :=
  ((Submodule.Quotient.equiv _ _ (coupledRowEquiv p hp DA DC)
      (map_coupledRow_range p m hp hm0 hm DA DC EA EC L c)).trans
    (Payment.quotProdEquiv _ _)).trans (LinearEquiv.prodComm A _ _)

end ColouredSand.OddTwist
