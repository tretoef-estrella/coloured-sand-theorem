module

public import RequestProject.Lemma35b.Basic
public import RequestProject.Lemma35.PartL1
public import RequestProject.Lemma35.PartL2

@[expose] public section

noncomputable section

/-!
# C24, Part L: Lemma 3.5, second sentence

This file formalizes Part L of `C24_lemma_35_second_sentence.md`: (L4), (L5) and (L6).

Encodings (reused from C18–C23, see `RequestProject/Lemma35b/Basic.lean`):
* a DP lattice `M : DPLattice A` is a finite free `A`-module `M.ι → A` with a weight
  grading; morphisms `Hom M N` carry an `A`-linear map `toLin`;
* `Doubling.Iso M N` is an isomorphism, given by `hom` and `inv` with
  underlying linear maps `hom.toLin` and `inv.toLin`;
* `tensor M N` has basis `M.ι × N.ι` (basis vector `Pi.single (m, n) 1`, equal to
  `tprod (Pi.single m 1) (Pi.single n 1)`), `dsum M N` has basis `M.ι ⊕ N.ι`;
* `frob h2 M` is the Frobenius twist `M^{[1]}` and `baseChange φ M` is `M^φ`
  (same basis, coefficients mapped by `φ`).
-/

/-! ### Basis vectors under the isomorphisms of the chain -/

namespace Lemma35b

open DPLattice Finset WeylFilt Doubling Lemma35 Tensor2 Twist

section steps

variable {A B : Type*} [CommRing A] [CommRing B]

lemma kron_single' {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) (i : ι) (j : κ) :
    kron f g (Pi.single (i, j) 1) = tprod (f (Pi.single i 1)) (g (Pi.single j 1)) := by
  rw [single_prod_eq_tprod, kron_tprod]

lemma tprod_single_single {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (i : ι) (j : κ) :
    tprod (Pi.single i (1 : A)) (Pi.single j 1) = Pi.single (i, j) 1 :=
  (single_prod_eq_tprod i j).symm

/-- A vector `v ⊗ n` as the combination `Σ_q v_q · (δ_q ⊗ n)`. -/
lemma tprod_eq_sum {ι κ : Type*} [Fintype ι] [DecidableEq ι] (v : ι → A) (n : κ → A) :
    tprod v n = ∑ q, v q • tprod (Pi.single q 1) n := by
  funext p
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Tensor2.tprod_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p.1]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · simp

lemma trans_single {M N P : DPLattice A} {u : Doubling.Iso M N} {v : Doubling.Iso N P} {m : M.ι}
    {m' : N.ι} {m'' : P.ι} (h1 : u.hom.toLin (Pi.single m 1) = Pi.single m' 1)
    (h2 : v.hom.toLin (Pi.single m' 1) = Pi.single m'' 1) :
    (u.trans v).hom.toLin (Pi.single m 1) = Pi.single m'' 1 := by
  rw [Iso.trans_hom_toLin, LinearMap.comp_apply, h1, h2]

lemma refl_single (M : DPLattice A) (m : M.ι) :
    (Iso.refl M).hom.toLin (Pi.single m 1) = Pi.single m 1 := rfl

lemma symm_single {M N : DPLattice A} {u : Doubling.Iso M N} {m : N.ι} {m' : M.ι}
    (h : u.inv.toLin (Pi.single m 1) = Pi.single m' 1) :
    u.symm.hom.toLin (Pi.single m 1) = Pi.single m' 1 := h

lemma tensorVIso_single {M N : DPLattice A} {u : Doubling.Iso M N} {m : M.ι} {m' : N.ι}
    (h : u.hom.toLin (Pi.single m 1) = Pi.single m' 1) (e : Fin 2) :
    (tensorVIso u).hom.toLin (Pi.single (e, m) 1) = Pi.single (e, m') 1 := by
  change kron (LinearMap.id : (Fin 2 → A) →ₗ[A] (Fin 2 → A)) u.hom.toLin
      (Pi.single (e, m) 1 : Fin 2 × M.ι → A) = (Pi.single (e, m') 1 : Fin 2 × N.ι → A)
  rw [kron_single', LinearMap.id_apply, h, tprod_single_single]

lemma tensorIso_single {M M' N N' : DPLattice A} {u : Doubling.Iso M M'} {v : Doubling.Iso N N'}
    {m : M.ι} {m' : M'.ι} {n : N.ι} {n' : N'.ι}
    (hu : u.hom.toLin (Pi.single m 1) = Pi.single m' 1)
    (hv : v.hom.toLin (Pi.single n 1) = Pi.single n' 1) :
    (Tensor2.tensorIso u v).hom.toLin (Pi.single (m, n) 1) = Pi.single (m', n') 1 := by
  change kron u.hom.toLin v.hom.toLin (Pi.single (m, n) 1 : M.ι × N.ι → A) =
    (Pi.single (m', n') 1 : M'.ι × N'.ι → A)
  rw [kron_single', hu, hv, tprod_single_single]

lemma tVIT_hom_single (M : DPLattice A) (e : Fin 2) (m : M.ι) :
    (tensorVIsoTensor M).hom.toLin (Pi.single (e, m) 1) = Pi.single (e, m) 1 := rfl

lemma tVIT_inv_single (M : DPLattice A) (e : Fin 2) (m : M.ι) :
    (tensorVIsoTensor M).inv.toLin (Pi.single (e, m) 1) = Pi.single (e, m) 1 := rfl

lemma assoc_hom_single (M N P : DPLattice A) (i : M.ι) (j : N.ι) (k : P.ι) :
    (assocIso M N P).hom.toLin (Pi.single ((i, j), k) 1) = Pi.single (i, (j, k)) 1 :=
  (Tensor2.P4 M N P).2.2.1 i j k

lemma assoc_inv_single (M N P : DPLattice A) (i : M.ι) (j : N.ι) (k : P.ι) :
    (assocIso M N P).inv.toLin (Pi.single (i, (j, k)) 1) = Pi.single ((i, j), k) 1 :=
  (Tensor2.P4 M N P).2.2.2 i j k

lemma distrib_inl_single (M N P : DPLattice A) (i : M.ι) (k : P.ι) :
    (distribRightIso M N P).hom.toLin (Pi.single (Sum.inl i, k) 1) =
      Pi.single (Sum.inl (i, k)) 1 :=
  (Tensor2.P5 M N P).1.2.2.1 i k

lemma distrib_inr_single (M N P : DPLattice A) (j : N.ι) (k : P.ι) :
    (distribRightIso M N P).hom.toLin (Pi.single (Sum.inr j, k) 1) =
      Pi.single (Sum.inr (j, k)) 1 :=
  (Tensor2.P5 M N P).1.2.2.2.1 j k

lemma dsumIso_inl_single {M M' N N' : DPLattice A} {u : Doubling.Iso M M'}
    (v : Doubling.Iso N N') {m : M.ι} {m' : M'.ι}
    (h : u.hom.toLin (Pi.single m 1) = Pi.single m' 1) :
    (dsumIso u v).hom.toLin (Pi.single (Sum.inl m) 1) = Pi.single (Sum.inl m') 1 := by
  change blk u.hom.toLin v.hom.toLin (Pi.single (Sum.inl m) 1 : M.ι ⊕ N.ι → A) =
    (Pi.single (Sum.inl m') 1 : M'.ι ⊕ N'.ι → A)
  rw [single_inl, single_inl, blk_inlL_apply, h]

lemma dsumIso_inr_single {M M' N N' : DPLattice A} (u : Doubling.Iso M M')
    {v : Doubling.Iso N N'} {n : N.ι} {n' : N'.ι}
    (h : v.hom.toLin (Pi.single n 1) = Pi.single n' 1) :
    (dsumIso u v).hom.toLin (Pi.single (Sum.inr n) 1) = Pi.single (Sum.inr n') 1 := by
  change blk u.hom.toLin v.hom.toLin (Pi.single (Sum.inr n) 1 : M.ι ⊕ N.ι → A) =
    (Pi.single (Sum.inr n') 1 : M'.ι ⊕ N'.ι → A)
  rw [single_inr, single_inr, blk_inrL_apply, h]

lemma dsumComm_inl_single (M N : DPLattice A) (i : M.ι) :
    (dsumComm M N).hom.toLin (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inr i) 1 :=
  (I2 M N).2.2.1 i

lemma dsumComm_inr_single (M N : DPLattice A) (j : N.ι) :
    (dsumComm M N).hom.toLin (Pi.single (Sum.inr j) 1) = Pi.single (Sum.inl j) 1 :=
  (I2 M N).2.2.2.1 j

lemma frobIso_single (h2 : (2 : B) = 0) {M N : DPLattice B} {u : Doubling.Iso M N} {m : M.ι}
    {m' : N.ι} (h : u.hom.toLin (Pi.single m 1) = Pi.single m' 1) :
    (frobIso h2 u).hom.toLin (Pi.single m 1) = Pi.single m' 1 := h

lemma frobTensorIso_inv_single (h2 : (2 : B) = 0) (M N : DPLattice B) (i : M.ι) (j : N.ι) :
    (frobTensorIso h2 M N).inv.toLin (Pi.single (i, j) 1) = Pi.single (i, j) 1 := rfl

lemma twistTensor_hom_single (φ : A →+* B) (M : DPLattice A) (e : Fin 2) (m : M.ι) :
    (Twist.tensorIso φ M).hom.toLin (Pi.single (e, m) 1) = Pi.single (e, m) 1 := rfl

lemma twistTensor_inv_single (φ : A →+* B) (M : DPLattice A) (e : Fin 2) (m : M.ι) :
    (Twist.tensorIso φ M).inv.toLin (Pi.single (e, m) 1) = Pi.single (e, m) 1 := rfl

lemma bcDsumIso_inv_inl_single (φ : A →+* B) (M N : DPLattice A) (i : M.ι) :
    (bcDsumIso φ M N).inv.toLin (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 := rfl

lemma bcDsumIso_inv_inr_single (φ : A →+* B) (M N : DPLattice A) (j : N.ι) :
    (bcDsumIso φ M N).inv.toLin (Pi.single (Sum.inr j) 1) = Pi.single (Sum.inr j) 1 := rfl

lemma prop31_hom_single (φ : A →+* B) (h2 : (2 : B) = 0) [IsDomain A] [CharZero A]
    [OddUnits A] (N : DPLattice A) (e : Fin 2) (i : N.ι) :
    (prop31Iso φ h2 N).hom.toLin (Pi.single (e, i) 1) = Pi.single (e, i) 1 := rfl

lemma prop31_inv_single (φ : A →+* B) (h2 : (2 : B) = 0) [IsDomain A] [CharZero A]
    [OddUnits A] (N : DPLattice A) (e : Fin 2) (i : N.ι) :
    (prop31Iso φ h2 N).inv.toLin (Pi.single (e, i) 1) = Pi.single (e, i) 1 := rfl

end steps

/-! ### (L4) -/

section L4

variable {B : Type*} [CommRing B] (h2 : (2 : B) = 0) (X : DPLattice B)

/-- (L4), (L5): the basis index `(e, e')` of `V ⊗ V^{[1]}` with `u(e_r) = δ_{(e,e')}`
(C22 (L2): `u(e_0) = b_0b'_0`, `u(e_1) = b_1b'_0`, `u(e_2) = b_0b'_1`, `u(e_3) = b_1b'_1`). -/
def uIdx : Fin 4 → Fin 2 × Fin 2 := ![(0, 0), (1, 0), (0, 1), (1, 1)]

/-- (L4), (L5): `u(e_r) = δ_{uIdx r}` (C22 `uL`). -/
theorem uL_single (r : Fin 4) :
    uL (Pi.single r 1 : Fin 4 → B) = (Pi.single (uIdx r) 1 : Fin 2 × Fin 2 → B) := by
  simp only [uL, ofImg_single]
  fin_cases r <;> rfl

/-- (L4), first step: `V ⊗ (V ⊗ (V ⊗ X)) ≅ V^{⊗3} ⊗ X` by (P3) and (P4) of C23 (identities and
the reassociation `(a,(b,(c,x))) ↦ ((a,(b,c)),x)`). -/
def L4stepA : Doubling.Iso (tensorV (tensorV (tensorV X))) (tensor (Lemma35.T3 B) X) :=
  (((((tensorVIso (tensorVIso (tensorVIsoTensor X))).trans
    (tensorVIso (tensorVIsoTensor (tensor (V B) X)))).trans
    (tensorVIsoTensor (tensor (V B) (tensor (V B) X)))).trans
    (Tensor2.tensorIso (Iso.refl (V B)) (assocIso (V B) (V B) X).symm)).trans
    (assocIso (V B) (tensor (V B) (V B)) X).symm).trans
    (Tensor2.tensorIso ((Tensor2.tensorIso (Iso.refl (V B)) (tensorVIsoTensor (V B)).symm).trans
      (tensorVIsoTensor (tensorV (V B))).symm) (Iso.refl X))

/-- (L4), second step: `tensorIso (isoL1 h2) (Iso.refl X) : V^{⊗3} ⊗ X ≅ D3 B ⊗ X`. -/
def L4stepB : Doubling.Iso (tensor (Lemma35.T3 B) X) (tensor (Lemma35.D3 B) X) :=
  Tensor2.tensorIso (isoL1 h2) (Iso.refl X)

/-- (L4), third step: (P5) of C23 twice, then `tensorIso (isoL2 h2) (Iso.refl X)` on the first
summand and (P3) of C23 backwards on the other two. -/
def L4stepC : Doubling.Iso (tensor (Lemma35.D3 B) X)
    (dsum (tensor (VV1 h2) X) (dsum (tensorV X) (tensorV X))) :=
  ((distribRightIso (delta B 3) (dsum (V B) (V B)) X).trans
    (dsumIso (Iso.refl _) (distribRightIso (V B) (V B) X))).trans
    (dsumIso (Tensor2.tensorIso (isoL2 h2) (Iso.refl X))
      (dsumIso (tensorVIsoTensor X).symm (tensorVIsoTensor X).symm))

/-- (L4) `V^{⊗3} ⊗ X ≅ (V ⊗ V^{[1]}) ⊗ X ⊕ (V ⊗ X)^2` over `B` with `2 = 0`:
`tensorV (tensorV (tensorV X)) ≅ dsum (tensor (VV1 h2) X) (dsum (tensorV X) (tensorV X))`,
the composite of the steps listed in the file. -/
def isoL4 : Doubling.Iso (tensorV (tensorV (tensorV X)))
    (dsum (tensor (VV1 h2) X) (dsum (tensorV X) (tensorV X))) :=
  ((L4stepA X).trans (L4stepB h2 X)).trans (L4stepC h2 X)

/-- (L4) the image of `δ_q` (`q` a basis index of `D3 B`) with `x` attached:
`δ_{inl r} ↦ u(e_r) ⊗ δ_x = δ_{inl ((e,e'),x)}` (where `u(e_r) = δ_{(e,e')}`) in the summand
`(V ⊗ V^{[1]}) ⊗ X`; `δ_{inr (inl e)} ↦ δ_{(e,x)}` in the first copy of `V ⊗ X`;
`δ_{inr (inr e)} ↦ δ_{(e,x)}` in the second copy of `V ⊗ X`. -/
def L4img (x : X.ι) : ID → (dsum (tensor (VV1 h2) X) (dsum (tensorV X) (tensorV X))).ι → B
  | Sum.inl r => Pi.single (Sum.inl (uIdx r, x)) 1
  | Sum.inr (Sum.inl e) => Pi.single (Sum.inr (Sum.inl (e, x))) 1
  | Sum.inr (Sum.inr e) => Pi.single (Sum.inr (Sum.inr (e, x))) 1

lemma L4stepA_single (a b c : Fin 2) (x : X.ι) :
    (L4stepA X).hom.toLin (Pi.single (a, (b, (c, x))) 1) = Pi.single ((a, (b, c)), x) 1 :=
  trans_single (trans_single (trans_single (trans_single (trans_single
    (tensorVIso_single (tensorVIso_single (tVIT_hom_single X c x) b) a)
    (tensorVIso_single (tVIT_hom_single (tensor (V B) X) b (c, x)) a))
    (tVIT_hom_single (tensor (V B) (tensor (V B) X)) a (b, (c, x))))
    (tensorIso_single (refl_single (V B) a) (symm_single (assoc_inv_single (V B) (V B) X b c x))))
    (symm_single (assoc_inv_single (V B) (tensor (V B) (V B)) X a (b, c) x)))
    (tensorIso_single (trans_single
      (tensorIso_single (refl_single (V B) a) (symm_single (tVIT_inv_single (V B) b c)))
      (symm_single (tVIT_inv_single (tensorV (V B)) a (b, c)))) (refl_single X x))

lemma L4stepB_single (a b c : Fin 2) (x : X.ι) :
    (L4stepB h2 X).hom.toLin (Pi.single ((a, (b, c)), x) 1) =
      ∑ q : ID, hL (Pi.single (a, (b, c)) 1 : IT → B) q •
        (Pi.single (q, x) 1 : (tensor (Lemma35.D3 B) X).ι → B) := by
  change kron hL (LinearMap.id : (X.ι → B) →ₗ[B] (X.ι → B))
      (Pi.single ((a, (b, c)), x) 1 : IT × X.ι → B) =
    ∑ q : ID, hL (Pi.single (a, (b, c)) 1 : IT → B) q • (Pi.single (q, x) 1 : ID × X.ι → B)
  rw [kron_single', LinearMap.id_apply, tprod_eq_sum]
  simp only [tprod_single_single]

lemma L4stepC_single (q : ID) (x : X.ι) :
    (L4stepC h2 X).hom.toLin (Pi.single (q, x) 1) = L4img h2 X x q := by
  rcases q with r | e | e
  · exact trans_single (trans_single
      (distrib_inl_single (delta B 3) (dsum (V B) (V B)) X r x)
      (dsumIso_inl_single _ (refl_single (tensor (delta B 3) X) (r, x))))
      (dsumIso_inl_single _ (tensorIso_single (uL_single r) (refl_single X x)))
  · exact trans_single (trans_single
      (distrib_inr_single (delta B 3) (dsum (V B) (V B)) X (Sum.inl e) x)
      (dsumIso_inr_single _ (distrib_inl_single (V B) (V B) X e x)))
      (dsumIso_inr_single _ (dsumIso_inl_single _ (symm_single (tVIT_inv_single X e x))))
  · exact trans_single (trans_single
      (distrib_inr_single (delta B 3) (dsum (V B) (V B)) X (Sum.inr e) x)
      (dsumIso_inr_single _ (distrib_inr_single (V B) (V B) X e x)))
      (dsumIso_inr_single _ (dsumIso_inr_single _ (symm_single (tVIT_inv_single X e x))))

/-- (L4) the statement of the file: `isoL4 h2 X : V^{⊗3} ⊗ X ≅ (V ⊗ V^{[1]}) ⊗ X ⊕ (V ⊗ X)^2`
over `B` with `2 = 0`, and its underlying linear map sends `δ_{(a,(b,(c,x)))}` to the image of
`h(δ_{(a,(b,c))})` (C22 `hL`) with `x` attached: writing `h(δ_{(a,(b,c))}) = Σ_q h_q δ_q`, the
image is `Σ_q h_q · L4img x q`, where `δ_{inl r}` goes on to `u(e_r)` (C22 `uL`) with `x`
attached, `δ_{inr (inl e)}` to `δ_{(e,x)}` in the first copy of `V ⊗ X`, and `δ_{inr (inr e)}`
to `δ_{(e,x)}` in the second copy. -/
theorem L4 (a b c : Fin 2) (x : X.ι) :
    (isoL4 h2 X).hom.toLin (Pi.single (a, (b, (c, x))) 1) =
      ∑ q : ID, hL (Pi.single (a, (b, c)) 1 : IT → B) q • L4img h2 X x q := by
  rw [isoL4, Iso.trans_hom_toLin, Iso.trans_hom_toLin, LinearMap.comp_apply,
    LinearMap.comp_apply, L4stepA_single, L4stepB_single, map_sum]
  simp only [map_smul, L4stepC_single]

end L4

/-! ### (L5) -/

section L5

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (h2 : (2 : B) = 0)
  [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A)

/-- (L5), steps 1–2: `(V ⊗ V ⊗ Φ(N))^φ ≅ V ⊗ (V ⊗ (V ⊗ X))`, `X = (N^φ)^{[1]}`
(`Twist.tensorIso` twice, the second inside `tensorVIso`; then `Twist.prop31Iso` inside
`tensorVIso` twice). -/
def L5step12 : Doubling.Iso (baseChange φ (tensorV (tensorV (phi N))))
    (tensorV (tensorV (tensorV (frob h2 (baseChange φ N))))) :=
  ((Twist.tensorIso φ (tensorV (phi N))).trans (tensorVIso (Twist.tensorIso φ (phi N)))).trans
    (tensorVIso (tensorVIso (prop31Iso φ h2 N)))

/-- (L5), steps 4–5: `(V ⊗ V^{[1]}) ⊗ X ≅ V ⊗ (V^{[1]} ⊗ X) ≅ V ⊗ (V ⊗ N̄)^{[1]} ≅
V ⊗ ((V ⊗ N)^φ)^{[1]} ≅ (Φ(V ⊗ N))^φ` ((P3), (P4) of C23, (F1) and `frobIso` backwards,
`Twist.prop31Iso` backwards). -/
def L5step45 : Doubling.Iso (tensor (VV1 h2) (frob h2 (baseChange φ N)))
    (baseChange φ (phi (tensorV N))) :=
  ((((((Tensor2.tensorIso (tensorVIsoTensor (frob h2 (V B))) (Iso.refl _)).trans
    (assocIso (V B) (frob h2 (V B)) (frob h2 (baseChange φ N)))).trans
    (Tensor2.tensorIso (Iso.refl (V B)) (frobTensorIso h2 (V B) (baseChange φ N)).symm)).trans
    (Tensor2.tensorIso (Iso.refl (V B))
      (frobIso h2 (tensorVIsoTensor (baseChange φ N)).symm))).trans
    (Tensor2.tensorIso (Iso.refl (V B)) (frobIso h2 (Twist.tensorIso φ N).symm))).trans
    (tensorVIsoTensor (frob h2 (baseChange φ (tensorV N)))).symm).trans
    (prop31Iso φ h2 (tensorV N)).symm

/-- (L5), steps 4–8: from `dsum ((V ⊗ V^{[1]}) ⊗ X) (dsum (V ⊗ X) (V ⊗ X))` to
`(Φ(N)^2 ⊕ Φ(V ⊗ N))^φ` (steps 4–5 on the first summand, step 6 on the two others (P7),
step 7 (I2), step 8 (B2) twice backwards). -/
def L5tail : Doubling.Iso
    (dsum (tensor (VV1 h2) (frob h2 (baseChange φ N)))
      (dsum (tensorV (frob h2 (baseChange φ N))) (tensorV (frob h2 (baseChange φ N)))))
    (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))) :=
  (((dsumIso (L5step45 φ h2 N) (dsumIso (prop31Iso φ h2 N).symm (prop31Iso φ h2 N).symm)).trans
    (dsumComm _ _)).trans
    (dsumIso (bcDsumIso φ (phi N) (phi N)).symm (Iso.refl _))).trans
    (bcDsumIso φ (dsum (phi N) (phi N)) (phi (tensorV N))).symm

/-- (L5) Lemma 3.5, second sentence, the explicit isomorphism
`lemma35Iso φ h2 N : (V ⊗ V ⊗ Φ(N))^φ ≅ (Φ(N)^2 ⊕ Φ(V ⊗ N))^φ`: the chain 1–8 of the file
(steps 1–2 `L5step12`, step 3 (L4) `isoL4`, steps 4–8 `L5tail`). -/
def lemma35Iso : Doubling.Iso (baseChange φ (tensorV (tensorV (phi N))))
    (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))) :=
  ((L5step12 φ h2 N).trans (isoL4 h2 (frob h2 (baseChange φ N)))).trans (L5tail φ h2 N)

/-- (L5) the image of `δ_q` (`q` a basis index of `D3 B`) with `i` attached:
`δ_{inl r} ↦ δ_{inr (e,(e',i))}` where `δ_{(e,e')} = u(e_r)` (`(e,e') = uIdx r`);
`δ_{inr (inl e)} ↦ δ_{inl (inl (e,i))}`; `δ_{inr (inr e)} ↦ δ_{inl (inr (e,i))}`. -/
def L5img (i : N.ι) :
    ID → (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))).ι → B
  | Sum.inl r => Pi.single (Sum.inr ((uIdx r).1, ((uIdx r).2, i))) 1
  | Sum.inr (Sum.inl e) => Pi.single (Sum.inl (Sum.inl (e, i))) 1
  | Sum.inr (Sum.inr e) => Pi.single (Sum.inl (Sum.inr (e, i))) 1

lemma L5step12_single (a b c : Fin 2) (i : N.ι) :
    (L5step12 φ h2 N).hom.toLin (Pi.single (a, (b, (c, i))) 1) =
      Pi.single (a, (b, (c, i))) 1 :=
  trans_single (trans_single (twistTensor_hom_single φ (tensorV (phi N)) a (b, (c, i)))
    (tensorVIso_single (twistTensor_hom_single φ (phi N) b (c, i)) a))
    (tensorVIso_single (tensorVIso_single (prop31_hom_single φ h2 N c i) b) a)

lemma L5step45_single (e e' : Fin 2) (i : N.ι) :
    (L5step45 φ h2 N).hom.toLin (Pi.single ((e, e'), i) 1) = Pi.single (e, (e', i)) 1 :=
  trans_single (trans_single (trans_single (trans_single (trans_single (trans_single
    (tensorIso_single (tVIT_hom_single (frob h2 (V B)) e e') (refl_single (frob h2 (baseChange φ N)) i))
    (assoc_hom_single (V B) (frob h2 (V B)) (frob h2 (baseChange φ N)) e e' i))
    (tensorIso_single (refl_single (V B) e)
      (symm_single (frobTensorIso_inv_single h2 (V B) (baseChange φ N) e' i))))
    (tensorIso_single (refl_single (V B) e)
      (frobIso_single h2 (symm_single (tVIT_inv_single (baseChange φ N) e' i)))))
    (tensorIso_single (refl_single (V B) e)
      (frobIso_single h2 (symm_single (twistTensor_inv_single φ N e' i)))))
    (symm_single (tVIT_inv_single (frob h2 (baseChange φ (tensorV N))) e (e', i))))
    (symm_single (prop31_inv_single φ h2 (tensorV N) e (e', i)))

lemma L5tail_L4img (q : ID) (i : N.ι) :
    (L5tail φ h2 N).hom.toLin (L4img h2 (frob h2 (baseChange φ N)) i q) = L5img φ N i q := by
  rcases q with r | e | e
  · exact trans_single (trans_single (trans_single
      (dsumIso_inl_single _ (L5step45_single φ h2 N (uIdx r).1 (uIdx r).2 i))
      (dsumComm_inl_single _ _ _))
      (dsumIso_inr_single _ (refl_single _ _)))
      (symm_single (bcDsumIso_inv_inr_single φ _ _ _))
  · exact trans_single (trans_single (trans_single
      (dsumIso_inr_single _ (dsumIso_inl_single _ (symm_single (prop31_inv_single φ h2 N e i))))
      (dsumComm_inr_single _ _ _))
      (dsumIso_inl_single _ (symm_single (bcDsumIso_inv_inl_single φ _ _ _))))
      (symm_single (bcDsumIso_inv_inl_single φ _ _ _))
  · exact trans_single (trans_single (trans_single
      (dsumIso_inr_single _ (dsumIso_inr_single _ (symm_single (prop31_inv_single φ h2 N e i))))
      (dsumComm_inr_single _ _ _))
      (dsumIso_inl_single _ (symm_single (bcDsumIso_inv_inr_single φ _ _ _))))
      (symm_single (bcDsumIso_inv_inl_single φ _ _ _))

/-- (L5) the statement of the file, explicit form: the underlying linear map of
`lemma35Iso φ h2 N` sends `δ_{(a,(b,(c,i)))}` (`a, b, c : Fin 2`, `i : N.ι`; the basis of
`phi N` is `Fin 2 × N.ι`) to `Σ_q h_q · L5img i q`, where `h(δ_{(a,(b,c))}) = Σ_q h_q δ_q`
(C22 `hL`) and `δ_{inl r}` becomes `δ_{inr (e,(e',i))}` with `δ_{(e,e')} = u(e_r)` (C22 `uL`),
`δ_{inr (inl e)}` becomes `δ_{inl (inl (e,i))}`, `δ_{inr (inr e)}` becomes `δ_{inl (inr (e,i))}`. -/
theorem lemma35Iso_single (a b c : Fin 2) (i : N.ι) :
    (lemma35Iso φ h2 N).hom.toLin (Pi.single (a, (b, (c, i))) 1) =
      ∑ q : ID, hL (Pi.single (a, (b, c)) 1 : IT → B) q • L5img φ N i q := by
  rw [lemma35Iso, Iso.trans_hom_toLin, Iso.trans_hom_toLin, LinearMap.comp_apply,
    LinearMap.comp_apply, L5step12_single, L4, map_sum]
  simp only [map_smul, L5tail_L4img]

include h2 in
/-- (L5) Lemma 3.5, second sentence: in the Setting (`A` with `[IsDomain A] [CharZero A]
[OddUnits A]`, `B` with `2 = 0`, any `φ : A →+* B`), for every DP-lattice `N` over `A`,
`(V ⊗ V ⊗ Φ(N))^φ ≅ (Φ(N)^2 ⊕ Φ(V ⊗ N))^φ`. -/
theorem L5 : Nonempty (Doubling.Iso (baseChange φ (tensorV (tensorV (phi N))))
    (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N))))) :=
  ⟨lemma35Iso φ h2 N⟩

end L5

/-! ### (L6) -/

/-- (L6) The case of the paper: for every DP-lattice `N` over `ℤ_[2]`,
`(V ⊗ V ⊗ Φ(N)) ⊗ 𝔽_2 ≅ (Φ(N)^2 ⊕ Φ(V ⊗ N)) ⊗ 𝔽_2`, with `φ = PadicInt.toZMod : ℤ_[2] → ZMod 2`
(the hypotheses `IsDomain`, `CharZero`, `OddUnits` and `2 = 0` are C21's `C3_hyp`). -/
theorem L6 (N : DPLattice ℤ_[2]) :
    Nonempty (Doubling.Iso (baseChange PadicInt.toZMod (tensorV (tensorV (phi N))))
      (baseChange PadicInt.toZMod (dsum (dsum (phi N) (phi N)) (phi (tensorV N))))) :=
  L5 PadicInt.toZMod Twist.C3_hyp.2.2.2.2.1 N

end Lemma35b
