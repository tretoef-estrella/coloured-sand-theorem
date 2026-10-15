module

public import RequestProject.Tensor2.All

@[expose] public section

noncomputable section

/-!
# `C24_lemma_35_second_sentence.md`: Part I — isomorphisms as a category

Encodings (namespace `Lemma35b`), reusing C18 (`DPLattice`, `Hom`), C19 (`WeylFilt.Hom.id`,
`WeylFilt.Hom.comp`), C20 (`Doubling.Iso`, `Doubling.Iso.trans`, `Doubling.Iso.symm`),
C22 (`Lemma35.dsum`) and C23 (`Tensor2.isoOfReindex`):

* An isomorphism `M ≅ N` is a `Doubling.Iso M N`: `hom : Hom M N`, `inv : Hom N M` with
  `Hom.comp inv hom = Hom.id M` and `Hom.comp hom inv = Hom.id N`. Its underlying linear maps are
  `u.hom.toLin` and `u.inv.toLin`.
* A reindexing along a bijection `e` of bases is the linear map `f ↦ f ∘ e⁻¹`
  (`LinearMap.funLeft A A e.symm`), which sends `δ_x` to `δ_{e x}`; its inverse is
  `g ↦ g ∘ e` (C23's `isoOfReindex`).
* (I2) `dsumComm M N` reindexes along `Equiv.sumComm`: `inl i ↦ inr i`, `inr j ↦ inl j`.
* (I3) `dsumAssoc M N P` reindexes along `Equiv.sumAssoc`: `inl (inl i) ↦ inl i`,
  `inl (inr j) ↦ inr (inl j)`, `inr k ↦ inr (inr k)`.
-/


namespace Lemma35b

open DPLattice Finset WeylFilt Doubling Lemma35 Tensor2

variable {A : Type*} [CommRing A]

/-! ### (I1) -/

/-- (I1) `Iso.refl M : M ≅ M`, with both underlying maps the identity. -/
def Iso.refl (M : DPLattice A) : Doubling.Iso M M where
  hom := Hom.id M
  inv := Hom.id M
  hom_inv := Hom.ext' rfl
  inv_hom := Hom.ext' rfl

@[simp] lemma Iso.refl_hom_toLin (M : DPLattice A) :
    (Iso.refl M).hom.toLin = LinearMap.id := rfl
@[simp] lemma Iso.refl_inv_toLin (M : DPLattice A) :
    (Iso.refl M).inv.toLin = LinearMap.id := rfl

@[simp] lemma Iso.trans_hom_toLin {M N P : DPLattice A} (u : Doubling.Iso M N)
    (v : Doubling.Iso N P) : (u.trans v).hom.toLin = v.hom.toLin ∘ₗ u.hom.toLin := rfl
@[simp] lemma Iso.trans_inv_toLin {M N P : DPLattice A} (u : Doubling.Iso M N)
    (v : Doubling.Iso N P) : (u.trans v).inv.toLin = u.inv.toLin ∘ₗ v.inv.toLin := rfl
@[simp] lemma Iso.symm_hom_toLin {M N : DPLattice A} (u : Doubling.Iso M N) :
    u.symm.hom.toLin = u.inv.toLin := rfl
@[simp] lemma Iso.symm_inv_toLin {M N : DPLattice A} (u : Doubling.Iso M N) :
    u.symm.inv.toLin = u.hom.toLin := rfl

/-- (I1) `Iso.refl M` has both underlying maps the identity; `Iso.trans` composes and
`Iso.symm` inverts (swaps) the underlying maps. -/
theorem I1 :
    (∀ M : DPLattice A, (Iso.refl M).hom.toLin = LinearMap.id ∧
      (Iso.refl M).inv.toLin = LinearMap.id) ∧
    (∀ {M N P : DPLattice A} (u : Doubling.Iso M N) (v : Doubling.Iso N P),
      (u.trans v).hom.toLin = v.hom.toLin ∘ₗ u.hom.toLin ∧
      (u.trans v).inv.toLin = u.inv.toLin ∘ₗ v.inv.toLin) ∧
    (∀ {M N : DPLattice A} (u : Doubling.Iso M N),
      u.symm.hom.toLin = u.inv.toLin ∧ u.symm.inv.toLin = u.hom.toLin) :=
  ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩

/-! ### (I2) -/

section I2

variable (M N P : DPLattice A)

/-- (I2) `dsum M N ≅ dsum N M`, reindexing along `inl i ↦ inr i`, `inr j ↦ inl j`. -/
def dsumComm : Doubling.Iso (dsum M N) (dsum N M) :=
  isoOfReindex (Equiv.sumComm M.ι N.ι) (fun p => by rcases p with i | i <;> rfl)
    (fun r => LinearMap.ext fun z => by funext p; rcases p with i | i <;> rfl)
    (fun r => LinearMap.ext fun z => by funext p; rcases p with i | i <;> rfl)

/-- (I2) the statement of the file: `dsum M N ≅ dsum N M` along `inl i ↦ inr i`,
`inr j ↦ inl j`; the underlying linear maps are this reindexing (`f ↦ f ∘ e⁻¹`) and its inverse,
and on basis vectors they act as stated. -/
theorem I2 :
    (dsumComm M N).hom.toLin = LinearMap.funLeft A A (Equiv.sumComm M.ι N.ι).symm ∧
    (dsumComm M N).inv.toLin = LinearMap.funLeft A A (Equiv.sumComm M.ι N.ι) ∧
    (∀ i, (dsumComm M N).hom.toLin (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inr i) 1) ∧
    (∀ j, (dsumComm M N).hom.toLin (Pi.single (Sum.inr j) 1) = Pi.single (Sum.inl j) 1) ∧
    (∀ i, (dsumComm M N).inv.toLin (Pi.single (Sum.inr i) 1) = Pi.single (Sum.inl i) 1) ∧
    (∀ j, (dsumComm M N).inv.toLin (Pi.single (Sum.inl j) 1) = Pi.single (Sum.inr j) 1) :=
  ⟨rfl, rfl, fun i => funLeft_symm_single (Equiv.sumComm M.ι N.ι) (Sum.inl i),
    fun j => funLeft_symm_single (Equiv.sumComm M.ι N.ι) (Sum.inr j),
    fun i => funLeft_single (Equiv.sumComm M.ι N.ι) (Sum.inl i),
    fun j => funLeft_single (Equiv.sumComm M.ι N.ι) (Sum.inr j)⟩

/-! ### (I3) -/

/-- (I3) `dsum (dsum M N) P ≅ dsum M (dsum N P)`, reindexing along `inl (inl i) ↦ inl i`,
`inl (inr j) ↦ inr (inl j)`, `inr k ↦ inr (inr k)`. -/
def dsumAssoc : Doubling.Iso (dsum (dsum M N) P) (dsum M (dsum N P)) :=
  isoOfReindex (Equiv.sumAssoc M.ι N.ι P.ι)
    (fun p => by rcases p with (i | i) | i <;> rfl)
    (fun r => LinearMap.ext fun z => by funext p; rcases p with i | i | i <;> rfl)
    (fun r => LinearMap.ext fun z => by funext p; rcases p with i | i | i <;> rfl)

/-- (I3) the statement of the file: `dsum (dsum M N) P ≅ dsum M (dsum N P)` along
`inl (inl i) ↦ inl i`, `inl (inr j) ↦ inr (inl j)`, `inr k ↦ inr (inr k)`; the underlying linear
maps are this reindexing and its inverse, and on basis vectors they act as stated. -/
theorem I3 :
    (dsumAssoc M N P).hom.toLin = LinearMap.funLeft A A (Equiv.sumAssoc M.ι N.ι P.ι).symm ∧
    (dsumAssoc M N P).inv.toLin = LinearMap.funLeft A A (Equiv.sumAssoc M.ι N.ι P.ι) ∧
    (∀ i, (dsumAssoc M N P).hom.toLin (Pi.single (Sum.inl (Sum.inl i)) 1) =
      Pi.single (Sum.inl i) 1) ∧
    (∀ j, (dsumAssoc M N P).hom.toLin (Pi.single (Sum.inl (Sum.inr j)) 1) =
      Pi.single (Sum.inr (Sum.inl j)) 1) ∧
    (∀ k, (dsumAssoc M N P).hom.toLin (Pi.single (Sum.inr k) 1) =
      Pi.single (Sum.inr (Sum.inr k)) 1) ∧
    (∀ i, (dsumAssoc M N P).inv.toLin (Pi.single (Sum.inl i) 1) =
      Pi.single (Sum.inl (Sum.inl i)) 1) ∧
    (∀ j, (dsumAssoc M N P).inv.toLin (Pi.single (Sum.inr (Sum.inl j)) 1) =
      Pi.single (Sum.inl (Sum.inr j)) 1) ∧
    (∀ k, (dsumAssoc M N P).inv.toLin (Pi.single (Sum.inr (Sum.inr k)) 1) =
      Pi.single (Sum.inr k) 1) :=
  ⟨rfl, rfl, fun i => funLeft_symm_single (Equiv.sumAssoc M.ι N.ι P.ι) (Sum.inl (Sum.inl i)),
    fun j => funLeft_symm_single (Equiv.sumAssoc M.ι N.ι P.ι) (Sum.inl (Sum.inr j)),
    fun k => funLeft_symm_single (Equiv.sumAssoc M.ι N.ι P.ι) (Sum.inr k),
    fun i => funLeft_single (Equiv.sumAssoc M.ι N.ι P.ι) (Sum.inl (Sum.inl i)),
    fun j => funLeft_single (Equiv.sumAssoc M.ι N.ι P.ι) (Sum.inl (Sum.inr j)),
    fun k => funLeft_single (Equiv.sumAssoc M.ι N.ι P.ι) (Sum.inr k)⟩

end I2

end Lemma35b

/-!
# `C24_lemma_35_second_sentence.md`: Part B — base change of `⊗` and `⊕` (any `φ : A →+* B`)

Encodings (namespace `Lemma35b`), reusing C21 (`Twist.bc`, `Twist.baseChange`, `Twist.bcHom`),
C22 (`Lemma35.dsum`, with the blockwise map `blk`) and C23 (`Tensor2.tensor`, `Tensor2.kron`):

* `A`, `B` are any commutative rings and `φ : A →+* B` any ring homomorphism.
* `M^φ` is `baseChange φ M` (same basis and weights, `F^{(r)} = bc φ (M.Fd r)`), and the base
  change of a linear map `f` is `bc φ f` (entrywise `φ` on the matrix of `f`).
* (B1) `bcTensorIso φ M N : (M ⊗ N)^φ ≅ M^φ ⊗ N^φ`, both underlying maps the identity of
  `M.ι × N.ι → B`.
* (B2) `bcDsumIso φ M N : (dsum M N)^φ ≅ dsum M^φ N^φ`, both underlying maps the identity of
  `M.ι ⊕ N.ι → B`.
* (B3) `bcIso φ u : M^φ ≅ N^φ` for `u : M ≅ N`, with underlying maps `bcHom φ u.hom`,
  `bcHom φ u.inv`.
-/


namespace Lemma35b

open DPLattice Finset WeylFilt Doubling Lemma35 Tensor2 Twist

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)

section ops

variable {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- (B1) `(f ⊠ g)^φ = f^φ ⊠ g^φ` (compare matrices entrywise; `φ` is multiplicative). -/
theorem bc_kron (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    bc φ (kron f g) = kron (bc φ f) (bc φ g) := by
  refine ext_single fun ⟨i, j⟩ => ?_
  funext ⟨i', j'⟩
  rw [bc_single_apply, kron_single_apply, kron_single_apply, bc_single_apply, bc_single_apply,
    map_mul]

/-- (B1) base change commutes with finite sums. -/
theorem bc_sum {α : Type*} (s : Finset α) (f : α → Module.End A (ι → A)) :
    bc φ (∑ a ∈ s, f a) = ∑ a ∈ s, bc φ (f a) :=
  map_sum (bcRingHom φ) f s

/-- (B1) `(Σ_{a=0}^{r} F^{(a)} ⊠ G^{(r−a)})^φ = Σ_{a=0}^{r} (F^{(a)})^φ ⊠ (G^{(r−a)})^φ`. -/
theorem bc_coFd (F : ℕ → Module.End A (ι → A)) (G : ℕ → Module.End A (κ → A)) (r : ℕ) :
    bc φ (coFd F G r) = coFd (fun r => bc φ (F r)) (fun r => bc φ (G r)) r := by
  simp only [coFd, bc_sum, bc_kron]

/-- (B2) `(f ⊕ g)^φ = f^φ ⊕ g^φ` (blockwise). -/
theorem bc_blk (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)) :
    bc φ (blk f g) = blk (bc φ f) (bc φ g) :=
  ext_comp φ fun x => by
    rw [bc_apply_comp]
    funext p
    rcases p with i | i
    · exact (congrFun (bc_apply_comp φ f (x ∘ Sum.inl)) i).symm
    · exact (congrFun (bc_apply_comp φ g (x ∘ Sum.inr)) i).symm

end ops

/-! ### (B1) -/

section B1

variable (M N : DPLattice A)

/-- (B1) the identity of `M.ι × N.ι → B`, as a morphism `(M ⊗ N)^φ → M^φ ⊗ N^φ`. -/
def bcTensorHom : Hom (baseChange φ (tensor M N)) (tensor (baseChange φ M) (baseChange φ N)) where
  toLin := LinearMap.id
  comm_F r := by
    show LinearMap.id ∘ₗ bc φ (coFd M.Fd N.Fd r) =
      coFd (fun r => bc φ (M.Fd r)) (fun r => bc φ (N.Fd r)) r ∘ₗ LinearMap.id
    rw [bc_coFd]; rfl
  comm_E r := by
    show LinearMap.id ∘ₗ bc φ (coFd M.Ed N.Ed r) =
      coFd (fun r => bc φ (M.Ed r)) (fun r => bc φ (N.Ed r)) r ∘ₗ LinearMap.id
    rw [bc_coFd]; rfl
  comm_H := rfl

/-- (B1) `(M ⊗ N)^φ ≅ M^φ ⊗ N^φ`, with both underlying linear maps the identity of
`M.ι × N.ι → B`. -/
def bcTensorIso :
    Doubling.Iso (baseChange φ (tensor M N)) (tensor (baseChange φ M) (baseChange φ N)) :=
  Iso.ofInverse (bcTensorHom φ M N) LinearMap.id rfl rfl

/-- (B1) the statement of the file: both sides have basis `M.ι × N.ι` and the same weights; the
operators agree (`((f ⊠ g))^φ = f^φ ⊠ g^φ`, and base change commutes with finite sums); and
`(M ⊗ N)^φ ≅ M^φ ⊗ N^φ` with both underlying linear maps the identity of `M.ι × N.ι → B`. -/
theorem B1 :
    (baseChange φ (tensor M N)).ι = (M.ι × N.ι) ∧
    (tensor (baseChange φ M) (baseChange φ N)).ι = (M.ι × N.ι) ∧
    (∀ p : M.ι × N.ι, (baseChange φ (tensor M N)).wt p =
      (tensor (baseChange φ M) (baseChange φ N)).wt p) ∧
    (∀ r, (baseChange φ (tensor M N)).Fd r = (tensor (baseChange φ M) (baseChange φ N)).Fd r) ∧
    (∀ r, (baseChange φ (tensor M N)).Ed r = (tensor (baseChange φ M) (baseChange φ N)).Ed r) ∧
    (∀ {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (f : (ι → A) →ₗ[A] (ι' → A)) (g : (κ → A) →ₗ[A] (κ' → A)),
      bc φ (kron f g) = kron (bc φ f) (bc φ g)) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} (s : Finset α)
      (f : α → Module.End A (ι → A)), bc φ (∑ a ∈ s, f a) = ∑ a ∈ s, bc φ (f a)) ∧
    (bcTensorIso φ M N).hom.toLin = (LinearMap.id : (M.ι × N.ι → B) →ₗ[B] (M.ι × N.ι → B)) ∧
    (bcTensorIso φ M N).inv.toLin = (LinearMap.id : (M.ι × N.ι → B) →ₗ[B] (M.ι × N.ι → B)) :=
  ⟨rfl, rfl, fun _ => rfl, fun r => bc_coFd φ M.Fd N.Fd r, fun r => bc_coFd φ M.Ed N.Ed r,
    fun f g => bc_kron φ f g, fun s f => bc_sum φ s f, rfl, rfl⟩

end B1

/-! ### (B2) -/

section B2

variable (M N : DPLattice A)

/-- (B2) the identity of `M.ι ⊕ N.ι → B`, as a morphism `(dsum M N)^φ → dsum M^φ N^φ`. -/
def bcDsumHom : Hom (baseChange φ (dsum M N)) (dsum (baseChange φ M) (baseChange φ N)) where
  toLin := LinearMap.id
  comm_F r := by
    show LinearMap.id ∘ₗ bc φ (blk (M.Fd r) (N.Fd r)) =
      blk (bc φ (M.Fd r)) (bc φ (N.Fd r)) ∘ₗ LinearMap.id
    rw [bc_blk]; rfl
  comm_E r := by
    show LinearMap.id ∘ₗ bc φ (blk (M.Ed r) (N.Ed r)) =
      blk (bc φ (M.Ed r)) (bc φ (N.Ed r)) ∘ₗ LinearMap.id
    rw [bc_blk]; rfl
  comm_H := rfl

/-- (B2) `(dsum M N)^φ ≅ dsum M^φ N^φ`, with both underlying linear maps the identity of
`M.ι ⊕ N.ι → B`. -/
def bcDsumIso :
    Doubling.Iso (baseChange φ (dsum M N)) (dsum (baseChange φ M) (baseChange φ N)) :=
  Iso.ofInverse (bcDsumHom φ M N) LinearMap.id rfl rfl

/-- (B2) the statement of the file: `(dsum M N)^φ ≅ dsum M^φ N^φ`, with both underlying linear
maps the identity of `M.ι ⊕ N.ι → B` (the operators agree: `(f ⊕ g)^φ = f^φ ⊕ g^φ`). -/
theorem B2 :
    (∀ r, (baseChange φ (dsum M N)).Fd r = (dsum (baseChange φ M) (baseChange φ N)).Fd r) ∧
    (∀ r, (baseChange φ (dsum M N)).Ed r = (dsum (baseChange φ M) (baseChange φ N)).Ed r) ∧
    (bcDsumIso φ M N).hom.toLin = (LinearMap.id : (M.ι ⊕ N.ι → B) →ₗ[B] (M.ι ⊕ N.ι → B)) ∧
    (bcDsumIso φ M N).inv.toLin = (LinearMap.id : (M.ι ⊕ N.ι → B) →ₗ[B] (M.ι ⊕ N.ι → B)) :=
  ⟨fun r => bc_blk φ (M.Fd r) (N.Fd r), fun r => bc_blk φ (M.Ed r) (N.Ed r), rfl, rfl⟩

end B2

/-! ### (B3) -/

/-- (B3) an isomorphism `u : M ≅ N` gives `bcIso φ u : M^φ ≅ N^φ`, with underlying morphisms
`bcHom φ u.hom` and `bcHom φ u.inv` (by C21 (R2)). -/
def bcIso {M N : DPLattice A} (u : Doubling.Iso M N) :
    Doubling.Iso (baseChange φ M) (baseChange φ N) where
  hom := bcHom φ u.hom
  inv := bcHom φ u.inv
  hom_inv := by rw [← (Twist.R2 φ).2.2, u.hom_inv, (Twist.R2 φ).2.1]
  inv_hom := by rw [← (Twist.R2 φ).2.2, u.inv_hom, (Twist.R2 φ).2.1]

/-- (B3) the statement of the file: `bcIso φ u : M^φ ≅ N^φ` has underlying morphisms
`bcHom φ u.hom`, `bcHom φ u.inv`, whose linear maps are `(u.hom.toLin)^φ`, `(u.inv.toLin)^φ`. -/
theorem B3 {M N : DPLattice A} (u : Doubling.Iso M N) :
    (bcIso φ u).hom = bcHom φ u.hom ∧ (bcIso φ u).inv = bcHom φ u.inv ∧
    (bcIso φ u).hom.toLin = bc φ u.hom.toLin ∧ (bcIso φ u).inv.toLin = bc φ u.inv.toLin :=
  ⟨rfl, rfl, rfl, rfl⟩

end Lemma35b

/-!
# `C24_lemma_35_second_sentence.md`: Part F — the twist is monoidal and additive (`2 = 0` in `B`)

Encodings (namespace `Lemma35b`), reusing C21 (`Twist.frob`, `Twist.frobOp`, `Twist.frobHom`),
C22 (`Lemma35.dsum`) and C23 (`Tensor2.tensor`):

* `B` is a commutative ring and `h2 : (2 : B) = 0`; `M^{[1]}` is `frob h2 M` (same basis,
  weights `2 · wt`, `F^{(r)} = frobOp M.Fd r`: `F^{(r/2)}` for even `r`, `0` for odd `r`).
* (F1) `frobTensorIso h2 M N : (M ⊗ N)^{[1]} ≅ M^{[1]} ⊗ N^{[1]}`, both underlying maps the
  identity of `M.ι × N.ι → B`.
* (F2) `frobDsumIso h2 M N : (dsum M N)^{[1]} ≅ dsum M^{[1]} N^{[1]}`, both underlying maps the
  identity of `M.ι ⊕ N.ι → B`.
* (F3) `frobIso h2 u : M^{[1]} ≅ N^{[1]}` for `u : M ≅ N`, with underlying morphisms
  `frobHom h2 u.hom`, `frobHom h2 u.inv`.
-/


namespace Lemma35b

open DPLattice Finset WeylFilt Doubling Lemma35 Tensor2 Twist

variable {B : Type*} [CommRing B]

section ops

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- (F1) the twist of a coproduct is the coproduct of the twists:
`frobOp (Σ_{a=0}^{·} F^{(a)} ⊠ G^{(·−a)}) r = Σ_{c=0}^{r} frobOp F c ⊠ frobOp G (r − c)`
(for `r = 2s` only even `c = 2a` survive; for `r` odd every term has an odd index). -/
theorem frobOp_coFd (F : ℕ → Module.End B (ι → B)) (G : ℕ → Module.End B (κ → B)) (r : ℕ) :
    frobOp (coFd F G) r = coFd (frobOp F) (frobOp G) r := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
  · rw [frobOp_even, coFd, coFd, sum_range_two_mul_add_one]
    rw [sum_eq_zero (s := range s) fun j _ => ?_, add_zero]
    · refine sum_congr rfl fun j _ => ?_
      rw [show 2 * s - 2 * j = 2 * (s - j) by omega, frobOp_even, frobOp_even]
    · rw [frobOp_odd, kron_zero_left]
  · rw [frobOp_odd, coFd]
    symm
    refine sum_eq_zero fun c hc => ?_
    simp only [mem_range] at hc
    rcases Nat.even_or_odd c with ⟨k, hk⟩ | hc'
    · rw [frobOp_of_odd G (n := 2 * s + 1 - c) ⟨s - k, by omega⟩, kron_zero_right]
    · rw [frobOp_of_odd F hc', kron_zero_left]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- (F2) the twist of a blockwise family is blockwise: `frobOp (F ⊕ G) r = frobOp F r ⊕ frobOp G r`. -/
theorem frobOp_blk (F : ℕ → Module.End B (ι → B)) (G : ℕ → Module.End B (κ → B)) (r : ℕ) :
    frobOp (fun r => blk (F r) (G r)) r = blk (frobOp F r) (frobOp G r) := by
  unfold frobOp
  split_ifs
  · rfl
  · ext z p; cases p <;> rfl

end ops

variable (h2 : (2 : B) = 0)

/-! ### (F1) -/

section F1

variable (M N : DPLattice B)

lemma frob_tensor_wt : (fun p : M.ι × N.ι => 2 * (M.wt p.1 + N.wt p.2)) =
    fun p => 2 * M.wt p.1 + 2 * N.wt p.2 := funext fun _ => mul_add _ _ _

/-- (F1) the identity of `M.ι × N.ι → B`, as a morphism `(M ⊗ N)^{[1]} → M^{[1]} ⊗ N^{[1]}`. -/
def frobTensorHom : Hom (frob h2 (tensor M N)) (tensor (frob h2 M) (frob h2 N)) where
  toLin := LinearMap.id
  comm_F r := by
    show LinearMap.id ∘ₗ frobOp (coFd M.Fd N.Fd) r = coFd (frobOp M.Fd) (frobOp N.Fd) r ∘ₗ
      LinearMap.id
    rw [frobOp_coFd]; rfl
  comm_E r := by
    show LinearMap.id ∘ₗ frobOp (coFd M.Ed N.Ed) r = coFd (frobOp M.Ed) (frobOp N.Ed) r ∘ₗ
      LinearMap.id
    rw [frobOp_coFd]; rfl
  comm_H := by
    show LinearMap.id ∘ₗ Hop (fun p : M.ι × N.ι => 2 * (M.wt p.1 + N.wt p.2)) =
      Hop (fun p : M.ι × N.ι => 2 * M.wt p.1 + 2 * N.wt p.2) ∘ₗ LinearMap.id
    rw [frob_tensor_wt]; rfl

/-- (F1) `frob h2 (M ⊗ N) ≅ frob h2 M ⊗ frob h2 N`, with both underlying linear maps the
identity of `M.ι × N.ι → B`. -/
def frobTensorIso : Doubling.Iso (frob h2 (tensor M N)) (tensor (frob h2 M) (frob h2 N)) :=
  Iso.ofInverse (frobTensorHom h2 M N) LinearMap.id rfl rfl

/-- (F1) the statement of the file: for DP-lattices `M`, `N` over `B` (with `2 = 0`),
`frob h2 (M ⊗ N) ≅ frob h2 M ⊗ frob h2 N`, with both underlying linear maps the identity of
`M.ι × N.ι → B`; the weights are `2 (wt i + wt j) = 2 wt i + 2 wt j` and the operators agree. -/
theorem F1 :
    (∀ p : M.ι × N.ι, (frob h2 (tensor M N)).wt p = (tensor (frob h2 M) (frob h2 N)).wt p) ∧
    (∀ r, (frob h2 (tensor M N)).Fd r = (tensor (frob h2 M) (frob h2 N)).Fd r) ∧
    (∀ r, (frob h2 (tensor M N)).Ed r = (tensor (frob h2 M) (frob h2 N)).Ed r) ∧
    (frobTensorIso h2 M N).hom.toLin =
      (LinearMap.id : (M.ι × N.ι → B) →ₗ[B] (M.ι × N.ι → B)) ∧
    (frobTensorIso h2 M N).inv.toLin =
      (LinearMap.id : (M.ι × N.ι → B) →ₗ[B] (M.ι × N.ι → B)) :=
  ⟨fun p => congrFun (frob_tensor_wt M N) p, fun r => frobOp_coFd M.Fd N.Fd r,
    fun r => frobOp_coFd M.Ed N.Ed r, rfl, rfl⟩

end F1

/-! ### (F2) -/

section F2

variable (M N : DPLattice B)

lemma frob_dsum_wt : (fun p : M.ι ⊕ N.ι => 2 * Sum.elim M.wt N.wt p) =
    Sum.elim (fun i => 2 * M.wt i) (fun i => 2 * N.wt i) := funext fun p => by cases p <;> rfl

/-- (F2) the identity of `M.ι ⊕ N.ι → B`, as a morphism `(dsum M N)^{[1]} → dsum M^{[1]} N^{[1]}`. -/
def frobDsumHom : Hom (frob h2 (dsum M N)) (dsum (frob h2 M) (frob h2 N)) where
  toLin := LinearMap.id
  comm_F r := by
    show LinearMap.id ∘ₗ frobOp (fun r => blk (M.Fd r) (N.Fd r)) r =
      blk (frobOp M.Fd r) (frobOp N.Fd r) ∘ₗ LinearMap.id
    rw [frobOp_blk]; rfl
  comm_E r := by
    show LinearMap.id ∘ₗ frobOp (fun r => blk (M.Ed r) (N.Ed r)) r =
      blk (frobOp M.Ed r) (frobOp N.Ed r) ∘ₗ LinearMap.id
    rw [frobOp_blk]; rfl
  comm_H := by
    show LinearMap.id ∘ₗ Hop (fun p : M.ι ⊕ N.ι => 2 * Sum.elim M.wt N.wt p) =
      Hop (Sum.elim (fun i => 2 * M.wt i) (fun i => 2 * N.wt i)) ∘ₗ LinearMap.id
    rw [frob_dsum_wt]; rfl

/-- (F2) `frob h2 (dsum M N) ≅ dsum (frob h2 M) (frob h2 N)`, with both underlying linear maps
the identity of `M.ι ⊕ N.ι → B`. -/
def frobDsumIso : Doubling.Iso (frob h2 (dsum M N)) (dsum (frob h2 M) (frob h2 N)) :=
  Iso.ofInverse (frobDsumHom h2 M N) LinearMap.id rfl rfl

/-- (F2) the statement of the file: `frob h2 (dsum M N) ≅ dsum (frob h2 M) (frob h2 N)`, with
both underlying linear maps the identity of `M.ι ⊕ N.ι → B` (weights and operators agree). -/
theorem F2 :
    (∀ p : M.ι ⊕ N.ι, (frob h2 (dsum M N)).wt p = (dsum (frob h2 M) (frob h2 N)).wt p) ∧
    (∀ r, (frob h2 (dsum M N)).Fd r = (dsum (frob h2 M) (frob h2 N)).Fd r) ∧
    (∀ r, (frob h2 (dsum M N)).Ed r = (dsum (frob h2 M) (frob h2 N)).Ed r) ∧
    (frobDsumIso h2 M N).hom.toLin =
      (LinearMap.id : (M.ι ⊕ N.ι → B) →ₗ[B] (M.ι ⊕ N.ι → B)) ∧
    (frobDsumIso h2 M N).inv.toLin =
      (LinearMap.id : (M.ι ⊕ N.ι → B) →ₗ[B] (M.ι ⊕ N.ι → B)) :=
  ⟨fun p => congrFun (frob_dsum_wt M N) p, fun r => frobOp_blk M.Fd N.Fd r,
    fun r => frobOp_blk M.Ed N.Ed r, rfl, rfl⟩

end F2

/-! ### (F3) -/

/-- (F3) an isomorphism `u : M ≅ N` gives `frobIso h2 u : frob h2 M ≅ frob h2 N`, with
underlying morphisms `frobHom h2 u.hom` and `frobHom h2 u.inv` (by C21 (T2)). -/
def frobIso {M N : DPLattice B} (u : Doubling.Iso M N) :
    Doubling.Iso (frob h2 M) (frob h2 N) where
  hom := frobHom h2 u.hom
  inv := frobHom h2 u.inv
  hom_inv := by rw [← (Twist.T2 h2).2.2, u.hom_inv, (Twist.T2 h2).2.1]
  inv_hom := by rw [← (Twist.T2 h2).2.2, u.inv_hom, (Twist.T2 h2).2.1]

/-- (F3) the statement of the file: `frobIso h2 u : frob h2 M ≅ frob h2 N` has underlying
morphisms `frobHom h2 u.hom`, `frobHom h2 u.inv`, whose linear maps are those of `u`. -/
theorem F3 {M N : DPLattice B} (u : Doubling.Iso M N) :
    (frobIso h2 u).hom = frobHom h2 u.hom ∧ (frobIso h2 u).inv = frobHom h2 u.inv ∧
    (frobIso h2 u).hom.toLin = u.hom.toLin ∧ (frobIso h2 u).inv.toLin = u.inv.toLin :=
  ⟨rfl, rfl, rfl, rfl⟩

end Lemma35b


