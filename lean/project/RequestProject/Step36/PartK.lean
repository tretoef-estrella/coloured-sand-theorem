module

public import RequestProject.Step36.PartW

@[expose] public section

noncomputable section

/-!
# `C30_the_step_of_theorem_36.md`: Part K — the kit of isomorphisms for the induction

Encodings (namespace `Step36`), reusing C18 (`DPLattice`, `one`, `V`, `tensorV`), C19
(`Hom.id`, `Hom.comp`, `Hom.ext'`), C20 (`phi`, `phiHom`, `Iso`, `Iso.trans`, `Iso.symm`, `D3`),
C22 (`dsum`), C23 (`isoOfReindex`, `dsumIso`, `tensorVIsoTensor`, `unitRightIso`,
`distribLeftIso`), C24 (`Iso.refl`, `dsumAssoc`) and C27 (`zeroL`):

* All isomorphisms are `Doubling.Iso` (morphisms both ways with identity composites); "`X ≅ Y`"
  is either an explicit `Iso X Y` (a `def`) or `Nonempty (Iso X Y)`.
* A reindexing along `e : M.ι ≃ N.ι` is C23's `isoOfReindex e …`, whose underlying maps are
  `f ↦ f ∘ e⁻¹` (sending `δ_x` to `δ_{e x}`) and `g ↦ g ∘ e`.
* (K2) `phiDsumIso M N : phi (dsum M N) ≅ dsum (phi M) (phi N)` reindexes along
  `Equiv.prodSumDistrib : Fin 2 × (M.ι ⊕ N.ι) ≃ (Fin 2 × M.ι) ⊕ (Fin 2 × N.ι)`,
  `(e, inl i) ↦ inl (e, i)`, `(e, inr j) ↦ inr (e, j)`.
* (K3) `dsumZeroIso M : dsum M (zeroL A) ≅ M` reindexes along `inl i ↦ i`,
  `zeroDsumIso M : dsum (zeroL A) M ≅ M` along `inr i ↦ i`; `tensorV (zeroL A)` and
  `phi (zeroL A)` have empty bases (`Fin 2 × Empty`) and are reindexed onto `zeroL A`.
* (K4) `dsumList : List (DPLattice A) → DPLattice A` is defined by structural recursion:
  `dsumList [] = zeroL A`, `dsumList (X :: L) = dsum X (dsumList L)` (theorems `dsumList_nil`,
  `dsumList_cons`). Pointwise isomorphisms of two lists are encoded as
  `List.Forall₂ (fun X Y => Nonempty (Iso X Y)) L L'` (equivalently: same length and
  `Nonempty (Iso (L.get k) (L'.get k))` for every `k`, see `K4b_get`).

Over `A` a domain of characteristic `0` all these maps are weight-preserving by C25 (P1); this is
not restated.
-/

namespace Step36

open DPLattice WeylFilt Doubling Twist Lemma35 Tensor2 Lemma35b LemmaW Cocycle Lift2

variable {A : Type*} [CommRing A]

/-! ### (K3), without `phi` -/

/-- (K3) the bijection `M.ι ⊕ Empty ≃ M.ι`, `inl i ↦ i`. -/
def sumEmptyEquiv (ι : Type*) : ι ⊕ Empty ≃ ι where
  toFun := Sum.elim id Empty.elim
  invFun := Sum.inl
  left_inv p := by rcases p with i | i <;> first | rfl | exact i.elim
  right_inv _ := rfl

/-- (K3) the bijection `Empty ⊕ M.ι ≃ M.ι`, `inr i ↦ i`. -/
def emptySumEquiv (ι : Type*) : Empty ⊕ ι ≃ ι where
  toFun := Sum.elim Empty.elim id
  invFun := Sum.inr
  left_inv p := by rcases p with i | i <;> first | rfl | exact i.elim
  right_inv _ := rfl

/-- (K3) the bijection of a type with an empty type onto `Empty`. -/
def toEmptyEquiv (ι : Type*) (h : IsEmpty ι) : ι ≃ Empty where
  toFun i := (h.false i).elim
  invFun e := e.elim
  left_inv i := (h.false i).elim
  right_inv e := e.elim

/-- (K3) `dsum M (zeroL A) ≅ M`, reindexing along `inl i ↦ i`. -/
def dsumZeroIso (M : DPLattice A) : Doubling.Iso (dsum M (zeroL A)) M :=
  isoOfReindex (M := dsum M (zeroL A)) (N := M) (sumEmptyEquiv M.ι)
    (fun p => by rcases p with i | i <;> first | rfl | exact i.elim)
    (fun _ => LinearMap.ext fun _ => rfl) (fun _ => LinearMap.ext fun _ => rfl)

/-- (K3) `dsum (zeroL A) M ≅ M`, reindexing along `inr i ↦ i`. -/
def zeroDsumIso (M : DPLattice A) : Doubling.Iso (dsum (zeroL A) M) M :=
  isoOfReindex (M := dsum (zeroL A) M) (N := M) (emptySumEquiv M.ι)
    (fun p => by rcases p with i | i <;> first | rfl | exact i.elim)
    (fun _ => LinearMap.ext fun _ => rfl) (fun _ => LinearMap.ext fun _ => rfl)

/-- (K3) an isomorphism onto `zeroL A` from a lattice with empty basis (reindexing). -/
def isoZeroOfIsEmpty (M : DPLattice A) (h : IsEmpty M.ι) : Doubling.Iso M (zeroL A) :=
  isoOfReindex (M := M) (N := zeroL A) (toEmptyEquiv M.ι h) (fun i => (h.false i).elim)
    (fun _ => LinearMap.ext fun _ => funext fun e => e.elim)
    (fun _ => LinearMap.ext fun _ => funext fun e => e.elim)

/-- (K3) `tensorV (zeroL A) ≅ zeroL A` (both bases are empty). -/
def tensorVZeroIso : Doubling.Iso (tensorV (zeroL A)) (zeroL A) :=
  isoZeroOfIsEmpty _ ⟨fun p => p.2.elim⟩

/-! ### (K1), without `phi` -/

/-- (K1) `tensorV (one A) ≅ V A`: C23 `tensorVIsoTensor` (`tensorV 𝟙 ≅ V ⊗ 𝟙`) followed by C23
`unitRightIso` (`V ⊗ 𝟙 ≅ V`). -/
def tensorVOneIso : Doubling.Iso (tensorV (one A)) (V A) :=
  (tensorVIsoTensor (one A)).trans (unitRightIso (V A))

/-- (K1) `tensorVOneIso` on basis vectors: `δ_{(e,())} ↦ δ_e`, and back. -/
theorem tensorVOneIso_single (e : Fin 2) :
    (tensorVOneIso (A := A)).hom.toLin (Pi.single (e, ()) 1) = Pi.single e 1 ∧
    (tensorVOneIso (A := A)).inv.toLin (Pi.single e 1) = Pi.single (e, ()) 1 :=
  ⟨(P8 (V A)).2.2.2.2.2.2.1 e, (P8 (V A)).2.2.2.2.2.2.2 e⟩

/-! ### (K4), definition and the parts without `phi` -/

/-- (K4) the finite direct sum of a list of DP-lattices: `dsumList [] = zeroL A`,
`dsumList (X :: L) = dsum X (dsumList L)`. -/
def dsumList : List (DPLattice A) → DPLattice A
  | [] => zeroL A
  | X :: L => dsum X (dsumList L)

/-- (K4) the defining equation `dsumList [] = zeroL A`. -/
theorem dsumList_nil : dsumList ([] : List (DPLattice A)) = zeroL A := rfl

/-- (K4) the defining equation `dsumList (X :: L) = dsum X (dsumList L)`. -/
theorem dsumList_cons (X : DPLattice A) (L : List (DPLattice A)) :
    dsumList (X :: L) = dsum X (dsumList L) := rfl

/-- (K4)(a) `dsumList (L₁ ++ L₂) ≅ dsum (dsumList L₁) (dsumList L₂)` (by induction on `L₁`,
with (K3) and C24 `dsumAssoc`). -/
def dsumListAppendIso : (L₁ L₂ : List (DPLattice A)) →
    Doubling.Iso (dsumList (L₁ ++ L₂)) (dsum (dsumList L₁) (dsumList L₂))
  | [], L₂ => (zeroDsumIso (dsumList L₂)).symm
  | X :: L₁, L₂ =>
      (dsumIso (Iso.refl X) (dsumListAppendIso L₁ L₂)).trans
        (dsumAssoc X (dsumList L₁) (dsumList L₂)).symm

/-- (K4)(a) the statement: `dsumList (L₁ ++ L₂) ≅ dsum (dsumList L₁) (dsumList L₂)`. -/
theorem K4a (L₁ L₂ : List (DPLattice A)) :
    Nonempty (Doubling.Iso (dsumList (L₁ ++ L₂)) (dsum (dsumList L₁) (dsumList L₂))) :=
  ⟨dsumListAppendIso L₁ L₂⟩

/-- (K4)(b) pointwise isomorphic lists (`List.Forall₂` of nonempty isomorphisms) have isomorphic
direct sums. -/
theorem K4b {L L' : List (DPLattice A)}
    (h : List.Forall₂ (fun X Y => Nonempty (Doubling.Iso X Y)) L L') :
    Nonempty (Doubling.Iso (dsumList L) (dsumList L')) := by
  induction h with
  | nil => exact ⟨Iso.refl _⟩
  | cons hXY _ ih =>
    obtain ⟨u⟩ := hXY
    obtain ⟨v⟩ := ih
    exact ⟨dsumIso u v⟩

/-- (K4)(b), the form of the file: if `L`, `L'` have the same length and
`Iso (L.get k) (L'.get k)` for every `k`, then `dsumList L ≅ dsumList L'`. -/
theorem K4b_get {L L' : List (DPLattice A)} (hlen : L.length = L'.length)
    (h : ∀ k : Fin L.length, Nonempty (Doubling.Iso (L.get k) (L'.get (k.cast hlen)))) :
    Nonempty (Doubling.Iso (dsumList L) (dsumList L')) := by
  refine K4b (List.forall₂_iff_get.mpr ⟨hlen, fun i h1 h2 => ?_⟩)
  exact h ⟨i, h1⟩

/-- (K4)(c), auxiliary: `tensorV (dsum M N) ≅ dsum (tensorV M) (tensorV N)` (C23 distributivity
`distribLeftIso` through `tensorVIsoTensor`). -/
def tensorVDsumIso (M N : DPLattice A) :
    Doubling.Iso (tensorV (dsum M N)) (dsum (tensorV M) (tensorV N)) :=
  ((tensorVIsoTensor (dsum M N)).trans (distribLeftIso (V A) M N)).trans
    (dsumIso (tensorVIsoTensor M).symm (tensorVIsoTensor N).symm)

/-- (K4)(c) `tensorV (dsumList L) ≅ dsumList (L.map tensorV)`. -/
def tensorVDsumListIso : (L : List (DPLattice A)) →
    Doubling.Iso (tensorV (dsumList L)) (dsumList (L.map tensorV))
  | [] => tensorVZeroIso
  | X :: L => (tensorVDsumIso X (dsumList L)).trans
      (dsumIso (Iso.refl (tensorV X)) (tensorVDsumListIso L))

/-- (K4)(c) the statement: `tensorV (dsumList L) ≅ dsumList (L.map tensorV)`. -/
theorem K4c (L : List (DPLattice A)) :
    Nonempty (Doubling.Iso (tensorV (dsumList L)) (dsumList (L.map tensorV))) :=
  ⟨tensorVDsumListIso L⟩

/-- (K4)(e) `dsumList [X] ≅ X` (it is `dsum X (zeroL A)`, then (K3)). -/
def dsumListSingletonIso (X : DPLattice A) : Doubling.Iso (dsumList [X]) X :=
  dsumZeroIso X

/-- (K4)(e) the statement: `dsumList [X] ≅ X`. -/
theorem K4e (X : DPLattice A) : Nonempty (Doubling.Iso (dsumList [X]) X) :=
  ⟨dsumListSingletonIso X⟩

/-! ### (K2), auxiliary lemmas -/

/-- (K2), auxiliary: on `Φ(M ⊕ N)`, the slotwise map `1 ⊗ inl` followed by the reindexing is the
inclusion of `Φ(M)`. -/
lemma funLeft_phiLin_inlL (M N : DPLattice A) (x : Fin 2 × M.ι → A) :
    LinearMap.funLeft A A (Equiv.prodSumDistrib (Fin 2) M.ι N.ι).symm
      (phiLin (inlL (A := A) (ι := M.ι) (κ := N.ι)) x) = inlL x := by
  funext p
  rcases p with ⟨e, i⟩ | ⟨e, j⟩
  · rcases fin_two_cases e with rfl | rfl <;> simp [phiLin, inlL, slice]
  · rcases fin_two_cases e with rfl | rfl <;> simp [phiLin, inlL, slice]

/-- (K2), auxiliary: the same for `1 ⊗ inr`. -/
lemma funLeft_phiLin_inrL (M N : DPLattice A) (x : Fin 2 × N.ι → A) :
    LinearMap.funLeft A A (Equiv.prodSumDistrib (Fin 2) M.ι N.ι).symm
      (phiLin (inrL (A := A) (ι := M.ι) (κ := N.ι)) x) = inrL x := by
  funext p
  rcases p with ⟨e, i⟩ | ⟨e, j⟩
  · rcases fin_two_cases e with rfl | rfl <;> simp [phiLin, inrL, slice]
  · rcases fin_two_cases e with rfl | rfl <;> simp [phiLin, inrL, slice]

lemma single_inl_eq_phiLin (M N : DPLattice A) (e : Fin 2) (i : M.ι) :
    (Pi.single (e, (Sum.inl i : M.ι ⊕ N.ι)) (1 : A) : Fin 2 × (M.ι ⊕ N.ι) → A) =
      phiLin (inlL (A := A) (ι := M.ι) (κ := N.ι)) (Pi.single (e, i) 1) := by
  rw [single_eq_bvec, single_eq_bvec, phiLin_bvec, Lemma35.single_inl]

lemma single_inr_eq_phiLin (M N : DPLattice A) (e : Fin 2) (j : N.ι) :
    (Pi.single (e, (Sum.inr j : M.ι ⊕ N.ι)) (1 : A) : Fin 2 × (M.ι ⊕ N.ι) → A) =
      phiLin (inrL (A := A) (ι := M.ι) (κ := N.ι)) (Pi.single (e, j) 1) := by
  rw [single_eq_bvec, single_eq_bvec, phiLin_bvec, Lemma35.single_inr]

/-- (K2), auxiliary: the reindexing intertwines a family of operators of `Φ(M ⊕ N)` with the
blockwise family on `Φ(M) ⊕ Φ(N)`, provided `1 ⊗ inl` and `1 ⊗ inr` intertwine them. -/
lemma phiDsum_comm (M N : DPLattice A) (G : Module.End A (Fin 2 × (M.ι ⊕ N.ι) → A))
    (GM : Module.End A (Fin 2 × M.ι → A)) (GN : Module.End A (Fin 2 × N.ι → A))
    (hl : phiLin inlL ∘ₗ GM = G ∘ₗ phiLin inlL) (hr : phiLin inrL ∘ₗ GN = G ∘ₗ phiLin inrL) :
    blk GM GN ∘ₗ LinearMap.funLeft A A (Equiv.prodSumDistrib (Fin 2) M.ι N.ι).symm =
      LinearMap.funLeft A A (Equiv.prodSumDistrib (Fin 2) M.ι N.ι).symm ∘ₗ G := by
  refine ext_single fun p => ?_
  rcases p with ⟨e, i | j⟩
  · simp only [LinearMap.comp_apply]
    rw [single_inl_eq_phiLin M N e i, ← LinearMap.comp_apply G, ← hl, LinearMap.comp_apply,
      funLeft_phiLin_inlL, funLeft_phiLin_inlL]
    exact LinearMap.congr_fun (blk_comp_inlL GM GN) _
  · simp only [LinearMap.comp_apply]
    rw [single_inr_eq_phiLin M N e j, ← LinearMap.comp_apply G, ← hr, LinearMap.comp_apply,
      funLeft_phiLin_inrL, funLeft_phiLin_inrL]
    exact LinearMap.congr_fun (blk_comp_inrL GM GN) _

/-! ### The parts with `phi` -/

section phi

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- **(K2)** `phi` is additive: `phi (dsum M N) ≅ dsum (phi M) (phi N)`, by the identity on the
reindexing `Fin 2 × (M.ι ⊕ N.ι) ≃ (Fin 2 × M.ι) ⊕ (Fin 2 × N.ι)` (C23 `isoOfReindex`; the
operators commute because `1 ⊗ inl`, `1 ⊗ inr` are the morphisms `phiHom inlHom`,
`phiHom inrHom`). -/
def phiDsumIso (M N : DPLattice A) : Doubling.Iso (phi (dsum M N)) (dsum (phi M) (phi N)) :=
  isoOfReindex (M := phi (dsum M N)) (N := dsum (phi M) (phi N))
    (Equiv.prodSumDistrib (Fin 2) M.ι N.ι)
    (fun p => by rcases p with ⟨e, i | j⟩ <;> rfl)
    (fun r => phiDsum_comm M N _ _ _ ((phiHom (inlHom M N)).comm_F r)
      ((phiHom (inrHom M N)).comm_F r))
    (fun r => phiDsum_comm M N _ _ _ ((phiHom (inlHom M N)).comm_E r)
      ((phiHom (inrHom M N)).comm_E r))

/-- **(K2)** the image of every basis vector: `δ_{(e, inl i)} ↦ δ_{inl (e,i)}`,
`δ_{(e, inr j)} ↦ δ_{inr (e,j)}` under `phiDsumIso M N`, and back under its inverse; the
underlying maps are the reindexing and its inverse. -/
theorem K2 (M N : DPLattice A) :
    (phiDsumIso M N).hom.toLin =
      LinearMap.funLeft A A (Equiv.prodSumDistrib (Fin 2) M.ι N.ι).symm ∧
    (phiDsumIso M N).inv.toLin = LinearMap.funLeft A A (Equiv.prodSumDistrib (Fin 2) M.ι N.ι) ∧
    (∀ (e : Fin 2) (i : M.ι), (phiDsumIso M N).hom.toLin (Pi.single (e, Sum.inl i) 1) =
      Pi.single (Sum.inl (e, i)) 1) ∧
    (∀ (e : Fin 2) (j : N.ι), (phiDsumIso M N).hom.toLin (Pi.single (e, Sum.inr j) 1) =
      Pi.single (Sum.inr (e, j)) 1) ∧
    (∀ (e : Fin 2) (i : M.ι), (phiDsumIso M N).inv.toLin (Pi.single (Sum.inl (e, i)) 1) =
      Pi.single (e, Sum.inl i) 1) ∧
    (∀ (e : Fin 2) (j : N.ι), (phiDsumIso M N).inv.toLin (Pi.single (Sum.inr (e, j)) 1) =
      Pi.single (e, Sum.inr j) 1) :=
  ⟨rfl, rfl, fun e i => funLeft_symm_single (Equiv.prodSumDistrib (Fin 2) M.ι N.ι) (e, Sum.inl i),
    fun e j => funLeft_symm_single (Equiv.prodSumDistrib (Fin 2) M.ι N.ι) (e, Sum.inr j),
    fun e i => funLeft_single (Equiv.prodSumDistrib (Fin 2) M.ι N.ι) (e, Sum.inl i),
    fun e j => funLeft_single (Equiv.prodSumDistrib (Fin 2) M.ι N.ι) (e, Sum.inr j)⟩

/-- (K3) `phi (zeroL A) ≅ zeroL A` (both bases are empty). -/
def phiZeroIso : Doubling.Iso (phi (zeroL A)) (zeroL A) :=
  isoZeroOfIsEmpty _ ⟨fun p => p.2.elim⟩

/-- **(K1)** `tensorV (one A) ≅ V A` (C23 `tensorVIsoTensor`, `unitRightIso`),
`phi (one A) ≅ V A` (C20 `D3`), hence `tensorV (one A) ≅ phi (one A)`. -/
theorem K1 : Nonempty (Doubling.Iso (tensorV (one A)) (V A)) ∧
    Nonempty (Doubling.Iso (phi (one A)) (V A)) ∧
    Nonempty (Doubling.Iso (tensorV (one A)) (phi (one A))) := by
  obtain ⟨u⟩ := Doubling.D3 (A := A)
  exact ⟨⟨tensorVOneIso⟩, ⟨u⟩, ⟨tensorVOneIso.trans u.symm⟩⟩

/-- **(K3)** `dsum M (zeroL A) ≅ M`, `dsum (zeroL A) M ≅ M`, `tensorV (zeroL A) ≅ zeroL A`,
`phi (zeroL A) ≅ zeroL A`. -/
theorem K3 (M : DPLattice A) : Nonempty (Doubling.Iso (dsum M (zeroL A)) M) ∧
    Nonempty (Doubling.Iso (dsum (zeroL A) M) M) ∧
    Nonempty (Doubling.Iso (tensorV (zeroL A)) (zeroL A)) ∧
    Nonempty (Doubling.Iso (phi (zeroL A)) (zeroL A)) :=
  ⟨⟨dsumZeroIso M⟩, ⟨zeroDsumIso M⟩, ⟨tensorVZeroIso⟩, ⟨phiZeroIso⟩⟩

/-- (K4)(d) `phi (dsumList L) ≅ dsumList (L.map phi)` (from (K2), (K3)). -/
def phiDsumListIso : (L : List (DPLattice A)) →
    Doubling.Iso (phi (dsumList L)) (dsumList (L.map phi))
  | [] => phiZeroIso
  | X :: L => (phiDsumIso X (dsumList L)).trans
      (dsumIso (Iso.refl (phi X)) (phiDsumListIso L))

/-- (K4)(d) the statement: `phi (dsumList L) ≅ dsumList (L.map phi)`. -/
theorem K4d (L : List (DPLattice A)) :
    Nonempty (Doubling.Iso (phi (dsumList L)) (dsumList (L.map phi))) :=
  ⟨phiDsumListIso L⟩

end phi

end Step36
