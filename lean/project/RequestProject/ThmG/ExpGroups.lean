module

public import Mathlib

/-!
# `CSG7_theorem_G.md`, auxiliary — finite abelian `p`-groups given by lists of exponents

Namespace `ColouredSand.ThmG`.  Auxiliary to Parts L, T, F, S and X of `CSG7_theorem_G.md`.

## Encoding

* A list of exponents `L : List ℕ` encodes the group `⊕_{e ∈ L} ℤ/p^e`, written
  `ExpGrp p L := (i : Fin L.length) → ZMod (p ^ L.get i)` (the product over the positions of `L`).
  This is exactly the shape `(i : Fin L.length) → ZMod (p ^ L.get i)` used in the statements of
  `CSG7_theorem_G.md`; `ExpGrp` is an `abbrev`, so the two are syntactically the same.
* "`≅`" of abelian groups is `≃+`.

## Contents

* `expCons`, `expAppend`, `expReplicate`, `expOne`, `expSingle`: the basic isomorphisms.
* `expPerm`: a permutation of the list of exponents gives an isomorphic group (used in (F2)).
* `expFlatMap`: the product over the positions of `L` of `ExpGrp p (f (L.get j))` is
  `ExpGrp p (L.flatMap f)` (used in (T2)).
* `expSum`: a finite product `Π σ, ExpGrp p (F σ)` is `ExpGrp p M` whenever the multiset union of
  the `F σ` is `M` (used in (X1)).
* `cancelFree`: from `A × S ≃+ B × T` with `A`, `B` torsion-free and `S`, `T` torsion, `S ≃+ T`
  (used in (T2): cancelling the free parts).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmG

/-- `ExpGrp p L = Π_{i : Fin L.length} ℤ/p^{L.get i}`, the group `⊕_{e ∈ L} ℤ/p^e`
(encoding used throughout `CSG7_theorem_G.md`). -/
abbrev ExpGrp (p : ℕ) (L : List ℕ) : Type := (i : Fin L.length) → ZMod (p ^ L.get i)

/-- The dependent `Fin.cons` as an additive equivalence `α 0 × Π i, α i.succ ≃+ Π i, α i`
(auxiliary). -/
def finConsAddEquiv {n : ℕ} (α : Fin (n + 1) → Type*) [∀ i, AddCommGroup (α i)] :
    (α 0 × ((i : Fin n) → α i.succ)) ≃+ ((i : Fin (n + 1)) → α i) where
  toEquiv := Fin.consEquiv α
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl

/-- Transport of `ExpGrp` along an equality of lists (auxiliary). -/
def expCast (p : ℕ) {L L' : List ℕ} (h : L = L') : ExpGrp p L ≃+ ExpGrp p L' := by
  subst h; exact AddEquiv.refl _

/-- A product indexed by `Fin n` with `n = 0` is trivial (auxiliary). -/
def uniqueFinZero {n : ℕ} (hn : n = 0) (G : Fin n → Type*) : Unique ((i : Fin n) → G i) := by
  subst hn; exact Pi.uniqueOfIsEmpty _

/-- Two products indexed by `Fin 0` are isomorphic (auxiliary). -/
def addEquivFinZero {n m : ℕ} (hn : n = 0) (hm : m = 0) (G : Fin n → Type*) (H : Fin m → Type*)
    [∀ i, AddCommGroup (G i)] [∀ i, AddCommGroup (H i)] :
    ((i : Fin n) → G i) ≃+ ((i : Fin m) → H i) := by
  subst hn hm; exact AddEquiv.ofUnique

/-- `ExpGrp p [] ` is trivial. -/
instance expNil_unique (p : ℕ) : Unique (ExpGrp p []) := uniqueFinZero rfl _

/-- Additive version of `Equiv.piCongrLeft'` (auxiliary). -/
def piCongrLeftAdd {ι ι' : Type*} (G : ι → Type*) [∀ i, AddCommGroup (G i)] (e : ι ≃ ι') :
    ((i : ι) → G i) ≃+ ((i : ι') → G (e.symm i)) where
  toEquiv := Equiv.piCongrLeft' G e
  map_add' _ _ := rfl

/-- `ExpGrp p (a :: L) ≃+ ℤ/p^a × ExpGrp p L`. -/
def expCons (p a : ℕ) (L : List ℕ) : ExpGrp p (a :: L) ≃+ ZMod (p ^ a) × ExpGrp p L :=
  (finConsAddEquiv (fun i : Fin (L.length + 1) => ZMod (p ^ (a :: L).get i))).symm

/-- `ExpGrp p [a] ≃+ ℤ/p^a`. -/
def expSingle (p a : ℕ) : ExpGrp p [a] ≃+ ZMod (p ^ a) :=
  (expCons p a []).trans AddEquiv.prodUnique

/-- `ExpGrp p (L₁ ++ L₂) ≃+ ExpGrp p L₁ × ExpGrp p L₂`. -/
def expAppend (p : ℕ) : (L₁ L₂ : List ℕ) → ExpGrp p (L₁ ++ L₂) ≃+ ExpGrp p L₁ × ExpGrp p L₂
  | [], _ => (AddEquiv.uniqueProd).symm
  | a :: L₁, L₂ =>
      ((expCons p a (L₁ ++ L₂)).trans ((AddEquiv.refl _).prodCongr (expAppend p L₁ L₂))).trans
        ((AddEquiv.prodAssoc).symm.trans ((expCons p a L₁).symm.prodCongr (AddEquiv.refl _)))

/-- `ExpGrp p (replicate n e) ≃+ (Fin n → ℤ/p^e)`. -/
def expReplicate (p e : ℕ) : (n : ℕ) → ExpGrp p (List.replicate n e) ≃+ (Fin n → ZMod (p ^ e))
  | 0 => addEquivFinZero rfl rfl _ _
  | n + 1 => ((expCons p e (List.replicate n e)).trans
      ((AddEquiv.refl _).prodCongr (expReplicate p e n))).trans
      (finConsAddEquiv (fun _ : Fin (n + 1) => ZMod (p ^ e)))

/-- `ℤ/p^1 ≃+ ℤ/p`. -/
def zmodPowOne (p : ℕ) : ZMod (p ^ 1) ≃+ ZMod p := (ZMod.ringEquivCongr (pow_one p)).toAddEquiv

/-- `ExpGrp p (replicate n 1) ≃+ (Fin n → ℤ/p)`, i.e. `(ℤ/p)^n`. -/
def expOne (p n : ℕ) : ExpGrp p (List.replicate n 1) ≃+ (Fin n → ZMod p) :=
  (expReplicate p 1 n).trans (AddEquiv.piCongrRight fun _ => zmodPowOne p)

/-- A permutation of the list of exponents gives an isomorphic group. -/
theorem expPerm (p : ℕ) {L L' : List ℕ} (h : L.Perm L') : Nonempty (ExpGrp p L ≃+ ExpGrp p L') := by
  induction h with
  | nil => exact ⟨AddEquiv.refl _⟩
  | cons x _ ih =>
      obtain ⟨e⟩ := ih
      exact ⟨((expCons p x _).trans ((AddEquiv.refl _).prodCongr e)).trans (expCons p x _).symm⟩
  | swap x y l =>
      exact ⟨((expCons p y _).trans ((AddEquiv.refl _).prodCongr (expCons p x l))).trans
        ((AddEquiv.prodAssoc.symm.trans ((AddEquiv.prodComm).prodCongr (AddEquiv.refl _))).trans
          (AddEquiv.prodAssoc.trans (((AddEquiv.refl _).prodCongr (expCons p y l).symm).trans
            (expCons p x _).symm)))⟩
  | trans _ _ ih1 ih2 =>
      obtain ⟨e1⟩ := ih1
      obtain ⟨e2⟩ := ih2
      exact ⟨e1.trans e2⟩

/-- `Π_{j : Fin L.length} ExpGrp p (f (L.get j)) ≃+ ExpGrp p (L.flatMap f)`. -/
def expFlatMap (p : ℕ) (f : ℕ → List ℕ) : (L : List ℕ) →
    ((j : Fin L.length) → ExpGrp p (f (L.get j))) ≃+ ExpGrp p (L.flatMap f)
  | [] => addEquivFinZero rfl rfl _ _
  | a :: L =>
      ((finConsAddEquiv (fun j : Fin (L.length + 1) => ExpGrp p (f ((a :: L).get j)))).symm.trans
        ((AddEquiv.refl _).prodCongr (expFlatMap p f L))).trans
        ((expAppend p (f a) (L.flatMap f)).symm.trans (expCast p (List.flatMap_cons).symm))

/-- `Π_{i : Fin n} ExpGrp p (F i) ≃+ ExpGrp p (ofFn F).flatten` (auxiliary for `expSum`). -/
def expOfFn (p : ℕ) : (n : ℕ) → (F : Fin n → List ℕ) →
    ((i : Fin n) → ExpGrp p (F i)) ≃+ ExpGrp p (List.ofFn F).flatten
  | 0, F => addEquivFinZero rfl (by simp) _ _
  | n + 1, F =>
      ((finConsAddEquiv (fun i : Fin (n + 1) => ExpGrp p (F i))).symm.trans
        ((AddEquiv.refl _).prodCongr (expOfFn p n (fun i => F i.succ)))).trans
        ((expAppend p _ _).symm.trans (expCast p (by rw [List.ofFn_succ, List.flatten_cons])))

lemma coe_flatten_ofFn : (n : ℕ) → (F : Fin n → List ℕ) →
    (((List.ofFn F).flatten : List ℕ) : Multiset ℕ) = ∑ i, (F i : Multiset ℕ)
  | 0, _ => by simp
  | n + 1, F => by
      rw [List.ofFn_succ, List.flatten_cons, ← Multiset.coe_add, coe_flatten_ofFn n,
        Fin.sum_univ_succ]

/-- A finite product of groups `ExpGrp p (F σ)` is `ExpGrp p M` when the multiset union of the
lists `F σ` is `M`. -/
theorem expSum (p : ℕ) {ι : Type*} [Fintype ι] (F : ι → List ℕ) (M : List ℕ)
    (h : ∑ σ, (F σ : Multiset ℕ) = (M : Multiset ℕ)) :
    Nonempty (((σ : ι) → ExpGrp p (F σ)) ≃+ ExpGrp p M) := by
  let e := Fintype.equivFin ι
  have e1 : ((σ : ι) → ExpGrp p (F σ)) ≃+ ((i : Fin (Fintype.card ι)) → ExpGrp p (F (e.symm i))) :=
    piCongrLeftAdd (fun σ => ExpGrp p (F σ)) e
  have hperm : (List.ofFn (fun i => F (e.symm i))).flatten.Perm M := by
    rw [← Multiset.coe_eq_coe, coe_flatten_ofFn, ← h]
    exact Equiv.sum_comp e.symm (fun σ => (F σ : Multiset ℕ))
  obtain ⟨e3⟩ := expPerm p hperm
  exact ⟨(e1.trans (expOfFn p _ _)).trans e3⟩

/-- Cancelling torsion-free parts: if `A`, `B` have no non-zero element of finite order and every
element of `S`, `T` has finite order, an isomorphism `A × S ≃+ B × T` restricts to `S ≃+ T`. -/
def cancelFree {A S B T : Type*} [AddCommGroup A] [AddCommGroup S] [AddCommGroup B]
    [AddCommGroup T] (hA : ∀ x : A, IsOfFinAddOrder x → x = 0)
    (hB : ∀ x : B, IsOfFinAddOrder x → x = 0) (hS : ∀ s : S, IsOfFinAddOrder s)
    (hT : ∀ t : T, IsOfFinAddOrder t) (e : A × S ≃+ B × T) : S ≃+ T :=
  have h1 : ∀ s : S, (e (0, s)).1 = 0 := fun s => hB _ (by
    have : IsOfFinAddOrder ((0 : A), s) := IsOfFinAddOrder.zero.prod_mk (hS s)
    exact (AddMonoidHom.isOfFinAddOrder e.toAddMonoidHom this).fst)
  have h2 : ∀ t : T, (e.symm (0, t)).1 = 0 := fun t => hA _ (by
    have : IsOfFinAddOrder ((0 : B), t) := IsOfFinAddOrder.zero.prod_mk (hT t)
    exact (AddMonoidHom.isOfFinAddOrder e.symm.toAddMonoidHom this).fst)
  { toFun := fun s => (e (0, s)).2
    invFun := fun t => (e.symm (0, t)).2
    left_inv := fun s => by
      have : ((0 : B), (e (0, s)).2) = e (0, s) := Prod.ext (h1 s).symm rfl
      simp only [this, AddEquiv.symm_apply_apply]
    right_inv := fun t => by
      have : ((0 : A), (e.symm (0, t)).2) = e.symm (0, t) := Prod.ext (h2 t).symm rfl
      simp only [this, AddEquiv.apply_symm_apply]
    map_add' := fun s s' => by
      have : ((0 : A), s + s') = (0, s) + (0, s') := by simp
      rw [this, map_add, Prod.snd_add] }

/-- `ExpGrp p L` is a torsion group (every element has finite order) for `p ≠ 0`. -/
lemma expGrp_torsion {p : ℕ} (hp : p ≠ 0) (L : List ℕ) (x : ExpGrp p L) : IsOfFinAddOrder x := by
  haveI : NeZero p := ⟨hp⟩
  exact isOfFinAddOrder_of_finite x

/-- A finite product of torsion groups is a torsion group. -/
lemma pi_torsion {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    (h : ∀ i (x : G i), IsOfFinAddOrder x) (x : (i : ι) → G i) : IsOfFinAddOrder x :=
  IsOfFinAddOrder.pi fun i => h i (x i)

/-- `R^n` has no non-zero element of finite order when `R` is a domain of characteristic zero. -/
lemma pi_torsionFree {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (n : ℕ)
    (x : Fin n → R) (hx : IsOfFinAddOrder x) : x = 0 := by
  obtain ⟨k, hk, h⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero).1 hx
  funext i
  have := congrFun h i
  rw [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hk.ne')

end ColouredSand.ThmG
