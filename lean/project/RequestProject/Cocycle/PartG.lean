module

public import RequestProject.Cocycle.Weights

/-!
# `C27_cocycles_and_filtrations.md`: Part G — (G2) submodule, (G3), (G4), (G5), (G6)

Encodings (namespace `Cocycle`):

* `cocycles M N : Submodule A (Pair M N)` is the submodule of cocycles ((G2), last sentence).
* (G3) `incl M N c hc : Hom N (glue M N c hc)` has underlying map `u ↦ Sum.elim u 0 = (u, 0)`;
  `proj M N c hc : Hom (glue M N c hc) M` has underlying map `z ↦ z ∘ Sum.inr`, i.e.
  `(u, v) ↦ v`.
* (G4) `d ψ = (r ↦ ψ ∘ M.Fd r − N.Fd r ∘ ψ, r ↦ ψ ∘ M.Ed r − N.Ed r ∘ ψ)`;
  `IsCoboundary c` means `∃ ψ, IsWtPres ψ ∧ d ψ = c`.
* (G6) `pcomp c i = c ∘ i = (r ↦ cF r ∘ i, r ↦ cE r ∘ i)` and
  `qcomp j c = j ∘ c = (r ↦ j ∘ cF r, r ↦ j ∘ cE r)`.
-/

@[expose] public section

noncomputable section

namespace Cocycle

open DPLattice WeylFilt Doubling LemmaW Finset

variable {A : Type*} [CommRing A]

variable {M N : DPLattice A}

/-! ### (G2) Cocycles form a submodule -/

lemma cocycleEqs_zero : CocycleEqs (0 : Pair M N) where
  W_F _ _ _ _ := rfl
  W_E _ _ _ _ := rfl
  P0_F := rfl
  P0_E := rfl
  P1_F _ _ := by simp
  P1_E _ _ := by simp
  K _ _ _ := by simp

lemma cocycleEqs_add {c c' : Pair M N} (h : CocycleEqs c) (h' : CocycleEqs c') :
    CocycleEqs (c + c') where
  W_F i r j hj := by simp [h.W_F i r j hj, h'.W_F i r j hj]
  W_E i r j hj := by simp [h.W_E i r j hj, h'.W_E i r j hj]
  P0_F := by simp [h.P0_F, h'.P0_F]
  P0_E := by simp [h.P0_E, h'.P0_E]
  P1_F a b := by
    calc N.Fd a ∘ₗ (c + c').1 b + (c + c').1 a ∘ₗ M.Fd b
        = (N.Fd a ∘ₗ c.1 b + c.1 a ∘ₗ M.Fd b) + (N.Fd a ∘ₗ c'.1 b + c'.1 a ∘ₗ M.Fd b) := by
          simp only [Prod.fst_add, Pi.add_apply, LinearMap.comp_add, LinearMap.add_comp]; abel
      _ = _ := by rw [h.P1_F, h'.P1_F, ← smul_add]; rfl
  P1_E a b := by
    calc N.Ed a ∘ₗ (c + c').2 b + (c + c').2 a ∘ₗ M.Ed b
        = (N.Ed a ∘ₗ c.2 b + c.2 a ∘ₗ M.Ed b) + (N.Ed a ∘ₗ c'.2 b + c'.2 a ∘ₗ M.Ed b) := by
          simp only [Prod.snd_add, Pi.add_apply, LinearMap.comp_add, LinearMap.add_comp]; abel
      _ = _ := by rw [h.P1_E, h'.P1_E, ← smul_add]; rfl
  K i r s := by
    have e := congrArg₂ (· + ·) (h.K i r s) (h'.K i r s)
    simp only at e
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.add_apply, map_add]
    rw [← Finset.sum_add_distrib] at e
    rw [show ∀ x y z w : N.ι → A, x + y + (z + w) = (x + z) + (y + w) from
      fun x y z w => by abel, e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_add]; congr 1; abel

lemma cocycleEqs_smul (t : A) {c : Pair M N} (h : CocycleEqs c) : CocycleEqs (t • c) where
  W_F i r j hj := by simp [h.W_F i r j hj]
  W_E i r j hj := by simp [h.W_E i r j hj]
  P0_F := by simp [h.P0_F]
  P0_E := by simp [h.P0_E]
  P1_F a b := by
    simp only [Prod.smul_fst, Pi.smul_apply, LinearMap.comp_smul, LinearMap.smul_comp]
    rw [← smul_add, h.P1_F, smul_comm]
  P1_E a b := by
    simp only [Prod.smul_snd, Pi.smul_apply, LinearMap.comp_smul, LinearMap.smul_comp]
    rw [← smul_add, h.P1_E, smul_comm]
  K i r s := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.smul_apply, map_smul]
    rw [← smul_add, h.K i r s, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    module

/-- (G2) In particular, the cocycles from `M` to `N` form an `A`-submodule of the pairs of
families. -/
def cocycles (M N : DPLattice A) : Submodule A (Pair M N) where
  carrier := {c | IsCocycle c}
  zero_mem' := (G2 0).mpr cocycleEqs_zero
  add_mem' {c c'} hc hc' := (G2 _).mpr (cocycleEqs_add ((G2 c).mp hc) ((G2 c').mp hc'))
  smul_mem' t c hc := (G2 _).mpr (cocycleEqs_smul t ((G2 c).mp hc))

lemma mem_cocycles {c : Pair M N} : c ∈ cocycles M N ↔ IsCocycle c := Iff.rfl

lemma isCocycle_zero : IsCocycle (0 : Pair M N) := (cocycles M N).zero_mem

lemma isCocycle_add {c c' : Pair M N} (hc : IsCocycle c) (hc' : IsCocycle c') :
    IsCocycle (c + c') := (cocycles M N).add_mem hc hc'

lemma isCocycle_sub {c c' : Pair M N} (hc : IsCocycle c) (hc' : IsCocycle c') :
    IsCocycle (c - c') := (cocycles M N).sub_mem hc hc'

/-! ### (G3) The extension -/

lemma hop_elim (u : N.ι → A) (v : M.ι → A) :
    Hop (gwt M N) (Sum.elim u v) = Sum.elim (Hop N.wt u) (Hop M.wt v) := by
  funext x; cases x <;> rfl

/-- (G3, auxiliary) the linear map `u ↦ (u, 0)`. -/
def inclL (M N : DPLattice A) : (N.ι → A) →ₗ[A] (N.ι ⊕ M.ι → A) where
  toFun u := Sum.elim u 0
  map_add' u u' := by simp
  map_smul' t u := by simp

@[simp] lemma inclL_apply (u : N.ι → A) : inclL M N u = Sum.elim u 0 := rfl

/-- (G3, auxiliary) the linear map `(u, v) ↦ v`. -/
def projL (M N : DPLattice A) : (N.ι ⊕ M.ι → A) →ₗ[A] (M.ι → A) :=
  LinearMap.funLeft A A Sum.inr

@[simp] lemma projL_apply (z : N.ι ⊕ M.ι → A) : projL M N z = z ∘ Sum.inr := rfl

lemma projL_elim (u : N.ι → A) (v : M.ι → A) : projL M N (Sum.elim u v) = v := rfl

/-- (G3) `incl : Hom N (glue M N c)`, `u ↦ (u, 0)`. -/
def incl (M N : DPLattice A) (c : Pair M N) (hc : IsCocycle c) : Hom N (glue M N c hc) where
  toLin := inclL M N
  comm_F r := LinearMap.ext fun u => by
    change Sum.elim (N.Fd r u) 0 = gF c r (Sum.elim u 0)
    rw [gF_elim, map_zero, map_zero, add_zero]
  comm_E r := LinearMap.ext fun u => by
    change Sum.elim (N.Ed r u) 0 = gE c r (Sum.elim u 0)
    rw [gE_elim, map_zero, map_zero, add_zero]
  comm_H := LinearMap.ext fun u => by
    change Sum.elim (Hop N.wt u) 0 = Hop (gwt M N) (Sum.elim u 0)
    rw [hop_elim, map_zero]

/-- (G3) `proj : Hom (glue M N c) M`, `(u, v) ↦ v`. -/
def proj (M N : DPLattice A) (c : Pair M N) (hc : IsCocycle c) : Hom (glue M N c hc) M where
  toLin := projL M N
  comm_F r := LinearMap.ext fun z => by
    rw [← elim_comp z]
    change projL M N (gF c r _) = _
    rw [gF_elim]; rfl
  comm_E r := LinearMap.ext fun z => by
    rw [← elim_comp z]
    change projL M N (gE c r _) = _
    rw [gE_elim]; rfl
  comm_H := LinearMap.ext fun z => by
    rw [← elim_comp z]
    change projL M N (Hop (gwt M N) _) = _
    rw [hop_elim]; rfl

@[simp] lemma incl_toLin (c : Pair M N) (hc : IsCocycle c) (u : N.ι → A) :
    (incl M N c hc).toLin u = Sum.elim u 0 := rfl

@[simp] lemma proj_toLin (c : Pair M N) (hc : IsCocycle c) (z : N.ι ⊕ M.ι → A) :
    (proj M N c hc).toLin z = z ∘ Sum.inr := rfl

/-- (G3) `incl` and `proj` are weight-preserving and `ShortExact incl proj`. -/
theorem G3 (c : Pair M N) (hc : IsCocycle c) :
    IsWtPres (incl M N c hc).toLin ∧ IsWtPres (proj M N c hc).toLin ∧
      ShortExact (incl M N c hc) (proj M N c hc) := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, ⟨fun u u' huu => ?_, fun v => ?_, ?_⟩⟩
  · cases j with
    | inl j =>
      have : j ≠ i := fun h => hij (h ▸ rfl)
      simp [this]
    | inr j => rfl
  · cases i with
    | inl i => rfl
    | inr i =>
      have : j ≠ i := fun h => hij (h ▸ rfl)
      show (Pi.single (Sum.inr i) (1 : A) : N.ι ⊕ M.ι → A) (Sum.inr j) = 0
      rw [single_inr]
      simp [this]
  · exact (elim_eq_iff.mp huu).1
  · exact ⟨Sum.elim 0 v, rfl⟩
  · ext z
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨u, rfl⟩; rfl
    · intro hz
      refine ⟨z ∘ Sum.inl, ?_⟩
      change Sum.elim (z ∘ Sum.inl) 0 = z
      rw [← elim_comp z]
      change Sum.elim (z ∘ Sum.inl) 0 = Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr)
      rw [show z ∘ Sum.inr = 0 from hz]

/-! ### (G4) Coboundaries -/

/-- (G4) `dψ := (r ↦ ψ ∘ M.Fd r − N.Fd r ∘ ψ, r ↦ ψ ∘ M.Ed r − N.Ed r ∘ ψ)`. -/
def d (ψ : Lin M N) : Pair M N :=
  (fun r => ψ ∘ₗ M.Fd r - N.Fd r ∘ₗ ψ, fun r => ψ ∘ₗ M.Ed r - N.Ed r ∘ₗ ψ)

@[simp] lemma d_fst (ψ : Lin M N) (r : ℕ) : (d ψ).1 r = ψ ∘ₗ M.Fd r - N.Fd r ∘ₗ ψ := rfl
@[simp] lemma d_snd (ψ : Lin M N) (r : ℕ) : (d ψ).2 r = ψ ∘ₗ M.Ed r - N.Ed r ∘ₗ ψ := rfl

lemma d_add (ψ ψ' : Lin M N) : d (ψ + ψ') = d ψ + d ψ' := by
  refine Prod.ext (funext fun r => ?_) (funext fun r => ?_) <;>
  · simp only [d_fst, d_snd, Prod.fst_add, Prod.snd_add, Pi.add_apply, LinearMap.add_comp,
      LinearMap.comp_add]
    abel

lemma d_zero : d (0 : Lin M N) = 0 := by
  refine Prod.ext (funext fun r => ?_) (funext fun r => ?_) <;> simp

/-- (G4) `c` is a *coboundary*: `c = dψ` for a weight-preserving `ψ`. -/
def IsCoboundary (c : Pair M N) : Prop := ∃ ψ : Lin M N, IsWtPres ψ ∧ d ψ = c

/-- (G4) For a weight-preserving `ψ`, `dψ` is a cocycle (the operator `[[1, ψ], [0, 1]]`
conjugates the glued data of `0` into those of `dψ`). -/
theorem G4 {ψ : Lin M N} (hψ : IsWtPres ψ) : IsCocycle (d ψ) := by
  refine isDP_transport (glue M N 0 isCocycle_zero)
    (blk (LinearMap.id : Module.End A (N.ι → A)) ψ (LinearMap.id : Module.End A (M.ι → A)))
    ?_ ?_ ?_ ?_
  · intro i k hik
    change gwt M N i ≠ gwt M N k at hik
    change blk LinearMap.id ψ LinearMap.id (Pi.single i (1 : A) : N.ι ⊕ M.ι → A) k = 0
    cases i with
    | inl i =>
      rw [single_inl, blk_elim]
      cases k with
      | inl k =>
        have : k ≠ i := fun h => hik (h ▸ rfl)
        simp [this]
      | inr k => simp
    | inr i =>
      rw [single_inr, blk_elim]
      cases k with
      | inl k => simpa using hψ i k hik
      | inr k =>
        have : k ≠ i := fun h => hik (h ▸ rfl)
        simp [this]
  · intro r
    change blk LinearMap.id ψ LinearMap.id ∘ₗ blk (N.Fd r) 0 (M.Fd r) =
      blk (N.Fd r) ((d ψ).1 r) (M.Fd r) ∘ₗ blk LinearMap.id ψ LinearMap.id
    rw [blk_comp, blk_comp, blk_eq_iff, d_fst]
    refine ⟨rfl, ?_, rfl⟩
    simp only [LinearMap.comp_id, LinearMap.comp_zero, zero_add]
    abel
  · intro r
    change blk LinearMap.id ψ LinearMap.id ∘ₗ blk (N.Ed r) 0 (M.Ed r) =
      blk (N.Ed r) ((d ψ).2 r) (M.Ed r) ∘ₗ blk LinearMap.id ψ LinearMap.id
    rw [blk_comp, blk_comp, blk_eq_iff, d_snd]
    refine ⟨rfl, ?_, rfl⟩
    simp only [LinearMap.comp_id, LinearMap.comp_zero, zero_add]
    abel
  · intro k
    cases k with
    | inl k =>
      refine ⟨Sum.elim (Pi.single k 1) 0, elim_inWt (inWt_single N.wt k) inWt_zero, ?_⟩
      show blk LinearMap.id ψ LinearMap.id (Sum.elim (Pi.single k 1) (0 : M.ι → A)) = _
      rw [single_inl, blk_elim]
      simp
    | inr k =>
      refine ⟨Sum.elim (-ψ (Pi.single k 1)) (Pi.single k 1), ?_, ?_⟩
      · exact elim_inWt (fun j hj => by simp [inWt_map hψ (inWt_single M.wt k) j hj])
          (inWt_single M.wt k)
      · show blk LinearMap.id ψ LinearMap.id
          (Sum.elim (-ψ (Pi.single k 1)) (Pi.single k (1 : A))) = _
        rw [single_inr, blk_elim]
        simp

end Cocycle
