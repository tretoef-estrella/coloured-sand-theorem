module

public import RequestProject.LemmaW.All

/-!
# `C27_cocycles_and_filtrations.md`: Setting, (G0), (G1), (G2)

Encodings (namespace `Cocycle`), reusing C18 (`DPLattice`, `IsDP`, `Hom`, `delta`, `nabla`,
`weylWt`), C19 (`Hom.id`, `Hom.comp`, `Hom.ext'`, `ShortExact`), C20 (`Iso`) and C25
(`IsWtPres`, `pr`, `HasWt`, `P1`, `P2`, `E1`, `E2`, `E3`, `exists_section`,
`exists_retraction_of_section`):

* A vector of a DP-lattice `M` is a function `M.ι → A`; `δ_i = Pi.single i 1`.
* `Lin M N` (Setting) is `(M.ι → A) →ₗ[A] (N.ι → A)`.
* A pair `c = (cF, cE)` of families `cF r, cE r : Lin(M, N)` is an element of
  `Pair M N := (ℕ → Lin M N) × (ℕ → Lin M N)` (an `A`-module); `c.1 = cF`, `c.2 = cE`.
* A vector `z : N.ι ⊕ M.ι → A` is `z = (u, v)` with `u = z ∘ Sum.inl`, `v = z ∘ Sum.inr`;
  conversely `(u, v)` is `Sum.elim u v`.
* `blk a b d` is the block upper-triangular operator `[[a, b], [0, d]]` on `N.ι ⊕ M.ι → A`:
  `(u, v) ↦ (a u + b v, d v)`.
* (G0) `zeroL A` has basis `Empty`, all operators `1`.
* (G1) The glued data of `c` have weights `gwt M N = Sum.elim N.wt M.wt` and operators
  `gF c r = blk (N.Fd r) (c.1 r) (M.Fd r)`, `gE c r = blk (N.Ed r) (c.2 r) (M.Ed r)`.
  `IsCocycle c` means `IsDP (gwt M N) (gF c) (gE c)`; for such `c`, `glue M N c hc` is the
  DP-lattice they define.
* (G2) `CocycleEqs c` bundles the equations (W), (P0), (P1), (K) of the file;
  `G2 : IsCocycle c ↔ CocycleEqs c`.
-/

@[expose] public section

noncomputable section

namespace Cocycle

open DPLattice WeylFilt Doubling LemmaW Finset

variable {A : Type*} [CommRing A]

/-! ### Setting -/

/-- Setting: `Lin(M, N) := (M.ι → A) →ₗ[A] (N.ι → A)`. -/
abbrev Lin (M N : DPLattice A) := (M.ι → A) →ₗ[A] (N.ι → A)

/-- (G1): a pair `c = (cF, cE)` of families `cF r, cE r : Lin(M, N)`, `r : ℕ`. -/
abbrev Pair (M N : DPLattice A) := (ℕ → Lin M N) × (ℕ → Lin M N)

/-! ### (G0) The zero lattice -/

/-- (G0, auxiliary) the raw data on `Empty` satisfy `IsDP`. -/
lemma zeroL_isDP : IsDP (A := A) (Empty.elim : Empty → ℤ) (fun _ => 1) (fun _ => 1) where
  W_F i := i.elim
  W_E i := i.elim
  P0_F := rfl
  P0_E := rfl
  P1_F _ _ := Subsingleton.elim _ _
  P1_E _ _ := Subsingleton.elim _ _
  K i := i.elim

/-- (G0) The zero lattice `zeroL A`: basis `Empty`; it is a DP-lattice. -/
def zeroL (A : Type*) [CommRing A] : DPLattice A where
  ι := Empty
  wt := Empty.elim
  Fd _ := 1
  Ed _ := 1
  isDP := zeroL_isDP

/-! ### Block upper-triangular operators -/

section blk

variable {ι κ ι' κ' ι'' κ'' : Type*}

/-- (G1) The block upper-triangular operator `[[a, b], [0, d]]` from `ι ⊕ κ → A` to
`ι' ⊕ κ' → A`: `(u, v) ↦ (a u + b v, d v)`. -/
def blk (a : (ι → A) →ₗ[A] (ι' → A)) (b : (κ → A) →ₗ[A] (ι' → A))
    (d : (κ → A) →ₗ[A] (κ' → A)) : (ι ⊕ κ → A) →ₗ[A] (ι' ⊕ κ' → A) where
  toFun z := Sum.elim (a (z ∘ Sum.inl) + b (z ∘ Sum.inr)) (d (z ∘ Sum.inr))
  map_add' z z' := by
    funext x
    cases x with
    | inl x =>
      simp only [Sum.elim_inl, Pi.add_apply]
      rw [show (z + z') ∘ Sum.inl = z ∘ Sum.inl + z' ∘ Sum.inl from rfl,
        show (z + z') ∘ Sum.inr = z ∘ Sum.inr + z' ∘ Sum.inr from rfl, map_add, map_add]
      simp only [Pi.add_apply]; ring
    | inr x =>
      simp only [Sum.elim_inr, Pi.add_apply]
      rw [show (z + z') ∘ Sum.inr = z ∘ Sum.inr + z' ∘ Sum.inr from rfl, map_add]
      rfl
  map_smul' t z := by
    funext x
    cases x with
    | inl x =>
      simp only [Sum.elim_inl, Pi.smul_apply, RingHom.id_apply]
      rw [show (t • z) ∘ Sum.inl = t • (z ∘ Sum.inl) from rfl,
        show (t • z) ∘ Sum.inr = t • (z ∘ Sum.inr) from rfl, map_smul, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    | inr x =>
      simp only [Sum.elim_inr, Pi.smul_apply, RingHom.id_apply]
      rw [show (t • z) ∘ Sum.inr = t • (z ∘ Sum.inr) from rfl, map_smul]
      rfl

@[simp] lemma blk_elim (a : (ι → A) →ₗ[A] (ι' → A)) (b : (κ → A) →ₗ[A] (ι' → A))
    (d : (κ → A) →ₗ[A] (κ' → A)) (u : ι → A) (v : κ → A) :
    blk a b d (Sum.elim u v) = Sum.elim (a u + b v) (d v) := rfl

lemma blk_apply (a : (ι → A) →ₗ[A] (ι' → A)) (b : (κ → A) →ₗ[A] (ι' → A))
    (d : (κ → A) →ₗ[A] (κ' → A)) (z : ι ⊕ κ → A) :
    blk a b d z = Sum.elim (a (z ∘ Sum.inl) + b (z ∘ Sum.inr)) (d (z ∘ Sum.inr)) := rfl

omit [CommRing A] in
lemma elim_comp (z : ι ⊕ κ → A) : Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr) = z :=
  Sum.elim_comp_inl_inr z

omit [CommRing A] in
lemma elim_eq_iff {u u' : ι → A} {v v' : κ → A} :
    Sum.elim u v = Sum.elim u' v' ↔ u = u' ∧ v = v' := by
  constructor
  · intro h
    exact ⟨funext fun x => congrFun h (Sum.inl x), funext fun x => congrFun h (Sum.inr x)⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] lemma elim_add (u u' : ι → A) (v v' : κ → A) :
    Sum.elim u v + Sum.elim u' v' = Sum.elim (u + u') (v + v') := by
  funext x; cases x <;> rfl

@[simp] lemma elim_smul (t : A) (u : ι → A) (v : κ → A) :
    t • Sum.elim u v = Sum.elim (t • u) (t • v) := by
  funext x; cases x <;> rfl

@[simp] lemma elim_zero : Sum.elim (0 : ι → A) (0 : κ → A) = 0 := by
  funext x; cases x <;> rfl

lemma elim_sum {β : Type*} (s : Finset β) (u : β → ι → A) (v : β → κ → A) :
    ∑ j ∈ s, Sum.elim (u j) (v j) = Sum.elim (∑ j ∈ s, u j) (∑ j ∈ s, v j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [sum_insert hx, sum_insert hx, sum_insert hx, ih, elim_add]

lemma single_inl [DecidableEq ι] [DecidableEq κ] (i : ι) :
    (Pi.single (Sum.inl i) (1 : A) : ι ⊕ κ → A) = Sum.elim (Pi.single i 1) (0 : κ → A) := by
  funext x; cases x with
  | inl x => by_cases h : x = i <;> simp [Pi.single_apply, h]
  | inr x => simp

lemma single_inr [DecidableEq ι] [DecidableEq κ] (i : κ) :
    (Pi.single (Sum.inr i) (1 : A) : ι ⊕ κ → A) = Sum.elim (0 : ι → A) (Pi.single i 1) := by
  funext x; cases x with
  | inl x => simp
  | inr x => by_cases h : x = i <;> simp [Pi.single_apply, h]

lemma blk_comp (a : (ι' → A) →ₗ[A] (ι'' → A)) (b : (κ' → A) →ₗ[A] (ι'' → A))
    (d : (κ' → A) →ₗ[A] (κ'' → A)) (a' : (ι → A) →ₗ[A] (ι' → A))
    (b' : (κ → A) →ₗ[A] (ι' → A)) (d' : (κ → A) →ₗ[A] (κ' → A)) :
    blk a b d ∘ₗ blk a' b' d' = blk (a ∘ₗ a') (a ∘ₗ b' + b ∘ₗ d') (d ∘ₗ d') := by
  refine LinearMap.ext fun z => ?_
  rw [← elim_comp z]
  simp only [LinearMap.comp_apply, blk_elim, LinearMap.add_apply, map_add]
  congr 1; abel

lemma blk_smul (t : A) (a : (ι → A) →ₗ[A] (ι' → A)) (b : (κ → A) →ₗ[A] (ι' → A))
    (d : (κ → A) →ₗ[A] (κ' → A)) : t • blk a b d = blk (t • a) (t • b) (t • d) := by
  refine LinearMap.ext fun z => ?_
  rw [← elim_comp z]
  simp only [LinearMap.smul_apply, blk_elim, elim_smul, smul_add]

lemma blk_one :
    blk (1 : Module.End A (ι → A)) (0 : (κ → A) →ₗ[A] (ι → A)) (1 : Module.End A (κ → A)) = 1 := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.one_apply, ← elim_comp z, blk_elim]
  simp only [Module.End.one_apply, LinearMap.zero_apply, add_zero]

lemma blk_eq_iff {a a' : (ι → A) →ₗ[A] (ι' → A)} {b b' : (κ → A) →ₗ[A] (ι' → A)}
    {d d' : (κ → A) →ₗ[A] (κ' → A)} :
    blk a b d = blk a' b' d' ↔ a = a' ∧ b = b' ∧ d = d' := by
  constructor
  · intro h
    have h1 : ∀ u v, a u + b v = a' u + b' v ∧ d v = d' v := fun u v => by
      have := LinearMap.congr_fun h (Sum.elim u v)
      simpa only [blk_elim, elim_eq_iff] using this
    refine ⟨LinearMap.ext fun u => ?_, LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
    · simpa using (h1 u 0).1
    · simpa using (h1 0 v).1
    · exact (h1 0 v).2
  · rintro ⟨rfl, rfl, rfl⟩; rfl

end blk

/-! ### (G1) Glued data -/

variable {M N : DPLattice A}

/-- (G1) the weights `Sum.elim N.wt M.wt` of the glued data on `N.ι ⊕ M.ι`. -/
abbrev gwt (M N : DPLattice A) : N.ι ⊕ M.ι → ℤ := Sum.elim N.wt M.wt

/-- (G1) the glued `F^{(r)} (u, v) := (N.Fd r u + cF r v, M.Fd r v)`. -/
def gF (c : Pair M N) (r : ℕ) : Module.End A (N.ι ⊕ M.ι → A) := blk (N.Fd r) (c.1 r) (M.Fd r)

/-- (G1) the glued `E^{(r)} (u, v) := (N.Ed r u + cE r v, M.Ed r v)`. -/
def gE (c : Pair M N) (r : ℕ) : Module.End A (N.ι ⊕ M.ι → A) := blk (N.Ed r) (c.2 r) (M.Ed r)

@[simp] lemma gF_elim (c : Pair M N) (r : ℕ) (u : N.ι → A) (v : M.ι → A) :
    gF c r (Sum.elim u v) = Sum.elim (N.Fd r u + c.1 r v) (M.Fd r v) := rfl

@[simp] lemma gE_elim (c : Pair M N) (r : ℕ) (u : N.ι → A) (v : M.ι → A) :
    gE c r (Sum.elim u v) = Sum.elim (N.Ed r u + c.2 r v) (M.Ed r v) := rfl

/-- (G1) `c` is a *cocycle from `M` to `N`*: the glued data satisfy `IsDP`. -/
def IsCocycle (c : Pair M N) : Prop := IsDP (gwt M N) (gF c) (gE c)

/-- (G1) For a cocycle `c`, the glued DP-lattice `glue M N c hc`: basis `N.ι ⊕ M.ι`, weights
`Sum.elim N.wt M.wt`, operators `gF c r`, `gE c r`. -/
def glue (M N : DPLattice A) (c : Pair M N) (hc : IsCocycle c) : DPLattice A where
  ι := N.ι ⊕ M.ι
  wt := gwt M N
  Fd := gF c
  Ed := gE c
  isDP := hc

/-! ### (G2) Cocycle equations -/

/-- (G2) The cocycle equations (W), (P0), (P1), (K) for a pair `c = (cF, cE) = (c.1, c.2)`. -/
structure CocycleEqs (c : Pair M N) : Prop where
  /-- (W) `cF r (δ_i) j = 0` unless `N.wt j = M.wt i − 2r`. -/
  W_F : ∀ (i : M.ι) (r : ℕ) (j : N.ι), N.wt j ≠ M.wt i - 2 * r → c.1 r (Pi.single i 1) j = 0
  /-- (W) `cE r (δ_i) j = 0` unless `N.wt j = M.wt i + 2r`. -/
  W_E : ∀ (i : M.ι) (r : ℕ) (j : N.ι), N.wt j ≠ M.wt i + 2 * r → c.2 r (Pi.single i 1) j = 0
  /-- (P0) `cF 0 = 0`. -/
  P0_F : c.1 0 = 0
  /-- (P0) `cE 0 = 0`. -/
  P0_E : c.2 0 = 0
  /-- (P1) `N.Fd a ∘ cF b + cF a ∘ M.Fd b = C(a + b, a) · cF (a + b)`. -/
  P1_F : ∀ a b : ℕ, N.Fd a ∘ₗ c.1 b + c.1 a ∘ₗ M.Fd b =
    ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • c.1 (a + b)
  /-- (P1) `N.Ed a ∘ cE b + cE a ∘ M.Ed b = C(a + b, a) · cE (a + b)`. -/
  P1_E : ∀ a b : ℕ, N.Ed a ∘ₗ c.2 b + c.2 a ∘ₗ M.Ed b =
    ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • c.2 (a + b)
  /-- (K) `N.Ed s (cF r δ_i) + cE s (M.Fd r δ_i) =
  Σ_{j ≤ min(r,s)} C(M.wt i + s − r, j) · (N.Fd (r−j) (cE (s−j) δ_i) + cF (r−j) (M.Ed (s−j) δ_i))`. -/
  K : ∀ (i : M.ι) (r s : ℕ), N.Ed s (c.1 r (Pi.single i 1)) + c.2 s (M.Fd r (Pi.single i 1)) =
    ∑ j ∈ range (min r s + 1), ((Ring.choose (M.wt i + s - r) j : ℤ) : A) •
      (N.Fd (r - j) (c.2 (s - j) (Pi.single i 1)) + c.1 (r - j) (M.Ed (s - j) (Pi.single i 1)))

/-- (G2) `c` is a cocycle iff the equations (W), (P0), (P1), (K) hold. -/
theorem G2 (c : Pair M N) : IsCocycle c ↔ CocycleEqs c := by
  constructor
  · intro h
    refine ⟨fun i r j hj => ?_, fun i r j hj => ?_, ?_, ?_, fun a b => ?_, fun a b => ?_,
      fun i r s => ?_⟩
    · have := h.W_F (Sum.inr i) r (Sum.inl j) hj
      rwa [single_inr, gF_elim, map_zero, zero_add, Sum.elim_inl] at this
    · have := h.W_E (Sum.inr i) r (Sum.inl j) hj
      rwa [single_inr, gE_elim, map_zero, zero_add, Sum.elim_inl] at this
    · have := h.P0_F
      rw [gF, N.isDP.P0_F, M.isDP.P0_F, ← blk_one, blk_eq_iff] at this
      exact this.2.1
    · have := h.P0_E
      rw [gE, N.isDP.P0_E, M.isDP.P0_E, ← blk_one, blk_eq_iff] at this
      exact this.2.1
    · have := h.P1_F a b
      rw [gF, gF, gF, blk_comp, blk_smul, blk_eq_iff] at this
      exact this.2.1
    · have := h.P1_E a b
      rw [gE, gE, gE, blk_comp, blk_smul, blk_eq_iff] at this
      exact this.2.1
    · have := h.K (Sum.inr i) r s
      simp only [single_inr, gF_elim, gE_elim, map_zero, zero_add, elim_smul, elim_sum,
        Sum.elim_inr, elim_eq_iff] at this
      exact this.1
  · intro h
    refine ⟨fun i r j hj => ?_, fun i r j hj => ?_, ?_, ?_, fun a b => ?_, fun a b => ?_,
      fun i r s => ?_⟩
    · cases i with
      | inl i =>
        cases j with
        | inl j =>
          rw [single_inl, gF_elim, map_zero, add_zero, Sum.elim_inl]
          exact N.isDP.W_F i r j hj
        | inr j => rw [single_inl, gF_elim, Sum.elim_inr, (M.Fd r).map_zero, Pi.zero_apply]
      | inr i =>
        cases j with
        | inl j =>
          rw [single_inr, gF_elim, map_zero, zero_add, Sum.elim_inl]
          exact h.W_F i r j hj
        | inr j =>
          rw [single_inr, gF_elim, Sum.elim_inr]
          exact M.isDP.W_F i r j hj
    · cases i with
      | inl i =>
        cases j with
        | inl j =>
          rw [single_inl, gE_elim, map_zero, add_zero, Sum.elim_inl]
          exact N.isDP.W_E i r j hj
        | inr j => rw [single_inl, gE_elim, Sum.elim_inr, (M.Ed r).map_zero, Pi.zero_apply]
      | inr i =>
        cases j with
        | inl j =>
          rw [single_inr, gE_elim, map_zero, zero_add, Sum.elim_inl]
          exact h.W_E i r j hj
        | inr j =>
          rw [single_inr, gE_elim, Sum.elim_inr]
          exact M.isDP.W_E i r j hj
    · rw [gF, N.isDP.P0_F, M.isDP.P0_F, h.P0_F, blk_one]
    · rw [gE, N.isDP.P0_E, M.isDP.P0_E, h.P0_E, blk_one]
    · rw [gF, gF, gF, blk_comp, blk_smul, N.isDP.P1_F, M.isDP.P1_F, h.P1_F]
    · rw [gE, gE, gE, blk_comp, blk_smul, N.isDP.P1_E, M.isDP.P1_E, h.P1_E]
    · cases i with
      | inl i =>
        simp only [single_inl, gF_elim, gE_elim, map_zero, add_zero, elim_smul, elim_sum,
          Sum.elim_inl, smul_zero, sum_const_zero]
        rw [N.isDP.K i r s]
      | inr i =>
        simp only [single_inr, gF_elim, gE_elim, map_zero, zero_add, elim_smul, elim_sum,
          Sum.elim_inr]
        rw [h.K i r s, M.isDP.K i r s]

end Cocycle
