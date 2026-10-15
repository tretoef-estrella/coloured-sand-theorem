module

public import RequestProject.Cocycle.All
public import RequestProject.Twist.All

/-!
# `C28_lifting_mod_2_and_corollary_34.md`: Setting and Part D (dividing by 2)

Encodings (namespace `Lift2`), reusing C18 (`DPLattice`, `IsDP`, `Hom`, `H`, `Hop`), C19
(`Hom.id`, `Hom.comp`, `Hom.ext'`), C20 (`Iso`, `Hom.ofInverse`, `Iso.ofInverse`), C21
(`bc`, `bc_comp`, `bc_id`, `bc_add`, `bc_smul`, `bc_single_apply`, `baseChange`, `bcHom`),
C25 (`IsWtPres`) and C27 (`Lin`, `Pair`, `IsCocycle`, `CocycleEqs`, `G2`, `d`, `G4`,
`HasDeltaFilt`, `HasNablaFilt`, `V4`):

* A vector of a DP-lattice `M` is a function `M.ι → A`; `δ_i = Pi.single i 1`.
* `Lin M N = (M.ι → A) →ₗ[A] (N.ι → A)` (C27); a pair is `c : Pair M N`, `c.1 = cF`, `c.2 = cE`.
* `A`, `B` are commutative rings and `φ : A →+* B` a ring homomorphism. The hypotheses
  of the file are the explicit propositions
  - `H1 φ` : (H1) `φ` is surjective;
  - `H2 φ` : (H2) `∀ a, φ a = 0 ↔ ∃ b, a = 2 * b`;
  - `H3 A` : (H3) `∀ a, 2 * a = 0 → a = 0`;
  - `OneAddTwoUnit A` : the hypothesis of (C1), `∀ a, IsUnit (1 + 2 * a)`.
  Each statement takes exactly the hypotheses it uses as arguments.
* A `B`-linear map `h̄` between reductions is "weight-preserving" when
  `IsWtPres (M := baseChange φ M) (N := baseChange φ N) h̄` (the weights of `baseChange φ M` are
  those of `M`).
-/

@[expose] public section

noncomputable section

namespace Lift2

open DPLattice WeylFilt Doubling Twist LemmaW Cocycle Finset

variable {A B : Type*} [CommRing A] [CommRing B]

/-! ### Setting: the hypotheses on the rings -/

/-- Setting, (H1): `φ` is surjective. -/
def H1 (φ : A →+* B) : Prop := Function.Surjective φ

/-- Setting, (H2): the kernel of `φ` is `2A`: `∀ a, φ a = 0 ↔ ∃ b, a = 2 * b`. -/
def H2 (φ : A →+* B) : Prop := ∀ a, φ a = 0 ↔ ∃ b, a = 2 * b

/-- Setting, (H3): `A` has no 2-torsion: `∀ a, 2 * a = 0 → a = 0`. -/
def H3 (A : Type*) [CommRing A] : Prop := ∀ a : A, 2 * a = 0 → a = 0

/-- (C1), hypothesis: every `1 + 2a` (`a : A`) is a unit of `A`. -/
def OneAddTwoUnit (A : Type*) [CommRing A] : Prop := ∀ a : A, IsUnit (1 + 2 * a)

variable {φ : A →+* B}

/-! ### Auxiliary lemmas -/

/-- (H3), auxiliary: cancelling `2` on vectors. -/
lemma two_smul_cancel (h3 : H3 A) {κ : Type*} {u v : κ → A}
    (h : (2 : A) • u = (2 : A) • v) : u = v := by
  funext j
  have := congrFun h j
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact sub_eq_zero.mp (h3 _ (by rw [mul_sub, this, sub_self]))

/-- (H3), auxiliary: cancelling `2` on linear maps. -/
lemma two_smul_cancel_lin (h3 : H3 A) {V : Type*} [AddCommGroup V] [Module A V] {κ : Type*}
    {f g : V →ₗ[A] (κ → A)} (h : (2 : A) • f = (2 : A) • g) : f = g :=
  LinearMap.ext fun x => two_smul_cancel h3 (by
    have := LinearMap.congr_fun h x
    simpa only [LinearMap.smul_apply] using this)

lemma bc_sub {ι κ : Type*} [Fintype ι] [DecidableEq ι] (f g : (ι → A) →ₗ[A] (κ → A)) :
    bc φ (f - g) = bc φ f - bc φ g := by
  rw [eq_sub_iff_add_eq, ← bc_add, sub_add_cancel]

/-- (G4), auxiliary: `d (t • ψ) = t • d ψ`. -/
lemma d_smul {M N : DPLattice A} (t : A) (ψ : Lin M N) : d (t • ψ) = t • d ψ := by
  refine Prod.ext (funext fun r => ?_) (funext fun r => ?_) <;>
  · simp only [d_fst, d_snd, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.smul_comp,
      LinearMap.comp_smul, smul_sub]

/-- (G4), auxiliary: `d (ψ − ψ') = d ψ − d ψ'`. -/
lemma d_sub {M N : DPLattice A} (ψ ψ' : Lin M N) : d (ψ - ψ') = d ψ - d ψ' := by
  rw [eq_sub_iff_add_eq, ← d_add, sub_add_cancel]

/-! ### Part D -/

/-- (D1), existence part (uses only (H2)): if `bc φ T = 0` then `T = 2 • U` for some `U`. -/
theorem D1_exists (h2 : H2 φ) {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (T : (ι → A) →ₗ[A] (κ → A)) (hT : bc φ T = 0) : ∃ U, T = (2 : A) • U := by
  classical
  have he : ∀ i j, ∃ b, T (Pi.single i 1) j = 2 * b := fun i j => (h2 _).mp (by
    rw [← bc_single_apply, hT]; rfl)
  choose b hb using he
  refine ⟨Matrix.toLin' (Matrix.of fun j i => b i j), ext_single fun i => ?_⟩
  funext j
  simp [Matrix.toLin'_apply, hb i j]

/-- (D1) Under (H2), (H3): if `T : Lin M N` and `bc φ T = 0`, there is a unique `U : Lin M N`
with `T = 2 • U`; and if `T` is weight-preserving, so is (every, hence the unique) such `U`. -/
theorem D1 (h2 : H2 φ) (h3 : H3 A) {M N : DPLattice A} (T : Lin M N) (hT : bc φ T = 0) :
    (∃! U : Lin M N, T = (2 : A) • U) ∧
    (IsWtPres T → ∀ U : Lin M N, T = (2 : A) • U → IsWtPres U) := by
  obtain ⟨U, hU⟩ := D1_exists h2 T hT
  refine ⟨⟨U, hU, fun U' hU' => two_smul_cancel_lin h3 (hU' ▸ hU)⟩, fun hw U' hU' i j hij => ?_⟩
  have := hw i j hij
  rw [hU'] at this
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] at this
  exact h3 _ this

/-- (D2) Under (H3): if `2 • c` is a cocycle (C27), then `c` is a cocycle. (Each equation of
(G2) for `2 • c` is twice the same equation for `c`.) -/
theorem D2 (h3 : H3 A) {M N : DPLattice A} (c : Pair M N) (hc : IsCocycle ((2 : A) • c)) :
    IsCocycle c := by
  rw [G2] at hc ⊢
  refine ⟨fun i r j hj => ?_, fun i r j hj => ?_, ?_, ?_, fun a b => ?_, fun a b => ?_,
    fun i r s => ?_⟩
  · have := hc.W_F i r j hj
    simp only [Prod.smul_fst, Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul] at this
    exact h3 _ this
  · have := hc.W_E i r j hj
    simp only [Prod.smul_snd, Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul] at this
    exact h3 _ this
  · have := hc.P0_F
    simp only [Prod.smul_fst, Pi.smul_apply] at this
    exact two_smul_cancel_lin h3 (by rw [this, smul_zero])
  · have := hc.P0_E
    simp only [Prod.smul_snd, Pi.smul_apply] at this
    exact two_smul_cancel_lin h3 (by rw [this, smul_zero])
  · have := hc.P1_F a b
    simp only [Prod.smul_fst, Pi.smul_apply, LinearMap.comp_smul, LinearMap.smul_comp] at this
    refine two_smul_cancel_lin h3 ?_
    rw [smul_add, this, smul_comm]
  · have := hc.P1_E a b
    simp only [Prod.smul_snd, Pi.smul_apply, LinearMap.comp_smul, LinearMap.smul_comp] at this
    refine two_smul_cancel_lin h3 ?_
    rw [smul_add, this, smul_comm]
  · have := hc.K i r s
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, LinearMap.smul_apply, map_smul,
      ← smul_add] at this
    refine two_smul_cancel h3 ?_
    rw [this, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

/-- (D3) Under (H2), (H3): if `φ0 : Lin M N` is weight-preserving and `bc φ φ0` commutes with
every `(baseChange φ M).Fd r`, `(baseChange φ M).Ed r` (i.e. `bc φ (d φ0) = 0` in both
components), then there is a pair `δ` with `d φ0 = 2 • δ`, and `δ` is a cocycle. -/
theorem D3 (h2 : H2 φ) (h3 : H3 A) {M N : DPLattice A} (φ0 : Lin M N) (hφ0 : IsWtPres φ0)
    (hF : ∀ r, bc φ φ0 ∘ₗ (baseChange φ M).Fd r = (baseChange φ N).Fd r ∘ₗ bc φ φ0)
    (hE : ∀ r, bc φ φ0 ∘ₗ (baseChange φ M).Ed r = (baseChange φ N).Ed r ∘ₗ bc φ φ0) :
    ∃ δ : Pair M N, d φ0 = (2 : A) • δ ∧ IsCocycle δ := by
  have hF' : ∀ r, ∃ U : Lin M N, (d φ0).1 r = (2 : A) • U := fun r => D1_exists h2 _ (by
    rw [d_fst, bc_sub, bc_comp, bc_comp, sub_eq_zero]; exact hF r)
  have hE' : ∀ r, ∃ U : Lin M N, (d φ0).2 r = (2 : A) • U := fun r => D1_exists h2 _ (by
    rw [d_snd, bc_sub, bc_comp, bc_comp, sub_eq_zero]; exact hE r)
  choose UF hUF using hF'
  choose UE hUE using hE'
  have hd : d φ0 = (2 : A) • ((UF, UE) : Pair M N) :=
    Prod.ext (funext fun r => hUF r) (funext fun r => hUE r)
  exact ⟨(UF, UE), hd, D2 h3 _ (hd ▸ G4 hφ0)⟩

end Lift2
