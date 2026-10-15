module

public import RequestProject.ThmH.Dictionary
public import RequestProject.TiltDec.All
public import RequestProject.Families.All
public import RequestProject.Splitting.All

/-!
# `CSG6_operator_on_the_blocks.md`, Part K — the operator `q(c+H)+U` on a DP-lattice

Namespace `ColouredSand.BlockOp`.  This is the odd-`p` analogue of
`RequestProject/ThmH/TheoremH.lean` (`opT_eq_sigL`, `T1equiv`) and follows it closely.

## Encodings

* `ℤ_[p]` is Mathlib's `PadicInt p`, `p` a prime (`[Fact p.Prime]`), with `hp2 : p ≠ 2` where
  `1/2` is needed.
* `B m R`, `H`, `U` and `opM m R q c = q • (c • id + H) + U` are the Coloured Sand objects of
  `ColouredSand.Strings`; `V^{⊗m}` is `Filt.tpow ℤ_[p] m`; the dictionary
  `Psi ℤ_[p] m : B m ℤ_[p] ≃ₗ V^{⊗m}` is `ColouredSand.ThmH.Psi` (`ThmH.D2`).
* (K0) `half p := Ring.inverse 2`, so `2 * half p = 1` when `p ≠ 2` (`two_mul_half`).
* (K1) `opT p M m q c` is the endomorphism
  `M.Fd 1 + q • (c • id + half p • (m • id − DPLattice.H M))` of `M.ι → ℤ_[p]`; on a vector of
  weight `h` it is `F^{(1)} + q (c + (m − h)/2)`.  (The prime `p` is an explicit argument.)
* The cokernel of an endomorphism `f` of `N` is `N ⧸ LinearMap.range f`.
* Direct sums of DP-lattices are `Step36.dsumList`; the summands of `V^{⊗m}` are indexed by the
  positions `j : Fin (LP p m).length` of the list `TiltDec.LP p m` (each `λ` repeated `m_λ(m)`
  times), and `λ_j = (LP p m).get j`.
* (K3)(b): `dsumTheta p f l` is the equivalence chosen in `Families.dsumMap_exists f l`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.BlockOp

open ColouredSand.Strings ColouredSand.ThmH ColouredSand.TiltP ColouredSand.TiltDec Families
open ColouredSand.Splitting

variable (p : ℕ) [Fact p.Prime]

/-! ### (K0) -/

/-- **(K0)** of `CSG6_operator_on_the_blocks.md`: `half p = Ring.inverse 2 ∈ ℤ_[p]`. -/
def half : ℤ_[p] := Ring.inverse 2

variable {p} in
/-- **(K0)** of `CSG6_operator_on_the_blocks.md`: `2 * half p = 1` for `p ≠ 2`. -/
theorem two_mul_half (hp2 : p ≠ 2) : 2 * half p = 1 := by
  have hu : IsUnit (2 : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    have : ‖((2 : ℕ) : ℤ_[p])‖ = 1 := by
      rw [PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp2
    exact_mod_cast this
  exact Ring.mul_inverse_cancel _ hu

/-! ### (K1) -/

/-- **(K1)** of `CSG6_operator_on_the_blocks.md`: on a DP-lattice `M` over `ℤ_[p]`,
`opT p M m q c = F^{(1)} + q • (c • id + half • (m • id − H))`, i.e. `F + q(c + (m − h)/2)` on a
vector of weight `h`. -/
def opT (M : DPLattice ℤ_[p]) (m q c : ℕ) : Module.End ℤ_[p] (M.ι → ℤ_[p]) :=
  M.Fd 1 + (q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id +
    half p • ((m : ℤ_[p]) • LinearMap.id - DPLattice.H M))

variable {p}

lemma opT_apply (M : DPLattice ℤ_[p]) (m q c : ℕ) (v : M.ι → ℤ_[p]) :
    opT p M m q c v = M.Fd 1 v + (q : ℤ_[p]) • ((c : ℤ_[p]) • v +
      half p • ((m : ℤ_[p]) • v - DPLattice.H M v)) := rfl

/-- `opT` only depends on `F^{(1)}` and `H`: a linear map intertwining `F^{(1)}` and `H`
intertwines `opT` (auxiliary for (K3) of `CSG6_operator_on_the_blocks.md`). -/
lemma opT_conj {X Y : DPLattice ℤ_[p]} (φ : (X.ι → ℤ_[p]) →ₗ[ℤ_[p]] (Y.ι → ℤ_[p]))
    (hF : ∀ v, φ (X.Fd 1 v) = Y.Fd 1 (φ v)) (hH : ∀ v, φ (DPLattice.H X v) = DPLattice.H Y (φ v))
    (m q c : ℕ) (v : X.ι → ℤ_[p]) : φ (opT p X m q c v) = opT p Y m q c (φ v) := by
  simp only [opT_apply, map_add, map_smul, map_sub, hF, hH]

/-! ### (K2) -/

/-- **(K2) the dictionary** of `CSG6_operator_on_the_blocks.md`: for `p ≠ 2` and every
`m q c`, `Psi ∘ opM m ℤ_[p] q c = opT (V^{⊗m}) m q c ∘ Psi`. -/
theorem K2 (hp2 : p ≠ 2) (m q c : ℕ) :
    (Psi ℤ_[p] m).toLinearMap ∘ₗ opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]) =
      opT p (Filt.tpow ℤ_[p] m) m q c ∘ₗ (Psi ℤ_[p] m).toLinearMap := by
  obtain ⟨hU, hH⟩ := ThmH.D2 ℤ_[p] m
  refine LinearMap.ext fun f => ?_
  have hU' := LinearMap.congr_fun hU f
  have hH' := LinearMap.congr_fun hH f
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply, map_smul,
    LinearMap.sub_apply, LinearMap.id_apply] at hU' hH'
  have hHf : Psi ℤ_[p] m (H m ℤ_[p] f) = half p • ((m : ℤ_[p]) • Psi ℤ_[p] m f -
      DPLattice.H (Filt.tpow ℤ_[p] m) (Psi ℤ_[p] m f)) := by
    rw [← hH', smul_smul, mul_comm, two_mul_half hp2, one_smul]
  simp only [opM, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul, hU', hHf, opT_apply]
  abel

/-! ### (K3) -/

/-- **(K3)(a)** of `CSG6_operator_on_the_blocks.md`: for `e : Doubling.Iso X Y`,
`isoEquiv e ∘ opT X m q c = opT Y m q c ∘ isoEquiv e`. -/
theorem K3a {X Y : DPLattice ℤ_[p]} (e : Doubling.Iso X Y) (m q c : ℕ) :
    (isoEquiv e).toLinearMap ∘ₗ opT p X m q c = opT p Y m q c ∘ₗ (isoEquiv e).toLinearMap :=
  LinearMap.ext fun v => opT_conj (isoEquiv e).toLinearMap
    (fun w => LinearMap.congr_fun (e.hom.comm_F 1) w)
    (fun w => LinearMap.congr_fun e.hom.comm_H w) m q c v

variable (p) in
/-- The equivalence `Θ : ⊕_j f(l_j) ≃ Π_j f(l_j)` of `Families.dsumMap_exists f l`
(used in (K3)(b) of `CSG6_operator_on_the_blocks.md`). -/
def dsumTheta {α : Type*} (f : α → DPLattice ℤ_[p]) (l : List α) :
    ((Step36.dsumList (l.map f)).ι → ℤ_[p]) ≃ₗ[ℤ_[p]]
      ((j : Fin l.length) → (f (l.get j)).ι → ℤ_[p]) :=
  Classical.choose (dsumMap_exists f l)

/-- **(K3)(b)** of `CSG6_operator_on_the_blocks.md`: the equivalence `Θ` of
`dsumMap_exists f l` conjugates `opT (dsumList (l.map f)) m q c` to the product map
`Π_j opT (f (l.get j)) m q c`. -/
theorem K3b {α : Type*} (f : α → DPLattice ℤ_[p]) (l : List α) (m q c : ℕ) :
    (dsumTheta p f l).toLinearMap ∘ₗ opT p (Step36.dsumList (l.map f)) m q c =
      LinearMap.pi (fun j => opT p (f (l.get j)) m q c ∘ₗ LinearMap.proj j) ∘ₗ
        (dsumTheta p f l).toLinearMap := by
  have hΘ := Classical.choose_spec (dsumMap_exists f l)
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, opT_apply, map_add, map_smul, map_sub]
  rw [show dsumTheta p f l = Classical.choose (dsumMap_exists f l) from rfl, hΘ.1, hΘ.2]
  funext j
  simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, opT_apply,
    Pi.add_apply, Pi.smul_apply, Pi.sub_apply]

/-! ### (K4) -/

/-- **(K4)** of `CSG6_operator_on_the_blocks.md` (explicit equivalence, from an isomorphism
`u : V^{⊗m} ≅ ⊕_j Ttilt p λ_j` as given by CSG5 `TiltDec.D2`): for `p ≠ 2`,
`coker (opM m ℤ_[p] q c) ≃ₗ[ℤ_[p]] Π_j coker (opT (Ttilt p λ_j) m q c)`, `λ_j = (LP p m).get j`.
Built exactly as `ThmH.T1equiv`: (K2), (K3), `cokerEquivOfConj`, `range_pi_comp_proj`,
`Submodule.quotientPi`. -/
def K4equiv (hp2 : p ≠ 2) (m q c : ℕ)
    (u : Doubling.Iso (Filt.tpow ℤ_[p] m) (Step36.dsumList ((LP p m).map (Ttilt p)))) :
    (B m ℤ_[p] ⧸ LinearMap.range (opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]))) ≃ₗ[ℤ_[p]]
      ((j : Fin (LP p m).length) → ((Ttilt p ((LP p m).get j)).ι → ℤ_[p]) ⧸
        LinearMap.range (opT p (Ttilt p ((LP p m).get j)) m q c)) :=
  let Θ := (Psi ℤ_[p] m).trans ((isoEquiv u).trans (dsumTheta p (Ttilt p) (LP p m)))
  let Gj : ∀ j : Fin (LP p m).length,
      Module.End ℤ_[p] ((Ttilt p ((LP p m).get j)).ι → ℤ_[p]) :=
    fun j => opT p (Ttilt p ((LP p m).get j)) m q c
  have hΘ : ∀ f, (LinearMap.pi fun j => Gj j ∘ₗ LinearMap.proj j) (Θ f) =
      Θ (opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]) f) := fun f => by
    have h2 := LinearMap.congr_fun (K2 hp2 m q c) f
    have h3 := LinearMap.congr_fun (K3a u m q c) (Psi ℤ_[p] m f)
    have h4 := LinearMap.congr_fun (K3b (Ttilt p) (LP p m) m q c) (isoEquiv u (Psi ℤ_[p] m f))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h2 h3 h4
    simp only [Θ, LinearEquiv.trans_apply, h2, h3, h4]
    rfl
  (cokerEquivOfConj _ _ Θ Θ hΘ).trans
    ((Submodule.quotEquivOfEq _ _ (range_pi_comp_proj Gj)).trans (Submodule.quotientPi _))

/-- **(K4) the decomposition of the cokernel** of `CSG6_operator_on_the_blocks.md`: for `p ≠ 2`,
`m ≤ p² + p − 1` and every `q c : ℕ`,
`coker (opM m ℤ_[p] q c) ≃ₗ[ℤ_[p]] Π_{j : Fin (LP p m).length} coker (opT (Ttilt p λ_j) m q c)`,
`λ_j = (LP p m).get j`.  From CSG5 `TiltDec.D2` and `K4equiv`. -/
theorem K4 (hp2 : p ≠ 2) {m : ℕ} (hm : m ≤ p ^ 2 + p - 1) (q c : ℕ) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range (opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]))) ≃ₗ[ℤ_[p]]
      ((j : Fin (LP p m).length) → ((Ttilt p ((LP p m).get j)).ι → ℤ_[p]) ⧸
        LinearMap.range (opT p (Ttilt p ((LP p m).get j)) m q c))) := by
  obtain ⟨u⟩ := TiltDec.D2 hp2 hm
  exact ⟨K4equiv hp2 m q c u⟩

end ColouredSand.BlockOp
