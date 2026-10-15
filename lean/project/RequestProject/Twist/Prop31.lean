module

public import RequestProject.Twist.PartC

/-!
# `C21_reduction_mod_2_and_the_twist.md`: Part C, (C1)–(C3), Proposition 3.1 (c)

Setting: `A` is a commutative ring with `[IsDomain A] [CharZero A] [Doubling.OddUnits A]` (C20),
`B` a commutative ring with `h2 : (2 : B) = 0`, and `φ : A →+* B` a ring homomorphism.
For a DP-lattice `N` over `A`, `N̄ = N^φ` is `baseChange φ N`, `(Φ(N))^φ` is
`baseChange φ (Doubling.phi N)` (basis `Fin 2 × N.ι`), and `tensorV ((N̄)^{[1]})` is
`tensorV (frob h2 (baseChange φ N))` (basis `Fin 2 × N.ι`). The vector `b_e n` is `bvec e n`.
-/

@[expose] public section

noncomputable section

namespace Twist

open DPLattice Finset WeylFilt Doubling

variable {A B : Type*} [CommRing A] [CommRing B] {φ : A →+* B}

omit [CommRing B] in
lemma ext_red {B : Type*} [CommRing B] {φ : A →+* B} {X : Type*} [AddCommGroup X] [Module B X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {T U : (ι → B) →ₗ[B] X}
    (h : ∀ i, T (⇑φ ∘ Pi.single i 1) = U (⇑φ ∘ Pi.single i 1)) : T = U :=
  ext_single fun i => by rw [← comp_single φ i]; exact h i

variable (h2 : (2 : B) = 0)

include h2 in
lemma comp_piOp {N : DPLattice A} (S : Finset ℕ) (c : ℕ → ℤ) (hc : ∀ j ∈ S, Odd (c j))
    (x : N.ι → A) : (⇑φ ∘ piOp N S c x) = ⇑φ ∘ x := by
  rw [← bc_apply_comp, bc_piOp h2 N S c hc]; rfl

variable [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A)

/-! ### (C1) -/

include h2 in
/-- (C1) On `(Φ(N))^φ`: `F^{(2s)}(b_e n) = b_e F^{(s)} n` (with `F^{(s)}` of `N̄ = N^φ`). -/
theorem C1_Fd_even (s : ℕ) (e : Fin 2) (n : N.ι → B) :
    (baseChange φ (phi N)).Fd (2 * s) (bvec e n) = bvec e ((baseChange φ N).Fd s n) := by
  refine LinearMap.congr_fun (ext_red (φ := φ) (T := bc φ (phiFd N (2 * s)) ∘ₗ bvec e)
    (U := bvec e ∘ₗ bc φ (N.Fd s)) fun i => ?_) n
  simp only [LinearMap.comp_apply, bvec_comp, bc_apply_comp]
  rw [phiFd_even, comp_smul, phi_dfi h2, one_smul]

include h2 in
/-- (C1) On `(Φ(N))^φ`: `F^{(2s+1)}(b_0 n) = b_1 F^{(s)} n`. -/
theorem C1_Fd_odd_b0 (s : ℕ) (n : N.ι → B) :
    (baseChange φ (phi N)).Fd (2 * s + 1) (bvec 0 n) = bvec 1 ((baseChange φ N).Fd s n) := by
  refine LinearMap.congr_fun (ext_red (φ := φ) (T := bc φ (phiFd N (2 * s + 1)) ∘ₗ bvec 0)
    (U := bvec 1 ∘ₗ bc φ (N.Fd s)) fun i => ?_) n
  simp only [LinearMap.comp_apply, bvec_comp, bc_apply_comp]
  rw [phiFd_odd_b0, comp_smul, phi_dfi h2, one_smul]

include h2 in
/-- (C1) On `(Φ(N))^φ`: `F^{(2s+1)}(b_1 n) = 0`. -/
theorem C1_Fd_odd_b1 (s : ℕ) (n : N.ι → B) :
    (baseChange φ (phi N)).Fd (2 * s + 1) (bvec 1 n) = 0 := by
  refine LinearMap.congr_fun (ext_red (φ := φ) (T := bc φ (phiFd N (2 * s + 1)) ∘ₗ bvec 1)
    (U := 0) fun i => ?_) n
  simp only [LinearMap.comp_apply, bvec_comp, bc_apply_comp, LinearMap.zero_apply]
  rw [phiFd_odd_b1, comp_smul, map_mul, map_natCast, show 2 * s + 2 = 2 * (s + 1) by ring,
    natCast_two_mul h2, zero_mul, zero_smul]

include h2 in
/-- (C1) On `(Φ(N))^φ`: `E^{(2s)}(b_e n) = b_e E^{(s)} n` (with `E^{(s)}` of `N̄ = N^φ`). -/
theorem C1_Ed_even (s : ℕ) (e : Fin 2) (n : N.ι → B) :
    (baseChange φ (phi N)).Ed (2 * s) (bvec e n) = bvec e ((baseChange φ N).Ed s n) := by
  refine LinearMap.congr_fun (ext_red (φ := φ) (T := bc φ (phiEd N (2 * s)) ∘ₗ bvec e)
    (U := bvec e ∘ₗ bc φ (N.Ed s)) fun i => ?_) n
  simp only [LinearMap.comp_apply, bvec_comp, bc_apply_comp]
  rcases fin_two_cases e with rfl | rfl
  · rw [phiEd_even_b0, comp_smul, phi_dfi h2, one_smul, ← bvec_comp,
      comp_piOp h2 _ _ (fun j _ => odd_cE _ _ _), bvec_comp]
  · rw [phiEd_even_b1, comp_smul, phi_dfi h2, one_smul, ← bvec_comp,
      comp_piOp h2 _ _ (fun j _ => odd_cE _ _ _), bvec_comp]

include h2 in
/-- (C1) On `(Φ(N))^φ`: `E^{(2s+1)}(b_1 n) = b_0 E^{(s)} n`. -/
theorem C1_Ed_odd_b1 (s : ℕ) (n : N.ι → B) :
    (baseChange φ (phi N)).Ed (2 * s + 1) (bvec 1 n) = bvec 0 ((baseChange φ N).Ed s n) := by
  refine LinearMap.congr_fun (ext_red (φ := φ) (T := bc φ (phiEd N (2 * s + 1)) ∘ₗ bvec 1)
    (U := bvec 0 ∘ₗ bc φ (N.Ed s)) fun i => ?_) n
  simp only [LinearMap.comp_apply, bvec_comp, bc_apply_comp]
  rw [phiEd_odd_b1, comp_smul, phi_dfi h2, one_smul, ← bvec_comp,
    comp_piOp h2 _ _ (fun j _ => odd_cE _ _ _), bvec_comp]

include h2 in
/-- (C1) On `(Φ(N))^φ`: `E^{(2s+1)}(b_0 n) = 0`. -/
theorem C1_Ed_odd_b0 (s : ℕ) (n : N.ι → B) :
    (baseChange φ (phi N)).Ed (2 * s + 1) (bvec 0 n) = 0 := by
  refine LinearMap.congr_fun (ext_red (φ := φ) (T := bc φ (phiEd N (2 * s + 1)) ∘ₗ bvec 0)
    (U := 0) fun i => ?_) n
  simp only [LinearMap.comp_apply, bvec_comp, bc_apply_comp, LinearMap.zero_apply]
  rw [phiEd_odd_b0, comp_smul, map_mul, map_natCast, natCast_two_mul h2, zero_mul, zero_smul]

include h2 in
/-- (C1) The six formulas modulo 2 on `(Φ(N))^φ`, for every `s ≥ 0`, every `e` and every vector
`n : N.ι → B` (with `F^{(s)}`, `E^{(s)}` those of `N̄ = N^φ`):
`F^{(2s)}(b_e n) = b_e F^{(s)} n`, `F^{(2s+1)}(b_0 n) = b_1 F^{(s)} n`, `F^{(2s+1)}(b_1 n) = 0`,
`E^{(2s)}(b_e n) = b_e E^{(s)} n`, `E^{(2s+1)}(b_1 n) = b_0 E^{(s)} n`, `E^{(2s+1)}(b_0 n) = 0`. -/
theorem C1 (s : ℕ) (e : Fin 2) (n : N.ι → B) :
    (baseChange φ (phi N)).Fd (2 * s) (bvec e n) = bvec e ((baseChange φ N).Fd s n) ∧
    (baseChange φ (phi N)).Fd (2 * s + 1) (bvec 0 n) = bvec 1 ((baseChange φ N).Fd s n) ∧
    (baseChange φ (phi N)).Fd (2 * s + 1) (bvec 1 n) = 0 ∧
    (baseChange φ (phi N)).Ed (2 * s) (bvec e n) = bvec e ((baseChange φ N).Ed s n) ∧
    (baseChange φ (phi N)).Ed (2 * s + 1) (bvec 1 n) = bvec 0 ((baseChange φ N).Ed s n) ∧
    (baseChange φ (phi N)).Ed (2 * s + 1) (bvec 0 n) = 0 :=
  ⟨C1_Fd_even h2 N s e n, C1_Fd_odd_b0 h2 N s n, C1_Fd_odd_b1 h2 N s n, C1_Ed_even h2 N s e n,
    C1_Ed_odd_b1 h2 N s n, C1_Ed_odd_b0 h2 N s n⟩

/-! ### (C2) -/

omit [IsDomain A] [CharZero A] [OddUnits A] in
lemma pred_frobOp_even {ι : Type*} (F : ℕ → Module.End B (ι → B)) (s : ℕ) :
    pred (frobOp F) (2 * s) = 0 := by
  rcases s with _ | s
  · rfl
  · rw [show 2 * (s + 1) = (2 * s + 1) + 1 by ring, pred_succ, frobOp_odd]

omit [IsDomain A] [CharZero A] [OddUnits A] in
lemma pred_frobOp_odd {ι : Type*} (F : ℕ → Module.End B (ι → B)) (s : ℕ) :
    pred (frobOp F) (2 * s + 1) = F s := by
  rw [pred_succ, frobOp_even]

include h2 in
lemma key_F (r : ℕ) :
    bc φ (phiFd N r) = tensorFd (frobOp fun r => bc φ (N.Fd r)) r := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
  · refine ext_bvec (fun m => ?_) (fun m => ?_)
    · rw [tensorFd_bvec0, pred_frobOp_even, frobOp_even]
      exact (C1_Fd_even h2 N s 0 m).trans (by simp; rfl)
    · rw [tensorFd_bvec1, frobOp_even]; exact C1_Fd_even h2 N s 1 m
  · refine ext_bvec (fun m => ?_) (fun m => ?_)
    · rw [tensorFd_bvec0, pred_frobOp_odd, frobOp_odd]
      exact (C1_Fd_odd_b0 h2 N s m).trans (by simp; rfl)
    · rw [tensorFd_bvec1, frobOp_odd]
      exact (C1_Fd_odd_b1 h2 N s m).trans (by simp)

include h2 in
lemma key_E (r : ℕ) :
    bc φ (phiEd N r) = tensorEd (frobOp fun r => bc φ (N.Ed r)) r := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
  · refine ext_bvec (fun m => ?_) (fun m => ?_)
    · rw [tensorEd_bvec0, frobOp_even]; exact C1_Ed_even h2 N s 0 m
    · rw [tensorEd_bvec1, pred_frobOp_even, frobOp_even]
      exact (C1_Ed_even h2 N s 1 m).trans (by simp; rfl)
  · refine ext_bvec (fun m => ?_) (fun m => ?_)
    · rw [tensorEd_bvec0, frobOp_odd]
      exact (C1_Ed_odd_b0 h2 N s m).trans (by simp)
    · rw [tensorEd_bvec1, pred_frobOp_odd, frobOp_odd]
      exact (C1_Ed_odd_b1 h2 N s m).trans (by simp; rfl)

omit [IsDomain A] [CharZero A] [OddUnits A] in
lemma key_wt : phiWt N = tensorWt (fun i => 2 * N.wt i) := by
  funext p; simp only [phiWt, tensorWt]; ring

variable (φ) in
/-- (C2) the identity map `(Φ(N))^φ → tensorV ((N̄)^{[1]})`, a morphism. -/
def prop31Hom : Hom (baseChange φ (phi N)) (tensorV (frob h2 (baseChange φ N))) where
  toLin := LinearMap.id
  comm_F r := by
    show LinearMap.id ∘ₗ bc φ (phiFd N r) =
      tensorFd (frobOp fun r => bc φ (N.Fd r)) r ∘ₗ LinearMap.id
    rw [key_F h2]; rfl
  comm_E r := by
    show LinearMap.id ∘ₗ bc φ (phiEd N r) =
      tensorEd (frobOp fun r => bc φ (N.Ed r)) r ∘ₗ LinearMap.id
    rw [key_E h2]; rfl
  comm_H := by
    show LinearMap.id ∘ₗ Hop (phiWt N) = Hop (tensorWt (fun i => 2 * N.wt i)) ∘ₗ LinearMap.id
    rw [key_wt]; rfl

variable (φ) in
/-- (C2) the identity map `tensorV ((N̄)^{[1]}) → (Φ(N))^φ`, a morphism. -/
def prop31HomInv : Hom (tensorV (frob h2 (baseChange φ N))) (baseChange φ (phi N)) where
  toLin := LinearMap.id
  comm_F r := by
    show LinearMap.id ∘ₗ tensorFd (frobOp fun r => bc φ (N.Fd r)) r =
      bc φ (phiFd N r) ∘ₗ LinearMap.id
    rw [key_F h2]; rfl
  comm_E r := by
    show LinearMap.id ∘ₗ tensorEd (frobOp fun r => bc φ (N.Ed r)) r =
      bc φ (phiEd N r) ∘ₗ LinearMap.id
    rw [key_E h2]; rfl
  comm_H := by
    show LinearMap.id ∘ₗ Hop (tensorWt (fun i => 2 * N.wt i)) = Hop (phiWt N) ∘ₗ LinearMap.id
    rw [key_wt]; rfl

variable (φ) in
/-- (C2) Proposition 3.1 (c): `(Φ(N))^φ ≅ tensorV ((N^φ)^{[1]})`, by the identity of
`Fin 2 × N.ι → B` (both ways). -/
def prop31Iso : Iso (baseChange φ (phi N)) (tensorV (frob h2 (baseChange φ N))) where
  hom := prop31Hom φ h2 N
  inv := prop31HomInv φ h2 N
  hom_inv := Hom.ext' rfl
  inv_hom := Hom.ext' rfl

variable (φ) in
/-- (C2) Proposition 3.1 (c): `(Φ(N))^φ ≅ tensorV ((N̄)^{[1]})` (`N̄ = N^φ`), by an isomorphism
(`Doubling.Iso`) whose underlying linear maps, both ways, are the identity of
`Fin 2 × N.ι → B`. -/
theorem C2 : ∃ u : Iso (baseChange φ (phi N)) (tensorV (frob h2 (baseChange φ N))),
    u.hom.toLin = (LinearMap.id : (Fin 2 × N.ι → B) →ₗ[B] (Fin 2 × N.ι → B)) ∧
    u.inv.toLin = (LinearMap.id : (Fin 2 × N.ι → B) →ₗ[B] (Fin 2 × N.ι → B)) :=
  ⟨prop31Iso φ h2 N, rfl, rfl⟩

/-! ### (C3) -/

/-- (C3) `2 = 0` in `ZMod 2`. -/
theorem zmod_two_eq_zero : (2 : ZMod 2) = 0 := rfl

/-- (C3) The instance check: `A = ℤ_[2]` is a domain of characteristic zero in which every odd
integer is a unit (`Doubling.OddUnits`), `B = ZMod 2` satisfies `2 = 0`, and
`φ = PadicInt.toZMod : ℤ_[2] →+* ZMod 2` is a ring homomorphism with `φ 2 = 0`. -/
theorem C3_hyp : IsDomain ℤ_[2] ∧ CharZero ℤ_[2] ∧ OddUnits ℤ_[2] ∧
    (∀ k : ℕ, IsUnit ((2 * k + 1 : ℕ) : ℤ_[2])) ∧ (2 : ZMod 2) = 0 ∧
    PadicInt.toZMod (2 : ℤ_[2]) = 0 :=
  ⟨inferInstance, inferInstance, inferInstance, padicInt_two_hodd, zmod_two_eq_zero,
    by rw [map_ofNat]; rfl⟩

/-- (C3) The case of the paper: for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod` and every
DP-lattice `N` over `ℤ_[2]`, `(Φ(N))^φ ≅ tensorV ((N^φ)^{[1]})`. -/
theorem C3 (N : DPLattice ℤ_[2]) :
    Nonempty (Iso (baseChange PadicInt.toZMod (phi N))
      (tensorV (frob zmod_two_eq_zero (baseChange PadicInt.toZMod N)))) :=
  ⟨prop31Iso PadicInt.toZMod zmod_two_eq_zero N⟩

end Twist
