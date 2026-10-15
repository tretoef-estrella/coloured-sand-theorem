module

public import RequestProject.OddTwistModP.PartC1

/-!
# `CSI2_reduction_mod_p.md`: Part C, (C2) and (C3) — Proposition 1.2 (c)

Encodings: `T = Tensor2.tensor (St φ) (frobP hp (baseChange φ N))` is `St ⊗ (N ⊗ B)^{[1]}` (C23's
tensor product), with basis `Fin (p − 1 + 1) × N.ι`; the identification of `Fin (p − 1 + 1)` with
`Fin p` is `Fin.cast` along `p − 1 + 1 = p`. The vector `e_j ⊗ n` is C23's
`Tensor2.tprod (Pi.single j 1) n`.

* `Dmap hp N` is the `B`-linear map `D` of (C2): `(D x)(j, i) = j! · x(j, i)`, so that
  `D (b_j n) = (j! : B) • (e_j ⊗ n)` (`Dmap_bv`), diagonal in the bases.
* `Dinv hp N` is its inverse `(D⁻¹ y)(j, i) = (j!)⁻¹ · y(j, i)` (`Ring.inverse`; `j!` is a unit of
  `B` for `j < p`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

local notation:10000 n "!" => Nat.factorial n

variable {B : Type*} [CommRing B] {p : ℕ} [Fact p.Prime] (hp : (p : B) = 0) (φ : ℤ_[p] →+* B)
  (N : DPLattice ℤ_[p])

lemma p_sub_one_add_one : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le

/-! ### The diagonal map `D` -/

section D

variable {ι : Type*}

variable (B p ι) in
/-- (C2) the diagonal map `D : (Fin p × ι → B) → (Fin (p − 1 + 1) × ι → B)`,
`D(b_j e_i) = (j! : B) · (e_j ⊗ e_i)`. -/
def Dmap : (Fin p × ι → B) →ₗ[B] (Fin (p - 1 + 1) × ι → B) where
  toFun x y := (((y.1 : ℕ)! : ℕ) : B) * x (Fin.cast p_sub_one_add_one y.1, y.2)
  map_add' x x' := by funext y; simp [mul_add]
  map_smul' c x := by funext y; simp; ring

variable (B p ι) in
/-- (C2) the inverse of `D`: `(D⁻¹ y)(j, i) = (j!)⁻¹ · y(j, i)`. -/
def Dinv : (Fin (p - 1 + 1) × ι → B) →ₗ[B] (Fin p × ι → B) where
  toFun y x := Ring.inverse ((((x.1 : ℕ)! : ℕ) : B)) * y (Fin.cast p_sub_one_add_one.symm x.1, x.2)
  map_add' x x' := by funext y; simp [mul_add]
  map_smul' c x := by funext y; simp; ring

@[simp] lemma Dmap_apply (x : Fin p × ι → B) (y : Fin (p - 1 + 1) × ι) :
    Dmap B p ι x y = (((y.1 : ℕ)! : ℕ) : B) * x (Fin.cast p_sub_one_add_one y.1, y.2) := rfl

@[simp] lemma Dinv_apply (y : Fin (p - 1 + 1) × ι → B) (x : Fin p × ι) :
    Dinv B p ι y x =
      Ring.inverse ((((x.1 : ℕ)! : ℕ) : B)) * y (Fin.cast p_sub_one_add_one.symm x.1, x.2) := rfl

include hp in
lemma Dinv_comp_Dmap : Dinv B p ι ∘ₗ Dmap B p ι = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  funext ⟨j, i⟩
  have hu := isUnit_factorial hp (t := (j : ℕ)) (by have := j.isLt; omega)
  simp only [LinearMap.comp_apply, Dinv_apply, Dmap_apply, Fin.val_cast, LinearMap.id_apply]
  rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  rfl

include hp in
lemma Dmap_comp_Dinv : Dmap B p ι ∘ₗ Dinv B p ι = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  funext ⟨j, i⟩
  have hu := isUnit_factorial hp (t := (j : ℕ)) (by have := j.isLt; omega)
  simp only [LinearMap.comp_apply, Dinv_apply, Dmap_apply, Fin.val_cast, LinearMap.id_apply]
  rw [← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]
  rfl

/-- (C2) `D(b_j n) = (j! : B) · (e_j ⊗ n)`; in particular `D(b_j e_i) = (j! : B) · (e_j ⊗ e_i)`. -/
theorem Dmap_bv [DecidableEq ι] (j : ℕ) (hj : j < p - 1 + 1) (n : ι → B) :
    Dmap B p ι (bv p j n) =
      ((j ! : ℕ) : B) • Tensor2.tprod (Pi.single (⟨j, hj⟩ : Fin (p - 1 + 1)) 1) n := by
  funext ⟨y, i⟩
  simp only [Dmap_apply, bv_apply, Fin.val_cast, Pi.smul_apply, Tensor2.tprod_apply,
    Pi.single_apply, Fin.ext_iff, smul_eq_mul]
  by_cases h : (y : ℕ) = j
  · simp [h]
  · simp [h]

end D

/-! ### The tensor product side -/

section T

variable {N}

lemma tprod_zero_left {ι κ : Type*} (n : κ → B) : Tensor2.tprod (0 : ι → B) n = 0 := by
  funext x; simp

lemma tprod_zero_right {ι κ : Type*} (m : ι → B) : Tensor2.tprod m (0 : κ → B) = 0 := by
  funext x; simp

omit [Fact p.Prime] in
lemma eq_of_dvd_sub {c t a : ℕ} (ht : t < p) (ha : a < p) (har : a ≤ p * c + t)
    (h : p ∣ p * c + t - a) : a = t := by
  obtain ⟨m, hm⟩ := h
  exact (eq_of_add_mul_eq (p := p) (c := c) (a := m) ht ha (by omega)).1.symm

/-- (C2, proof) On `T = St ⊗ M^{[1]}`, `F^{(pc+t)}(e_j ⊗ n) = F^{(t)} e_j ⊗ F^{(c)} n` for
`t < p`: only the term `a = t`, `b = pc` of the coproduct survives. -/
lemma tensor_Fd_frob (M : DPLattice B) (c t : ℕ) (ht : t < p) (j : Fin (p - 1 + 1))
    (n : M.ι → B) :
    (Tensor2.tensor (St φ) (frobP hp M)).Fd (p * c + t) (Tensor2.tprod (Pi.single j 1) n) =
      Tensor2.tprod ((St φ).Fd t (Pi.single j 1)) (M.Fd c n) := by
  rw [Tensor2.tensor_Fd_tprod, Finset.sum_eq_single t]
  · congr 2
    show frobOpP p M.Fd (p * c + t - t) = _
    rw [Nat.add_sub_cancel, frobOpP_mul]
  · intro a ha hat
    simp only [mem_range] at ha
    by_cases hap : p ≤ a
    · rw [St_Fd_high φ hap, LinearMap.zero_apply, tprod_zero_left]
    · have : ¬ p ∣ p * c + t - a := fun h => hat (eq_of_dvd_sub ht (by omega) (by omega) h)
      show Tensor2.tprod _ (frobOpP p M.Fd (p * c + t - a) n) = 0
      rw [frobOpP_of_not_dvd _ this, LinearMap.zero_apply, tprod_zero_right]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

/-- (C2, proof) On `T = St ⊗ M^{[1]}`, `E^{(pc+t)}(e_j ⊗ n) = E^{(t)} e_j ⊗ E^{(c)} n` for `t < p`. -/
lemma tensor_Ed_frob (M : DPLattice B) (c t : ℕ) (ht : t < p) (j : Fin (p - 1 + 1))
    (n : M.ι → B) :
    (Tensor2.tensor (St φ) (frobP hp M)).Ed (p * c + t) (Tensor2.tprod (Pi.single j 1) n) =
      Tensor2.tprod ((St φ).Ed t (Pi.single j 1)) (M.Ed c n) := by
  rw [Tensor2.tensor_Ed_tprod, Finset.sum_eq_single t]
  · congr 2
    show frobOpP p M.Ed (p * c + t - t) = _
    rw [Nat.add_sub_cancel, frobOpP_mul]
  · intro a ha hat
    simp only [mem_range] at ha
    by_cases hap : p ≤ a
    · rw [St_Ed_high φ hap, LinearMap.zero_apply, tprod_zero_left]
    · have : ¬ p ∣ p * c + t - a := fun h => hat (eq_of_dvd_sub ht (by omega) (by omega) h)
      show Tensor2.tprod _ (frobOpP p M.Ed (p * c + t - a) n) = 0
      rw [frobOpP_of_not_dvd _ this, LinearMap.zero_apply, tprod_zero_right]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

end T

/-! ### (C2) -/

/-- (C2) the lattice `T = St ⊗ (N ⊗ B)^{[1]}`. -/
abbrev Tlat : DPLattice B := Tensor2.tensor (St φ) (frobP hp (Twist.baseChange φ N))

lemma single_eq_bv' (x : Fin p × N.ι) :
    (Pi.single x (1 : B) : Fin p × N.ι → B) = bv p (x.1 : ℕ) (Pi.single x.2 1) := by
  obtain ⟨j, i⟩ := x; exact single_eq_bv p j i

include hp in
lemma Dmap_comm_F (r : ℕ) :
    Dmap B p N.ι ∘ₗ (Twist.baseChange φ (twist p N)).Fd r =
      (Tlat hp φ N).Fd r ∘ₗ Dmap B p N.ι := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  refine ext_single fun (x : Fin p × N.ι) => ?_
  obtain ⟨j, i⟩ := x
  have hj := j.isLt
  rw [single_eq_bv']
  simp only [LinearMap.comp_apply]
  set n : N.ι → B := Pi.single i 1
  have hr : r = p * (r / p) + r % p := (Nat.div_add_mod r p).symm
  have ht : r % p < p := Nat.mod_lt _ (by omega)
  set c := r / p
  set t := r % p
  have hC1 := C1_F hp φ N c t (by omega) j hj n
  rw [← hr] at hC1
  show _ = (Tlat hp φ N).Fd r (Dmap B p N.ι (bv p j n))
  rw [Dmap_bv (j := j) (hj := by omega), map_smul, hr, tensor_Fd_frob hp φ _ c t ht, ← hr,
    St_Fd_single]
  split_ifs with hjt
  · dsimp only at hjt ⊢
    have hu := isUnit_factorial hp (t := t) (by omega)
    have key := congrArg (Dmap B p N.ι) (hC1.1 hjt)
    rw [map_smul] at key
    erw [Dmap_bv (j := j + t) (hj := by omega)] at key
    rw [← hu.smul_left_cancel]
    refine key.trans ?_
    rw [Tensor2.tprod_smul_left, smul_smul, smul_smul]
    congr 1
    rw [← Nat.add_choose_mul_factorial_mul_factorial (j : ℕ) t]
    push_cast; ring
  · dsimp only at hjt
    erw [hC1.2 (by omega)]
    rw [map_zero, tprod_zero_left, smul_zero]

include hp in
lemma Dmap_comm_E (r : ℕ) :
    Dmap B p N.ι ∘ₗ (Twist.baseChange φ (twist p N)).Ed r =
      (Tlat hp φ N).Ed r ∘ₗ Dmap B p N.ι := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  refine ext_single fun (x : Fin p × N.ι) => ?_
  obtain ⟨j, i⟩ := x
  have hj := j.isLt
  rw [single_eq_bv']
  simp only [LinearMap.comp_apply]
  set n : N.ι → B := Pi.single i 1
  have hr : r = p * (r / p) + r % p := (Nat.div_add_mod r p).symm
  have ht : r % p < p := Nat.mod_lt _ (by omega)
  set c := r / p
  set t := r % p
  have hC1 := C1_E hp φ N c t (by omega) j hj n
  rw [← hr] at hC1
  show _ = (Tlat hp φ N).Ed r (Dmap B p N.ι (bv p j n))
  rw [Dmap_bv (j := j) (hj := by omega), map_smul, hr, tensor_Ed_frob hp φ _ c t ht, ← hr,
    St_Ed_single]
  split_ifs with hjt
  · dsimp only at hjt ⊢
    have hu := isUnit_factorial hp (t := (j : ℕ) - t) (by omega)
    have key := congrArg (Dmap B p N.ι) (hC1.1 hjt)
    rw [map_smul, map_smul] at key
    erw [Dmap_bv (j := j - t) (hj := by omega)] at key
    rw [← hu.smul_left_cancel]
    refine key.trans ?_
    rw [Tensor2.tprod_smul_left, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  · dsimp only at hjt
    erw [hC1.2 (by omega)]
    rw [map_zero, tprod_zero_left, smul_zero]

lemma Dmap_comm_H :
    Dmap B p N.ι ∘ₗ H (Twist.baseChange φ (twist p N)) = H (Tlat hp φ N) ∘ₗ Dmap B p N.ι := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  refine LinearMap.ext fun x => ?_
  funext ⟨j, i⟩
  show (((j : ℕ)! : ℕ) : B) * ((Twist.baseChange φ (twist p N)).wt (Fin.cast p_sub_one_add_one j, i) *
      x (Fin.cast p_sub_one_add_one j, i)) =
    (Tlat hp φ N).wt (j, i) * ((((j : ℕ)! : ℕ) : B) * x (Fin.cast p_sub_one_add_one j, i))
  have hw : (Twist.baseChange φ (twist p N)).wt (Fin.cast p_sub_one_add_one j, i) =
      (Tlat hp φ N).wt (j, i) := by
    show twWt p N _ = weylWt (p - 1) j + p * N.wt i
    simp only [twWt, weylWt, Fin.val_cast]
    push_cast [Nat.cast_sub hp1.le]
    ring
  rw [← hw]; ring

/-- (C2) the morphism `D : baseChange φ (twist p N) → T`. -/
def Dhom : Hom (Twist.baseChange φ (twist p N)) (Tlat hp φ N) where
  toLin := Dmap B p N.ι
  comm_F := Dmap_comm_F hp φ N
  comm_E := Dmap_comm_E hp φ N
  comm_H := Dmap_comm_H hp φ N

/-- (C2) Proposition 1.2 (c): `Φ_p(N) ⊗ B ≅ St ⊗ (N ⊗ B)^{[1]}` by `D` and `D⁻¹`. -/
def prop12Iso : Doubling.Iso (Twist.baseChange φ (twist p N)) (Tlat hp φ N) :=
  Doubling.Iso.ofInverse (Dhom hp φ N) (Dinv B p N.ι) (Dinv_comp_Dmap hp) (Dmap_comp_Dinv hp)

/-- (C2) Proposition 1.2 (c). The diagonal `B`-linear map `D` from `Fin p × N.ι → B` to
`Fin (p − 1 + 1) × N.ι → B` with `D(b_j e_i) = (j! : B) · (e_j ⊗ e_i)` and its inverse are `Hom`s
between `baseChange φ (twist p N)` and `T = Tensor2.tensor St (frobP hp (baseChange φ N))`; this
gives a `Doubling.Iso (baseChange φ (twist p N)) T` whose underlying maps are `D` and `D⁻¹`. -/
theorem oddModP_C2 :
    (∀ (j : ℕ) (hj : j < p - 1 + 1) (i : N.ι),
      Dmap B p N.ι (bv p j (Pi.single i 1)) =
        ((j ! : ℕ) : B) • Tensor2.tprod (Pi.single (⟨j, hj⟩ : Fin (p - 1 + 1)) 1)
          (Pi.single i 1)) ∧
    ∃ u : Doubling.Iso (Twist.baseChange φ (twist p N))
        (Tensor2.tensor (St φ) (frobP hp (Twist.baseChange φ N))),
      u.hom.toLin = Dmap B p N.ι ∧ u.inv.toLin = Dinv B p N.ι :=
  ⟨fun j hj _ => Dmap_bv j hj _, prop12Iso hp φ N, rfl, rfl⟩

/-! ### (C3) -/

/-- (C3) The case of the paper satisfies the hypotheses of the Setting: `p = 0` in `ZMod p`, and
`PadicInt.toZMod : ℤ_[p] →+* ZMod p` is a ring homomorphism sending `p` to `0`. -/
theorem C3_hyp : ((p : ZMod p) = 0) ∧ PadicInt.toZMod (p : ℤ_[p]) = 0 :=
  ⟨ZMod.natCast_self p, by rw [map_natCast, ZMod.natCast_self]⟩

/-- (C3) The case of the paper: for `B = ZMod p`, `φ = PadicInt.toZMod` and every DP-lattice `N`
over `ℤ_[p]`, `Φ_p(N) ⊗ 𝔽_p ≅ St ⊗ (N ⊗ 𝔽_p)^{[1]}`. -/
theorem oddModP_C3 (N : DPLattice ℤ_[p]) :
    Nonempty (Doubling.Iso (Twist.baseChange PadicInt.toZMod (twist p N))
      (Tensor2.tensor (Twist.baseChange PadicInt.toZMod (delta ℤ_[p] (p - 1)))
        (frobP (ZMod.natCast_self p) (Twist.baseChange PadicInt.toZMod N)))) :=
  ⟨prop12Iso (ZMod.natCast_self p) PadicInt.toZMod N⟩

end ColouredSand.OddTwist
