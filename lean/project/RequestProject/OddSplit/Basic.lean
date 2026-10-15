module

public import RequestProject.OddTwist.All
public import RequestProject.Filt.Sub

/-!
# `CSI3_the_split.md`: Part Q0, and the encodings used in the whole folder

Namespace `ColouredSand.OddTwist`. We reuse C18 (`DPLattice`, `IsDP`, `H`, `Hom`, `InWt`, `V`),
C20 (`Doubling.homOfOne`, `Doubling.factorial_smul_of_rec`, `Doubling.dp_rec_F`, …),
C23 (`Tensor2.tensor`, `Tensor2.tprod`, `Tensor2.tensor_Fd_tprod`, `Tensor2.tensor_Ed_tprod`),
C29 (`Filt.sub`) and CSI1 (`bv`, `twist`, `B1`).

Encodings (used in every file of `RequestProject/OddSplit/`):

* `p` is a natural number with `[Fact p.Prime]`; the ring is `ℤ_[p]`.
* The basis of `Ψ_r(N)` is `Bool × Fin p × N.ι`: `false` stands for the letter `A`, `true` for
  the letter `C`. For a vector `n : N.ι → ℤ_[p]` and a natural number `k`,
  `aV p k n` is `A_k n` and `cV p k n` is `C_k n` (the vector with `n` in the slot `(false, k)`,
  resp. `(true, k)`; it is `0` if `k ≥ p`, which never occurs in the formulas). They are built as
  `sv false (bv p k n)` and `sv true (bv p k n)`, where `bv` is CSI1's slot vector and
  `sv e y` puts `y : Y → A` in the component `e` of `Bool × Y → A`.
* The tensor product `V ⊗ M` is C23's `Tensor2.tensor (V ℤ_[p]) M` (basis `Fin 2 × M.ι`), and
  `tv e x = Tensor2.tprod (Pi.single e 1) x` is `b̂_e ⊗ x`.
* "`x ≡ y` modulo `p`" is `ModP p x y : ∃ z, x - y = p • z` (in any `ℤ_[p]`-module).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset

open scoped Nat

/-! ### Part Q0 -/

section Q0

/-- (Q0a) For every DP-lattice `M` over a commutative ring and every `r`:
`r! • F^{(r)} = (F^{(1)})^r` and `r! • E^{(r)} = (E^{(1)})^r`. -/
theorem Q0a {A : Type*} [CommRing A] (M : DPLattice A) (r : ℕ) :
    ((r ! : ℕ) : A) • M.Fd r = M.Fd 1 ^ r ∧ ((r ! : ℕ) : A) • M.Ed r = M.Ed 1 ^ r :=
  ⟨Doubling.factorial_smul_of_rec _ M.isDP.P0_F (Doubling.dp_rec_F M) r,
    Doubling.factorial_smul_of_rec _ M.isDP.P0_E (Doubling.dp_rec_E M) r⟩

lemma factorial_ne_zero_cast {A : Type*} [CommRing A] [IsDomain A] [CharZero A] (r : ℕ) :
    ((r ! : ℕ) : A) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r

/-- (Q0b) Two DP-lattice structures with the same basis type `ι` and the same weights `wt`
whose `F^{(1)}` and `E^{(1)}` agree have the same `F^{(r)}` and `E^{(r)}` for every `r`.
Stated for every domain of characteristic zero (more general than `ℤ_[p]`). -/
theorem Q0b {A : Type*} [CommRing A] [IsDomain A] [CharZero A] {ι : Type} [Fintype ι]
    [DecidableEq ι] (wt : ι → ℤ) {Fd Ed Fd' Ed' : ℕ → Module.End A (ι → A)}
    (h : IsDP wt Fd Ed) (h' : IsDP wt Fd' Ed') (hF : Fd 1 = Fd' 1) (hE : Ed 1 = Ed' 1) :
    Fd = Fd' ∧ Ed = Ed' := by
  let M : DPLattice A := ⟨ι, wt, Fd, Ed, h⟩
  let M' : DPLattice A := ⟨ι, wt, Fd', Ed', h'⟩
  refine ⟨funext fun r => LinearMap.ext fun x => ?_, funext fun r => LinearMap.ext fun x => ?_⟩
  · apply Doubling.cancel_smul (factorial_ne_zero_cast (A := A) r)
    have e1 := LinearMap.congr_fun (Q0a M r).1 x
    have e2 := LinearMap.congr_fun (Q0a M' r).1 x
    simp only [LinearMap.smul_apply] at e1 e2
    rw [e1, e2]
    change (Fd 1 ^ r) x = (Fd' 1 ^ r) x
    rw [hF]
  · apply Doubling.cancel_smul (factorial_ne_zero_cast (A := A) r)
    have e1 := LinearMap.congr_fun (Q0a M r).2 x
    have e2 := LinearMap.congr_fun (Q0a M' r).2 x
    simp only [LinearMap.smul_apply] at e1 e2
    rw [e1, e2]
    change (Ed 1 ^ r) x = (Ed' 1 ^ r) x
    rw [hE]

/-- (Q0c) A linear map commuting with `F^{(1)}`, `E^{(1)}` and `H` is a morphism of DP-lattices
(over any domain of characteristic zero, e.g. `ℤ_[p]`). This is C20's `Doubling.homOfOne`. -/
def Q0c {A : Type*} [CommRing A] [IsDomain A] [CharZero A] {M M' : DPLattice A}
    (f : (M.ι → A) →ₗ[A] (M'.ι → A)) (hF : f ∘ₗ M.Fd 1 = M'.Fd 1 ∘ₗ f)
    (hE : f ∘ₗ M.Ed 1 = M'.Ed 1 ∘ₗ f) (hH : f ∘ₗ H M = H M' ∘ₗ f) : Hom M M' :=
  Doubling.homOfOne f hF hE hH

/-- (Q0c) the morphism of (Q0c) has the given underlying linear map. -/
theorem Q0c_toLin {A : Type*} [CommRing A] [IsDomain A] [CharZero A] {M M' : DPLattice A}
    (f : (M.ι → A) →ₗ[A] (M'.ι → A)) (hF : f ∘ₗ M.Fd 1 = M'.Fd 1 ∘ₗ f)
    (hE : f ∘ₗ M.Ed 1 = M'.Ed 1 ∘ₗ f) (hH : f ∘ₗ H M = H M' ∘ₗ f) :
    (Q0c f hF hE hH).toLin = f := rfl

/-- (Q0d) Saturation: if `j` has a left inverse `ρ`, `c ≠ 0` and `c • y ∈ range j`, then
`y ∈ range j` (over any domain, for a torsion-free target). -/
theorem Q0d {A : Type*} [CommRing A] [IsDomain A] {X Y : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] [Module.IsTorsionFree A Y] (j : X →ₗ[A] Y) (ρ : Y →ₗ[A] X)
    (hρ : ρ ∘ₗ j = LinearMap.id) {c : A} (hc : c ≠ 0) {y : Y} (hy : c • y ∈ LinearMap.range j) :
    y ∈ LinearMap.range j := by
  obtain ⟨z, hz⟩ := hy
  have hz' : z = c • ρ y := by
    have := congrArg ρ hz
    rwa [← LinearMap.comp_apply, hρ, LinearMap.id_apply, map_smul] at this
  refine ⟨ρ y, Doubling.cancel_smul hc ?_⟩
  rw [← map_smul, ← hz', hz]

/-- `j ∘ T^r = G^r ∘ j` when `j ∘ T = G ∘ j`. -/
lemma comp_pow_of_comm {A : Type*} [CommRing A] {X Y : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (j : X →ₗ[A] Y) (T : Module.End A X) (G : Module.End A Y)
    (h : j ∘ₗ T = G ∘ₗ j) (r : ℕ) (x : X) : j ((T ^ r) x) = (G ^ r) (j x) := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih,
      ← LinearMap.comp_apply j T, h, LinearMap.comp_apply]

/-- (Q0e) Stability from the single operators: if `X` is a DP-lattice over a domain of
characteristic zero (e.g. `ℤ_[p]`), `j` is linear with a left inverse, and `j ∘ T = F^{(1)} ∘ j`,
`j ∘ S = E^{(1)} ∘ j`, then `range j` is stable under every `F^{(r)}` and `E^{(r)}` of `X`. -/
theorem Q0e {A : Type*} [CommRing A] [IsDomain A] [CharZero A] (X : DPLattice A) {κ : Type*}
    [AddCommGroup κ] [Module A κ] (j : κ →ₗ[A] (X.ι → A)) (ρ : (X.ι → A) →ₗ[A] κ)
    (hρ : ρ ∘ₗ j = LinearMap.id) (T S : Module.End A κ) (hT : j ∘ₗ T = X.Fd 1 ∘ₗ j)
    (hS : j ∘ₗ S = X.Ed 1 ∘ₗ j) :
    (∀ r x, X.Fd r (j x) ∈ LinearMap.range j) ∧ (∀ r x, X.Ed r (j x) ∈ LinearMap.range j) := by
  refine ⟨fun r x => Q0d j ρ hρ (factorial_ne_zero_cast (A := A) r) ⟨(T ^ r) x, ?_⟩,
    fun r x => Q0d j ρ hρ (factorial_ne_zero_cast (A := A) r) ⟨(S ^ r) x, ?_⟩⟩
  · rw [comp_pow_of_comm j T _ hT, ← (Q0a X r).1]; rfl
  · rw [comp_pow_of_comm j S _ hS, ← (Q0a X r).2]; rfl

end Q0

/-! ### Congruences modulo `p` -/

section modp

variable (p : ℕ) [Fact p.Prime]

/-- `x ≡ y` modulo `p`: `x − y = p • z` for some `z`. -/
def ModP {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] (x y : M) : Prop :=
  ∃ z, x - y = (p : ℤ_[p]) • z

variable {p} {M M' : Type*} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup M'] [Module ℤ_[p] M']

lemma ModP.refl (x : M) : ModP p x x := ⟨0, by simp⟩

lemma ModP.of_eq {x y : M} (h : x = y) : ModP p x y := h ▸ ModP.refl x

lemma ModP.symm {x y : M} (h : ModP p x y) : ModP p y x := by
  obtain ⟨z, hz⟩ := h; exact ⟨-z, by rw [smul_neg, ← hz]; abel⟩

lemma ModP.trans {x y z : M} (h1 : ModP p x y) (h2 : ModP p y z) : ModP p x z := by
  obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2
  exact ⟨a + b, by rw [smul_add, ← ha, ← hb]; abel⟩

lemma ModP.add {x y x' y' : M} (h1 : ModP p x y) (h2 : ModP p x' y') : ModP p (x + x') (y + y') := by
  obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2
  exact ⟨a + b, by rw [smul_add, ← ha, ← hb]; abel⟩

lemma ModP.sub {x y x' y' : M} (h1 : ModP p x y) (h2 : ModP p x' y') : ModP p (x - x') (y - y') := by
  obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2
  exact ⟨a - b, by rw [smul_sub, ← ha, ← hb]; abel⟩

lemma ModP.smul (c : ℤ_[p]) {x y : M} (h : ModP p x y) : ModP p (c • x) (c • y) := by
  obtain ⟨a, ha⟩ := h; exact ⟨c • a, by rw [← smul_sub, ha, smul_comm]⟩

lemma ModP.map (f : M →ₗ[ℤ_[p]] M') {x y : M} (h : ModP p x y) : ModP p (f x) (f y) := by
  obtain ⟨a, ha⟩ := h; exact ⟨f a, by rw [← map_sub, ha, map_smul]⟩

lemma ModP.p_smul (x : M) : ModP p ((p : ℤ_[p]) • x) 0 := ⟨x, by simp⟩

lemma ModP.smul_congr {c d : ℤ_[p]} (h : ∃ e, c - d = (p : ℤ_[p]) * e) (x : M) :
    ModP p (c • x) (d • x) := by
  obtain ⟨e, he⟩ := h; exact ⟨e • x, by rw [← sub_smul, he, mul_smul]⟩

lemma ModP.coord {ι : Type*} {x y : ι → ℤ_[p]} (h : ModP p x y) (i : ι) :
    ∃ e, x i - y i = (p : ℤ_[p]) * e := by
  obtain ⟨z, hz⟩ := h; exact ⟨z i, by simpa using congr_fun hz i⟩

end modp

/-! ### Slot vectors on `Bool × Fin p × ι` -/

section slots

variable {A : Type*} [CommRing A]

/-- The vector of `Bool × Y → A` with `y` in the component `e` (and `0` in the other one). -/
def sv {Y : Type*} (e : Bool) : (Y → A) →ₗ[A] (Bool × Y → A) where
  toFun y x := if x.1 = e then y x.2 else 0
  map_add' m m' := by funext x; by_cases h : x.1 = e <;> simp [h]
  map_smul' c m := by funext x; by_cases h : x.1 = e <;> simp [h]

@[simp] lemma sv_apply {Y : Type*} (e : Bool) (y : Y → A) (x : Bool × Y) :
    sv e y x = if x.1 = e then y x.2 else 0 := rfl

variable (p : ℕ) {ι : Type*}

/-- `A_k n`: the vector of `Bool × Fin p × ι → A` with `n` in the slot `(false, k)`. -/
def aV (k : ℕ) : (ι → A) →ₗ[A] (Bool × Fin p × ι → A) := sv false ∘ₗ bv p k

/-- `C_k n`: the vector of `Bool × Fin p × ι → A` with `n` in the slot `(true, k)`. -/
def cV (k : ℕ) : (ι → A) →ₗ[A] (Bool × Fin p × ι → A) := sv true ∘ₗ bv p k

lemma aV_apply (k : ℕ) (n : ι → A) (x : Bool × Fin p × ι) :
    aV p k n x = if x.1 = false ∧ (x.2.1 : ℕ) = k then n x.2.2 else 0 := by
  simp only [aV, LinearMap.comp_apply, sv_apply, bv_apply]
  by_cases h1 : x.1 = false <;> by_cases h2 : (x.2.1 : ℕ) = k <;> simp [h1, h2]

lemma cV_apply (k : ℕ) (n : ι → A) (x : Bool × Fin p × ι) :
    cV p k n x = if x.1 = true ∧ (x.2.1 : ℕ) = k then n x.2.2 else 0 := by
  simp only [cV, LinearMap.comp_apply, sv_apply, bv_apply]
  by_cases h1 : x.1 = true <;> by_cases h2 : (x.2.1 : ℕ) = k <;> simp [h1, h2]

lemma aV_of_ge {k : ℕ} (hk : p ≤ k) (n : ι → A) : aV p k n = 0 := by
  simp [aV, bv_of_ge p hk]

lemma cV_of_ge {k : ℕ} (hk : p ≤ k) (n : ι → A) : cV p k n = 0 := by
  simp [cV, bv_of_ge p hk]

lemma single_false [DecidableEq ι] (j : Fin p) (i : ι) :
    (Pi.single (false, j, i) (1 : A) : Bool × Fin p × ι → A) = aV p j (Pi.single i 1) := by
  funext ⟨b, j', i'⟩
  rw [aV_apply]
  by_cases hb : b = false <;> by_cases hj : j' = j <;> by_cases hi : i' = i <;>
    simp [Pi.single_apply, hb, hj, hi, Fin.val_eq_val]

lemma single_true [DecidableEq ι] (j : Fin p) (i : ι) :
    (Pi.single (true, j, i) (1 : A) : Bool × Fin p × ι → A) = cV p j (Pi.single i 1) := by
  funext ⟨b, j', i'⟩
  rw [cV_apply]
  by_cases hb : b = true <;> by_cases hj : j' = j <;> by_cases hi : i' = i <;>
    simp [Pi.single_apply, hb, hj, hi, Fin.val_eq_val]

/-- Two linear maps out of `Bool × Fin p × ι → A` agreeing on every `A_j δ_i` and `C_j δ_i`
(`j < p`) are equal. -/
lemma ext_aV_cV [Fintype ι] [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module A M]
    {f g : (Bool × Fin p × ι → A) →ₗ[A] M}
    (hA : ∀ (j : ℕ) (i : ι), j < p → f (aV p j (Pi.single i 1)) = g (aV p j (Pi.single i 1)))
    (hC : ∀ (j : ℕ) (i : ι), j < p → f (cV p j (Pi.single i 1)) = g (cV p j (Pi.single i 1))) :
    f = g := by
  refine ext_single fun x => ?_
  obtain ⟨b, j, i⟩ := x
  cases b
  · rw [single_false]; exact hA j i j.isLt
  · rw [single_true]; exact hC j i j.isLt

end slots

/-! ### The tensor product `V ⊗ M` -/

section tensorV

variable {A : Type*} [CommRing A] {ι : Type*}

/-- `b̂_e ⊗ x` in `Fin 2 × ι → A`. -/
def tv (e : Fin 2) : (ι → A) →ₗ[A] (Fin 2 × ι → A) where
  toFun x := Tensor2.tprod (Pi.single e 1) x
  map_add' _ _ := Tensor2.tprod_add_right _ _ _
  map_smul' _ _ := Tensor2.tprod_smul_right _ _ _

lemma tv_apply (e : Fin 2) (x : ι → A) (y : Fin 2 × ι) :
    tv e x y = if y.1 = e then x y.2 else 0 := by
  simp only [tv, LinearMap.coe_mk, AddHom.coe_mk, Tensor2.tprod_apply, Pi.single_apply]
  split_ifs <;> simp

variable (M : DPLattice A)

lemma tensorV_Fd1_tv0 (x : M.ι → A) :
    (Tensor2.tensor (V A) M).Fd 1 (tv 0 x) = tv 1 x + tv 0 (M.Fd 1 x) := by
  change (Tensor2.tensor (V A) M).Fd 1 (Tensor2.tprod _ x) = _
  rw [Tensor2.tensor_Fd_tprod, Finset.sum_range_succ, Finset.sum_range_one, (V A).isDP.P0_F,
    M.isDP.P0_F, V_Fd_one_b0]
  simp only [Module.End.one_apply, Nat.sub_zero]
  rw [add_comm]; rfl

lemma tensorV_Fd1_tv1 (x : M.ι → A) :
    (Tensor2.tensor (V A) M).Fd 1 (tv 1 x) = tv 1 (M.Fd 1 x) := by
  change (Tensor2.tensor (V A) M).Fd 1 (Tensor2.tprod _ x) = _
  rw [Tensor2.tensor_Fd_tprod, Finset.sum_range_succ, Finset.sum_range_one, (V A).isDP.P0_F,
    V_Fd_one_b1]
  simp only [Module.End.one_apply, Nat.sub_self, Nat.sub_zero, Tensor2.tprod_zero_left,
    add_zero]
  rfl

lemma tensorV_Ed1_tv0 (x : M.ι → A) :
    (Tensor2.tensor (V A) M).Ed 1 (tv 0 x) = tv 0 (M.Ed 1 x) := by
  change (Tensor2.tensor (V A) M).Ed 1 (Tensor2.tprod _ x) = _
  rw [Tensor2.tensor_Ed_tprod, Finset.sum_range_succ, Finset.sum_range_one, (V A).isDP.P0_E,
    V_Ed_one_b0]
  simp only [Module.End.one_apply, Nat.sub_self, Nat.sub_zero, Tensor2.tprod_zero_left,
    add_zero]
  rfl

lemma tensorV_Ed1_tv1 (x : M.ι → A) :
    (Tensor2.tensor (V A) M).Ed 1 (tv 1 x) = tv 0 x + tv 1 (M.Ed 1 x) := by
  change (Tensor2.tensor (V A) M).Ed 1 (Tensor2.tprod _ x) = _
  rw [Tensor2.tensor_Ed_tprod, Finset.sum_range_succ, Finset.sum_range_one, (V A).isDP.P0_E,
    M.isDP.P0_E, V_Ed_one_b1]
  simp only [Module.End.one_apply, Nat.sub_zero]
  rw [add_comm]; rfl

lemma tensorV_Fpow_tv1 (k : ℕ) (x : M.ι → A) :
    ((Tensor2.tensor (V A) M).Fd 1 ^ k) (tv 1 x) = tv 1 ((M.Fd 1 ^ k) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, Module.End.mul_apply, tensorV_Fd1_tv1, ih, pow_succ]; rfl

/-- `F^k (b̂_0 ⊗ x) = b̂_0 ⊗ F^k x + k · b̂_1 ⊗ F^{k−1} x` on `V ⊗ M`. -/
lemma tensorV_Fpow_tv0 (k : ℕ) (x : M.ι → A) :
    ((Tensor2.tensor (V A) M).Fd 1 ^ k) (tv 0 x) =
      tv 0 ((M.Fd 1 ^ k) x) + (k : A) • tv 1 ((M.Fd 1 ^ (k - 1)) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, tensorV_Fd1_tv0,
      tensorV_Fd1_tv1, pow_succ', Module.End.mul_apply]
    rcases k with _ | k
    · simp [add_comm]
    · simp only [Nat.add_sub_cancel, pow_succ', Module.End.mul_apply]
      push_cast
      module

lemma inWt_tv (e : Fin 2) {μ : ℤ} {x : M.ι → A} (hx : InWt M.wt μ x) :
    InWt (Tensor2.tensor (V A) M).wt (wtV e + μ) (tv e x) := by
  intro ⟨e', i⟩ h
  rw [tv_apply]
  split_ifs with he
  · subst he; exact hx i fun h' => h (by simp [Tensor2.tensor, V, h'])
  · rfl

end tensorV

end ColouredSand.OddTwist
