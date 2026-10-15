module

public import RequestProject.Strings.Basic

/-!
# (Q3) The Jordan type of the up operator `U` over `𝔽_3`

This file corresponds to **(Q3) The Jordan type of U over F_3** of
`CS6_corollaries_1_and_6.md`.

## Encoding

* `B_m(ZMod 3) = Finset (Fin m) → ZMod 3` and `U = U m (ZMod 3)` are those of
  `RequestProject/Strings/Basic.lean` (`(U f) T = ∑_{x ∈ T} f (T \ {x})`, i.e.
  `U e_S = ∑_{x ∉ S} e_{S ∪ {x}}`).
* `rank A` is `Module.finrank (ZMod 3) (LinearMap.range A)`; powers are powers in `Module.End`.
* `(a_m, b_m, c_m)` is `(jA m, jB m, jC m)`, defined by the recursion of the file
  (`jordanABC`).  `[m odd]` is written `m % 2`.
* `f(m) = dim_{𝔽_3} coker (U on B_m(𝔽_3))` is `fCoker m`, the `finrank` of
  `B_m(ZMod 3) ⧸ range U`.
* The Jordan-block reading (`a_m` blocks of size 1, `b_m` of size 2, `c_m` of size 3) is
  equivalent to the rank statements together with `U^3 = 0` and `a_m + 2 b_m + 3 c_m = 2^m`
  (`jordan_dim`): the number of blocks of size `≥ i` is `rank U^{i−1} − rank U^i`.

## Proof

The direct proof suggested in the file, with no Hopf algebra: `B_{m+1} ≅ B_m × B_m`
(`splitEquiv`, splitting on whether `m ∈ S`) turns `U_{m+1}` into `T(x,y) = (U_m x, x + U_m y)`
(`splitEquiv_U`).  For any `A` on a finite-dimensional space, `rank T = dim V + rank A^2`
(`finrank_range_blockOp`), and, if `A^3 = 0` and `2 ≠ 0`, `rank T^2 = rank A`
(`finrank_range_blockOp_sq`); in characteristic 3, `T^3 = 0` when `A^3 = 0` (`blockOp_cube`).
The main results are `U_cube_zmod_three`, `rank_U_zmod_three`, `jordanABC_closed` and
`fCoker_formula`, collected in `jordan_type_U_zmod_three`.
-/

@[expose] public section

namespace ColouredSand.Corollaries

open Module

section abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The block operator `T(x, y) = (A x, x + A y)` on `V × V`. -/
def blockOp (A : V →ₗ[K] V) : (V × V) →ₗ[K] (V × V) :=
  LinearMap.prod (A ∘ₗ LinearMap.fst K V V)
    (LinearMap.fst K V V + A ∘ₗ LinearMap.snd K V V)

@[simp] lemma blockOp_apply (A : V →ₗ[K] V) (x : V × V) :
    blockOp A x = (A x.1, x.1 + A x.2) := rfl

lemma blockOp_sq_apply (A : V →ₗ[K] V) (x : V × V) :
    (blockOp A ^ 2) x = (A (A x.1), (2 : K) • A x.1 + A (A x.2)) := by
  rw [pow_two, Module.End.mul_apply]
  simp only [blockOp_apply, map_add, Prod.mk.injEq, true_and]
  rw [two_smul]; abel

lemma blockOp_cube_apply (A : V →ₗ[K] V) (x : V × V) :
    (blockOp A ^ 3) x = (A (A (A x.1)), (3 : K) • A (A x.1) + A (A (A x.2))) := by
  rw [pow_succ, Module.End.mul_apply, blockOp_apply, blockOp_sq_apply]
  simp only [map_add, Prod.mk.injEq, true_and]
  have : (3 : K) = 2 + 1 := by norm_num
  rw [this, add_smul, one_smul]; abel

lemma finrank_ker_blockOp (A : V →ₗ[K] V) :
    finrank K (LinearMap.ker (blockOp A)) = finrank K (LinearMap.ker (A ^ 2)) := by
  let j : LinearMap.ker (A ^ 2) →ₗ[K] V × V :=
    LinearMap.prod (-(A ∘ₗ (LinearMap.ker (A ^ 2)).subtype)) (LinearMap.ker (A ^ 2)).subtype
  have hj : Function.Injective j := by
    intro y z h
    exact Subtype.ext (congrArg Prod.snd h)
  have hr : LinearMap.range j = LinearMap.ker (blockOp A) := by
    ext ⟨x, y⟩
    simp only [LinearMap.mem_range, LinearMap.mem_ker, blockOp_apply, Prod.mk_eq_zero]
    constructor
    · rintro ⟨⟨z, hz⟩, h⟩
      simp only [j, LinearMap.prod_apply, Submodule.coe_subtype] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply] at hz
      simp [hz]
    · rintro ⟨h1, h2⟩
      have hx : x = -A y := eq_neg_of_add_eq_zero_left h2
      refine ⟨⟨y, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply]
        rw [hx, map_neg, neg_eq_zero] at h1; exact h1
      · simp [j, hx]
  rw [← hr, LinearMap.finrank_range_of_inj hj]

lemma finrank_range_blockOp [FiniteDimensional K V] (A : V →ₗ[K] V) :
    finrank K (LinearMap.range (blockOp A)) =
      finrank K V + finrank K (LinearMap.range (A ^ 2)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (blockOp A)
  have h2 := LinearMap.finrank_range_add_finrank_ker (A ^ 2)
  rw [finrank_ker_blockOp, Module.finrank_prod] at h1
  omega

lemma finrank_ker_blockOp_sq [FiniteDimensional K V] (A : V →ₗ[K] V) (hA : A ^ 3 = 0) (h2 : (2 : K) ≠ 0) :
    finrank K (LinearMap.ker (blockOp A ^ 2)) = finrank K (LinearMap.ker A) + finrank K V := by
  have hA3 : ∀ v, A (A (A v)) = 0 := fun v => by
    have := LinearMap.congr_fun hA v
    simpa [pow_succ, Module.End.mul_apply] using this
  let j : (LinearMap.ker A × V) →ₗ[K] V × V :=
    { toFun := fun z => ((2 : K)⁻¹ • ((z.1 : V) - A z.2), z.2)
      map_add' := fun a b => by
        ext
        · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add, ← smul_add]
          congr 1; abel
        · rfl
      map_smul' := fun c a => by
        ext
        · simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, map_smul,
            RingHom.id_apply, Prod.smul_mk, ← smul_sub, smul_comm c]
        · rfl }
  have hj : Function.Injective j := by
    intro a b h
    simp only [j, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq] at h
    obtain ⟨h1, h2'⟩ := h
    rw [h2'] at h1
    have := smul_right_injective V (inv_ne_zero h2) h1
    simp only [sub_left_inj] at this
    exact Prod.ext (Subtype.ext this) h2'
  have hr : LinearMap.range j = LinearMap.ker (blockOp A ^ 2) := by
    ext ⟨x, y⟩
    simp only [LinearMap.mem_range, LinearMap.mem_ker, blockOp_sq_apply, Prod.mk_eq_zero]
    constructor
    · rintro ⟨⟨⟨k, hk⟩, z⟩, h⟩
      simp only [j, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [LinearMap.mem_ker] at hk
      simp only [map_smul, map_sub, hk, zero_sub, smul_neg, smul_smul,
        mul_inv_cancel₀ h2, one_smul, neg_add_cancel, and_true, smul_zero, map_neg, hA3, neg_zero]
    · rintro ⟨-, h⟩
      refine ⟨⟨⟨(2 : K) • x + A y, ?_⟩, y⟩, ?_⟩
      · rw [LinearMap.mem_ker, map_add, map_smul]; exact h
      · simp only [j, LinearMap.coe_mk, AddHom.coe_mk, add_sub_cancel_right, smul_smul,
          inv_mul_cancel₀ h2, one_smul]
  rw [← hr, LinearMap.finrank_range_of_inj hj, Module.finrank_prod]

lemma finrank_range_blockOp_sq [FiniteDimensional K V] (A : V →ₗ[K] V) (hA : A ^ 3 = 0) (h2 : (2 : K) ≠ 0) :
    finrank K (LinearMap.range (blockOp A ^ 2)) = finrank K (LinearMap.range A) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (blockOp A ^ 2)
  have h3 := LinearMap.finrank_range_add_finrank_ker A
  rw [finrank_ker_blockOp_sq A hA h2, Module.finrank_prod] at h1
  omega

lemma blockOp_cube (A : V →ₗ[K] V) (hA : A ^ 3 = 0) (h3 : (3 : K) = 0) :
    blockOp A ^ 3 = 0 := by
  have hA3 : ∀ v, A (A (A v)) = 0 := fun v => by
    have := LinearMap.congr_fun hA v
    simpa [pow_succ, Module.End.mul_apply] using this
  ext x <;> simp [blockOp_cube_apply, hA3, h3]

/-- Ranks are invariant under conjugation. -/
lemma finrank_range_conj {W : Type*} [AddCommGroup W] [Module K W] (e : W ≃ₗ[K] V)
    (T : V →ₗ[K] V) :
    finrank K (LinearMap.range (e.symm.toLinearMap ∘ₗ T ∘ₗ e.toLinearMap)) =
      finrank K (LinearMap.range T) := by
  rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ e.range]
  exact LinearEquiv.finrank_map_eq e.symm _

end abstract


/-! ### Splitting `B_{m+1}` as `B_m × B_m` -/

section split

open ColouredSand.Strings Finset

variable {m : ℕ} {R : Type*} [CommRing R]

/-- The sets `T ⊆ Fin (m+1)`, read as subsets of `Fin m` by forgetting `m`. -/
noncomputable def restr (T : Finset (Fin (m + 1))) : Finset (Fin m) :=
  T.preimage Fin.castSucc (Fin.castSucc_injective m).injOn

lemma restr_map (S : Finset (Fin m)) : restr (S.map Fin.castSuccEmb) = S := by
  ext i; simp [restr]

lemma restr_insert_map (S : Finset (Fin m)) :
    restr (insert (Fin.last m) (S.map Fin.castSuccEmb)) = S := by
  ext i; simp [restr, Fin.castSucc_ne_last]

lemma last_not_mem_map (S : Finset (Fin m)) : Fin.last m ∉ S.map Fin.castSuccEmb := by
  simp [Fin.castSucc_ne_last]

lemma map_restr_of_not_mem {T : Finset (Fin (m + 1))} (h : Fin.last m ∉ T) :
    (restr T).map Fin.castSuccEmb = T := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [h, Fin.castSucc_ne_last]
  | cast i => simp [restr]

lemma insert_map_restr_of_mem {T : Finset (Fin (m + 1))} (h : Fin.last m ∈ T) :
    insert (Fin.last m) ((restr T).map Fin.castSuccEmb) = T := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [h]
  | cast i => simp [restr, Fin.castSucc_ne_last]

/-- `B_{m+1} ≅ B_m × B_m`: the first component collects the coefficients of the sets not
containing `m`, the second those of the sets containing `m`. -/
noncomputable def splitEquiv : B (m + 1) R ≃ₗ[R] B m R × B m R where
  toFun f := (fun S => f (S.map Fin.castSuccEmb),
    fun S => f (insert (Fin.last m) (S.map Fin.castSuccEmb)))
  invFun g T := if Fin.last m ∈ T then g.2 (restr T) else g.1 (restr T)
  map_add' f g := rfl
  map_smul' c f := rfl
  left_inv f := by
    funext T
    by_cases h : Fin.last m ∈ T
    · simp only [if_pos h, insert_map_restr_of_mem h]
    · simp only [if_neg h, map_restr_of_not_mem h]
  right_inv g := by
    ext S
    · simp [restr_map]
    · simp [restr_insert_map]

/-- In the splitting, `U_{m+1} = [[U_m, 0], [1, U_m]]`. -/
lemma splitEquiv_U (f : B (m + 1) R) :
    splitEquiv (U (m + 1) R f) =
      (U m R (splitEquiv f).1, (splitEquiv f).1 + U m R (splitEquiv f).2) := by
  ext S
  · change ∑ x ∈ S.map Fin.castSuccEmb, f ((S.map Fin.castSuccEmb).erase x) =
      ∑ x ∈ S, f ((S.erase x).map Fin.castSuccEmb)
    rw [sum_map]
    refine sum_congr rfl fun x _ => ?_
    rw [map_erase]
  · change ∑ x ∈ insert (Fin.last m) (S.map Fin.castSuccEmb),
        f ((insert (Fin.last m) (S.map Fin.castSuccEmb)).erase x) =
      f (S.map Fin.castSuccEmb) +
        ∑ x ∈ S, f (insert (Fin.last m) ((S.erase x).map Fin.castSuccEmb))
    rw [sum_insert (last_not_mem_map S), erase_insert (last_not_mem_map S), sum_map]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    rw [erase_insert_of_ne (show Fin.last m ≠ Fin.castSuccEmb x from (Fin.castSucc_ne_last x).symm),
      map_erase]

end split

/-! ### The Jordan type of `U` over `𝔽_3` -/

section jordan

open ColouredSand.Strings Finset

/-- The triple `(a_m, b_m, c_m)`: `(a_0,b_0,c_0) = (1,0,0)` and
`(a_{m+1}, b_{m+1}, c_{m+1}) = (b_m, a_m, b_m + 2 c_m)`. -/
def jordanABC : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 0, 0)
  | m + 1 => ((jordanABC m).2.1, (jordanABC m).1, (jordanABC m).2.1 + 2 * (jordanABC m).2.2)

/-- `a_m`, the number of Jordan blocks of size `1`. -/
def jA (m : ℕ) : ℕ := (jordanABC m).1
/-- `b_m`, the number of Jordan blocks of size `2`. -/
def jB (m : ℕ) : ℕ := (jordanABC m).2.1
/-- `c_m`, the number of Jordan blocks of size `3`. -/
def jC (m : ℕ) : ℕ := (jordanABC m).2.2

@[simp] lemma jA_zero : jA 0 = 1 := rfl
@[simp] lemma jB_zero : jB 0 = 0 := rfl
@[simp] lemma jC_zero : jC 0 = 0 := rfl
lemma jA_succ (m : ℕ) : jA (m + 1) = jB m := rfl
lemma jB_succ (m : ℕ) : jB (m + 1) = jA m := rfl
lemma jC_succ (m : ℕ) : jC (m + 1) = jB m + 2 * jC m := rfl

lemma one_add_mod_two_le_two_pow (m : ℕ) : 1 + m % 2 ≤ 2 ^ m := by
  rcases m with _ | m
  · simp
  · have : 2 ≤ 2 ^ (m + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- `a_m + b_m = 1`, `b_m = [m odd]` (written `m % 2`) and `3 c_m = 2^m − 1 − [m odd]`. -/
theorem jordanABC_closed (m : ℕ) :
    jA m + jB m = 1 ∧ jB m = m % 2 ∧ 3 * jC m = 2 ^ m - 1 - m % 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have h4 := one_add_mod_two_le_two_pow m
    rw [jA_succ, jB_succ, jC_succ, pow_succ]
    omega

/-- `a_m + 2 b_m + 3 c_m = 2^m` (the block sizes add up to `dim B_m`). -/
lemma jordan_dim (m : ℕ) : jA m + 2 * jB m + 3 * jC m = 2 ^ m := by
  obtain ⟨h1, h2, h3⟩ := jordanABC_closed m
  have h4 := one_add_mod_two_le_two_pow m
  omega

variable {K : Type*} [Field K]

lemma splitEquiv_U_pow {m : ℕ} (k : ℕ) (f : B (m + 1) K) :
    splitEquiv ((U (m + 1) K ^ k) f) = (blockOp (U m K) ^ k) (splitEquiv f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, splitEquiv_U, ih, pow_succ', Module.End.mul_apply]
    rfl

lemma U_pow_succ_eq_conj (m k : ℕ) :
    U (m + 1) K ^ k = splitEquiv.symm.toLinearMap ∘ₗ (blockOp (U m K) ^ k) ∘ₗ
      splitEquiv.toLinearMap := by
  refine LinearMap.ext fun f => ?_
  change _ = splitEquiv.symm ((blockOp (U m K) ^ k) (splitEquiv f))
  rw [← splitEquiv_U_pow, LinearEquiv.symm_apply_apply]

lemma finrank_range_U_pow_succ (m k : ℕ) :
    finrank K (LinearMap.range (U (m + 1) K ^ k)) =
      finrank K (LinearMap.range (blockOp (U m K) ^ k)) := by
  rw [U_pow_succ_eq_conj]
  exact finrank_range_conj _ _

lemma U_zero_eq : U 0 K = 0 := by
  ext f T
  have : T = ∅ := Subsingleton.elim _ _
  simp [this]

lemma finrank_B (m : ℕ) : finrank K (B m K) = 2 ^ m := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_finset, Fintype.card_fin]

/-- **(Q3)** `U^3 = 0` on `B_m(𝔽_3)`. -/
theorem U_cube_zmod_three (m : ℕ) : U m (ZMod 3) ^ 3 = 0 := by
  induction m with
  | zero => rw [U_zero_eq]; rfl
  | succ m ih =>
    rw [U_pow_succ_eq_conj, blockOp_cube _ ih (by decide)]
    simp

/-- **(Q3)** On `B_m(𝔽_3)`: `rank U = b_m + 2 c_m` and `rank U^2 = c_m`. -/
theorem rank_U_zmod_three (m : ℕ) :
    finrank (ZMod 3) (LinearMap.range (U m (ZMod 3))) = jB m + 2 * jC m ∧
      finrank (ZMod 3) (LinearMap.range (U m (ZMod 3) ^ 2)) = jC m := by
  induction m with
  | zero => simp [U_zero_eq]
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · have := finrank_range_U_pow_succ (K := ZMod 3) m 1
      rw [pow_one, pow_one] at this
      rw [this, finrank_range_blockOp, finrank_B, h2, jB_succ, jC_succ]
      have := jordan_dim m
      omega
    · rw [finrank_range_U_pow_succ, finrank_range_blockOp_sq _ (U_cube_zmod_three m) (by decide),
        h1, jC_succ]

/-- `f(m) = dim_{𝔽_3} coker (U on B_m(𝔽_3))`. -/
noncomputable def fCoker (m : ℕ) : ℕ :=
  finrank (ZMod 3) (B m (ZMod 3) ⧸ LinearMap.range (U m (ZMod 3)))

lemma fCoker_eq (m : ℕ) :
    fCoker m = 2 ^ m - finrank (ZMod 3) (LinearMap.range (U m (ZMod 3))) := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (U m (ZMod 3)))
  rw [finrank_B] at h
  unfold fCoker
  omega

/-- **(Q3)** `3 (f(m) − 1) = 2^m − 1 − [m odd]`. -/
theorem fCoker_formula (m : ℕ) : 3 * (fCoker m - 1) = 2 ^ m - 1 - m % 2 := by
  rw [fCoker_eq, (rank_U_zmod_three m).1]
  obtain ⟨h1, h2, h3⟩ := jordanABC_closed m
  have := jordan_dim m
  have h4 := one_add_mod_two_le_two_pow m
  omega

/-- **(Q3) The Jordan type of `U` over `𝔽_3`, all statements.**  On `B_m(ZMod 3)`:
`U^3 = 0`, `rank U = b_m + 2 c_m`, `rank U^2 = c_m`, `a_m + b_m = 1`, `b_m = [m odd]`,
`3 c_m = 2^m − 1 − [m odd]`, `f(m) = 2^m − rank U` and `3 (f(m) − 1) = 2^m − 1 − [m odd]`. -/
theorem jordan_type_U_zmod_three (m : ℕ) :
    U m (ZMod 3) ^ 3 = 0 ∧
    finrank (ZMod 3) (LinearMap.range (U m (ZMod 3))) = jB m + 2 * jC m ∧
    finrank (ZMod 3) (LinearMap.range (U m (ZMod 3) ^ 2)) = jC m ∧
    jA m + jB m = 1 ∧ jB m = m % 2 ∧ 3 * jC m = 2 ^ m - 1 - m % 2 ∧
    fCoker m = 2 ^ m - finrank (ZMod 3) (LinearMap.range (U m (ZMod 3))) ∧
    3 * (fCoker m - 1) = 2 ^ m - 1 - m % 2 :=
  ⟨U_cube_zmod_three m, (rank_U_zmod_three m).1, (rank_U_zmod_three m).2,
    (jordanABC_closed m).1, (jordanABC_closed m).2.1, (jordanABC_closed m).2.2, fCoker_eq m,
    fCoker_formula m⟩

end jordan

end ColouredSand.Corollaries
