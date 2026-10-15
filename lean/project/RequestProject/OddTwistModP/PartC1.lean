module

public import RequestProject.OddTwistModP.PartS

/-!
# `CSI2_reduction_mod_p.md`: Part C, (C1) — the formulas modulo `p`

Encodings: `N : DPLattice ℤ_[p]`, `N̄ = baseChange φ N`, and `baseChange φ (twist p N)` is
`Φ_p(N) ⊗ B` (basis `Fin p × N.ι`). The slot vector `b_j n` (for `n : N.ι → B`) is CSI1's
`bv p j n` (with `A = B`). `F̄^{(c)}`, `Ē^{(c)}` are `(baseChange φ N).Fd c`,
`(baseChange φ N).Ed c`. The divisions by `t!` and `(j − t)!` of the file are stated
multiplicatively (both are units of `B`, `isUnit_factorial`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice Finset Polynomial

local notation:10000 n "!" => Nat.factorial n

variable {B : Type*} [CommRing B] {p : ℕ} [Fact p.Prime]

/-! ### Reduction of the slot vectors and of `P_{j,r}` -/

lemma bv_comp (φ : ℤ_[p] →+* B) {ι : Type*} (k : ℕ) (m : ι → ℤ_[p]) :
    bv p k (⇑φ ∘ m) = ⇑φ ∘ bv p k m := by
  funext x; by_cases h : (x.1 : ℕ) = k <;> simp [h]

variable (hp : (p : B) = 0) (φ : ℤ_[p] →+* B)

include hp in
lemma map_pFactor (w : ℤ) (ak : ℕ × ℕ) :
    (pFactor p w ak).map φ = C (-((ak.2 : ℕ) : B) ^ 2) := by
  rw [pFactor, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_C, map_pow, map_natCast, hp, map_intCast,
    show ((0 : B) ^ 2) = 0 by ring, C_0, zero_mul, zero_add]
  congr 1
  push_cast
  rw [hp]; ring

include hp in
/-- (C1, proof) `P_{j,r}` reduces modulo `p` to the scalar `∏_{(a,k) ∈ S} (−k²)`. -/
lemma bc_PP (N : DPLattice ℤ_[p]) (w : ℤ) (S : Finset (ℕ × ℕ)) :
    Twist.bc φ (PP p N w S) = (∏ ak ∈ S, (-((ak.2 : ℕ) : B) ^ 2)) • (1 : Module.End B (N.ι → B)) := by
  rw [PP, Twist.bc_aeval, Polynomial.map_prod]
  simp_rw [map_pFactor hp φ w]
  rw [← map_prod, aeval_C, Module.algebraMap_end_eq_smul_id]
  rfl

/-! ### The set `S(j, r)` for `r = pc + t`, `t ≤ j` -/

lemma mem_Sset_mul_add {j t c : ℕ} (hj : j < p) (ht : t ≤ j) (a k : ℕ) :
    (a, k) ∈ Sset p j (p * c + t) ↔
      1 ≤ k ∧ k ≤ p - 1 ∧ (a = 0 → k ≤ j) ∧ (a < c ∨ (a = c ∧ j < t + k)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  rw [mem_Sset p (by omega)]
  simp only
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    rcases lt_trichotomy a c with h | h | h
    · exact Or.inl h
    · subst h; right; exact ⟨rfl, by omega⟩
    · have : p * c + p ≤ p * a := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
      omega
  · rintro ⟨h1, h2, h3, h4 | ⟨rfl, h4⟩⟩
    · refine ⟨h1, h2, h3, ?_⟩
      have : p * a + p ≤ p * c := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h4
      omega
    · exact ⟨h1, h2, h3, by omega⟩

include hp in
lemma prod_neg_sq_wilson : ∏ k ∈ Ioc 0 (p - 1), (-((k : ℕ) : B) ^ 2) = 1 := by
  have hpp : p.Prime := Fact.out
  have hfact : ∀ n : ℕ, ∏ k ∈ Ioc 0 n, (k : ℕ) = n ! := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.prod_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ]; ring
  rw [prod_neg, prod_pow, ← Nat.cast_prod, hfact, wilson_B hp, Nat.card_Ioc]
  rcases hpp.eq_two_or_odd' with h2 | hodd
  · subst h2
    have h2 : (2 : B) = 0 := by simpa using hp
    rw [show (2 : ℕ) - 1 - 0 = 1 from rfl]
    linear_combination -h2
  · obtain ⟨m, hm⟩ := hodd
    rw [show p - 1 - 0 = 2 * m by omega, pow_mul]; norm_num

include hp in
/-- (C1, proof) For `t ≤ j < p`: `∏_{(a,k) ∈ S(j, pc+t)} (−k²) = ∏_{j−t < k ≤ j} (−k²)` in `B`. -/
lemma prod_Sset (j t : ℕ) (hj : j < p) (ht : t ≤ j) (c : ℕ) :
    ∏ ak ∈ Sset p j (p * c + t), (-((ak.2 : ℕ) : B) ^ 2) =
      ∏ k ∈ Ioc (j - t) j, (-((k : ℕ) : B) ^ 2) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  induction c with
  | zero =>
    have : Sset p j (p * 0 + t) = (Ioc (j - t) j).image (fun k => (0, k)) := by
      ext ⟨a, k⟩
      rw [mem_Sset_mul_add hj ht]
      simp only [mem_image, mem_Ioc, Prod.mk.injEq]
      constructor
      · rintro ⟨h1, h2, h3, h4 | ⟨rfl, h4⟩⟩
        · omega
        · exact ⟨k, ⟨by omega, h3 rfl⟩, rfl, rfl⟩
      · rintro ⟨k', ⟨h1, h2⟩, rfl, rfl⟩
        exact ⟨by omega, by omega, fun _ => h2, Or.inr ⟨rfl, by omega⟩⟩
    rw [this, prod_image (fun x _ y _ h => (Prod.mk.inj h).2)]
  | succ c ih =>
    have hS : Sset p j (p * (c + 1) + t) = (Sset p j (p * c + t) ∪
        (Ioc 0 (j - t)).image (fun k => (c, k))) ∪ (Ioc (j - t) (p - 1)).image (fun k => (c + 1, k)) := by
      ext ⟨a, k⟩
      rw [mem_union, mem_union, mem_Sset_mul_add hj ht, mem_Sset_mul_add hj ht]
      simp only [mem_image, mem_Ioc, Prod.mk.injEq]
      constructor
      · rintro ⟨h1, h2, h3, h4 | ⟨rfl, h4⟩⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp h4 with h | rfl
          · exact Or.inl (Or.inl ⟨h1, h2, h3, Or.inl h⟩)
          · by_cases hk : j < t + k
            · exact Or.inl (Or.inl ⟨h1, h2, h3, Or.inr ⟨rfl, hk⟩⟩)
            · exact Or.inl (Or.inr ⟨k, ⟨h1, by omega⟩, rfl, rfl⟩)
        · exact Or.inr ⟨k, ⟨by omega, h2⟩, rfl, rfl⟩
      · rintro ((⟨h1, h2, h3, h4 | ⟨rfl, h4⟩⟩ | ⟨k', ⟨h1, h2⟩, rfl, rfl⟩) | ⟨k', ⟨h1, h2⟩, rfl, rfl⟩)
        · exact ⟨h1, h2, h3, Or.inl (by omega)⟩
        · exact ⟨h1, h2, h3, Or.inl (by omega)⟩
        · exact ⟨by omega, by omega, fun _ => by omega, Or.inl (by omega)⟩
        · exact ⟨by omega, h2, fun h => by omega, Or.inr ⟨rfl, by omega⟩⟩
    have hd1 : Disjoint (Sset p j (p * c + t)) ((Ioc 0 (j - t)).image (fun k => (c, k))) := by
      rw [Finset.disjoint_left]
      rintro ⟨a, k⟩ h1 h2
      rw [mem_Sset_mul_add hj ht] at h1
      simp only [mem_image, mem_Ioc, Prod.mk.injEq] at h2
      obtain ⟨k', ⟨h5, h6⟩, rfl, rfl⟩ := h2
      omega
    have hd2 : Disjoint (Sset p j (p * c + t) ∪ (Ioc 0 (j - t)).image (fun k => (c, k)))
        ((Ioc (j - t) (p - 1)).image (fun k => (c + 1, k))) := by
      rw [Finset.disjoint_left]
      rintro ⟨a, k⟩ h1 h2
      rw [mem_union, mem_Sset_mul_add hj ht] at h1
      simp only [mem_image, mem_Ioc, Prod.mk.injEq] at h1 h2
      obtain ⟨k', ⟨h5, h6⟩, rfl, rfl⟩ := h2
      omega
    rw [hS, prod_union hd2, prod_union hd1, ih, prod_image (fun x _ y _ h => (Prod.mk.inj h).2),
      prod_image (fun x _ y _ h => (Prod.mk.inj h).2), mul_assoc,
      prod_Ioc_consecutive _ (Nat.zero_le _) (by omega), prod_neg_sq_wilson hp, mul_one]

/-! ### The coefficient identities -/

lemma factorial_mul_prod_Ioc (j t : ℕ) :
    (j - t)! * ∏ k ∈ Ioc (j - t) j, k = j ! := by
  have hfact : ∀ n : ℕ, ∏ k ∈ Ioc 0 n, (k : ℕ) = n ! := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.prod_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ]; ring
  rw [← hfact, ← hfact, prod_Ioc_consecutive _ (Nat.zero_le _) (Nat.sub_le j t)]

omit [Fact p.Prime] in
include hp in
lemma descFactorial_cast (j : ℕ) (hj : j < p) : ∀ t : ℕ, t ≤ j →
    (((p - 1 - j + t).descFactorial t : ℕ) : B) = (-1) ^ t * ((∏ k ∈ Ioc (j - t) j, k : ℕ) : B) := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    intro ht
    have e : p - 1 - j + (t + 1) = (p - 1 - j + t) + 1 := by ring
    rw [e, Nat.succ_descFactorial_succ, Nat.cast_mul, ih (by omega)]
    rw [← prod_Ioc_consecutive _ (show j - (t + 1) ≤ j - t by omega) (Nat.sub_le j t),
      show j - t = j - (t + 1) + 1 by omega, Nat.Ioc_succ_singleton, prod_singleton,
      ← show j - t = j - (t + 1) + 1 by omega]
    have : ((p - 1 - j + t + 1 : ℕ) : B) = -((j - t : ℕ) : B) := by
      rw [show p - 1 - j + t + 1 = p - (j - t) by omega, Nat.cast_sub (by omega), hp]; ring
    push_cast [this]
    ring

omit [Fact p.Prime] in
include hp in
/-- (C1, proof) `(j − t)! · ∏_{j−t < k ≤ j} (−k²) = t! · j! · C(p − 1 − j + t, t)` in `B`, for
`t ≤ j < p`. -/
lemma coef_E (j t : ℕ) (hj : j < p) (ht : t ≤ j) :
    (((j - t)! : ℕ) : B) * ∏ k ∈ Ioc (j - t) j, (-((k : ℕ) : B) ^ 2) =
      ((t ! : ℕ) : B) * ((j ! : ℕ) : B) * ((p - 1 - j + t).choose t : B) := by
  have h1 := factorial_mul_prod_Ioc j t
  have h2 := descFactorial_cast hp j hj t ht
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h2
  rw [prod_neg, prod_pow, Nat.card_Ioc, show j - (j - t) = t by omega]
  have h1' := congrArg (Nat.cast : ℕ → B) h1
  push_cast at h2 h1' ⊢
  linear_combination (-1 : B) ^ t * (∏ k ∈ Ioc (j - t) j, (k : B)) * h1' -
    ((j ! : ℕ) : B) * h2

/-! ### (C1) on basis vectors -/

variable (N : DPLattice ℤ_[p])

include hp in
lemma C1_F_single (c t : ℕ) (ht : t ≤ p - 1) (j : ℕ) (hj : j < p) (i : N.ι) :
    (j + t ≤ p - 1 → ((t ! : ℕ) : B) • Twist.bc φ (twFd p N (p * c + t)) (bv p j (Pi.single i 1)) =
      bv p (j + t) (Twist.bc φ (N.Fd c) (Pi.single i 1))) ∧
    (p - 1 < j + t → Twist.bc φ (twFd p N (p * c + t)) (bv p j (Pi.single i 1)) = 0) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have key := twFd_single p N (p * c + t) ⟨j, hj⟩ i
  simp only at key
  rw [← Twist.comp_single φ i, bv_comp, Twist.bc_apply_comp, key, Twist.comp_smul,
    Twist.bc_apply_comp, ← bv_comp]
  have hC0 := C0 hp φ c t ht
  constructor
  · intro hjt
    have hd : (j + (p * c + t)) / p = c :=
      (div_mod_unique (m := j + t) (by ring) (by omega)).1
    rw [hd, show j + (p * c + t) - p * c = j + t by omega, smul_smul, map_mul, map_pow, map_neg,
      map_one]
    rw [show ((t ! : ℕ) : B) * ((-1) ^ c * φ (qc p c (p * c + t))) =
      (-1) ^ c * (φ (qc p c (p * c + t)) * ((t ! : ℕ) : B)) by ring, hC0.1, ← pow_add, ← two_mul,
      pow_mul]
    simp
  · intro hjt
    have hd : (j + (p * c + t)) / p = c + 1 :=
      (div_mod_unique (m := j + t - p) (by rw [Nat.mul_succ]; omega) (by omega)).1
    rw [hd, map_mul, hC0.2 (c + 1) le_rfl, mul_zero, zero_smul]

include hp in
lemma C1_E_single (c t : ℕ) (ht : t ≤ p - 1) (j : ℕ) (hj : j < p) (i : N.ι) :
    (t ≤ j → (((j - t)! : ℕ) : B) • Twist.bc φ (twEd p N (p * c + t)) (bv p j (Pi.single i 1)) =
      (((j ! : ℕ) : B) * ((p - 1 - j + t).choose t : B)) •
        bv p (j - t) (Twist.bc φ (N.Ed c) (Pi.single i 1))) ∧
    (j < t → Twist.bc φ (twEd p N (p * c + t)) (bv p j (Pi.single i 1)) = 0) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have key := twEd_single p N (p * c + t) ⟨j, hj⟩ i
  simp only at key
  rw [← Twist.comp_single φ i, bv_comp, Twist.bc_apply_comp, key, Twist.comp_smul,
    Twist.bc_apply_comp, ← bv_comp]
  have hC0 := C0 hp φ c t ht
  constructor
  · intro htj
    have hd : (p * c + t + p - 1 - j) / p = c :=
      (div_mod_unique (m := t + p - 1 - j) (by omega) (by omega)).1
    have hPP : ⇑φ ∘ (N.Ed c) ((PP p N (N.wt i) (Sset p j (p * c + t))) (Pi.single i 1)) =
        (∏ ak ∈ Sset p j (p * c + t), (-((ak.2 : ℕ) : B) ^ 2)) •
          (⇑φ ∘ (N.Ed c) (Pi.single i 1)) := by
      rw [← Twist.bc_apply_comp, ← Twist.bc_apply_comp φ (PP p N (N.wt i) _), Twist.comp_single,
        bc_PP hp φ, LinearMap.smul_apply, Module.End.one_apply, map_smul, ← Twist.comp_single φ i,
        Twist.bc_apply_comp]
    rw [hd, show j + p * c - (p * c + t) = j - t by omega, hPP, map_smul, smul_smul, smul_smul,
      prod_Sset hp j t hj htj c, map_mul, map_pow, map_neg, map_one]
    congr 1
    have hE := coef_E hp j t hj htj
    have h3 : ((-1 : B) ^ c) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    linear_combination (-1 : B) ^ c * φ (qc p c (p * c + t)) * hE +
      ((j ! : ℕ) : B) * ((p - 1 - j + t).choose t : B) * (-1 : B) ^ c * hC0.1 +
      ((j ! : ℕ) : B) * ((p - 1 - j + t).choose t : B) * h3
  · intro htj
    have hd : (p * c + t + p - 1 - j) / p = c + 1 :=
      (div_mod_unique (m := t - 1 - j) (by rw [Nat.mul_succ]; omega) (by omega)).1
    rw [hd, map_mul, hC0.2 (c + 1) le_rfl, mul_zero, zero_smul]

/-! ### (C1) -/

omit [Fact p.Prime] in
lemma ext_red {X : Type*} [AddCommGroup X] [Module B X] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T U : (ι → B) →ₗ[B] X} (h : ∀ i, T (Pi.single i 1) = U (Pi.single i 1)) : T = U :=
  ext_single h

include hp in
/-- (C1) The `F` formula modulo `p`. On `baseChange φ (twist p N)` (`Φ_p(N) ⊗ B`), for
`r = p·c + t` (`0 ≤ t ≤ p − 1`), every slot `j < p` and every `n : N.ι → B`:
`(t! : B) • F^{(r)}(b_j n) = b_{j+t} (F̄^{(c)} n)` if `j + t ≤ p − 1`, and `F^{(r)}(b_j n) = 0`
otherwise (`F̄^{(c)}` of `N̄ = baseChange φ N`). -/
theorem C1_F (c t : ℕ) (ht : t ≤ p - 1) (j : ℕ) (hj : j < p) (n : N.ι → B) :
    (j + t ≤ p - 1 → ((t ! : ℕ) : B) • (Twist.baseChange φ (twist p N)).Fd (p * c + t) (bv p j n) =
      bv p (j + t) ((Twist.baseChange φ N).Fd c n)) ∧
    (p - 1 < j + t → (Twist.baseChange φ (twist p N)).Fd (p * c + t) (bv p j n) = 0) := by
  constructor
  · intro hjt
    have := ext_red (T := ((t ! : ℕ) : B) • (Twist.bc φ (twFd p N (p * c + t)) ∘ₗ bv p j))
      (U := bv p (j + t) ∘ₗ Twist.bc φ (N.Fd c))
      (fun i => (C1_F_single hp φ N c t ht j hj i).1 hjt)
    exact LinearMap.congr_fun this n
  · intro hjt
    have := ext_red (T := Twist.bc φ (twFd p N (p * c + t)) ∘ₗ bv p j) (U := 0)
      (fun i => (C1_F_single hp φ N c t ht j hj i).2 hjt)
    exact LinearMap.congr_fun this n

include hp in
/-- (C1) The `E` formula modulo `p`. On `baseChange φ (twist p N)`, for `r = p·c + t`
(`0 ≤ t ≤ p − 1`), every slot `j < p` and every `n : N.ι → B`:
`((j − t)! : B) • E^{(r)}(b_j n) = (j! : B) · C(p − 1 − j + t, t) • b_{j−t} (Ē^{(c)} n)` if `t ≤ j`,
and `E^{(r)}(b_j n) = 0` otherwise (`Ē^{(c)}` of `N̄ = baseChange φ N`). -/
theorem C1_E (c t : ℕ) (ht : t ≤ p - 1) (j : ℕ) (hj : j < p) (n : N.ι → B) :
    (t ≤ j → (((j - t)! : ℕ) : B) • (Twist.baseChange φ (twist p N)).Ed (p * c + t) (bv p j n) =
      (((j ! : ℕ) : B) * ((p - 1 - j + t).choose t : B)) •
        bv p (j - t) ((Twist.baseChange φ N).Ed c n)) ∧
    (j < t → (Twist.baseChange φ (twist p N)).Ed (p * c + t) (bv p j n) = 0) := by
  constructor
  · intro htj
    have := ext_red (T := (((j - t)! : ℕ) : B) • (Twist.bc φ (twEd p N (p * c + t)) ∘ₗ bv p j))
      (U := (((j ! : ℕ) : B) * ((p - 1 - j + t).choose t : B)) •
        (bv p (j - t) ∘ₗ Twist.bc φ (N.Ed c)))
      (fun i => (C1_E_single hp φ N c t ht j hj i).1 htj)
    exact LinearMap.congr_fun this n
  · intro htj
    have := ext_red (T := Twist.bc φ (twEd p N (p * c + t)) ∘ₗ bv p j) (U := 0)
      (fun i => (C1_E_single hp φ N c t ht j hj i).2 htj)
    exact LinearMap.congr_fun this n

include hp in
/-- (C1) The formulas modulo `p` on `baseChange φ (twist p N)`, for `r = p·c + t`
(`0 ≤ t ≤ p − 1`), every slot `j < p` and every `n : N.ι → B`:
* `(t! : B) • F^{(r)}(b_j n) = b_{j+t} (F̄^{(c)} n)` if `j + t ≤ p − 1`, and `F^{(r)}(b_j n) = 0`
  otherwise;
* `((j − t)! : B) • E^{(r)}(b_j n) = (j! : B) · C(p − 1 − j + t, t) • b_{j−t} (Ē^{(c)} n)` if
  `t ≤ j`, and `E^{(r)}(b_j n) = 0` otherwise. -/
theorem oddModP_C1 (c t : ℕ) (ht : t ≤ p - 1) (j : ℕ) (hj : j < p) (n : N.ι → B) :
    (j + t ≤ p - 1 → ((t ! : ℕ) : B) • (Twist.baseChange φ (twist p N)).Fd (p * c + t) (bv p j n) =
      bv p (j + t) ((Twist.baseChange φ N).Fd c n)) ∧
    (p - 1 < j + t → (Twist.baseChange φ (twist p N)).Fd (p * c + t) (bv p j n) = 0) ∧
    (t ≤ j → (((j - t)! : ℕ) : B) • (Twist.baseChange φ (twist p N)).Ed (p * c + t) (bv p j n) =
      (((j ! : ℕ) : B) * ((p - 1 - j + t).choose t : B)) •
        bv p (j - t) ((Twist.baseChange φ N).Ed c n)) ∧
    (j < t → (Twist.baseChange φ (twist p N)).Ed (p * c + t) (bv p j n) = 0) :=
  ⟨(C1_F hp φ N c t ht j hj n).1, (C1_F hp φ N c t ht j hj n).2, (C1_E hp φ N c t ht j hj n).1,
    (C1_E hp φ N c t ht j hj n).2⟩

end ColouredSand.OddTwist
