module

public import RequestProject.ThmG.ExpGroups

/-!
# `CSI19_theorem_TOTAL.md`, Part S (S3), auxiliary — uniqueness of the exponents

Namespace `ColouredSand.OddTwist`; every new name starts with `oddTotal`.

The exponents of a finite abelian `p`-group are unique: if `ExpGrp p L ≃+ ExpGrp p L'`
(`ExpGrp p L = Π_{i} ℤ/p^{L_i}`, CSG7's encoding of `⊕_{e ∈ L} ℤ/p^e`) and no entry of `L`, `L'`
is `0`, then `L` is a permutation of `L'`.  The invariant used is the cardinality of
`p^k G = {p^k • x}`, which is `p^{Σ_i (L_i − k)}` for `G = ExpGrp p L`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open ColouredSand.ThmG

/-- The number of elements of `n • G` (auxiliary for (S3) of `CSI19_theorem_TOTAL.md`). -/
def oddTotalSmulCard (G : Type*) [AddCommGroup G] (n : ℕ) : ℕ :=
  Nat.card (Set.range fun x : G => n • x)

lemma oddTotalSmulCard_congr {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (e : G ≃+ G')
    (n : ℕ) : oddTotalSmulCard G n = oddTotalSmulCard G' n := by
  unfold oddTotalSmulCard
  have : (Set.range fun y : G' => n • y) = e '' Set.range fun x : G => n • x := by
    ext y
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨n • e.symm y, ⟨e.symm y, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp⟩
  rw [this, Nat.card_image_of_injective e.injective]

lemma oddTotalSmulCard_prod (A B : Type*) [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    oddTotalSmulCard (A × B) n = oddTotalSmulCard A n * oddTotalSmulCard B n := by
  unfold oddTotalSmulCard
  have : (Set.range fun x : A × B => n • x) =
      (Set.range fun x : A => n • x) ×ˢ (Set.range fun x : B => n • x) := by
    ext ⟨a, b⟩
    simp only [Set.mem_range, Set.mem_prod, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd,
      Prod.exists]
    constructor
    · rintro ⟨x, y, h1, h2⟩; exact ⟨⟨x, h1⟩, ⟨y, h2⟩⟩
    · rintro ⟨⟨x, h1⟩, ⟨y, h2⟩⟩; exact ⟨x, y, h1, h2⟩
  rw [this, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]

lemma oddTotalSmulCard_zmod (p : ℕ) [Fact p.Prime] (a k : ℕ) :
    oddTotalSmulCard (ZMod (p ^ a)) (p ^ k) = p ^ (a - k) := by
  have hp : p.Prime := Fact.out
  have hn : p ^ a ≠ 0 := pow_ne_zero _ hp.ne_zero
  unfold oddTotalSmulCard
  have : (Set.range fun x : ZMod (p ^ a) => (p ^ k) • x) =
      (AddSubgroup.zmultiples (((p ^ k : ℕ)) : ZMod (p ^ a)) : Set (ZMod (p ^ a))) := by
    ext y
    simp only [Set.mem_range, SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(x.val : ℤ), ?_⟩
      rw [natCast_zsmul, nsmul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
    · rintro ⟨z, rfl⟩
      exact ⟨(z : ZMod (p ^ a)), by rw [zsmul_eq_mul, nsmul_eq_mul, mul_comm]⟩
  rw [this]
  change Nat.card (AddSubgroup.zmultiples _) = _
  rw [Nat.card_zmultiples, ZMod.addOrderOf_coe _ hn]
  rcases le_total a k with h | h
  · rw [Nat.gcd_eq_left (pow_dvd_pow p h), Nat.div_self (pow_pos hp.pos _),
      Nat.sub_eq_zero_of_le h, pow_zero]
  · rw [Nat.gcd_eq_right (pow_dvd_pow p h), Nat.pow_div h hp.pos]

lemma oddTotalSmulCard_expGrp (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (L : List ℕ) → oddTotalSmulCard (ExpGrp p L) (p ^ k) = p ^ (L.map (· - k)).sum
  | [] => by
      unfold oddTotalSmulCard
      rw [Nat.card_unique]; simp
  | a :: L => by
      rw [oddTotalSmulCard_congr (expCons p a L), oddTotalSmulCard_prod, oddTotalSmulCard_zmod,
        oddTotalSmulCard_expGrp p k L, List.map_cons, List.sum_cons, pow_add]

lemma oddTotal_sum_sub_succ (k : ℕ) :
    (L : List ℕ) → (L.map (· - k)).sum = (L.map (· - (k + 1))).sum + L.countP (fun a => k < a)
  | [] => by simp
  | a :: L => by
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.countP_cons,
        oddTotal_sum_sub_succ k L]
      by_cases h : k < a
      · simp [h]; omega
      · simp [h]; omega

lemma oddTotal_countP_lt_pred (v : ℕ) (hv : v ≠ 0) :
    (L : List ℕ) → L.countP (fun a => v - 1 < a) = L.count v + L.countP (fun a => v < a)
  | [] => by simp
  | a :: L => by
      rw [List.countP_cons, List.countP_cons, List.count_cons, oddTotal_countP_lt_pred v hv L]
      by_cases h1 : a = v
      · subst h1
        simp only [beq_self_eq_true, lt_irrefl, decide_false, decide_true, show a - 1 < a by omega]
        simp
        omega
      · have h1' : (a == v) = false := by simpa using h1
        rw [h1']
        by_cases h2 : v < a
        · simp [h2, show v - 1 < a by omega]
          omega
        · simp [h2, show ¬ v - 1 < a by omega]

/-- **Uniqueness of the exponents** (auxiliary for (S3) of `CSI19_theorem_TOTAL.md`): if
`⊕_{e ∈ L} ℤ/p^e ≃+ ⊕_{e ∈ L'} ℤ/p^e` and no exponent is `0`, then `L` is a permutation of `L'`. -/
theorem oddTotal_perm_of_expGrp (p : ℕ) [Fact p.Prime] {L L' : List ℕ} (hL : ∀ a ∈ L, a ≠ 0)
    (hL' : ∀ a ∈ L', a ≠ 0) (e : ExpGrp p L ≃+ ExpGrp p L') : L.Perm L' := by
  have hp : p.Prime := Fact.out
  have hs : ∀ k, (L.map (· - k)).sum = (L'.map (· - k)).sum := fun k =>
    Nat.pow_right_injective hp.two_le (by
      simp only
      rw [← oddTotalSmulCard_expGrp, ← oddTotalSmulCard_expGrp, oddTotalSmulCard_congr e])
  have hc : ∀ k, L.countP (fun a => k < a) = L'.countP (fun a => k < a) := fun k => by
    have h1 := oddTotal_sum_sub_succ k L
    have h2 := oddTotal_sum_sub_succ k L'
    rw [hs k, hs (k + 1)] at h1
    omega
  rw [List.perm_iff_count]
  intro v
  by_cases hv : v = 0
  · subst hv
    rw [List.count_eq_zero.2 (fun h => hL 0 h rfl), List.count_eq_zero.2 (fun h => hL' 0 h rfl)]
  · have h1 := oddTotal_countP_lt_pred v hv L
    have h2 := oddTotal_countP_lt_pred v hv L'
    rw [hc (v - 1), hc v] at h1
    omega

end ColouredSand.OddTwist
