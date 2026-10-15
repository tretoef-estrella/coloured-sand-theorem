module

public import RequestProject.OddPotential.Flat

/-!
# `CSI16_theorem_F_at_p.md` — *Part T*: Theorem F_p and Corollary F′_p

Base-`p` analogue of `RequestProject/Potential/TheoremF.lean` (C8).  Encodings as in
`RequestProject/OddPotential/LemmaP.lean`.  In Corollary F′_p, subsets of `I` are `Finset ℕ`s with
`D ⊆ I`, `rank_I = GoldenMatching.rank I` (C4; by CSI14 (A2), `A2_rank`, it is also the rank
`rankP p dg I` in the base-`p` o-order) and the o-order is the base-`p` one, `o_E = oW p dg E`.
-/

@[expose] public section

namespace ColouredSand.OddTwist

open Finset AntitonicFit TheoremF Potential

variable {p : ℕ}

/-- Base of the induction of Theorem F_p: for `I = ∅`, `V := 0` is a potential.  (No hypothesis
is needed.) -/
lemma oddF_potential_empty (k : ℕ) (dg : ℕ → ℕ) (ℓ : ℕ) (e : ℤ) :
    IsPotentialP p k ∅ dg ℓ e (fun _ => 0) := by
  refine ⟨fun q hq => ?_, fun _ _ _ _ => le_rfl, fun q q' harr => ?_⟩
  · simp only [card_empty, pow_zero] at hq
    obtain rfl : q = 0 := by omega
    have h1 := A2 (oddF_xH_antisymm p k (∅ : Finset ℕ) dg ℓ e) 0 (by simp)
    simp only [card_empty, pow_zero] at h1
    simp only [yhatP, card_empty, pow_zero, sub_self]
    simp at h1; omega
  · exfalso
    obtain ⟨-, -, hss⟩ := harr
    have h := lemma_0a (∅ : Finset ℕ) q
    rw [subset_empty] at h
    rw [h] at hss
    exact not_ssubset_empty _ hss

variable [hp : Fact p.Prime]

/-- Induction step of Theorem F_p: from a potential `V'` for `H'`, Lemma N (if `X_1(M − 1) > 0`) or
Lemma F with `c_F := lo` (if `X_1(M − 1) ≤ 0`) gives a potential for `H`. -/
lemma oddF_potential_step {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) (hne : I.Nonempty)
    {c : ℕ} (hc : c = I.max' hne) {V' : ℕ → ℤ}
    (hV' : IsPotentialP p c (I.erase c) dg (ℓ % p ^ c) e V') :
    ∃ V, IsPotentialP p k I dg ℓ e V := by
  by_cases hX : 0 < X1P p k I dg ℓ e c (2 ^ #(I.erase c) - 1)
  · exact ⟨_, oddF_lemma_N hI hd hℓ he hne hc hV' hX⟩
  · push_neg at hX
    obtain ⟨f, hf⟩ := oddF_exists_flat_start hX
    exact ⟨_, oddF_F4_flat hI hd hℓ he hne hc hV' hf _ le_rfl (oddF_F3_flat hd hne hc hV' hf)⟩

/-- Theorem F_p by induction on `n = |I|`. -/
lemma oddF_potential_exists_aux (dg : ℕ → ℕ) : ∀ (n : ℕ) (I : Finset ℕ) (k ℓ : ℕ) (e : ℤ),
    #I = n → (∀ t ∈ I, t < k) → (∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) → ℓ < p ^ k → 1 ≤ e →
      ∃ V, IsPotentialP p k I dg ℓ e V := by
  intro n
  induction n with
  | zero =>
    intro I k ℓ e hn _ _ _ _
    rw [card_eq_zero.1 hn]
    exact ⟨_, oddF_potential_empty k dg ℓ e⟩
  | succ n ih =>
    intro I k ℓ e hn hI hd hℓ he
    have hne : I.Nonempty := card_pos.1 (by omega)
    set c := I.max' hne with hc
    have hcI : c ∈ I := I.max'_mem hne
    have hI' : ∀ t ∈ I.erase c, t < c := fun t ht =>
      lt_of_le_of_ne (I.le_max' t (mem_of_mem_erase ht)) (ne_of_mem_erase ht)
    have hn' : #(I.erase c) = n := by rw [card_erase_of_mem hcI]; omega
    obtain ⟨V', hV'⟩ := ih (I.erase c) c (ℓ % p ^ c) e hn' hI' (hd_erase hd c)
      (Nat.mod_lt _ (pow_pos hp.out.pos c)) he
    exact oddF_potential_step hI hd hℓ he hne hc hV'

/-- **Theorem F_p** (`CSI16_theorem_F_at_p.md`, Part T): every base-`p` house
`H = (I, k, ℓ, e, d)` (`I ⊆ {0, …, k − 1}`, `ℓ < p^k`, `d_t ∈ [1, p − 1]` on `I`, `e ≥ 1`) has a
potential `V`, i.e. (E), (M), (G) hold. -/
theorem oddF_theorem_F {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    ∃ V : ℕ → ℤ, IsPotentialP p k I dg ℓ e V :=
  oddF_potential_exists_aux dg _ I k ℓ e rfl hI hd hℓ he

/-- **Corollary F′_p** (the subset form; `CSI16_theorem_F_at_p.md`, Part T): for every base-`p`
house there is `W : Finset ℕ → ℤ` with, for `D, E, F, a, b ⊆ I`:
(E) `W(D) − W(I ∖ D) = ŷ_H(rank_I(D))`;
(M) `o_E ≤ o_F ⟹ W(F) ≤ W(E)`, in the base-`p` o-order `o_E = Σ_{t∈E} d_t p^t`;
(G) `b ⊊ a ⟹ W(a) − W(b) ≤ ĉ_H(a, b)` (CSI15's `cHatHP`).
Here `W(D) := V(rank_I(D))` for a potential `V` (Theorem F_p). -/
theorem oddF_corollary_F' {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (hℓ : ℓ < p ^ k) (he : 1 ≤ e) :
    ∃ W : Finset ℕ → ℤ,
      (∀ D, D ⊆ I → W D - W (I \ D) = yhatP p k I dg ℓ e (GoldenMatching.rank I D)) ∧
      (∀ E F, E ⊆ I → F ⊆ I → oW p dg E ≤ oW p dg F → W F ≤ W E) ∧
      (∀ a b, a ⊆ I → b ⊆ I → b ⊂ a → W a - W b ≤ cHatHP p k I dg ℓ e a b) := by
  obtain ⟨V, hV⟩ := oddF_theorem_F hI hd hℓ he
  refine ⟨fun D => V (GoldenMatching.rank I D), fun D hD => ?_, fun E F hE hF hEF => ?_,
    fun a b ha hb hab => ?_⟩
  · simp only
    rw [GoldenMatching.lemma_C1_rank hD]
    exact hV.E _ (GoldenMatching.rank_lt hD)
  · simp only
    apply hV.M _ _ _ (GoldenMatching.rank_lt hF)
    by_contra hlt
    push_neg at hlt
    have h1 := lemma_0b hlt (GoldenMatching.rank_lt hE)
    rw [dancer_rank hE, dancer_rank hF] at h1
    have h2 := (A1_same_order oddHou_two_le_p hd hF hE).2 h1
    exact absurd hEF (not_le.2 h2)
  · have harr : IsArrow I (GoldenMatching.rank I a) (GoldenMatching.rank I b) :=
      ⟨GoldenMatching.rank_lt ha, GoldenMatching.rank_lt hb, by
        rw [dancer_rank ha, dancer_rank hb]; exact hab⟩
    have := hV.G _ _ harr
    simp only [cHatSeqP, dancer_rank ha, dancer_rank hb] at this
    exact this

end ColouredSand.OddTwist

namespace ColouredSand.OddTwist

open Finset AntitonicFit TheoremF Potential

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Part Δ, step 1** of `CSI16_theorem_F_at_p.md` (the bound behind `(Λ_p)`): for a house with
`I ≠ ∅`, `c = max I`, `h = k − c` and every `q < M`,
`d_1(q) ≤ −τ + [AND]·κ = e d_c p^c − h + ([OR ∨ DIG] + [AND])·κ ≤ e d_c p^c`, and
`X_1(q) ≤ e·o_{I'} + e d_c p^c = e·o_I`. -/
theorem oddF_delta_step1 {I : Finset ℕ} {k ℓ : ℕ} {dg : ℕ → ℕ} {e : ℤ} (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 1 ≤ dg t ∧ dg t ≤ p - 1) (he : 1 ≤ e) (hne : I.Nonempty) {c : ℕ}
    (hc : c = I.max' hne) :
    ∀ q < 2 ^ #(I.erase c),
      dWalkP p k I dg ℓ e c q ≤
        -tauP p k I dg ℓ e c + (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) ∧
      -tauP p k I dg ℓ e c + (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) =
        e * dg c * (p : ℤ) ^ c - ((k - c : ℕ) : ℤ) +
          ((if typP p dg ℓ c = .OR ∨ typP p dg ℓ c = .DIG then (kapP p k I ℓ c : ℤ) else 0) +
            (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0)) ∧
      e * dg c * (p : ℤ) ^ c - ((k - c : ℕ) : ℤ) +
          ((if typP p dg ℓ c = .OR ∨ typP p dg ℓ c = .DIG then (kapP p k I ℓ c : ℤ) else 0) +
            (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0)) ≤ e * dg c * (p : ℤ) ^ c ∧
      X1P p k I dg ℓ e c q ≤ e * (oW p dg (I.erase c) : ℤ) + e * dg c * (p : ℤ) ^ c ∧
      e * (oW p dg (I.erase c) : ℤ) + e * dg c * (p : ℤ) ^ c = e * (oW p dg I : ℤ) := by
  intro q hq
  have hcI : c ∈ I := hc ▸ I.max'_mem hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ I.le_max' t ht
  have hck : c < k := hI c hcI
  have hh : Rulers.h k I c = k - c := Houses.h_max hI hcI hcmax
  have hκ : kapP p k I ℓ c ≤ k - c := hh ▸ kapP_le_h (by omega)
  have hκ' : (kapP p k I ℓ c : ℤ) ≤ ((k - c : ℕ) : ℤ) := by exact_mod_cast hκ
  have hI' : ∀ t ∈ I.erase c, t < c := fun t ht =>
    lt_of_le_of_ne (hcmax t (mem_of_mem_erase ht)) (ne_of_mem_erase ht)
  have hτ : tauP p k I dg ℓ e c = ((k - c : ℕ) : ℤ) - e * (dg c : ℤ) * (p : ℤ) ^ c -
      (if typP p dg ℓ c = .OR ∨ typP p dg ℓ c = .DIG then (kapP p k I ℓ c : ℤ) else 0) := by
    unfold tauP; rw [hh]
  have hT4 : typP p dg ℓ c = .OR ∨ typP p dg ℓ c = .DIG ∨ typP p dg ℓ c = .AND ∨
      typP p dg ℓ c = .NEV := by cases typP p dg ℓ c <;> simp
  have hbs : (if typP p dg ℓ c = .OR ∨ typP p dg ℓ c = .DIG then (kapP p k I ℓ c : ℤ) else 0) +
      (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) ≤ kapP p k I ℓ c := by
    rcases hT4 with h | h | h | h <;> simp [h]
  have hd1 : dWalkP p k I dg ℓ e c q ≤
      -tauP p k I dg ℓ e c + (if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0) := by
    rw [dWalkP_eq e c hq]
    have ha0 : (0 : ℤ) ≤ if typP p dg ℓ c = .OR then (kapP p k I ℓ c : ℤ) else 0 := by
      split_ifs <;> simp
    have hb0 : (0 : ℤ) ≤ if typP p dg ℓ c = .AND then (kapP p k I ℓ c : ℤ) else 0 := by
      split_ifs <;> simp
    have h1 : (JHseqP p c (I.erase c) dg (ℓ % p ^ c) (2 ^ #(I.erase c) - 1 - q) : ℤ) ≤ 1 := by
      exact_mod_cast JHseqP_le_one _ _ _ _ _ _
    have p1 := mul_nonneg ha0 (Nat.cast_nonneg (α := ℤ) (JHseqP p c (I.erase c) dg (ℓ % p ^ c) q))
    have p2 := mul_le_mul_of_nonneg_left h1 hb0
    linarith
  have hoI : (oW p dg I : ℤ) = oW p dg (I.erase c) + dg c * (p : ℤ) ^ c := by
    rw [oW_erase_add hcI]; push_cast; ring
  have hΛ := (abs_le.1 (oddF_F1_Lambda hI' (hd_erase hd c)
    (Nat.mod_lt ℓ (pow_pos hp.out.pos c)) he q hq)).2
  refine ⟨hd1, by rw [hτ]; ring, by linarith, ?_, by rw [hoI]; ring⟩
  simp only [X1P, yhatP]
  rw [hτ] at hd1
  linarith

end ColouredSand.OddTwist
