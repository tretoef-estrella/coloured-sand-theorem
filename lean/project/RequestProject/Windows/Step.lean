module

public import RequestProject.Windows.Labels

/-!
# Part W of `C14_windows_and_theorem_D.md`: one move of the dance on window data

* `win α i a b = ∏_{d ∈ [a, b)} π_0(d)` (a window product, over `Finset.Ico`).
* `WinForm J α i h P p κ`: the data `(p, κ)` on `Fin r` are in the window form of (W) at level
  `h`, with coefficients `c_h = Deficit.c J h` and with the slot `s` labelled by `Dlab P s`.
* The coefficient identities `c_zero_of_le`, `c_succ_of_notMem`, `c_succ_insert`.
* `core_pay`, `core_coupling`: the twisted payment and the twisted coupling of window data are
  window data at level `h + 1` (the *Twist move* of the proof of (W)).
* `twist_step`, `split_step`: the twist move and the split move (relabelled by `(s, j) ↦ 2s + j`)
  preserve the window form (the induction step of the proof of (W)).
-/

@[expose] public section

namespace Windows

open Finset Deficit Payment Split Dance

/-- The window product `∏_{d ∈ [a, b)} π_0(d)` (*Part W*, (W), of
`C14_windows_and_theorem_D.md`). -/
def win (α : ℤ) (i a b : ℕ) : ℚ := ∏ d ∈ Ico a b, pi0 α i d

/-- Window data at level `h` (*Part W*, (W), of `C14_windows_and_theorem_D.md`): for every slot
`s` and floor `f`, `p_s(f) = ½ c_h(∅) ∏_{[2^h f + o(L_s), 2^h f + o(L_s) + 2^h)} π_0`, and for
`s' < s`, `κ_{s s'}(f) = ½ c_h(L_s ∖ L_{s'}) ∏_{[2^h f + o(L_s), 2^h f + o(L_{s'}) + 2^h)} π_0` if
`L_{s'} ⊆ L_s` and `0` otherwise, where `L_s = Dlab P s` and `c_h = Deficit.c J h`. -/
def WinForm (J : Finset ℕ) (α : ℤ) (i h : ℕ) (P : Finset ℕ) {r : ℕ} (p : Fin r → ℕ → ℚ)
    (κ : Fin r → Fin r → ℕ → ℚ) : Prop :=
  (∀ s f, p s f = 1 / 2 * c J h ∅ *
      win α i (2 ^ h * f + Rulers.oE (Dlab P s)) (2 ^ h * f + Rulers.oE (Dlab P s) + 2 ^ h)) ∧
  (∀ s s' f, s' < s → κ s s' f =
      if Dlab P s' ⊆ Dlab P s then 1 / 2 * c J h (Dlab P s \ Dlab P s') *
        win α i (2 ^ h * f + Rulers.oE (Dlab P s)) (2 ^ h * f + Rulers.oE (Dlab P s') + 2 ^ h)
      else 0)

/-- Two consecutive windows multiply to their union (*Part W*, proof of (W), of
`C14_windows_and_theorem_D.md`). -/
lemma win_mul {α : ℤ} {i a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    win α i a b * win α i b c = win α i a c := by
  unfold win
  exact prod_Ico_consecutive (fun d => pi0 α i d) hab hbc

/-- The two adjacent windows of level `h` at the floors `g + 1` and `g` multiply to the window of
level `h + 1` (*Part W*, proof of (W), of `C14_windows_and_theorem_D.md`). -/
lemma win_pair {α : ℤ} {i h g a b e : ℕ} (heb : e ≤ b + 2 ^ h) (hba : b ≤ a + 2 ^ h) :
    win α i (2 ^ h * (g + 1) + b) (2 ^ h * (g + 1) + a + 2 ^ h) *
        win α i (2 ^ h * g + e) (2 ^ h * g + b + 2 ^ h) =
      win α i (2 ^ h * g + e) (2 ^ h * g + a + 2 ^ (h + 1)) := by
  rw [mul_comm, show 2 ^ h * (g + 1) + b = 2 ^ h * g + b + 2 ^ h by ring,
    show 2 ^ h * (g + 1) + a + 2 ^ h = 2 ^ h * g + a + 2 ^ (h + 1) by ring]
  exact win_mul (by omega) (by rw [pow_succ]; omega)

/-- `c_h(Δ) = 0` if `Δ` has an element `≥ h` (*Part W*, proof of (W), of
`C14_windows_and_theorem_D.md`; from `Deficit.B1_rescaling` and (A1) of C10). -/
lemma c_zero_of_le (J : Finset ℕ) (h : ℕ) {Δ : Finset ℕ} {t : ℕ} (ht : t ∈ Δ) (hth : h ≤ t) :
    c J h Δ = 0 := by
  rw [B1_rescaling, A1_support J h Δ (fun hs => by
    have := mem_filter.1 (hs ht); omega)]
  simp

/-- `c_{h+1}(Δ) = −½ (c_h ⋆ c_h)(Δ)` if `h ∉ Δ` (*Part W*, proof of (W), of
`C14_windows_and_theorem_D.md`). -/
lemma c_succ_of_notMem (J : Finset ℕ) (h : ℕ) {Δ : Finset ℕ} (hΔ : h ∉ Δ) :
    c J (h + 1) Δ = -(1 / 2) * starMul (c J h) (c J h) Δ := by
  simp [c, hΔ]

/-- `c_{h+1}(Δ ∪ {h}) = −c_h(Δ)` if `h ∈ J` and every element of `Δ` is `< h` (*Part W*, proof of
(W), *Split move*, of `C14_windows_and_theorem_D.md`). -/
lemma c_succ_insert {J : Finset ℕ} {h : ℕ} (hJ : h ∈ J) {Δ : Finset ℕ} (hΔ : ∀ t ∈ Δ, t < h) :
    c J (h + 1) (insert h Δ) = - c J h Δ := by
  have hhΔ : h ∉ Δ := fun hh => lt_irrefl _ (hΔ h hh)
  have hstar : starMul (c J h) (c J h) (insert h Δ) = 0 := by
    apply sum_eq_zero
    intro Δ₁ _
    by_cases h1 : h ∈ Δ₁
    · rw [c_zero_of_le J h h1 le_rfl, zero_mul]
    · rw [c_zero_of_le J h (Δ := insert h Δ \ Δ₁) (t := h) (by simp [h1]) le_rfl, mul_zero]
  have hd : insert h Δ \ {h} = Δ := by
    ext t; by_cases hth : t = h <;> simp_all
  simp only [c, hstar, hJ, mem_insert_self, if_true, hd]
  ring

/-- `(c ⋆ c)(∅) = c(∅)^2` (*Part W*, proof of (W), of `C14_windows_and_theorem_D.md`). -/
lemma starMul_empty (f : Finset ℕ → ℚ) : starMul f f ∅ = f ∅ * f ∅ := by
  simp [starMul]

/-- The twisted payment of window data at the floors `g, g + 1` is a window payment of level
`h + 1`: `−p_s(g) p_s(g+1) = ½ c_{h+1}(∅) ∏_{[2^h g + o(L_s), 2^h g + o(L_s) + 2^{h+1})} π_0`
(*Part W*, proof of (W), *Twist move*, of `C14_windows_and_theorem_D.md`). -/
lemma core_pay {J : Finset ℕ} {α : ℤ} {i h : ℕ} {P : Finset ℕ} {r : ℕ} {p : Fin r → ℕ → ℚ}
    {κ : Fin r → Fin r → ℕ → ℚ} (hW : WinForm J α i h P p κ) (s : Fin r) (g : ℕ) :
    -(p s g * p s (g + 1)) = 1 / 2 * c J (h + 1) ∅ *
      win α i (2 ^ h * g + Rulers.oE (Dlab P s))
        (2 ^ h * g + Rulers.oE (Dlab P s) + 2 ^ (h + 1)) := by
  rw [hW.1, hW.1, c_succ_of_notMem J h (notMem_empty h), starMul_empty]
  have := win_pair (α := α) (i := i) (h := h) (g := g) (a := Rulers.oE (Dlab P s))
    (b := Rulers.oE (Dlab P s)) (e := Rulers.oE (Dlab P s)) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  rw [← this]; ring

/-- The twisted coupling of window data at the floors `g, g + 1` is a window coupling of level
`h + 1` (*Part W*, proof of (W), *Twist move*, of `C14_windows_and_theorem_D.md`): for `s' < u`,
`−[p_{s'}(g+1) κ_{us'}(g) + κ_{us'}(g+1) p_u(g) + Σ_{s'<v<u} κ_{vs'}(g+1) κ_{uv}(g)]` is
`½ c_{h+1}(L_u ∖ L_{s'}) ∏_{[2^h g + o(L_u), 2^h g + o(L_{s'}) + 2^{h+1})} π_0` if
`L_{s'} ⊆ L_u`, and `0` otherwise. -/
lemma core_coupling {J : Finset ℕ} {α : ℤ} {i h : ℕ} {P : Finset ℕ} {r : ℕ}
    {p : Fin r → ℕ → ℚ} {κ : Fin r → Fin r → ℕ → ℚ} (hP : ∀ t ∈ P, t < h)
    (hr : r = 2 ^ P.card) (hW : WinForm J α i h P p κ) (g : ℕ) (u s' : Fin r) (hlt : s' < u) :
    -(p s' (g + 1) * κ u s' g + κ u s' (g + 1) * p u g +
        ∑ v ∈ univ.filter (fun v => s' < v ∧ v < u), κ v s' (g + 1) * κ u v g) =
      if Dlab P s' ⊆ Dlab P u then 1 / 2 * c J (h + 1) (Dlab P u \ Dlab P s') *
        win α i (2 ^ h * g + Rulers.oE (Dlab P u))
          (2 ^ h * g + Rulers.oE (Dlab P s') + 2 ^ (h + 1))
      else 0 := by
  have hLlt : ∀ (v : Fin r) t, t ∈ Dlab P v → t < h := fun v t ht => Dlab_lt hP v t ht
  have hmono : ∀ v w : Fin r, Dlab P v ⊆ Dlab P w → v ≤ w := fun v w hvw =>
    Fin.le_def.2 (Dlab_mono P v w (hr ▸ v.isLt) (hr ▸ w.isLt) hvw)
  have hinj : ∀ v w : Fin r, Dlab P v = Dlab P w → v = w := fun v w e =>
    le_antisymm (hmono v w e.le) (hmono w v e.ge)
  have hO : ∀ v w : Fin r, Dlab P v ⊆ Dlab P w →
      Rulers.oE (Dlab P w) ≤ Rulers.oE (Dlab P v) + 2 ^ h := by
    intro v w hvw
    have h1 := Rulers.oE_sdiff hvw
    have h2 := Rulers.oE_lt (Dlab P w \ Dlab P v) h (fun t ht => hLlt w t (mem_sdiff.1 ht).1)
    omega
  by_cases hnest : Dlab P s' ⊆ Dlab P u
  · rw [if_pos hnest]
    set X := win α i (2 ^ h * g + Rulers.oE (Dlab P u))
      (2 ^ h * g + Rulers.oE (Dlab P s') + 2 ^ (h + 1)) with hX
    set T : Fin r → ℚ := fun v =>
      1 / 4 * X * (c J h (Dlab P v \ Dlab P s') * c J h (Dlab P u \ Dlab P v)) with hT
    have hterm : ∀ v, s' < v → v < u → κ v s' (g + 1) * κ u v g =
        if Dlab P s' ⊆ Dlab P v ∧ Dlab P v ⊆ Dlab P u then T v else 0 := by
      intro v h1 h2
      rw [hW.2 v s' (g + 1) h1, hW.2 u v g h2]
      by_cases ha : Dlab P s' ⊆ Dlab P v
      · by_cases hb : Dlab P v ⊆ Dlab P u
        · rw [if_pos ha, if_pos hb, if_pos ⟨ha, hb⟩]
          have := win_pair (α := α) (i := i) (h := h) (g := g) (a := Rulers.oE (Dlab P s'))
            (b := Rulers.oE (Dlab P v)) (e := Rulers.oE (Dlab P u)) (hO v u hb) (hO s' v ha)
          rw [hT, hX, ← this]; ring
        · rw [if_neg hb, if_neg (show ¬(Dlab P s' ⊆ Dlab P v ∧ Dlab P v ⊆ Dlab P u) from
            fun h => hb h.2)]; simp
      · rw [if_neg ha, if_neg (show ¬(Dlab P s' ⊆ Dlab P v ∧ Dlab P v ⊆ Dlab P u) from
            fun h => ha h.1)]; simp
    have h1 : p s' (g + 1) * κ u s' g = T s' := by
      rw [hW.1, hW.2 u s' g hlt, if_pos hnest]
      have := win_pair (α := α) (i := i) (h := h) (g := g) (a := Rulers.oE (Dlab P s'))
        (b := Rulers.oE (Dlab P s')) (e := Rulers.oE (Dlab P u)) (hO s' u hnest) (Nat.le_add_right _ _)
      rw [hT, hX, ← this]; simp only [sdiff_self, bot_eq_empty]; ring
    have h2 : κ u s' (g + 1) * p u g = T u := by
      rw [hW.1, hW.2 u s' (g + 1) hlt, if_pos hnest]
      have := win_pair (α := α) (i := i) (h := h) (g := g) (a := Rulers.oE (Dlab P s'))
        (b := Rulers.oE (Dlab P u)) (e := Rulers.oE (Dlab P u)) (Nat.le_add_right _ _) (hO s' u hnest)
      rw [hT, hX, ← this]; simp only [sdiff_self, bot_eq_empty]; ring
    set M := univ.filter (fun v : Fin r =>
      (s' < v ∧ v < u) ∧ (Dlab P s' ⊆ Dlab P v ∧ Dlab P v ⊆ Dlab P u)) with hM
    have hsum : ∑ v ∈ univ.filter (fun v => s' < v ∧ v < u), κ v s' (g + 1) * κ u v g =
        ∑ v ∈ M, T v := by
      rw [hM, ← filter_filter (fun v : Fin r => s' < v ∧ v < u)
        (fun v : Fin r => Dlab P s' ⊆ Dlab P v ∧ Dlab P v ⊆ Dlab P u)]
      conv_rhs => rw [sum_filter]
      apply sum_congr rfl
      intro v hv
      rw [mem_filter] at hv
      exact hterm v hv.2.1 hv.2.2
    have hTset : univ.filter (fun v : Fin r => Dlab P s' ⊆ Dlab P v ∧ Dlab P v ⊆ Dlab P u) =
        insert s' (insert u M) := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_insert, hM]
      constructor
      · rintro ⟨ha, hb⟩
        by_cases e1 : v = s'
        · left; exact e1
        by_cases e2 : v = u
        · right; left; exact e2
        right; right
        exact ⟨⟨lt_of_le_of_ne (hmono _ _ ha) (Ne.symm e1),
          lt_of_le_of_ne (hmono _ _ hb) e2⟩, ha, hb⟩
      · rintro (rfl | rfl | ⟨_, ha, hb⟩)
        · exact ⟨subset_refl _, hnest⟩
        · exact ⟨hnest, subset_refl _⟩
        · exact ⟨ha, hb⟩
    have hstar : ∑ v ∈ univ.filter (fun v : Fin r => Dlab P s' ⊆ Dlab P v ∧ Dlab P v ⊆ Dlab P u),
        c J h (Dlab P v \ Dlab P s') * c J h (Dlab P u \ Dlab P v) =
        starMul (c J h) (c J h) (Dlab P u \ Dlab P s') := by
      unfold starMul
      apply Finset.sum_bij (fun (v : Fin r) _ => Dlab P v \ Dlab P s')
      · intro v hv
        rw [mem_filter] at hv
        rw [mem_powerset]; exact sdiff_subset_sdiff hv.2.2 (subset_refl _)
      · intro v hv w hw e
        rw [mem_filter] at hv hw
        apply hinj
        rw [← sdiff_union_of_subset hv.2.1, e, sdiff_union_of_subset hw.2.1]
      · intro E hE
        rw [mem_powerset] at hE
        have hEP : Dlab P s' ∪ E ⊆ P :=
          union_subset (Dlab_subset _ _) (hE.trans (sdiff_subset.trans (Dlab_subset _ _)))
        obtain ⟨n, hn, hnE⟩ := Dlab_surj P _ hEP
        refine ⟨⟨n, hr ▸ hn⟩, ?_, ?_⟩
        · rw [mem_filter]
          refine ⟨mem_univ _, ?_, ?_⟩
          · show Dlab P s' ⊆ Dlab P n
            rw [hnE]; exact subset_union_left
          · show Dlab P n ⊆ Dlab P u
            rw [hnE]; exact union_subset hnest (hE.trans sdiff_subset)
        · show Dlab P n \ Dlab P s' = E
          rw [hnE]
          ext t
          have := @hE t
          simp only [mem_sdiff, mem_union] at this ⊢
          tauto
      · intro v hv
        rw [mem_filter] at hv
        congr 2
        ext t
        have h1 := @hv.2.1 t
        have h2 := @hv.2.2 t
        simp only [mem_sdiff]
        tauto
    have hΔh : h ∉ Dlab P u \ Dlab P s' := fun hh => lt_irrefl _ (hLlt u h (mem_sdiff.1 hh).1)
    have hs'M : s' ∉ insert u M := by
      rw [mem_insert, hM, mem_filter]
      rintro (e | ⟨_, ⟨e, _⟩, _⟩)
      · exact absurd e (ne_of_lt hlt)
      · exact absurd e (lt_irrefl _)
    have huM : u ∉ M := by
      rw [hM, mem_filter]
      rintro ⟨_, ⟨_, e⟩, _⟩
      exact absurd e (lt_irrefl _)
    have hTsum : ∑ v ∈ insert s' (insert u M), T v = T s' + (T u + ∑ v ∈ M, T v) := by
      rw [sum_insert hs'M, sum_insert huM]
    have hTsum' : ∑ v ∈ insert s' (insert u M), T v = 1 / 4 * X *
        starMul (c J h) (c J h) (Dlab P u \ Dlab P s') := by
      rw [← hstar, hTset, mul_sum]
    rw [h1, h2, hsum, c_succ_of_notMem J h hΔh]
    linear_combination hTsum - hTsum'
  · rw [if_neg hnest]
    have e1 : κ u s' g = 0 := by rw [hW.2 u s' g hlt, if_neg hnest]
    have e2 : κ u s' (g + 1) = 0 := by rw [hW.2 u s' (g + 1) hlt, if_neg hnest]
    have e3 : ∑ v ∈ univ.filter (fun v => s' < v ∧ v < u), κ v s' (g + 1) * κ u v g = 0 := by
      apply sum_eq_zero
      intro v hv
      rw [mem_filter] at hv
      rw [hW.2 v s' (g + 1) hv.2.1, hW.2 u v g hv.2.2]
      by_cases ha : Dlab P s' ⊆ Dlab P v
      · rw [if_pos ha, if_neg (fun hb => hnest (ha.trans hb)), mul_zero]
      · rw [if_neg ha, zero_mul]
    rw [e1, e2, e3]; ring

end Windows
