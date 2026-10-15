module

public import RequestProject.NumberOfFactors.Inclusion

/-!
# An abstract diagonal-form criterion over `ℤ`

Auxiliary file for **(D1) Wilson's diagonal form** of `CS5_theorem_D_number_of_factors.md`.

Let `u : M → M'` be an injective map of finitely generated `ℤ`-modules, and let
`0 = F₀ ≤ F₁ ≤ … ≤ F_n = M` and `0 = F'₀ ≤ F'₁ ≤ …` be filtrations by saturated submodules with
`F_{j+1} = F_j + G_j(P_j)`, `F'_{j+1} = F'_j + G'_j(P_j)` and `u ∘ G_j = d_j · G'_j` with
`d_j ≠ 0`.  Then (`abstract_diag`) there are bases `b` of `M` and `b'` of `M'` and an injection
`φ` with `u (b a) = d_{lab a} • b' (φ a)`, where the label `j` occurs
`rank F_{j+1} − rank F_j` times.
-/

@[expose] public section

open Module Submodule

namespace ColouredSand.NumberOfFactors

variable {M M' : Type} [AddCommGroup M] [AddCommGroup M']

lemma isTorsionFree_quot (N : Submodule ℤ M) (hN : IsSat N) : Module.IsTorsionFree ℤ (M ⧸ N) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r x hx => ?_
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      exact (Submodule.Quotient.mk_eq_zero N).mpr (hN r y hr hx)

lemma sum_mem_iff_zero_of_basis {N : Submodule ℤ M} {Q : Submodule ℤ (M ⧸ N)} {κ : Type}
    [Fintype κ] (e : Basis κ ℤ Q) (w : κ → M) (hw : ∀ k, N.mkQ (w k) = (e k : M ⧸ N))
    (c : κ → ℤ) (hc : ∑ k, c k • w k ∈ N) : c = 0 := by
  have h1 : (∑ k, c k • e k : Q) = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, ← hw, ← map_zsmul, ← map_sum,
      Submodule.coe_zero]
    exact (Submodule.Quotient.mk_eq_zero N).mpr hc
  funext k
  exact Fintype.linearIndependent_iff.mp e.linearIndependent c h1 k

lemma linearIndependent_of_sum_mem {N : Submodule ℤ M} {κ : Type} [Fintype κ] (w : κ → M)
    (h : ∀ c : κ → ℤ, ∑ k, c k • w k ∈ N → c = 0) : LinearIndependent ℤ w := by
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have := h c (by rw [hc]; exact N.zero_mem)
  rw [this]; rfl

lemma disjoint_of_sum_mem {N : Submodule ℤ M} {κ : Type} [Fintype κ] (w : κ → M)
    (h : ∀ c : κ → ℤ, ∑ k, c k • w k ∈ N → c = 0) : Disjoint N (span ℤ (Set.range w)) := by
  rw [Submodule.disjoint_def]
  intro x hxN hxw
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hxw
  rw [h c hxN]
  simp

/-- The data of a filtration step: a linearly independent family spanning `F j` and `F' j`. -/
structure DiagData (u : M →ₗ[ℤ] M') (F : ℕ → Submodule ℤ M) (F' : ℕ → Submodule ℤ M')
    (d : ℕ → ℤ) (j : ℕ) where
  ι : Type
  fin : Fintype ι
  v : ι → M
  vv : ι → M'
  lab : ι → ℕ
  li : LinearIndependent ℤ v
  sp : span ℤ (Set.range v) = F j
  lli : LinearIndependent ℤ vv
  ssp : span ℤ (Set.range vv) = F' j
  lab_lt : ∀ a, lab a < j
  rel : ∀ a, u (v a) = d (lab a) • vv a
  card : ∀ i < j, Nat.card {a // lab a = i} = finrank ℤ (F (i + 1)) - finrank ℤ (F i)

/-- **Abstract diagonal form.** -/
theorem abstract_diag [Module.Finite ℤ M] [Module.Finite ℤ M']
    (u : M →ₗ[ℤ] M') (hu : Function.Injective u)
    (F : ℕ → Submodule ℤ M) (F' : ℕ → Submodule ℤ M')
    (P : ℕ → Type) [∀ j, AddCommGroup (P j)] [∀ j, Module ℤ (P j)]
    (G : ∀ j, P j →ₗ[ℤ] M) (G' : ∀ j, P j →ₗ[ℤ] M') (d : ℕ → ℤ) (n : ℕ)
    (hF0 : F 0 = ⊥) (hF'0 : F' 0 = ⊥)
    (hFs : ∀ j, F (j + 1) = F j ⊔ LinearMap.range (G j))
    (hF's : ∀ j, F' (j + 1) = F' j ⊔ LinearMap.range (G' j))
    (huG : ∀ j < n, ∀ x, u (G j x) = d j • G' j x)
    (hd : ∀ j < n, d j ≠ 0)
    (hsat : ∀ j ≤ n, IsSat (F j)) (hsat' : ∀ j ≤ n, IsSat (F' j))
    (htop : F n = ⊤) :
    ∃ (ι κ : Type) (_ : Fintype ι) (_ : Fintype κ) (b : Basis ι ℤ M) (b' : Basis κ ℤ M')
      (φ : ι ↪ κ) (lab : ι → ℕ),
      (∀ a, lab a < n) ∧ (∀ a, u (b a) = d (lab a) • b' (φ a)) ∧
      ∀ j < n, Fintype.card {a // lab a = j} = finrank ℤ (F (j + 1)) - finrank ℤ (F j) := by
  classical
  -- `u (F j) ⊆ F' j`
  have hmapF : ∀ j ≤ n, (F j).map u ≤ F' j := by
    intro j
    induction j with
    | zero => intro _; rw [hF0, Submodule.map_bot]; exact bot_le
    | succ j ih =>
      intro hj
      rw [hFs, hF's, Submodule.map_sup]
      refine sup_le_sup (ih (by omega)) ?_
      rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
      rw [huG j (by omega)]
      exact Submodule.smul_mem _ _ ⟨p, rfl⟩
  -- `N • F' j ⊆ u (F j)`
  have hN : ∀ j ≤ n, ∃ N : ℤ, N ≠ 0 ∧ ∀ y ∈ F' j, N • y ∈ (F j).map u := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨1, one_ne_zero, fun y hy => by
        rw [hF'0, Submodule.mem_bot] at hy; simp [hy]⟩
    | succ j ih =>
      intro hj
      obtain ⟨N, hN0, hN⟩ := ih (by omega)
      refine ⟨N * d j, mul_ne_zero hN0 (hd j (by omega)), fun y hy => ?_⟩
      rw [hF's] at hy
      obtain ⟨y1, hy1, y2, ⟨p, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hy
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · obtain ⟨f, hf, hfy⟩ := hN y1 hy1
        refine ⟨d j • f, ?_, ?_⟩
        · rw [hFs]; exact Submodule.mem_sup_left (Submodule.smul_mem _ _ hf)
        · rw [map_zsmul, hfy, smul_smul, mul_comm]
      · refine ⟨N • G j p, ?_, ?_⟩
        · rw [hFs]; exact Submodule.mem_sup_right (Submodule.smul_mem _ _ ⟨p, rfl⟩)
        · rw [map_zsmul, huG j (by omega), smul_smul]
  -- the inductive construction
  have step : ∀ j, j ≤ n → Nonempty (DiagData u F F' d j) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨{
        ι := Empty
        fin := inferInstance
        v := Empty.elim
        vv := Empty.elim
        lab := Empty.elim
        li := linearIndependent_empty_type
        sp := by rw [hF0, Set.range_eq_empty, Submodule.span_empty]
        lli := linearIndependent_empty_type
        ssp := by rw [hF'0, Set.range_eq_empty, Submodule.span_empty]
        lab_lt := fun a => a.elim
        rel := fun a => a.elim
        card := fun i hi => by omega }⟩
    | succ j ih =>
      intro hj
      obtain ⟨D⟩ := ih (by omega)
      letI := D.fin
      have hsj := hsat j (by omega)
      have hsj' := hsat' j (by omega)
      haveI := isTorsionFree_quot (F j) hsj
      let Q : Submodule ℤ (M ⧸ F j) := (F (j + 1)).map (F j).mkQ
      haveI : Module.Finite ℤ Q := Module.Finite.of_injective Q.subtype Q.subtype_injective
      haveI : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
      let κ := Module.Free.ChooseBasisIndex ℤ Q
      let e : Basis κ ℤ Q := Module.Free.chooseBasis ℤ Q
      have hQ : ∀ k, ∃ p : P j, (F j).mkQ (G j p) = (e k : M ⧸ F j) := by
        intro k
        obtain ⟨x, hx, hxe⟩ := (e k).2
        rw [hFs] at hx
        obtain ⟨x1, hx1, x2, ⟨p, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
        refine ⟨p, ?_⟩
        have h0 : (F j).mkQ x1 = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx1
        rw [← hxe, map_add, h0, zero_add]
      choose σ hσ using hQ
      let w : κ → M := fun k => G j (σ k)
      let w' : κ → M' := fun k => G' j (σ k)
      have hw0 : ∀ c : κ → ℤ, ∑ k, c k • w k ∈ F j → c = 0 :=
        sum_mem_iff_zero_of_basis e w hσ
      -- spanning modulo `F j`
      have hspan : ∀ x ∈ F (j + 1), ∃ c : κ → ℤ, x - ∑ k, c k • w k ∈ F j := by
        intro x hx
        let xq : Q := ⟨(F j).mkQ x, ⟨x, hx, rfl⟩⟩
        refine ⟨fun k => e.repr xq k, ?_⟩
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
        have h1 : (F j).mkQ x = ((∑ k, e.repr xq k • e k : Q) : M ⧸ F j) := by
          rw [e.sum_repr]
        rw [h1, Submodule.coe_sum, sub_eq_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, Submodule.coe_smul, hσ]
      -- the new family for `F' (j+1)`
      have hw'0 : ∀ c : κ → ℤ, ∑ k, c k • w' k ∈ F' j → c = 0 := by
        intro c hc
        obtain ⟨N, hN0, hNF⟩ := hN j (by omega)
        obtain ⟨f, hf, hfu⟩ := hNF _ hc
        apply hw0
        apply hsj N _ hN0
        have : d j • f = N • ∑ k, c k • w k := by
          apply hu
          rw [map_zsmul, map_zsmul, hfu, map_sum, smul_comm]
          congr 1
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_zsmul, huG j (by omega), smul_comm]
        rw [← this]
        exact Submodule.smul_mem _ _ hf
      have hspan' : ∀ p : P j, ∃ c : κ → ℤ, G' j p - ∑ k, c k • w' k ∈ F' j := by
        intro p
        obtain ⟨c, hc⟩ := hspan (G j p) (by
          rw [hFs]; exact Submodule.mem_sup_right ⟨p, rfl⟩)
        refine ⟨c, hsj' (d j) _ (hd j (by omega)) ?_⟩
        have := hmapF j (by omega) ⟨_, hc, rfl⟩
        convert this using 1
        rw [map_sub, map_sum, huG j (by omega), smul_sub, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, huG j (by omega), smul_comm]
      have hli : LinearIndependent ℤ (Sum.elim D.v w) := by
        refine D.li.sum_type (linearIndependent_of_sum_mem w hw0) ?_
        rw [D.sp]; exact disjoint_of_sum_mem w hw0
      have hsp : span ℤ (Set.range (Sum.elim D.v w)) = F (j + 1) := by
        rw [Set.Sum.elim_range, Submodule.span_union, D.sp]
        apply le_antisymm
        · refine sup_le (fun x hx => ?_) ?_
          · rw [hFs]; exact Submodule.mem_sup_left hx
          · rw [Submodule.span_le]
            rintro _ ⟨k, rfl⟩
            rw [hFs]; exact Submodule.mem_sup_right ⟨σ k, rfl⟩
        · intro x hx
          obtain ⟨c, hc⟩ := hspan x hx
          have : x = (x - ∑ k, c k • w k) + ∑ k, c k • w k := by abel
          rw [this]
          refine Submodule.add_mem_sup hc ?_
          exact Submodule.sum_mem _ fun k _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      refine ⟨{
        ι := D.ι ⊕ κ
        fin := inferInstance
        v := Sum.elim D.v w
        vv := Sum.elim D.vv w'
        lab := Sum.elim D.lab (fun _ => j)
        li := hli
        sp := hsp
        lli := ?_
        ssp := ?_
        lab_lt := ?_
        rel := ?_
        card := ?_ }⟩
      · refine D.lli.sum_type (linearIndependent_of_sum_mem w' hw'0) ?_
        rw [D.ssp]; exact disjoint_of_sum_mem w' hw'0
      · rw [Set.Sum.elim_range, Submodule.span_union, D.ssp, hF's]
        apply le_antisymm
        · refine sup_le_sup le_rfl ?_
          rw [Submodule.span_le]
          rintro _ ⟨k, rfl⟩
          exact ⟨σ k, rfl⟩
        · refine sup_le le_sup_left ?_
          rintro _ ⟨p, rfl⟩
          obtain ⟨c, hc⟩ := hspan' p
          have : G' j p = (G' j p - ∑ k, c k • w' k) + ∑ k, c k • w' k := by abel
          rw [this]
          refine Submodule.add_mem_sup hc ?_
          exact Submodule.sum_mem _ fun k _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      · rintro (a | k)
        · exact (D.lab_lt a).trans (Nat.lt_succ_self j)
        · exact Nat.lt_succ_self j
      · rintro (a | k)
        · exact D.rel a
        · exact huG j (by omega) (σ k)
      · intro i hi
        rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
        simp only [Sum.elim_inl, Sum.elim_inr]
        have hcardι : Fintype.card D.ι = finrank ℤ (F j) := by
          rw [← D.sp, finrank_span_eq_card D.li]
        have hcard2 : Fintype.card (D.ι ⊕ κ) = finrank ℤ (F (j + 1)) := by
          rw [← hsp, finrank_span_eq_card hli]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hij | rfl
        · have h0 : Nat.card {k : κ // j = i} = 0 := by
            rw [Nat.card_eq_zero]; left; exact ⟨fun k => by have := k.2; omega⟩
          rw [h0, add_zero]
          exact D.card i hij
        · have h0 : Nat.card {a : D.ι // D.lab a = i} = 0 := by
            rw [Nat.card_eq_zero]; left
            exact ⟨fun a => by have := D.lab_lt a.1; have := a.2; omega⟩
          have h1 : Nat.card {k : κ // i = i} = Fintype.card κ := by
            rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl), Nat.card_eq_fintype_card]
          rw [h0, h1, zero_add, ← hcard2, ← hcardι, Fintype.card_sum]
          omega
  obtain ⟨D⟩ := step n le_rfl
  letI := D.fin
  -- the basis of `M`
  let b : Basis D.ι ℤ M := Basis.mk D.li (by rw [D.sp, htop])
  -- extend `v'` to a basis of `M'`
  haveI := isTorsionFree_quot (F' n) (hsat' n le_rfl)
  haveI : Module.Free ℤ (M' ⧸ F' n) := Module.free_of_finite_type_torsion_free'
  let κ := Module.Free.ChooseBasisIndex ℤ (M' ⧸ F' n)
  let e : Basis κ ℤ (M' ⧸ F' n) := Module.Free.chooseBasis ℤ (M' ⧸ F' n)
  have hlift : ∀ k, ∃ y : M', (F' n).mkQ y = e k := fun k => (F' n).mkQ_surjective (e k)
  choose l hl using hlift
  have hl0 : ∀ c : κ → ℤ, ∑ k, c k • l k ∈ F' n → c = 0 := by
    intro c hc
    have h1 : ∑ k, c k • e k = 0 := by
      simp only [← hl, ← map_zsmul, ← map_sum]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hc
    funext k
    exact Fintype.linearIndependent_iff.mp e.linearIndependent c h1 k
  have hli : LinearIndependent ℤ (Sum.elim D.vv l) := by
    refine D.lli.sum_type (linearIndependent_of_sum_mem l hl0) ?_
    rw [D.ssp]; exact disjoint_of_sum_mem l hl0
  have hsp : ⊤ ≤ span ℤ (Set.range (Sum.elim D.vv l)) := by
    intro y _
    rw [Set.Sum.elim_range, Submodule.span_union, D.ssp]
    have h1 : (F' n).mkQ y = ∑ k, e.repr ((F' n).mkQ y) k • e k := (e.sum_repr _).symm
    have h2 : y - ∑ k, e.repr ((F' n).mkQ y) k • l k ∈ F' n := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum, sub_eq_zero]
      conv_lhs => rw [h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, hl]
    have : y = (y - ∑ k, e.repr ((F' n).mkQ y) k • l k) + ∑ k, e.repr ((F' n).mkQ y) k • l k := by
      abel
    rw [this]
    refine Submodule.add_mem_sup h2 ?_
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b' : Basis (D.ι ⊕ κ) ℤ M' := Basis.mk hli hsp
  refine ⟨D.ι, D.ι ⊕ κ, D.fin, inferInstance, b, b', Function.Embedding.inl, D.lab, D.lab_lt,
    fun a => ?_, fun j hj => ?_⟩
  · simp only [b, b', Basis.mk_apply, Function.Embedding.inl_apply, Sum.elim_inl]
    exact D.rel a
  · rw [← Nat.card_eq_fintype_card]; exact D.card j hj

end ColouredSand.NumberOfFactors
