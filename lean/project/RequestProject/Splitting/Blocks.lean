module

public import RequestProject.Splitting.Conjugation

/-!
# The block decomposition of the Laplacian in the tensor basis

Part of the proof of **(A2) The splitting** of `CS2_theorem_A_splitting.md` (third to sixth
bullets of its proof).  We write `q = n + 2`.

A tensor-basis index `y : Fin d → Fin q` is split into
* the *type* `k : Fin d → Option (Fin n)`: `kᵢ = some w` iff `yᵢ = w + 2` (the position `i`
  carries `f_{w+1} ∈ W`), and `kᵢ = none` iff `yᵢ ∈ {0, 1}` (position `i` carries `e_0` or `−σ`,
  i.e. lies in `A`).  The set `T = {i | kᵢ ≠ none}` has `j = |T|` elements (`blockJ k`) and
  `T` together with the labels `w` is the index of a copy of `W^{⊗T} ≅ ℤ^{(q−2)^j}`;
* a set `S ⊆ Tᶜ` (positions carrying `−σ`), transported to `S ⊆ Fin (d − j)` by the increasing
  enumeration `blockEmb k : Fin (d − j) ↪ Tᶜ` (`blockM k = |Tᶜ| = d − j`).

`blockEquiv` is the resulting bijection `(Σ k, Finset (Fin (blockM k))) ≃ (Fin d → Fin q)`, and
`Nop_block` says that `Nop` (the Laplacian in the tensor basis) is block diagonal along it, the
block of `k` being `M_q(d − j, j) = q (j + H) + U` on `B_{d−j}`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Splitting

open ColouredSand.Strings

variable {n d : ℕ}

/-- The complement `Tᶜ = {i | kᵢ = none}` of the support of a type `k`. -/
def blockTc (k : Fin d → Option (Fin n)) : Finset (Fin d) := univ.filter fun i => k i = none

/-- `|Tᶜ|`. -/
def blockM (k : Fin d → Option (Fin n)) : ℕ := (blockTc k).card

/-- `j = |T|`, `T = {i | kᵢ ≠ none}`. -/
def blockJ (k : Fin d → Option (Fin n)) : ℕ := (univ.filter fun i => k i ≠ none).card

lemma blockM_eq (k : Fin d → Option (Fin n)) : blockM k = d - blockJ k := by
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin d)))
    (fun i => k i = none)
  simp only [card_univ, Fintype.card_fin] at this
  have h2 : blockJ k = (univ.filter fun i => ¬ k i = none).card := rfl
  rw [blockM, blockTc, h2]
  omega

lemma blockJ_le (k : Fin d → Option (Fin n)) : blockJ k ≤ d :=
  (card_le_univ _).trans_eq (Fintype.card_fin d)

/-- The increasing enumeration `Fin |Tᶜ| ↪ Fin d` of `Tᶜ`. -/
def blockEmb (k : Fin d → Option (Fin n)) : Fin (blockM k) ↪o Fin d :=
  (blockTc k).orderEmbOfFin rfl

lemma blockEmb_none (k : Fin d → Option (Fin n)) (a : Fin (blockM k)) : k (blockEmb k a) = none := by
  have := (blockTc k).orderEmbOfFin_mem rfl a
  exact (mem_filter.mp this).2

lemma exists_blockEmb (k : Fin d → Option (Fin n)) {i : Fin d} (hi : k i = none) :
    ∃ a, blockEmb k a = i := by
  have : i ∈ Set.range (blockEmb k) := by
    rw [blockEmb, Finset.range_orderEmbOfFin]
    simpa [blockTc] using hi
  exact this

/-- The tensor-basis index `y` of the pair `(k, S)`. -/
def blockPhi (k : Fin d → Option (Fin n)) (S : Finset (Fin (blockM k))) : Fin d → Fin (n + 2) :=
  fun i => match k i with
    | some w => w.succ.succ
    | none => if i ∈ S.map (blockEmb k).toEmbedding then 1 else 0

/-- Recover the type from an entry: `w + 2 ↦ some w`, `0, 1 ↦ none`. -/
def blockCls (a : Fin (n + 2)) : Option (Fin n) :=
  if h : 2 ≤ (a : ℕ) then some ⟨a - 2, by omega⟩ else none

lemma blockPhi_some {k : Fin d → Option (Fin n)} (S : Finset (Fin (blockM k))) {i : Fin d}
    {w : Fin n} (h : k i = some w) : blockPhi k S i = w.succ.succ := by
  simp [blockPhi, h]

lemma blockPhi_none {k : Fin d → Option (Fin n)} (S : Finset (Fin (blockM k))) {i : Fin d}
    (h : k i = none) :
    blockPhi k S i = if i ∈ S.map (blockEmb k).toEmbedding then 1 else 0 := by
  simp [blockPhi, h]

lemma blockPhi_emb {k : Fin d → Option (Fin n)} (S : Finset (Fin (blockM k))) (a : Fin (blockM k)) :
    blockPhi k S (blockEmb k a) = if a ∈ S then 1 else 0 := by
  rw [blockPhi_none S (blockEmb_none k a)]
  congr 1
  exact propext (Finset.mem_map' (blockEmb k).toEmbedding)

lemma not_mem_map_of_some {k : Fin d → Option (Fin n)} (S : Finset (Fin (blockM k))) {i : Fin d}
    {w : Fin n} (h : k i = some w) : i ∉ S.map (blockEmb k).toEmbedding := by
  intro hi
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hi
  simp [blockEmb_none] at h

lemma blockCls_succ_succ (w : Fin n) : blockCls w.succ.succ = some w := by
  simp [blockCls]

lemma blockCls_of_lt {a : Fin (n + 2)} (h : (a : ℕ) < 2) : blockCls a = none := by
  simp [blockCls]; omega

lemma blockCls_blockPhi (k : Fin d → Option (Fin n)) (S : Finset (Fin (blockM k))) (i : Fin d) :
    blockCls (blockPhi k S i) = k i := by
  rcases h : k i with _ | w
  · rw [blockPhi_none S h]
    split_ifs <;> exact blockCls_of_lt (by simp)
  · rw [blockPhi_some S h, blockCls_succ_succ]

lemma eq_of_blockCls_some {a : Fin (n + 2)} {w : Fin n} (h : blockCls a = some w) :
    a = w.succ.succ := by
  unfold blockCls at h
  split_ifs at h with h2
  simp only [Option.some.injEq] at h
  subst h
  ext
  simp
  omega

lemma lt_of_blockCls_none {a : Fin (n + 2)} (h : blockCls a = none) : (a : ℕ) < 2 := by
  unfold blockCls at h
  split_ifs at h with h2
  omega

lemma blockPhi_injective :
    Function.Injective (fun p : (Σ k : Fin d → Option (Fin n), Finset (Fin (blockM k))) =>
      blockPhi p.1 p.2) := by
  rintro ⟨k, S⟩ ⟨k', S'⟩ h
  simp only at h
  have hk : k = k' := funext fun i => by
    rw [← blockCls_blockPhi k S i, ← blockCls_blockPhi k' S' i, h]
  subst hk
  have hS : S = S' := by
    ext a
    have := congrFun h (blockEmb k a)
    rw [blockPhi_emb, blockPhi_emb] at this
    by_cases ha : a ∈ S <;> by_cases ha' : a ∈ S' <;> simp_all
  subst hS
  rfl

lemma blockPhi_surjective :
    Function.Surjective (fun p : (Σ k : Fin d → Option (Fin n), Finset (Fin (blockM k))) =>
      blockPhi p.1 p.2) := by
  intro y
  set k : Fin d → Option (Fin n) := fun i => blockCls (y i) with hk
  refine ⟨⟨k, univ.filter fun a => y (blockEmb k a) = 1⟩, funext fun i => ?_⟩
  simp only
  rcases h : k i with _ | w
  · obtain ⟨a, rfl⟩ := exists_blockEmb k h
    rw [blockPhi_emb]
    have hlt := lt_of_blockCls_none h
    simp only [mem_filter, mem_univ, true_and]
    split_ifs with h1
    · exact h1.symm
    · ext
      simp only [Fin.val_zero]
      have : (y (blockEmb k a) : ℕ) ≠ 1 := fun h' => h1 (Fin.ext h')
      omega
  · rw [blockPhi_some _ h]
    exact (eq_of_blockCls_some h).symm

/-- The bijection `(Σ k, Finset (Fin (blockM k))) ≃ (Fin d → Fin q)`, `(k, S) ↦ blockPhi k S`. -/
noncomputable def blockEquiv (n d : ℕ) :
    (Σ k : Fin d → Option (Fin n), Finset (Fin (blockM k))) ≃ (Fin d → Fin (n + 2)) :=
  Equiv.ofBijective _ ⟨blockPhi_injective, blockPhi_surjective⟩

lemma blockEquiv_apply (k : Fin d → Option (Fin n)) (S : Finset (Fin (blockM k))) :
    blockEquiv n d ⟨k, S⟩ = blockPhi k S := rfl

/-! ### `Nop` is block diagonal -/

lemma filter_blockPhi_ne_zero (k : Fin d → Option (Fin n)) (S : Finset (Fin (blockM k))) :
    (univ.filter fun i => blockPhi k S i ≠ 0) =
      (univ.filter fun i => k i ≠ none) ∪ S.map (blockEmb k).toEmbedding := by
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_union]
  rcases h : k i with _ | w
  · rw [blockPhi_none S h]
    split_ifs with hm <;> simp [hm]
  · rw [blockPhi_some S h]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_or, iff_true]
    exact Fin.succ_ne_zero _

lemma card_blockPhi_ne_zero (k : Fin d → Option (Fin n)) (S : Finset (Fin (blockM k))) :
    (univ.filter fun i => blockPhi k S i ≠ 0).card = blockJ k + S.card := by
  rw [filter_blockPhi_ne_zero, card_union_of_disjoint, card_map, blockJ]
  rw [Finset.disjoint_left]
  intro i hi hi'
  simp only [mem_filter, mem_univ, true_and] at hi
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hi
  exact not_mem_map_of_some S hw hi'

lemma filter_blockPhi_eq_one (k : Fin d → Option (Fin n)) (S : Finset (Fin (blockM k))) :
    (univ.filter fun i => blockPhi k S i = 1) = S.map (blockEmb k).toEmbedding := by
  ext i
  simp only [mem_filter, mem_univ, true_and]
  rcases h : k i with _ | w
  · rw [blockPhi_none S h]
    split_ifs with hm
    · simp [hm]
    · simp [hm]
  · rw [blockPhi_some S h]
    simp only [not_mem_map_of_some S h, iff_false]
    intro h1
    have := congrArg Fin.val h1
    simp at this

lemma update_blockPhi (k : Fin d → Option (Fin n)) (S : Finset (Fin (blockM k)))
    (a : Fin (blockM k)) :
    Function.update (blockPhi k S) (blockEmb k a) 0 = blockPhi k (S.erase a) := by
  funext i
  by_cases hi : i = blockEmb k a
  · subst hi
    rw [Function.update_self, blockPhi_emb]
    simp
  · rw [Function.update_of_ne hi]
    rcases h : k i with _ | w
    · rw [blockPhi_none S h, blockPhi_none _ h]
      congr 1
      apply propext
      simp only [mem_map, mem_erase, RelEmbedding.coe_toEmbedding]
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b, ⟨fun hba => hi (by rw [hba]), hb⟩, rfl⟩
      · rintro ⟨b, ⟨-, hb⟩, rfl⟩
        exact ⟨b, hb, rfl⟩
    · rw [blockPhi_some S h, blockPhi_some _ h]

/-- **`Nop` is block diagonal**: on the block of the type `k` (with `j = |T|` and
`m = |Tᶜ| = d − j`), it is `M_q(m, j) = q (j + H) + U` on `B_m`. -/
theorem Nop_block (f : (Fin d → Fin (n + 2)) → ℤ) (k : Fin d → Option (Fin n))
    (S : Finset (Fin (blockM k))) :
    Nop n d f (blockEquiv n d ⟨k, S⟩) =
      Mq (n + 2) (blockM k) (blockJ k) (fun S' => f (blockEquiv n d ⟨k, S'⟩)) S := by
  rw [Mq_apply, blockEquiv_apply, Nop_apply, card_blockPhi_ne_zero, filter_blockPhi_eq_one,
    Finset.sum_map]
  simp only [blockEquiv_apply, RelEmbedding.coe_toEmbedding]
  rw [Finset.sum_congr rfl fun a ha => by rw [update_blockPhi k S a]]
  push_cast
  ring

/-! ### Counting the blocks -/

/-- There are `C(d,j) (q−2)^j` types `k` with `|T| = j`. -/
theorem card_blockJ (j : ℕ) :
    Fintype.card {k : Fin d → Option (Fin n) // blockJ k = j} = d.choose j * n ^ j := by
  rw [Fintype.card_subtype]
  set supp : (Fin d → Option (Fin n)) → Finset (Fin d) := fun k => univ.filter fun i => k i ≠ none
  have hfib : ∀ T : Finset (Fin d),
      (univ.filter fun k : Fin d → Option (Fin n) => supp k = T).card = n ^ T.card := by
    intro T
    have : (univ.filter fun k : Fin d → Option (Fin n) => supp k = T) =
        Fintype.piFinset (fun i => if i ∈ T then univ.map ⟨some, Option.some_injective _⟩
          else {none}) := by
      ext k
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, supp]
      constructor
      · rintro rfl i
        by_cases h : k i = none
        · simp [h]
        · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp h
          simp [hw]
      · intro hk
        ext i
        have := hk i
        by_cases hi : i ∈ T
        · simp only [hi, if_true, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk] at this
          obtain ⟨w, hw⟩ := this
          simp [hi, ← hw]
        · simp only [hi, if_false, mem_singleton] at this
          simp [hi, this]
    rw [this, Fintype.card_piFinset]
    simp only [apply_ite Finset.card, card_map, card_univ, Fintype.card_fin, card_singleton]
    rw [Finset.prod_ite_mem, univ_inter, prod_const]
  rw [Finset.card_eq_sum_card_fiberwise (f := supp) (t := powersetCard j univ)]
  · rw [Finset.sum_congr rfl fun T hT => ?_]
    · rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
    · have hTc : T.card = j := (mem_powersetCard.mp hT).2
      rw [Finset.filter_filter, ← hTc, ← hfib T]
      congr 1
      ext k
      simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      rintro rfl
      rfl
  · intro k hk
    rw [mem_coe, mem_filter] at hk
    rw [mem_coe, mem_powersetCard]
    exact ⟨subset_univ _, hk.2⟩

end ColouredSand.Splitting
