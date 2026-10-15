module

public import RequestProject.Split.Decomp

/-!
# The split data in block form (*Proof* of Theorem B of `C12_split_move.md`)

* `sum_lex_gt`: a sum over the slots `(u, X) > (s', k)` of `Lex (S × Fin 2)`.
* The values of `pSp`, `κSp` on the pairs of the Setting.
* `split2`: `M^{S×{A,C}} ≃ A ⊕ C = M^S × M^S`.
* `proj2_comp_G`: in that decomposition, `G'' = G[fl, F, p'', κ'']` is the block operator
  `(a, c) ↦ (F a + E0 a, −D1 a + F c + E1 c)`, where `E0 = DS fl p' κ'` (the twisted data of C11 at
  the floors `(2f, 2f+1)`), `E1` is the same at the floors `(2f+1, 2f+2)`, and
  `D1 = DS (2 fl + 1) p κ`.
* `DS_comp_shift`: `D1 ∘ D2 = −2 E1`.
-/

@[expose] public section

namespace Split

open DirectSum Finset Payment
open scoped Pointwise

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]
variable {S : Type*} [LinearOrder S]

/-- The data shifted by one floor, `p_s(n + 1)` (used to express the `C`-part of the split data
through the twisted data of C11 at the floors `(2f+1, 2f+2)`; *Proof* of Theorem B of
`C12_split_move.md`). -/
def shiftP (p : S → ℕ → A) (s : S) (n : ℕ) : A := p s (n + 1)

/-- The couplings shifted by one floor, `κ_{us}(n + 1)` (*Proof* of Theorem B of
`C12_split_move.md`). -/
def shiftK (κ : S → S → ℕ → A) (u s : S) (n : ℕ) : A := κ u s (n + 1)

/-! ### Values of the split data -/

omit [LinearOrder S] in
/-- `p''_{(s,A)} = p'_s` (*Setting*, "The split data", of `C12_split_move.md`). -/
@[simp] lemma pSp_A (p : S → ℕ → A) (s : S) (f : ℕ) : pSp p (toLex (s, 0)) f = pT p s f := by
  simp [pSp, pT]

omit [LinearOrder S] in
/-- `p''_{(s,C)}` is `p'_s` at the floors `(2f+1, 2f+2)` (*Setting*, "The split data", of
`C12_split_move.md`). -/
@[simp] lemma pSp_C (p : S → ℕ → A) (s : S) (f : ℕ) :
    pSp p (toLex (s, 1)) f = pT (shiftP p) s f := by
  simp only [pSp, ofLex_toLex, one_ne_zero, if_false, pT, shiftP]

variable [Fintype S]

/-- `κ''_{(u,A),(s',A)} = κ'_{us'}` for `u > s'`, and `0` otherwise (*Setting*, "The split data",
of `C12_split_move.md`). -/
@[simp] lemma κSp_AA (p : S → ℕ → A) (κ : S → S → ℕ → A) (u s' : S) (f : ℕ) :
    κSp p κ (toLex (u, 0)) (toLex (s', 0)) f = if s' < u then κT p κ u s' f else 0 := by
  simp [κSp, κT]

/-- `κ''_{(u,C),(s',C)}` is `κ'_{us'}` at the floors `(2f+1, 2f+2)` for `u > s'`, and `0` otherwise
(*Setting*, "The split data", of `C12_split_move.md`). -/
@[simp] lemma κSp_CC (p : S → ℕ → A) (κ : S → S → ℕ → A) (u s' : S) (f : ℕ) :
    κSp p κ (toLex (u, 1)) (toLex (s', 1)) f =
      if s' < u then κT (shiftP p) (shiftK κ) u s' f else 0 := by
  simp only [κSp, ofLex_toLex, one_ne_zero, false_and, if_false, true_and, if_true, κT, shiftP,
    shiftK]

/-- `κ''_{(u,C),(s',A)}`: `−p_{s'}(2f+1)` for `u = s'`, `−κ_{us'}(2f+1)` for `u > s'`, and `0`
otherwise (*Setting*, "The split data", of `C12_split_move.md`). -/
@[simp] lemma κSp_CA (p : S → ℕ → A) (κ : S → S → ℕ → A) (u s' : S) (f : ℕ) :
    κSp p κ (toLex (u, 1)) (toLex (s', 0)) f =
      if u = s' then -p s' (2 * f + 1) else if s' < u then -κ u s' (2 * f + 1) else 0 := by
  simp [κSp]

/-- There is no coupling from a slot `C` to a slot `A`: `κ''_{(u,A),(s',C)} = 0` (*Setting*, "The
split data", of `C12_split_move.md`). -/
@[simp] lemma κSp_AC (p : S → ℕ → A) (κ : S → S → ℕ → A) (u s' : S) (f : ℕ) :
    κSp p κ (toLex (u, 0)) (toLex (s', 1)) f = 0 := by
  simp [κSp]

/-- `κ''_{(u,A),(s',A)} = κ'_{us'}` for `u > s'` (*Setting* of `C12_split_move.md`). -/
lemma κSp_AA_of_lt (p : S → ℕ → A) (κ : S → S → ℕ → A) {u s' : S} (h : s' < u) (f : ℕ) :
    κSp p κ (toLex (u, 0)) (toLex (s', 0)) f = κT p κ u s' f := by
  simp [h]

/-- `κ''_{(u,C),(s',C)}` for `u > s'` (*Setting* of `C12_split_move.md`). -/
lemma κSp_CC_of_lt (p : S → ℕ → A) (κ : S → S → ℕ → A) {u s' : S} (h : s' < u) (f : ℕ) :
    κSp p κ (toLex (u, 1)) (toLex (s', 1)) f = κT (shiftP p) (shiftK κ) u s' f := by
  simp [h]

/-- `κ''_{(u,C),(s',A)} = −κ_{us'}(2f+1)` for `u > s'` (*Setting* of `C12_split_move.md`). -/
lemma κSp_CA_of_lt (p : S → ℕ → A) (κ : S → S → ℕ → A) {u s' : S} (h : s' < u) (f : ℕ) :
    κSp p κ (toLex (u, 1)) (toLex (s', 0)) f = -κ u s' (2 * f + 1) := by
  simp [h, h.ne']

/-- `κ''_{(s',C),(s',A)} = −p_{s'}(2f+1)` (*Setting* of `C12_split_move.md`). -/
lemma κSp_CA_self (p : S → ℕ → A) (κ : S → S → ℕ → A) (s' : S) (f : ℕ) :
    κSp p κ (toLex (s', 1)) (toLex (s', 0)) f = -p s' (2 * f + 1) := by
  simp

/-- A sum over the slots `q > (s', k)` of `Lex (S × Fin 2)`: the slot `(s', C)` if `k = A`, plus
both slots `(u, A)`, `(u, C)` for every `u > s'` (*Proof* of Theorem B of `C12_split_move.md`). -/
lemma sum_lex_gt {M : Type*} [AddCommMonoid M] (s' : S) (k : Fin 2) (g : Lex (S × Fin 2) → M) :
    ∑ q ∈ Finset.univ.filter (toLex (s', k) < ·), g q =
      (if k = 0 then g (toLex (s', 1)) else 0) +
        ∑ u ∈ Finset.univ.filter (s' < ·), (g (toLex (u, 0)) + g (toLex (u, 1))) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp toLex, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Prod.Lex.toLex_lt_toLex]
  have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  rcases hk with rfl | rfl
  · have : ∀ u, ((if s' < u ∨ s' = u ∧ (0 : Fin 2) < 0 then g (toLex (u, 0)) else 0) +
        (if s' < u ∨ s' = u ∧ (0 : Fin 2) < 1 then g (toLex (u, 1)) else 0)) =
        (if s' = u then g (toLex (s', 1)) else 0) +
          (if s' < u then g (toLex (u, 0)) + g (toLex (u, 1)) else 0) := by
      intro u
      rcases lt_trichotomy s' u with h | rfl | h
      · simp [h, h.ne]
      · simp
      · simp [h.not_gt, h.ne']
    rw [Finset.sum_congr rfl (fun u _ => this u), Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  · have : ∀ u, ((if s' < u ∨ s' = u ∧ (1 : Fin 2) < 0 then g (toLex (u, 0)) else 0) +
        (if s' < u ∨ s' = u ∧ (1 : Fin 2) < 1 then g (toLex (u, 1)) else 0)) =
        (if s' < u then g (toLex (u, 0)) + g (toLex (u, 1)) else 0) := by
      intro u
      by_cases h : s' < u <;> simp [h]
    rw [Finset.sum_congr rfl (fun u _ => this u)]
    simp

/-! ### The decomposition `M^{S×{A,C}} = A ⊕ C` -/

variable (A N S) in
/-- `M^{S×{A,C}} → M^S × M^S`, `x ι_{(s,A),i} ↦ (x ι_{s,i}, 0)`, `x ι_{(s,C),i} ↦ (0, x ι_{s,i})`
(*Proof* of Theorem B of `C12_split_move.md`). -/
def proj2 : Sys N (Lex (S × Fin 2)) →ₗ[A] (Sys N S × Sys N S) :=
  DirectSum.toModule A (Lex (S × Fin 2) × ι) _ (fun q =>
    (if (ofLex q.1).2 = 0 then LinearMap.inl A (Sys N S) (Sys N S)
      else LinearMap.inr A (Sys N S) (Sys N S)) ∘ₗ slotLof A N S (ofLex q.1).1 q.2)

variable (A N S) in
/-- The copy of `M^S` with label `X ∈ {A, C}` inside `M^{S×{A,C}}`, `x ι_{s,i} ↦ x ι_{(s,X),i}`
(*Proof* of Theorem B of `C12_split_move.md`). -/
def emb2 (k : Fin 2) : Sys N S →ₗ[A] Sys N (Lex (S × Fin 2)) :=
  DirectSum.toModule A (S × ι) _ (fun q => slotLof A N (Lex (S × Fin 2)) (toLex (q.1, k)) q.2)

omit [Fintype S] in
/-- `proj2 (x ι_{(s,A),i}) = (x ι_{s,i}, 0)` (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma proj2_slotLof0 (s : S) (i : ι) (x : N i) :
    proj2 A N S (slotLof A N (Lex (S × Fin 2)) (toLex (s, 0)) i x) = (slotLof A N S s i x, 0) := by
  simp [proj2, slotLof_eq, DirectSum.toModule_lof]

omit [Fintype S] in
/-- `proj2 (x ι_{(s,C),i}) = (0, x ι_{s,i})` (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma proj2_slotLof1 (s : S) (i : ι) (x : N i) :
    proj2 A N S (slotLof A N (Lex (S × Fin 2)) (toLex (s, 1)) i x) = (0, slotLof A N S s i x) := by
  simp [proj2, slotLof_eq, DirectSum.toModule_lof]

omit [Fintype S] in
/-- `emb2 X (x ι_{s,i}) = x ι_{(s,X),i}` (*Proof* of Theorem B of `C12_split_move.md`). -/
@[simp] lemma emb2_slotLof (k : Fin 2) (s : S) (i : ι) (x : N i) :
    emb2 A N S k (slotLof A N S s i x) = slotLof A N (Lex (S × Fin 2)) (toLex (s, k)) i x := by
  simp [emb2, slotLof_eq, DirectSum.toModule_lof]

omit [Fintype S] in
/-- `proj2 ∘ emb2 A = inl` and `proj2 ∘ emb2 C = inr` (*Proof* of Theorem B of
`C12_split_move.md`). -/
lemma proj2_comp_emb2 :
    proj2 A N S ∘ₗ emb2 A N S 0 = LinearMap.inl A _ _ ∧
      proj2 A N S ∘ₗ emb2 A N S 1 = LinearMap.inr A _ _ := by
  constructor <;>
  · apply DirectSum.linearMap_ext; rintro ⟨s, i⟩; refine LinearMap.ext fun x => ?_
    change proj2 A N S (emb2 A N S _ (slotLof A N S s i x)) = _
    simp only [emb2_slotLof, proj2_slotLof0, proj2_slotLof1]
    rfl

omit [Fintype S] in
/-- `M^{S×{A,C}} = A ⊕ C ≃ M^S × M^S` (*Proof* of Theorem B of `C12_split_move.md`). -/
def split2 : Sys N (Lex (S × Fin 2)) ≃ₗ[A] (Sys N S × Sys N S) :=
  LinearEquiv.ofLinear (proj2 A N S) ((emb2 A N S 0).coprod (emb2 A N S 1))
    (by
      obtain ⟨h0, h1⟩ := proj2_comp_emb2 (A := A) (N := N) (S := S)
      apply LinearMap.prod_ext
      · rw [LinearMap.comp_assoc, LinearMap.coprod_inl, h0]; rfl
      · rw [LinearMap.comp_assoc, LinearMap.coprod_inr, h1]; rfl)
    (by
      apply DirectSum.linearMap_ext; rintro ⟨q, i⟩; refine LinearMap.ext fun x => ?_
      obtain ⟨⟨s, k⟩, rfl⟩ := toLex.surjective q
      change (emb2 A N S 0).coprod (emb2 A N S 1)
        (proj2 A N S (slotLof A N (Lex (S × Fin 2)) (toLex (s, k)) i x)) =
          slotLof A N (Lex (S × Fin 2)) (toLex (s, k)) i x
      have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
      rcases hk with rfl | rfl <;> simp)

omit [Fintype S] in
/-- The underlying map of `split2` is `proj2` (*Proof* of Theorem B of `C12_split_move.md`). -/
lemma split2_toLinearMap :
    (split2 (A := A) (N := N) (S := S) : Sys N (Lex (S × Fin 2)) →ₗ[A] _) = proj2 A N S := rfl

omit [Fintype S] in
/-- `proj2 ((m) ι_{(s,X)}) = ` `m ι_s` in the `X`-th factor (*Proof* of Theorem B of
`C12_split_move.md`). -/
lemma proj2_slotEmb (s : S) (m : ⨁ i, N i) :
    proj2 A N S (slotEmb A N (Lex (S × Fin 2)) (toLex (s, 0)) m) = (slotEmb A N S s m, 0) ∧
      proj2 A N S (slotEmb A N (Lex (S × Fin 2)) (toLex (s, 1)) m) = (0, slotEmb A N S s m) := by
  have h0 : (proj2 A N S ∘ₗ slotEmb A N (Lex (S × Fin 2)) (toLex (s, 0)) : (⨁ i, N i) →ₗ[A] _) =
      LinearMap.inl A _ _ ∘ₗ slotEmb A N S s := by
    apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
    simp
  have h1 : (proj2 A N S ∘ₗ slotEmb A N (Lex (S × Fin 2)) (toLex (s, 1)) : (⨁ i, N i) →ₗ[A] _) =
      LinearMap.inr A _ _ ∘ₗ slotEmb A N S s := by
    apply DirectSum.linearMap_ext; intro i; refine LinearMap.ext fun x => ?_
    simp
  exact ⟨LinearMap.congr_fun h0 m, LinearMap.congr_fun h1 m⟩

/-- `D1 = DS (2 fl + 1) p κ` is `DS (2 fl) (shift p) (shift κ)` (*Proof* of Theorem B of
`C12_split_move.md`). -/
lemma DS_shift1 (fl : ι → ℕ) (p : S → ℕ → A) (κ : S → S → ℕ → A) :
    DS (N := N) (fun i => 2 * fl i + 1) p κ = DS (fun i => 2 * fl i) (shiftP p) (shiftK κ) := rfl

/-- `D2 = DS (2 fl + 2) p κ` is `DS (2 fl + 1) (shift p) (shift κ)` (*Proof* of Theorem B of
`C12_split_move.md`). -/
lemma DS_shift2 (fl : ι → ℕ) (p : S → ℕ → A) (κ : S → S → ℕ → A) :
    DS (N := N) (fun i => 2 * fl i + 2) p κ =
      DS (fun i => 2 * fl i + 1) (shiftP p) (shiftK κ) := rfl

/-- The coefficient identity at the floors `(2f+1, 2f+2)`:
`D1 ∘ D2 = −2 · E1` with `E1 = DS fl (p' at (2f+1, 2f+2)) (κ' at (2f+1, 2f+2))` (*Proof* of
Theorem B of `C12_split_move.md`; C11's identity applied to the shifted data). -/
lemma DS_comp_shift (fl : ι → ℕ) (p : S → ℕ → A) (κ : S → S → ℕ → A) :
    DS (fun i => 2 * fl i + 1) p κ ∘ₗ DS (fun i => 2 * fl i + 2) p κ =
      -(2 : A) • DS (N := N) fl (pT (shiftP p)) (κT (shiftP p) (shiftK κ)) := by
  rw [DS_shift1, DS_shift2, DS_comp]

/-- The *Proof* of Theorem B of `C12_split_move.md`: in the decomposition `A ⊕ C`,
`G'' = G[fl, F, p'', κ'']` is the block operator `(a, c) ↦ (F a + E0 a, −D1 a + F c + E1 c)`. -/
lemma proj2_comp_G (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A)
    (κ : S → S → ℕ → A) :
    proj2 A N S ∘ₗ G fl F (pSp p) (κSp p κ) =
      blkH (FS F) (DS (fun i => 2 * fl i + 1) p κ) (DS fl (pT p) (κT p κ))
        (DS fl (pT (shiftP p)) (κT (shiftP p) (shiftK κ))) ∘ₗ proj2 A N S := by
  apply DirectSum.linearMap_ext; rintro ⟨q, i⟩; refine LinearMap.ext fun x => ?_
  obtain ⟨⟨s', k⟩, rfl⟩ := toLex.surjective q
  change proj2 A N S (G fl F (pSp p) (κSp p κ)
      (slotLof A N (Lex (S × Fin 2)) (toLex (s', k)) i x)) =
    blkH (FS F) (DS (fun i => 2 * fl i + 1) p κ) (DS fl (pT p) (κT p κ))
        (DS fl (pT (shiftP p)) (κT (shiftP p) (shiftK κ)))
      (proj2 A N S (slotLof A N (Lex (S × Fin 2)) (toLex (s', k)) i x))
  rw [G_eq, LinearMap.add_apply, FS_slotLof, DS_slotLof, sum_lex_gt]
  have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  rcases hk with rfl | rfl
  · simp only [if_true, map_add, map_smul, map_sum, (proj2_slotEmb _ _).1, proj2_slotLof0,
      proj2_slotLof1, pSp_A, κSp_CA_self, blkH_apply, FS_slotLof, DS_slotLof, map_zero,
      Finset.sum_filter]
    simp +contextual only [κSp_AA_of_lt, κSp_CA_of_lt]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sum, smul_zero, zero_add]
      congr 2
      refine Finset.sum_congr rfl fun u _ => ?_
      split_ifs <;> simp
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sum, smul_zero, zero_add,
        add_zero, neg_add, ← Finset.sum_neg_distrib, neg_smul, mul_neg]
      congr 1
      refine Finset.sum_congr rfl fun u _ => ?_
      split_ifs <;> simp
  · simp only [one_ne_zero, if_false, zero_add, map_add, map_smul, map_sum,
      (proj2_slotEmb _ _).2, proj2_slotLof1, pSp_C, κSp_AC, mul_zero, zero_smul,
      blkH_apply, FS_slotLof, DS_slotLof, map_zero, Finset.sum_filter]
    simp +contextual only [κSp_CC_of_lt]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sum, smul_zero, zero_add]
      refine Finset.sum_eq_zero fun u _ => ?_
      split_ifs <;> simp
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sum, zero_add, neg_zero]
      congr 2
      refine Finset.sum_congr rfl fun u _ => ?_
      split_ifs <;> simp

end Split
