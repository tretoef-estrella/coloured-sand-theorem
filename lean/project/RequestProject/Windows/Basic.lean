module

public import RequestProject.Dance.Proposition
public import RequestProject.Deficit.ClosedForm
public import RequestProject.Deficit.Rescaling

/-!
# The *Setting* of `C14_windows_and_theorem_D.md`

## Encoding (namespace `Windows`)

We reuse, unchanged: from `C10_deficit_law.md` (`RequestProject/Deficit/`) `Deficit.starMul`,
`Deficit.a`, `Deficit.c`, `Deficit.pi0`, `Deficit.Mc`, `Deficit.B1_rescaling`,
`Deficit.C2_integrality_valuation`; from `C3_rulers_gold_clocks.md` (`RequestProject/Rulers/`)
`Rulers.oE`, `Rulers.delta`, `Rulers.v2`; from `C11_payment_systems_twist.md` `Payment.pT`,
`Payment.κT`; from `C12_split_move.md` `Split.pSp`, `Split.κSp`; and from `C13_the_dance.md`
`Dance.mCount`, `Dance.dance`, `Dance.danceAux`, `Dance.splitIso`, `Dance.relabP`, `Dance.relabK`,
`Dance.Mfin`, `Dance.pσ`, `Dance.κσ`, `Dance.sigma`, `Dance.proposition_4_3`.

* **Digit lists** are `ds : List Bool`, lowest digit first; `ds[t]?` is the `t`-th entry (as an
  `Option Bool`), `k = ds.length`, `m = Dance.mCount ds`.
* **The family** `I(ds) := {t < length ds : ds[t] = true}` is `Ids ds : Finset ℕ`, the filter of
  `Finset.range ds.length` by `ds[t]? = some true` (`mem_Ids : t ∈ Ids ds ↔ ds[t]? = some true`).
* **The rank** `rank(t) := #{u ∈ I : u < t}` is `rank I t`, for any `I : Finset ℕ`.
* **The dancers of a slot** `D(ds, s) := {t ∈ I(ds) : Nat.testBit s (m − 1 − rank t) = true}` is
  `Dset ds s` (for a natural number `s`; a slot `s : Fin _` is read through its value `s.val`).
  The same formula for an arbitrary finite set `P` (with `m` replaced by `P.card`) is `Dlab P s`;
  `Dset ds s = Dlab (Ids ds) s` (`Dset_eq_Dlab`), since `(Ids ds).card = mCount ds`.
* **Prefixes**: the digit list of the first `h` moves is `ds.take h`.
* **Scalars**: `π_0(d) = Deficit.pi0 α i d` with `α : ℤ` (for `α : ℕ` we use `(α : ℤ)`),
  `c_h = Deficit.c (Ids ds) h`, `o = Rulers.oE`; windows are `Finset.Ico`.
* **Ring homomorphisms** act on data pointwise: `φ ∘ p` is `fun s f => φ (p s f)`, `φ ∘ κ` is
  `fun s u f => φ (κ s u f)`, and on matrices by `Matrix.map`.
-/

@[expose] public section

namespace Windows

open Finset

/-- The family `I(ds) := {t < length ds : ds[t] = true}` as a `Finset ℕ` (*Setting*, "The family of
a digit list", of `C14_windows_and_theorem_D.md`). -/
def Ids (ds : List Bool) : Finset ℕ :=
  (Finset.range ds.length).filter (fun t => ds[t]? = some true)

/-- `rank(t) := #{u ∈ I : u < t}` (*Setting*, "The family of a digit list", of
`C14_windows_and_theorem_D.md`). -/
def rank (I : Finset ℕ) (t : ℕ) : ℕ := (I.filter (· < t)).card

/-- The labels `{t ∈ P : Nat.testBit s (|P| − 1 − rank t) = true}` for an arbitrary finite set `P`
(the formula of `D(ds, s)` with `I(ds)` replaced by `P`; *Setting*, "The dancers of a slot", of
`C14_windows_and_theorem_D.md`). -/
def Dlab (P : Finset ℕ) (s : ℕ) : Finset ℕ :=
  P.filter (fun t => Nat.testBit s (P.card - 1 - rank P t) = true)

/-- The dancers of a final slot,
`D(ds, s) := {t ∈ I(ds) : Nat.testBit s (mCount ds − 1 − rank t) = true}` (*Setting*, "The dancers
of a slot", of `C14_windows_and_theorem_D.md`). -/
def Dset (ds : List Bool) (s : ℕ) : Finset ℕ :=
  (Ids ds).filter (fun t => Nat.testBit s (Dance.mCount ds - 1 - rank (Ids ds) t) = true)

/-- Membership in `I(ds)` (*Setting* of `C14_windows_and_theorem_D.md`). -/
lemma mem_Ids {ds : List Bool} {t : ℕ} : t ∈ Ids ds ↔ ds[t]? = some true := by
  unfold Ids
  rw [mem_filter, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)

/-- Every `t ∈ I(ds)` satisfies `t < length ds` (*Setting* of `C14_windows_and_theorem_D.md`). -/
lemma lt_of_mem_Ids {ds : List Bool} {t : ℕ} (h : t ∈ Ids ds) : t < ds.length := by
  unfold Ids at h
  exact mem_range.1 (mem_filter.1 h).1

/-- `I(d :: l) = (if d then {0} else ∅) ∪ (I(l) + 1)` (*Setting* of
`C14_windows_and_theorem_D.md`). -/
lemma Ids_cons (d : Bool) (l : List Bool) :
    Ids (d :: l) = (if d = true then {0} else ∅) ∪ (Ids l).image (· + 1) := by
  ext t
  rw [mem_union, mem_image, mem_Ids]
  rcases t with _ | t
  · cases d <;> simp
  · simp only [List.getElem?_cons_succ, mem_Ids]
    constructor
    · intro h; right; exact ⟨t, h, rfl⟩
    · rintro (h | ⟨u, hu, hut⟩)
      · split_ifs at h <;> simp at h
      · have : u = t := by omega
        subst this; exact hu

/-- `|I(ds)| = m(ds)` (*Setting* of `C14_windows_and_theorem_D.md`). -/
lemma card_Ids (ds : List Bool) : (Ids ds).card = Dance.mCount ds := by
  induction ds with
  | nil => simp [Ids, Dance.mCount]
  | cons d l ih =>
    rw [Ids_cons]
    have hdisj : Disjoint (if d = true then ({0} : Finset ℕ) else ∅) ((Ids l).image (· + 1)) := by
      split_ifs
      · simp
      · simp
    rw [card_union_of_disjoint hdisj, card_image_of_injective _ (add_left_injective 1), ih]
    cases d <;> simp [Dance.mCount, add_comm]

/-- `D(ds, s) = Dlab (I(ds)) s` (*Setting*, "The dancers of a slot", of
`C14_windows_and_theorem_D.md`). -/
lemma Dset_eq_Dlab (ds : List Bool) (s : ℕ) : Dset ds s = Dlab (Ids ds) s := by
  simp only [Dset, Dlab, card_Ids]

/-- `I(ds.take h) = {t ∈ I(ds) : t < h}` (*Setting*, "Prefixes", of
`C14_windows_and_theorem_D.md`). -/
lemma Ids_take (ds : List Bool) (h : ℕ) : Ids (ds.take h) = (Ids ds).filter (· < h) := by
  ext t
  rw [mem_filter, mem_Ids, mem_Ids, List.getElem?_take]
  split_ifs with ht <;> simp [ht]

end Windows
