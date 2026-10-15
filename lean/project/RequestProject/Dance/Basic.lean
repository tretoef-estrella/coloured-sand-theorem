module

public import RequestProject.Split.TheoremB

/-!
# The *Setting* of `C13_the_dance.md`

## Encoding (namespace `Dance`)

Everything is over an arbitrary commutative ring `A` (`A : Type u`, `[CommRing A]`).  We reuse,
unchanged, from `C11_payment_systems_twist.md` (`RequestProject/Payment/`): `Payment.Sys`,
`Payment.slotLof`, `Payment.slotEmb`, `Payment.G` (halved data), `Payment.NΦ`, `Payment.flΦ`,
`Payment.FΦ`, `Payment.pT`, `Payment.κT`, `Payment.theorem_A`; and from `C12_split_move.md`
(`RequestProject/Split/`): `Split.NΨ`, `Split.flΨ`, `Split.FΨ`, `Split.pSp`, `Split.κSp`,
`Split.theorem_B`.

* **Counts.** `nLen ds = ds.length` (`n(ds)`); `mCount ds` is the number of `true` entries
  (`m(ds)`), defined by recursion on `ds` (`mCount_eq_count : mCount ds = ds.count true`).
* **The tower `T(ds)`** is defined by recursion on `ds : List Bool`, all its modules being `A`:
  - index type `Idx ds`: `Idx [] = Unit`, `Idx (false :: rest) = Idx rest × Fin 2`,
    `Idx (true :: rest) = Idx rest × Fin 4` (with `DecidableEq` and `Fintype` instances, also by
    recursion);
  - floor `fl ds : Idx ds → ℕ`: `fl [] = 0`, `fl (false :: rest) = flΦ (fl rest)`,
    `fl (true :: rest) = flΨ (fl rest)`;
  - operator `F A ds : (⨁ _ : Idx ds, A) →ₗ[A] (⨁ _ : Idx ds, A)`: `F A [] = 0`,
    `F A (false :: rest) = FΦ (F A rest)`, `F A (true :: rest) = FΨ (F A rest)`.
  The module of a system on `T(ds)` with slot type `S` is `Payment.Sys (fun _ : Idx ds => A) S`,
  abbreviated `SysT A ds S`.
* **Relabelling slots.** For an order isomorphism `e : S ≃o S'` and data `(p', κ')` on `S'`,
  `relabP e p' = fun s => p' (e s)` and `relabK e κ' = fun s u => κ' (e s) (e u)`.
  The split slots `Lex (Fin r × Fin 2)` are relabelled to `Fin (r * 2)` by the order isomorphism
  `splitIso r : Lex (Fin r × Fin 2) ≃o Fin (r * 2)`, `(s, j) ↦ 2 s + j`, whose underlying map is
  `finProdFinEquiv ∘ ofLex` (`splitIso_apply`, `splitIso_val`); `relab` of the file is
  `relabP`/`relabK` along `(splitIso r).symm`.
* **The dance data.** `danceAux ds r p κ` is defined by exactly the recursion of the Setting, with
  values data on `Fin (slots ds r)`, where `slots [] r = r`, `slots (false :: rest) r =
  slots rest r`, `slots (true :: rest) r = slots rest (r * 2)` (so no cast is needed inside the
  recursion).  Since `slots ds r = r * 2 ^ mCount ds` (`slots_eq`), `dance ds r p κ`, data on
  `Fin (r * 2 ^ mCount ds)`, is `danceAux ds r p κ` composed with `Fin.cast (slots_eq ds r)`
  (the order isomorphism `Fin.castOrderIso`) in every slot argument.  The recursion equations of
  the Setting hold for `dance` up to this cast (`dance_nil`, `dance_false`, `dance_true`).
  Data `(p, κ)` on `S` are a pair in `Data A S = (S → ℕ → A) × (S → S → ℕ → A)`.
* **The final matrix.** `Mfin p κ : Matrix (Fin R) (Fin R) A`,
  `Mfin p κ s s' = if s = s' then 2 * p s 0 else if s' < s then 2 * κ s s' 0 else 0`.
* **The operator `σ`.** `pσ α i : Fin 1 → ℕ → A`, `pσ α i _ f = 2 ^ (α - 1) * (i + f)`;
  `κσ = 0`; `sigma A ds α i = G (fl ds) (F A ds) (pσ α i) κσ` on `SysT A ds (Fin 1)`.
* **The clocks.** `Clocks A ds r h : ModuleCat A` (a bundled `A`-module, so that the recursion
  also produces the module structure): `Clocks [] r h = PUnit`, `Clocks (false :: rest) r h =
  (SysT rest (Fin r) ⧸ 2^h • ⊤) × Clocks rest r (h + 1)`, `Clocks (true :: rest) r h =
  (SysT rest (Fin r) ⧸ 2^h • ⊤) × (SysT rest (Fin r) ⧸ 2^h • ⊤) × Clocks rest (r * 2) (h + 1)`.
* Scalars: `c · G` is `c • G` and `c · ⊤` is the pointwise scalar multiple `c • ⊤` of a submodule.
-/

@[expose] public section

universe u

namespace Dance

open DirectSum Payment Split
open scoped Pointwise

/-! ### Counts -/

/-- `n(ds) := length ds` (*Setting* of `C13_the_dance.md`). -/
abbrev nLen (ds : List Bool) : ℕ := ds.length

/-- `m(ds) :=` the number of entries of `ds` equal to `true`, by recursion on `ds`
(*Setting* of `C13_the_dance.md`). -/
def mCount : List Bool → ℕ
  | [] => 0
  | false :: rest => mCount rest
  | true :: rest => mCount rest + 1

/-- `m(ds)` is the number of entries equal to `true` (*Setting* of `C13_the_dance.md`). -/
lemma mCount_eq_count (ds : List Bool) : mCount ds = ds.count true := by
  induction ds with
  | nil => rfl
  | cons d rest ih => cases d <;> simp [mCount, ih]

/-! ### The tower `T(ds)` -/

/-- The index type `Idx(ds)` of the tower `T(ds)` (*Setting*, "The tower", of
`C13_the_dance.md`). -/
def Idx : List Bool → Type
  | [] => Unit
  | false :: rest => Idx rest × Fin 2
  | true :: rest => Idx rest × Fin 4

/-- Decidable equality on `Idx(ds)` (*Setting*, "The tower", of `C13_the_dance.md`). -/
instance instDecEqIdx : (ds : List Bool) → DecidableEq (Idx ds)
  | [] => inferInstanceAs (DecidableEq Unit)
  | false :: rest =>
    letI := instDecEqIdx rest
    inferInstanceAs (DecidableEq (Idx rest × Fin 2))
  | true :: rest =>
    letI := instDecEqIdx rest
    inferInstanceAs (DecidableEq (Idx rest × Fin 4))

/-- `Idx(ds)` is finite (*Setting*, "The tower", of `C13_the_dance.md`). -/
instance instFintypeIdx : (ds : List Bool) → Fintype (Idx ds)
  | [] => inferInstanceAs (Fintype Unit)
  | false :: rest =>
    letI := instFintypeIdx rest
    inferInstanceAs (Fintype (Idx rest × Fin 2))
  | true :: rest =>
    letI := instFintypeIdx rest
    inferInstanceAs (Fintype (Idx rest × Fin 4))

/-- The floor `fl_ds` of the tower `T(ds)`: `0` on `T([])`, `flΦ` for a digit `false`, `flΨ` for
a digit `true` (*Setting*, "The tower", of `C13_the_dance.md`). -/
def fl : (ds : List Bool) → Idx ds → ℕ
  | [] => fun _ => 0
  | false :: rest => flΦ (fl rest)
  | true :: rest => flΨ (fl rest)

variable (A : Type u) [CommRing A]

/-- The operator `F_ds` of the tower `T(ds)` (all modules equal to `A`): `0` on `T([])`, `FΦ` for a
digit `false`, `FΨ` for a digit `true` (*Setting*, "The tower", of `C13_the_dance.md`). -/
noncomputable def F : (ds : List Bool) → (⨁ _ : Idx ds, A) →ₗ[A] (⨁ _ : Idx ds, A)
  | [] => 0
  | false :: rest => FΦ (N := fun _ : Idx rest => A) (F rest)
  | true :: rest => FΨ (N := fun _ : Idx rest => A) (F rest)

/-- The module `Sys(T(ds), S)` of a system on the tower with slot type `S` (*Setting*, "The tower",
of `C13_the_dance.md`). -/
abbrev SysT (ds : List Bool) (S : Type) := Sys (fun _ : Idx ds => A) S

variable {A}

/-! ### Relabelling slots -/

/-- Relabelled payments `p := p' ∘ e` (*Part R*, (R1), and *Setting*, "Relabelling the split
slots", of `C13_the_dance.md`). -/
def relabP {S S' : Type*} [LE S] [LE S'] (e : S ≃o S') (p' : S' → ℕ → A) : S → ℕ → A :=
  fun s => p' (e s)

/-- Relabelled couplings `κ s u := κ' (e s) (e u)` (*Part R*, (R1), and *Setting*, "Relabelling
the split slots", of `C13_the_dance.md`). -/
def relabK {S S' : Type*} [LE S] [LE S'] (e : S ≃o S') (κ' : S' → S' → ℕ → A) :
    S → S → ℕ → A :=
  fun s u => κ' (e s) (e u)

/-- `(s, j) ↦ 2 s + j` is strictly monotone for the lexicographic order (*Setting*, "Relabelling
the split slots", of `C13_the_dance.md`). -/
lemma strictMono_finProdFinEquiv_ofLex (r : ℕ) :
    StrictMono (fun q : Lex (Fin r × Fin 2) => finProdFinEquiv (ofLex q)) := by
  intro a b hab
  induction a using Lex.rec with | _ a => ?_
  induction b using Lex.rec with | _ b => ?_
  rcases a with ⟨s, j⟩
  rcases b with ⟨t, k⟩
  rw [Prod.Lex.toLex_lt_toLex] at hab
  simp only [Fin.lt_def, finProdFinEquiv_apply_val, ofLex_toLex]
  dsimp only at hab
  rcases hab with h | ⟨rfl, h⟩
  · rw [Fin.lt_def] at h; omega
  · rw [Fin.lt_def] at h; omega

/-- The order isomorphism `Lex (Fin r × Fin 2) ≃o Fin (r * 2)`, `(s, j) ↦ 2 s + j`
(`finProdFinEquiv` read through `ofLex`) (*Setting*, "Relabelling the split slots", of
`C13_the_dance.md`). -/
noncomputable def splitIso (r : ℕ) : Lex (Fin r × Fin 2) ≃o Fin (r * 2) :=
  StrictMono.orderIsoOfSurjective _ (strictMono_finProdFinEquiv_ofLex r)
    (fun y => ⟨toLex (finProdFinEquiv.symm y), by simp only [ofLex_toLex, Equiv.apply_symm_apply]⟩)

/-- `splitIso r q = finProdFinEquiv (ofLex q)` (*Setting*, "Relabelling the split slots", of
`C13_the_dance.md`). -/
lemma splitIso_apply (r : ℕ) (q : Lex (Fin r × Fin 2)) :
    splitIso r q = finProdFinEquiv (ofLex q) := rfl

/-- `splitIso r (s, j)` has value `2 s + j` (*Setting*, "Relabelling the split slots", of
`C13_the_dance.md`). -/
lemma splitIso_val (r : ℕ) (s : Fin r) (j : Fin 2) :
    (splitIso r (toLex (s, j)) : ℕ) = 2 * s + j := by
  simp [splitIso_apply, finProdFinEquiv_apply_val]; ring

/-! ### The dance data -/

/-- Halved data on the slot type `S` (*Setting* of `C13_the_dance.md`). -/
abbrev Data (A : Type u) (S : Type) := (S → ℕ → A) × (S → S → ℕ → A)

/-- The slot count of the dance, by recursion: `slots [] r = r`, `slots (false :: rest) r =
slots rest r`, `slots (true :: rest) r = slots rest (r * 2)` (*Setting*, "The dance data", of
`C13_the_dance.md`). -/
def slots : List Bool → ℕ → ℕ
  | [], r => r
  | false :: rest, r => slots rest r
  | true :: rest, r => slots rest (r * 2)

/-- The slot count is `r * 2^{m(ds)}` (*Setting*, "The dance data", of `C13_the_dance.md`). -/
lemma slots_eq (ds : List Bool) (r : ℕ) : slots ds r = r * 2 ^ mCount ds := by
  induction ds generalizing r with
  | nil => simp [slots, mCount]
  | cons d rest ih =>
    cases d
    · simp only [slots, mCount, ih]
    · simp only [slots, mCount, ih]; ring

/-- The dance data, by the recursion of the Setting, on `Fin (slots ds r)`:
`danceAux [] r p κ = (p, κ)`, `danceAux (false :: rest) r p κ = danceAux rest r (pT p) (κT p κ)`,
`danceAux (true :: rest) r p κ = danceAux rest (r * 2) (relab (pSp p)) (relab (κSp p κ))`
(*Setting*, "The dance data", of `C13_the_dance.md`). -/
noncomputable def danceAux : (ds : List Bool) → (r : ℕ) → (Fin r → ℕ → A) →
    (Fin r → Fin r → ℕ → A) → Data A (Fin (slots ds r))
  | [], _, p, κ => (p, κ)
  | false :: rest, r, p, κ => danceAux rest r (pT p) (κT p κ)
  | true :: rest, r, p, κ =>
    danceAux rest (r * 2) (relabP (splitIso r).symm (pSp p))
      (relabK (splitIso r).symm (κSp p κ))

/-- The dance data `dance ds r p κ`, on slots `Fin (r * 2^{m(ds)})`: the data `danceAux ds r p κ`
read through the cast `Fin (r * 2^{m(ds)}) ≃o Fin (slots ds r)` (*Setting*, "The dance data", of
`C13_the_dance.md`). -/
noncomputable def dance (ds : List Bool) (r : ℕ) (p : Fin r → ℕ → A) (κ : Fin r → Fin r → ℕ → A) :
    Data A (Fin (r * 2 ^ mCount ds)) :=
  (relabP (Fin.castOrderIso (slots_eq ds r).symm) (danceAux ds r p κ).1,
    relabK (Fin.castOrderIso (slots_eq ds r).symm) (danceAux ds r p κ).2)

/-- `dance [] r p κ = (p, κ)` up to the cast `Fin (r * 2^0) ≃o Fin r` (*Setting*, "The dance
data", of `C13_the_dance.md`). -/
lemma dance_nil (r : ℕ) (p : Fin r → ℕ → A) (κ : Fin r → Fin r → ℕ → A) :
    dance [] r p κ = (relabP (Fin.castOrderIso (slots_eq [] r).symm) p,
      relabK (Fin.castOrderIso (slots_eq [] r).symm) κ) := rfl

/-- `dance (false :: rest) r p κ = dance rest r (pT p) (κT p κ)` (*Setting*, "The dance data", of
`C13_the_dance.md`). -/
lemma dance_false (rest : List Bool) (r : ℕ) (p : Fin r → ℕ → A) (κ : Fin r → Fin r → ℕ → A) :
    dance (false :: rest) r p κ = dance rest r (pT p) (κT p κ) := rfl

/-- `dance (true :: rest) r p κ = dance rest (r * 2) (relab (pSp p)) (relab (κSp p κ))`, up to the
cast `Fin (r * 2^{m(rest)+1}) ≃o Fin (r * 2 * 2^{m(rest)})` (*Setting*, "The dance data", of
`C13_the_dance.md`). -/
lemma dance_true (rest : List Bool) (r : ℕ) (p : Fin r → ℕ → A) (κ : Fin r → Fin r → ℕ → A)
    (h : r * 2 ^ mCount (true :: rest) = r * 2 * 2 ^ mCount rest) :
    dance (true :: rest) r p κ =
      (relabP (Fin.castOrderIso h) (dance rest (r * 2) (relabP (splitIso r).symm (pSp p))
          (relabK (splitIso r).symm (κSp p κ))).1,
        relabK (Fin.castOrderIso h) (dance rest (r * 2) (relabP (splitIso r).symm (pSp p))
          (relabK (splitIso r).symm (κSp p κ))).2) := rfl

/-! ### The final matrix and the operator `σ` -/

/-- The final matrix `Mfin(p, κ)`: `2 p_s(0)` on the diagonal, `2 κ_{s s'}(0)` for `s' < s`, `0`
for `s < s'` (*Setting*, "The final matrix", of `C13_the_dance.md`). -/
def Mfin {R : ℕ} (p : Fin R → ℕ → A) (κ : Fin R → Fin R → ℕ → A) : Matrix (Fin R) (Fin R) A :=
  fun s s' => if s = s' then 2 * p s 0 else if s' < s then 2 * κ s s' 0 else 0

/-- The halved payments of `σ^{(α)}_i`: `pσ(f) := 2^{α−1} (i + f)` (*Setting*, "The operator
`σ`", of `C13_the_dance.md`). -/
def pσ (α i : ℕ) : Fin 1 → ℕ → A := fun _ f => 2 ^ (α - 1) * ((i : A) + (f : A))

/-- The halved couplings of `σ^{(α)}_i`: `κσ := 0` (*Setting*, "The operator `σ`", of
`C13_the_dance.md`). -/
def κσ : Fin 1 → Fin 1 → ℕ → A := 0

variable (A) in
/-- The operator `σ^{(α)}_i := G[fl_ds, F_ds, pσ, κσ]` on `Sys(T(ds), Fin 1)` (*Setting*, "The
operator `σ`", of `C13_the_dance.md`). -/
noncomputable def sigma (ds : List Bool) (α i : ℕ) : SysT A ds (Fin 1) →ₗ[A] SysT A ds (Fin 1) :=
  G (fl ds) (F A ds) (pσ α i) κσ

/-! ### The clocks -/

variable (A) in
/-- The clocks `Clocks(ds, r, h)`, a bundled `A`-module defined by recursion:
`Clocks([], r, h) = PUnit`,
`Clocks(false :: rest, r, h) = (Sys(T(rest), Fin r) ⧸ 2^h·⊤) × Clocks(rest, r, h + 1)`,
`Clocks(true :: rest, r, h) = (Sys(T(rest), Fin r) ⧸ 2^h·⊤) × (Sys(T(rest), Fin r) ⧸ 2^h·⊤)
  × Clocks(rest, r · 2, h + 1)` (*Part D*, (D1), of `C13_the_dance.md`). -/
noncomputable def Clocks : List Bool → ℕ → ℕ → ModuleCat.{u} A
  | [], _, _ => ModuleCat.of A PUnit
  | false :: rest, r, h => ModuleCat.of A
      ((SysT A rest (Fin r) ⧸ (2 : A) ^ h • (⊤ : Submodule A (SysT A rest (Fin r)))) ×
        Clocks rest r (h + 1))
  | true :: rest, r, h => ModuleCat.of A
      ((SysT A rest (Fin r) ⧸ (2 : A) ^ h • (⊤ : Submodule A (SysT A rest (Fin r)))) ×
        (SysT A rest (Fin r) ⧸ (2 : A) ^ h • (⊤ : Submodule A (SysT A rest (Fin r)))) ×
        Clocks rest (r * 2) (h + 1))

end Dance
