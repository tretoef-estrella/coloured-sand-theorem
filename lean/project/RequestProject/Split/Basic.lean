module

public import RequestProject.Payment.TheoremA

/-!
# The *Setting* of `C12_split_move.md`

## Encoding (namespace `Split`)

Everything is over an arbitrary commutative ring `A`, with the graded families, slot types,
`Payment.Sys`, `Payment.slotLof`, `Payment.slotEmb`, the payment system `Payment.G` (halved data)
and the twisted data `Payment.pT`, `Payment.κT` of `C11_payment_systems_twist.md`, reused
unchanged.  `M = ⨁ i, N i`.

* **The tensor model `V ⊗ Φ`**: index type `ι × Fin 2 × Fin 2`; the element `x` at `(i, e, e')`
  (`x : N i`) is the paper's `b_e ⊗ b_{e'} x`.  Modules `NVΦ N (i, e, e') = N i`; floor
  `flVΦ fl (i, e, e') = 2 fl(i) + e + e'` (`e, e'` read as `0, 1` through `Fin.val`); operator
  `FVΦ F`, defined on generators with `DirectSum.toModule`, as the sum of the `F_V` part
  (`x` at `(i,1,e')` if `e = 0`, `0` if `e = 1`) and the `F^Φ` part (`x` at `(i,e,1)` if `e' = 0`,
  `2 • (F x placed at (·, e, 0))` if `e' = 1`).  `embVΦ A N e e' : M → M_{VΦ}` places `x` at `i` as
  `x` at `(i, e, e')`.
* **The split model `Ψ`**: index type `ι × Fin 4` with `0 = A`, `1 = B`, `2 = C`, `3 = Dd`;
  modules `NΨ N (i, j) = N i`; floor `flΨ fl (i, j) = 2 fl(i) + ![0, 1, 1, 2] j`; operator `FΨ F`,
  defined on generators with `DirectSum.toModule`:
  `A x ↦ B x + 2 • C x`, `B x ↦ 2 • A(F x)`, `C x ↦ Dd x`, `Dd x ↦ 2 • C(F x)`, where
  `J(F x) = embΨ A N J (F x)` places `F x ∈ M` with label `J`.
* **The change of basis** `θ = theta : M_{VΦ} →ₗ[A] M_Ψ`, defined on generators with
  `DirectSum.toModule`: `b_0b_0 x ↦ A x`, `b_0b_1 x ↦ B x + C x`, `b_1b_0 x ↦ C x`,
  `b_1b_1 x ↦ Dd x`; its inverse `thetaInv` (`A x ↦ b_0b_0 x`, `B x ↦ b_0b_1 x − b_1b_0 x`,
  `C x ↦ b_1b_0 x`, `Dd x ↦ b_1b_1 x`).  The slotwise map `θ_S = thetaS` sends `x ι_{s,(i,e,e')}`
  to `(θ (x at (i,e,e'))) ι_s`.
* **The split data**: the split slot type is `Lex (S × Fin 2)` (`0 = A`, `1 = C`, ordered
  lexicographically, so `(s, A) < (s, C) < (u, A)` for `s < u`); `pSp p` and `κSp p κ` are the
  file's `p''` and `κ''`, given by the formulas of the Setting with no division; `κSp` is `0` on
  every pair that is not listed.
* Scalars: `c · G` is `c • G` and `c M^S` is `c • ⊤` (pointwise scalar multiple of a submodule).
-/

@[expose] public section

namespace Split

open DirectSum Finset Payment

variable {A : Type*} [CommRing A]
variable {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ i, AddCommGroup (N i)]
  [∀ i, Module A (N i)]

/-! ### The tensor model `V ⊗ Φ` -/

/-- The modules of the tensor model: `N^{VΦ}(i, e, e') = N i`; the element `x` at `(i, e, e')`
is the paper's `b_e ⊗ b_{e'} x` (*Setting*, "The tensor model `V ⊗ Φ`", of
`C12_split_move.md`). -/
abbrev NVΦ (q : ι × Fin 2 × Fin 2) : Type _ := N q.1

/-- The floor of the tensor model: `fl^{VΦ}(i, e, e') = 2 fl(i) + e + e'` (*Setting*, "The tensor
model `V ⊗ Φ`", of `C12_split_move.md`). -/
def flVΦ (fl : ι → ℕ) (q : ι × Fin 2 × Fin 2) : ℕ := 2 * fl q.1 + q.2.1.val + q.2.2.val

variable (A) in
/-- `b_e b_{e'} : M → M_{VΦ}`, placing `x` at `i` as `x` at `(i, e, e')` (*Setting*, "The tensor
model `V ⊗ Φ`", of `C12_split_move.md`). -/
def embVΦ (e e' : Fin 2) : (⨁ i, N i) →ₗ[A] (⨁ q, NVΦ N q) :=
  DirectSum.toModule A ι _ (fun i => DirectSum.lof A (ι × Fin 2 × Fin 2) (NVΦ N) (i, e, e'))

variable {N}

/-- The operator of the tensor model `F^{VΦ} = F_V ⊗ 1 + 1 ⊗ F^Φ`: on `x` at `(i, e, e')`, the
`F_V` part is `x` at `(i, 1, e')` if `e = 0` and `0` if `e = 1`, and the `F^Φ` part is `x` at
`(i, e, 1)` if `e' = 0` and `2 · (F x)` placed at `(·, e, 0)` if `e' = 1` (*Setting*, "The tensor
model `V ⊗ Φ`", of `C12_split_move.md`). -/
def FVΦ (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) : (⨁ q, NVΦ N q) →ₗ[A] (⨁ q, NVΦ N q) :=
  DirectSum.toModule A (ι × Fin 2 × Fin 2) _ (fun q =>
    (if q.2.1 = 0 then DirectSum.lof A (ι × Fin 2 × Fin 2) (NVΦ N) (q.1, 1, q.2.2) else 0)
    + (if q.2.2 = 0 then DirectSum.lof A (ι × Fin 2 × Fin 2) (NVΦ N) (q.1, q.2.1, 1)
       else (2 : A) • (embVΦ A N q.2.1 0 ∘ₗ F ∘ₗ DirectSum.lof A ι N q.1)))

/-! ### The split model `Ψ` -/

variable (N) in
/-- The modules of the split model: `N^Ψ(i, j) = N i`, with `j : Fin 4`, `0 = A`, `1 = B`,
`2 = C`, `3 = Dd` (*Setting*, "The split model `Ψ`", of `C12_split_move.md`). -/
abbrev NΨ (q : ι × Fin 4) : Type _ := N q.1

/-- The floor of the split model: `fl^Ψ(i, A) = 2 fl(i)`, `fl^Ψ(i, B) = fl^Ψ(i, C) = 2 fl(i) + 1`,
`fl^Ψ(i, Dd) = 2 fl(i) + 2` (*Setting*, "The split model `Ψ`", of `C12_split_move.md`). -/
def flΨ (fl : ι → ℕ) (q : ι × Fin 4) : ℕ := 2 * fl q.1 + (![0, 1, 1, 2] : Fin 4 → ℕ) q.2

variable (A N) in
/-- `J : M → M_Ψ`, placing `x` at `i` as `x` at `(i, J)` (*Setting*, "The split model `Ψ`", of
`C12_split_move.md`). -/
def embΨ (j : Fin 4) : (⨁ i, N i) →ₗ[A] (⨁ q, NΨ N q) :=
  DirectSum.toModule A ι _ (fun i => DirectSum.lof A (ι × Fin 4) (NΨ N) (i, j))

/-- The operator of the split model, on `x ∈ N i`:
`F^Ψ(A x) = B x + 2·C x`, `F^Ψ(B x) = 2·A(F x)`, `F^Ψ(C x) = Dd x`, `F^Ψ(Dd x) = 2·C(F x)`
(*Setting*, "The split model `Ψ`", of `C12_split_move.md`). -/
def FΨ (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) : (⨁ q, NΨ N q) →ₗ[A] (⨁ q, NΨ N q) :=
  DirectSum.toModule A (ι × Fin 4) _ (fun q =>
    (![DirectSum.lof A (ι × Fin 4) (NΨ N) (q.1, 1)
          + (2 : A) • DirectSum.lof A (ι × Fin 4) (NΨ N) (q.1, 2),
        (2 : A) • (embΨ A N 0 ∘ₗ F ∘ₗ DirectSum.lof A ι N q.1),
        DirectSum.lof A (ι × Fin 4) (NΨ N) (q.1, 3),
        (2 : A) • (embΨ A N 2 ∘ₗ F ∘ₗ DirectSum.lof A ι N q.1)] :
      Fin 4 → (N q.1 →ₗ[A] (⨁ q, NΨ N q))) q.2)

/-! ### The change of basis -/

/-- The change of basis `θ : M_{VΦ} → M_Ψ`: `θ(b_0b_0 x) = A x`, `θ(b_0b_1 x) = B x + C x`,
`θ(b_1b_0 x) = C x`, `θ(b_1b_1 x) = Dd x` (*Setting*, "The change of basis", of
`C12_split_move.md`). -/
def theta : (⨁ q, NVΦ N q) →ₗ[A] (⨁ q, NΨ N q) :=
  DirectSum.toModule A (ι × Fin 2 × Fin 2) _ (fun q =>
    if q.2.1 = 0 then
      (if q.2.2 = 0 then DirectSum.lof A (ι × Fin 4) (NΨ N) (q.1, 0)
       else DirectSum.lof A (ι × Fin 4) (NΨ N) (q.1, 1)
         + DirectSum.lof A (ι × Fin 4) (NΨ N) (q.1, 2))
    else
      (if q.2.2 = 0 then DirectSum.lof A (ι × Fin 4) (NΨ N) (q.1, 2)
       else DirectSum.lof A (ι × Fin 4) (NΨ N) (q.1, 3)))

/-- The inverse of the change of basis: `A x ↦ b_0b_0 x`, `B x ↦ b_0b_1 x − b_1b_0 x`,
`C x ↦ b_1b_0 x`, `Dd x ↦ b_1b_1 x` (*Part A*, (A1), of `C12_split_move.md`). -/
def thetaInv : (⨁ q, NΨ N q) →ₗ[A] (⨁ q, NVΦ N q) :=
  DirectSum.toModule A (ι × Fin 4) _ (fun q =>
    (![DirectSum.lof A (ι × Fin 2 × Fin 2) (NVΦ N) (q.1, 0, 0),
        DirectSum.lof A (ι × Fin 2 × Fin 2) (NVΦ N) (q.1, 0, 1)
          - DirectSum.lof A (ι × Fin 2 × Fin 2) (NVΦ N) (q.1, 1, 0),
        DirectSum.lof A (ι × Fin 2 × Fin 2) (NVΦ N) (q.1, 1, 0),
        DirectSum.lof A (ι × Fin 2 × Fin 2) (NVΦ N) (q.1, 1, 1)] :
      Fin 4 → (N q.1 →ₗ[A] (⨁ q, NVΦ N q))) q.2)

variable (S : Type*) [Fintype S] [LinearOrder S]

/-- The slotwise change of basis `θ_S : Sys_{VΦ} → Sys_Ψ`, `x ι_{s,(i,e,e')} ↦ (θ(b_e b_{e'} x)) ι_s`
(*Part A*, (A3), of `C12_split_move.md`). -/
def thetaS : Sys (NVΦ N) S →ₗ[A] Sys (NΨ N) S :=
  DirectSum.toModule A (S × (ι × Fin 2 × Fin 2)) _ (fun q =>
    slotEmb A (NΨ N) S q.1 ∘ₗ theta ∘ₗ DirectSum.lof A (ι × Fin 2 × Fin 2) (NVΦ N) q.2)

/-- The slotwise inverse change of basis `Sys_Ψ → Sys_{VΦ}` (*Part A*, (A3), of
`C12_split_move.md`). -/
def thetaInvS : Sys (NΨ N) S →ₗ[A] Sys (NVΦ N) S :=
  DirectSum.toModule A (S × (ι × Fin 4)) _ (fun q =>
    slotEmb A (NVΦ N) S q.1 ∘ₗ thetaInv ∘ₗ DirectSum.lof A (ι × Fin 4) (NΨ N) q.2)

variable {S}

/-! ### The split data -/

/-- The split payments (halved), on the slot type `Lex (S × Fin 2)` (`0 = A`, `1 = C`):
`p''_{(s,A)}(f) := −p_s(2f) p_s(2f+1)`, `p''_{(s,C)}(f) := −p_s(2f+1) p_s(2f+2)`
(*Setting*, "The split data", of `C12_split_move.md`). -/
def pSp (p : S → ℕ → A) (q : Lex (S × Fin 2)) (f : ℕ) : A :=
  if (ofLex q).2 = 0 then -(p (ofLex q).1 (2 * f) * p (ofLex q).1 (2 * f + 1))
  else -(p (ofLex q).1 (2 * f + 1) * p (ofLex q).1 (2 * f + 2))

/-- The split couplings (halved) `κ''_{q' q}(f)` (coupling from the slot `q = (s', Y)` to the slot
`q' = (u, X)`), on the slot type `Lex (S × Fin 2)` (`0 = A`, `1 = C`):
* for `u > s'`: `κ''_{(u,A),(s',A)}(f) := −[p_{s'}(2f+1) κ_{us'}(2f) + κ_{us'}(2f+1) p_u(2f)
  + Σ_{s'<s<u} κ_{ss'}(2f+1) κ_{us}(2f)]`;
* for `u > s'`: `κ''_{(u,C),(s',C)}(f) := −[p_{s'}(2f+2) κ_{us'}(2f+1) + κ_{us'}(2f+2) p_u(2f+1)
  + Σ_{s'<s<u} κ_{ss'}(2f+2) κ_{us}(2f+1)]`;
* `κ''_{(s',C),(s',A)}(f) := −p_{s'}(2f+1)`;
* for `u > s'`: `κ''_{(u,C),(s',A)}(f) := −κ_{us'}(2f+1)`;
* all other values are `0`
(*Setting*, "The split data", of `C12_split_move.md`). -/
def κSp (p : S → ℕ → A) (κ : S → S → ℕ → A) (q' q : Lex (S × Fin 2)) (f : ℕ) : A :=
  if (ofLex q).2 = 0 ∧ (ofLex q').2 = 0 then
    (if (ofLex q).1 < (ofLex q').1 then
      -(p (ofLex q).1 (2 * f + 1) * κ (ofLex q').1 (ofLex q).1 (2 * f)
        + κ (ofLex q').1 (ofLex q).1 (2 * f + 1) * p (ofLex q').1 (2 * f)
        + ∑ s ∈ Finset.univ.filter (fun s => (ofLex q).1 < s ∧ s < (ofLex q').1),
            κ s (ofLex q).1 (2 * f + 1) * κ (ofLex q').1 s (2 * f))
    else 0)
  else if (ofLex q).2 = 1 ∧ (ofLex q').2 = 1 then
    (if (ofLex q).1 < (ofLex q').1 then
      -(p (ofLex q).1 (2 * f + 2) * κ (ofLex q').1 (ofLex q).1 (2 * f + 1)
        + κ (ofLex q').1 (ofLex q).1 (2 * f + 2) * p (ofLex q').1 (2 * f + 1)
        + ∑ s ∈ Finset.univ.filter (fun s => (ofLex q).1 < s ∧ s < (ofLex q').1),
            κ s (ofLex q).1 (2 * f + 2) * κ (ofLex q').1 s (2 * f + 1))
    else 0)
  else if (ofLex q).2 = 0 ∧ (ofLex q').2 = 1 then
    (if (ofLex q').1 = (ofLex q).1 then -p (ofLex q).1 (2 * f + 1)
     else if (ofLex q).1 < (ofLex q').1 then -κ (ofLex q').1 (ofLex q).1 (2 * f + 1)
     else 0)
  else 0

end Split
