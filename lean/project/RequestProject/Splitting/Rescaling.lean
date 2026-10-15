module

public import RequestProject.Splitting.Basic
public import RequestProject.Strings.TheoremE

/-!
# (A3) Only the valuations matter, and (A4) its corollary

This file corresponds to **(A3) Only the valuations matter (Lemma 2)** and **(A4) Corollary** of
`CS2_theorem_A_splitting.md`.

## Encoding

* `B_m(R) = Finset (Fin m) → R` and `U` are those of `RequestProject/Strings/Basic.lean`.
* For `a : ℕ → R`, the diagonal operator `diag(a_{|S|})` is `diagOp m R a`, i.e.
  `(diagOp a f) T = a_{|T|} f T`, so `diagOp a e_S = a_{|S|} e_S`.
* "Diagonal invertible `P = diag(λ_{|S|})`" is `diagOp m R (fun s => (λ s : R))` with
  `λ : ℕ → Rˣ`; the product `P M Q` is the composition `P ∘ₗ M ∘ₗ Q`.
* `coker f = B_m(R) ⧸ LinearMap.range f`, and "`≅`" is the existence of an `R`-linear equivalence.

## Results

* `rescaling` / `rescaling_coker`: the lemma over an *arbitrary* commutative ring `R`, for any
  factorisation `a_s = t_s u_s` with `u_s` a unit (more general than the file, which takes
  `t_s = p^{w_s}`).
* `rescaling_padic` / `rescaling_padic_coker`: the statement of (A3) over `ℤ_[p]`, with
  `w_s = v_p(a_s)` (`PadicInt.valuation`) and `p^{w_s}` read as `0` when `a_s = 0`.
* `opM_coker_equiv_valuations` and `opM_coker_depends_only_on_valuations`: (A4).
-/

@[expose] public section

open Finset

namespace ColouredSand.Splitting

open ColouredSand.Strings

section general

variable (m : ℕ) (R : Type*) [CommRing R]

/-- The diagonal operator `diag(a_{|S|})` on `B_m(R)`: `(diagOp a f) T = a_{|T|} f T`. -/
def diagOp (a : ℕ → R) : B m R →ₗ[R] B m R where
  toFun f T := a T.card * f T
  map_add' f g := by ext T; simp [mul_add]
  map_smul' c f := by ext T; simp; ring

variable {m R}

@[simp] lemma diagOp_apply (a : ℕ → R) (f : B m R) (T : Finset (Fin m)) :
    diagOp m R a f T = a T.card * f T := rfl

/-- A diagonal operator with unit entries, as a linear equivalence. -/
def diagEquiv (u : ℕ → Rˣ) : B m R ≃ₗ[R] B m R :=
  LinearEquiv.ofLinear (diagOp m R (fun s => (u s : R))) (diagOp m R (fun s => ((u s)⁻¹ : Rˣ)))
    (by ext f T; simp) (by ext f T; simp)

@[simp] lemma diagEquiv_apply (u : ℕ → Rˣ) (f : B m R) :
    diagEquiv u f = diagOp m R (fun s => (u s : R)) f := rfl

/-- The scaling factors `μ` of (A3): `μ_0 = 1`, `μ_{s+1} = μ_s u_{s+1}^{-1}`. -/
def rescaleMu (u : ℕ → Rˣ) : ℕ → Rˣ
  | 0 => 1
  | s + 1 => rescaleMu u s * (u (s + 1))⁻¹

/-- The scaling factors `λ` of (A3): `λ_0 = u_0^{-1}`, `λ_{s+1} = μ_s^{-1}`. -/
def rescaleLam (u : ℕ → Rˣ) : ℕ → Rˣ
  | 0 => (u 0)⁻¹
  | s + 1 => (rescaleMu u s)⁻¹

lemma rescale_diag (u : ℕ → Rˣ) (s : ℕ) :
    (rescaleLam u s : R) * u s * rescaleMu u s = 1 := by
  cases s with
  | zero => simp [rescaleLam, rescaleMu]
  | succ s =>
    simp only [rescaleLam, rescaleMu, Units.val_mul]
    have h1 : (((rescaleMu u s)⁻¹ : Rˣ) : R) * (rescaleMu u s : R) = 1 := by simp
    have h2 : (u (s + 1) : R) * (((u (s + 1))⁻¹ : Rˣ) : R) = 1 := by simp
    linear_combination ((u (s + 1) : R) * (((u (s + 1))⁻¹ : Rˣ) : R)) * h1 + h2

lemma rescale_sub (u : ℕ → Rˣ) (s : ℕ) : (rescaleLam u (s + 1) : R) * rescaleMu u s = 1 := by
  simp [rescaleLam]

/-- **(A3), general form.**  Let `a_s = t_s u_s` with `u_s` units.  Then there are diagonal
invertible `P = diag(λ_{|S|})`, `Q = diag(μ_{|S|})` with `P (diag(a_{|S|}) + U) Q =
diag(t_{|S|}) + U`.  (The file takes `t_s = p^{w_s}`; here `R` is any commutative ring.) -/
theorem rescaling (a t : ℕ → R) (u : ℕ → Rˣ) (ha : ∀ s, a s = t s * u s) :
    ∃ lam mu : ℕ → Rˣ,
      diagOp m R (fun s => (lam s : R)) ∘ₗ (diagOp m R a + U m R) ∘ₗ
        diagOp m R (fun s => (mu s : R)) = diagOp m R t + U m R := by
  refine ⟨rescaleLam u, rescaleMu u, ?_⟩
  refine LinearMap.ext fun f => funext fun T => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, diagOp_apply, U_apply, Pi.add_apply]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · rw [ha]
    linear_combination (t T.card * f T) * rescale_diag u T.card
  · refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨r, hr⟩ : ∃ r, T.card = r + 1 :=
      ⟨T.card - 1, by have := Finset.card_pos.mpr ⟨x, hx⟩; omega⟩
    rw [Finset.card_erase_of_mem hx, hr, Nat.add_sub_cancel, ← mul_assoc, rescale_sub, one_mul]

/-- **(A3), general form, cokernels.**  `coker (diag(a_{|S|}) + U) ≅ coker (diag(t_{|S|}) + U)`. -/
theorem rescaling_coker (a t : ℕ → R) (u : ℕ → Rˣ) (ha : ∀ s, a s = t s * u s) :
    Nonempty ((B m R ⧸ LinearMap.range (diagOp m R a + U m R)) ≃ₗ[R]
      (B m R ⧸ LinearMap.range (diagOp m R t + U m R))) := by
  obtain ⟨lam, mu, h⟩ := rescaling (m := m) a t u ha
  refine ⟨cokerEquivOfConj _ _ (diagEquiv (fun s => (mu s)⁻¹)) (diagEquiv lam) ?_⟩
  intro f
  rw [← h]
  simp only [LinearMap.comp_apply, diagEquiv_apply]
  congr 2
  ext T
  simp

end general

section padic

variable {p : ℕ} [Fact p.Prime]

open scoped Classical in
/-- The normalised entry `p^{w}` with `w = v_p(x)`, read as `0` when `x = 0`. -/
noncomputable def padicNormalize (x : ℤ_[p]) : ℤ_[p] := if x = 0 then 0 else (p : ℤ_[p]) ^ x.valuation

open scoped Classical in
/-- The unit part `u` of `x = p^{v_p(x)} u` (`u = 1` when `x = 0`). -/
noncomputable def padicUnitPart (x : ℤ_[p]) : ℤ_[p]ˣ :=
  if hx : x = 0 then 1 else PadicInt.unitCoeff hx

lemma padic_factor (x : ℤ_[p]) : x = padicNormalize x * padicUnitPart x := by
  by_cases hx : x = 0
  · simp [padicNormalize, hx]
  · rw [padicNormalize, padicUnitPart, dif_neg hx, if_neg hx]
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    ring

/-- **(A3) Only the valuations matter (Lemma 2), over `ℤ_[p]`.**  Let `a_0, …, a_m ∈ ℤ_[p]` and
`M = diag(a_{|S|}) + U`.  There are diagonal invertible `P = diag(λ_{|S|})`, `Q = diag(μ_{|S|})`
with `P M Q = diag(p^{w_{|S|}}) + U`, where `w_s = v_p(a_s)` and `p^{w_s}` is read as `0` when
`a_s = 0` (`padicNormalize`). -/
theorem rescaling_padic (m : ℕ) (a : ℕ → ℤ_[p]) :
    ∃ lam mu : ℕ → ℤ_[p]ˣ,
      diagOp m ℤ_[p] (fun s => (lam s : ℤ_[p])) ∘ₗ (diagOp m ℤ_[p] a + U m ℤ_[p]) ∘ₗ
        diagOp m ℤ_[p] (fun s => (mu s : ℤ_[p])) =
      diagOp m ℤ_[p] (fun s => padicNormalize (a s)) + U m ℤ_[p] :=
  rescaling a _ (fun s => padicUnitPart (a s)) (fun s => padic_factor (a s))

/-- **(A3), "in particular"**: `coker M ≅ coker (diag(p^{w_{|S|}}) + U)` over `ℤ_[p]`. -/
theorem rescaling_padic_coker (m : ℕ) (a : ℕ → ℤ_[p]) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range (diagOp m ℤ_[p] a + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      (B m ℤ_[p] ⧸ LinearMap.range
        (diagOp m ℤ_[p] (fun s => padicNormalize (a s)) + U m ℤ_[p]))) :=
  rescaling_coker a _ (fun s => padicUnitPart (a s)) (fun s => padic_factor (a s))

/-! ### (A4) -/

/-- `M_q(m,c) = q (c + H) + U` is the operator `diag(q (c + |S|)) + U`. -/
lemma opM_eq_diagOp {R : Type*} [CommRing R] (m : ℕ) (q c : R) :
    opM m R q c = diagOp m R (fun s => q * (c + s)) + U m R := by
  ext f T
  simp [opM]
  ring

/-- The normalised entry `p^{v_p(z)}` of an integer `z`, read as `0` when `z = 0`. -/
noncomputable def intNormalize (z : ℤ) : ℤ_[p] :=
  if z = 0 then 0 else (p : ℤ_[p]) ^ padicValInt p z

lemma int_factor (z : ℤ) : ∃ u : ℤ_[p]ˣ, (z : ℤ_[p]) = intNormalize (p := p) z * u := by
  by_cases hz : z = 0
  · exact ⟨1, by simp [intNormalize, hz]⟩
  · obtain ⟨u, hu⟩ := padicInt_associated_intCast (p := p) hz
    exact ⟨u⁻¹, by rw [intNormalize, if_neg hz, ← hu]; simp⟩

/-- **(A4), explicit form.**  Over `ℤ_[p]`, `coker (M_q(m,c) ⊗ ℤ_[p]) ≅ coker (diag(π_{|S|}) + U)`
where `π_s = p^{v_p(q (c + s))}` (and `π_s = 0` if `q (c + s) = 0`).  Here `q, c ∈ ℤ`
(more general than `q, c ∈ ℕ`). -/
theorem opM_coker_equiv_valuations (m : ℕ) (q c : ℤ) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range (opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]))) ≃ₗ[ℤ_[p]]
      (B m ℤ_[p] ⧸ LinearMap.range
        (diagOp m ℤ_[p] (fun s => intNormalize (q * (c + s))) + U m ℤ_[p]))) := by
  choose u hu using fun s : ℕ => int_factor (p := p) (q * (c + s))
  rw [opM_eq_diagOp]
  exact rescaling_coker _ _ u (fun s => by rw [← hu]; push_cast; ring)

lemma diagOp_congr {R : Type*} [CommRing R] (m : ℕ) (a b : ℕ → R) (h : ∀ s ≤ m, a s = b s) :
    diagOp m R a = diagOp m R b := by
  refine LinearMap.ext fun f => funext fun T => ?_
  simp only [diagOp_apply]
  rw [h _ ((Finset.card_le_univ T).trans_eq (Fintype.card_fin m))]

/-- **(A4) Corollary.**  For a prime `p`, the `ℤ_[p]`-module `coker (M_q(m,c) ⊗ ℤ_[p])` depends
only on `m` and the valuations `v_p(q (c + s))`, `0 ≤ s ≤ m`: if `(q, c)` and `(q', c')` give
the same valuations (and the same vanishing pattern of `q (c + s)`, since `v_p(0)` is not
defined) for all `s ≤ m`, the two cokernels are isomorphic.  Here `q, c ∈ ℤ`. -/
theorem opM_coker_depends_only_on_valuations (m : ℕ) (q c q' c' : ℤ)
    (hzero : ∀ s ≤ m, (q * (c + s) = 0 ↔ q' * (c' + s) = 0))
    (hval : ∀ s ≤ m, padicValInt p (q * (c + s)) = padicValInt p (q' * (c' + s))) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range (opM m ℤ_[p] (q : ℤ_[p]) (c : ℤ_[p]))) ≃ₗ[ℤ_[p]]
      (B m ℤ_[p] ⧸ LinearMap.range (opM m ℤ_[p] (q' : ℤ_[p]) (c' : ℤ_[p])))) := by
  obtain ⟨e₁⟩ := opM_coker_equiv_valuations (p := p) m q c
  obtain ⟨e₂⟩ := opM_coker_equiv_valuations (p := p) m q' c'
  have hd : diagOp m ℤ_[p] (fun s => intNormalize (q * (c + s))) =
      diagOp m ℤ_[p] (fun s => intNormalize (q' * (c' + s))) := by
    refine diagOp_congr m _ _ fun s hs => ?_
    simp only [intNormalize, hzero s hs, hval s hs]
  rw [hd] at e₁
  exact ⟨e₁.trans e₂.symm⟩

end padic

end ColouredSand.Splitting
