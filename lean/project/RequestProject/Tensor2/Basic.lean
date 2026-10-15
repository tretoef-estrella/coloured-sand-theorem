module

public import RequestProject.Tensor2.Kron
public import RequestProject.Tensor2.Comb

/-!
# `C23_the_tensor_product.md`: (P1) the tensor product `M ⊗ N`

Encodings (namespace `Tensor2`), reusing C18 (`DPLattice`, `IsDP`, `H`):

* `coFd F G r = Σ_{a=0}^{r} F a ⊠ G (r − a)` (`⊠` is `kron`), the coproduct of two families of
  divided powers; on pure tensors `coFd F G r (m ⊗ n) = Σ_{a=0}^{r} F^{(a)} m ⊗ G^{(r−a)} n`
  (`coFd_tprod`).
* `tensor M N` is `M ⊗ N`: basis `M.ι × N.ι`, weights `wt (i, j) = M.wt i + N.wt j`,
  `F^{(r)} = coFd M.Fd N.Fd r`, `E^{(r)} = coFd M.Ed N.Ed r`.
-/

@[expose] public section

noncomputable section

namespace Tensor2

open DPLattice Finset

variable {A : Type*} [CommRing A]

section linsum

variable {X Y Z : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
  [AddCommGroup Z] [Module A Z] {α : Type*}

lemma lin_comp_sum (s : Finset α) (g : Y →ₗ[A] Z) (f : α → X →ₗ[A] Y) :
    g ∘ₗ (∑ a ∈ s, f a) = ∑ a ∈ s, g ∘ₗ f a := LinearMap.ext fun x => by simp

lemma lin_sum_comp (s : Finset α) (g : α → Y →ₗ[A] Z) (f : X →ₗ[A] Y) :
    (∑ a ∈ s, g a) ∘ₗ f = ∑ a ∈ s, g a ∘ₗ f := LinearMap.ext fun x => by simp

end linsum

section coFd

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- (P1) the coproduct `Σ_{a=0}^{r} F a ⊠ G (r − a)` of two families of endomorphisms. -/
def coFd (F : ℕ → Module.End A (ι → A)) (G : ℕ → Module.End A (κ → A)) (r : ℕ) :
    Module.End A (ι × κ → A) :=
  ∑ a ∈ range (r + 1), kron (F a) (G (r - a))

/-- (P1) `F^{(r)}(m ⊗ n) = Σ_{a+b=r} F^{(a)} m ⊗ F^{(b)} n`. -/
theorem coFd_tprod (F : ℕ → Module.End A (ι → A)) (G : ℕ → Module.End A (κ → A)) (r : ℕ)
    (m : ι → A) (n : κ → A) :
    coFd F G r (tprod m n) = ∑ a ∈ range (r + 1), tprod (F a m) (G (r - a) n) := by
  simp only [coFd, LinearMap.coe_sum, Finset.sum_apply, kron_tprod]

lemma coFd_P0 {F : ℕ → Module.End A (ι → A)} {G : ℕ → Module.End A (κ → A)} (hF : F 0 = 1)
    (hG : G 0 = 1) : coFd F G 0 = 1 := by
  simp [coFd, hF, hG, kron_one]

lemma coFd_P1 {F : ℕ → Module.End A (ι → A)} {G : ℕ → Module.End A (κ → A)}
    (hF : ∀ a b : ℕ, F a ∘ₗ F b = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • F (a + b))
    (hG : ∀ a b : ℕ, G a ∘ₗ G b = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • G (a + b))
    (a b : ℕ) : coFd F G a ∘ₗ coFd F G b =
      ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • coFd F G (a + b) := by
  have step : coFd F G a ∘ₗ coFd F G b = ∑ c ∈ range (a + 1), ∑ d ∈ range (b + 1),
      ((c + d).choose c * ((a - c) + (b - d)).choose (a - c)) •
        kron (F (c + d)) (G ((a - c) + (b - d))) := by
    rw [coFd, coFd, lin_sum_comp]
    refine sum_congr rfl fun c _ => ?_
    rw [lin_comp_sum]
    refine sum_congr rfl fun d _ => ?_
    rw [kron_comp, hF, hG, kron_smul_left, kron_smul_right, smul_smul, choose_natAdd,
      choose_natAdd, Int.cast_natCast, Int.cast_natCast, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul]
  rw [step, vand_P1 a b (fun x y => kron (F x) (G y)), choose_natAdd, Int.cast_natCast,
    Nat.cast_smul_eq_nsmul]
  rfl

end coFd

section tensor

variable (M N : DPLattice A)

lemma tensor_W {D : ℕ → Module.End A (M.ι → A)} {G : ℕ → Module.End A (N.ι → A)}
    (σ : ℤ)
    (hD : ∀ (i : M.ι) (r : ℕ) (j : M.ι), M.wt j ≠ M.wt i + σ * r → D r (Pi.single i 1) j = 0)
    (hG : ∀ (i : N.ι) (r : ℕ) (j : N.ι), N.wt j ≠ N.wt i + σ * r → G r (Pi.single i 1) j = 0)
    (p : M.ι × N.ι) (r : ℕ) (q : M.ι × N.ι)
    (h : M.wt q.1 + N.wt q.2 ≠ M.wt p.1 + N.wt p.2 + σ * r) :
    coFd D G r (Pi.single p 1) q = 0 := by
  obtain ⟨i, j⟩ := p
  obtain ⟨i', j'⟩ := q
  rw [single_prod_eq_tprod, coFd_tprod, Finset.sum_apply]
  refine Finset.sum_eq_zero fun a ha => ?_
  simp only [mem_range] at ha
  rw [tprod_apply]
  by_cases h1 : M.wt i' = M.wt i + σ * a
  · have h2 : N.wt j' ≠ N.wt j + σ * ((r - a : ℕ) : ℤ) := by
      intro h2; apply h; push_cast [Nat.cast_sub (by omega : a ≤ r)] at h2 ⊢; rw [h1, h2]; ring
    rw [hG j (r - a) j' h2, mul_zero]
  · rw [hD i a i' h1, zero_mul]

lemma tensor_K (i : M.ι) (j : N.ι) (r s : ℕ) :
    coFd M.Ed N.Ed s (coFd M.Fd N.Fd r (Pi.single (i, j) 1)) =
      ∑ m ∈ range (min r s + 1), ((Ring.choose (M.wt i + N.wt j + s - r) m : ℤ) : A) •
        coFd M.Fd N.Fd (r - m) (coFd M.Ed N.Ed (s - m) (Pi.single (i, j) 1)) := by
  set T : ℕ → ℕ → ℕ → ℕ → (M.ι × N.ι → A) := fun a' c' b' d' =>
    tprod (M.Fd a' (M.Ed c' (Pi.single i 1))) (N.Fd b' (N.Ed d' (Pi.single j 1))) with hT
  have lhs : coFd M.Ed N.Ed s (coFd M.Fd N.Fd r (Pi.single (i, j) 1)) =
      ∑ a ∈ range (r + 1), ∑ c ∈ range (s + 1), ∑ k ∈ range (min a c + 1),
        ∑ l ∈ range (min (r - a) (s - c) + 1),
          (Ring.choose (M.wt i + c - a) k *
            Ring.choose (N.wt j + ((s - c : ℕ) : ℤ) - ((r - a : ℕ) : ℤ)) l) •
            T (a - k) (c - k) (r - a - l) (s - c - l) := by
    rw [single_prod_eq_tprod, coFd_tprod, map_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [coFd_tprod]
    refine sum_congr rfl fun c _ => ?_
    rw [M.isDP.K, N.isDP.K, tprod_sum_left]
    refine sum_congr rfl fun k _ => ?_
    rw [tprod_sum_right]
    refine sum_congr rfl fun l _ => ?_
    rw [tprod_smul_left, tprod_smul_right, smul_smul, ← Int.cast_mul, Int.cast_smul_eq_zsmul,
      mul_comm]
  have rhs : ∑ m ∈ range (min r s + 1), ((Ring.choose (M.wt i + N.wt j + s - r) m : ℤ) : A) •
        coFd M.Fd N.Fd (r - m) (coFd M.Ed N.Ed (s - m) (Pi.single (i, j) 1)) =
      ∑ m ∈ range (min r s + 1), Ring.choose (M.wt i + N.wt j + s - r) m •
        ∑ c' ∈ range (s - m + 1), ∑ a' ∈ range (r - m + 1), T a' c' (r - m - a') (s - m - c') := by
    refine sum_congr rfl fun m _ => ?_
    rw [Int.cast_smul_eq_zsmul, single_prod_eq_tprod, coFd_tprod, map_sum]
    congr 1
    refine sum_congr rfl fun c' _ => ?_
    rw [coFd_tprod]
  rw [lhs, rhs, vand_K]

/-- (P1) The data of `M ⊗ N` (basis `M.ι × N.ι`, weights `M.wt i + N.wt j`,
`F^{(r)} = Σ_{a=0}^{r} M.Fd a ⊠ N.Fd (r − a)`, `E^{(r)} = Σ_{a=0}^{r} M.Ed a ⊠ N.Ed (r − a)`)
satisfy `IsDP`: (W), (P0), (P1) and (K). -/
theorem tensor_isDP : IsDP (fun p : M.ι × N.ι => M.wt p.1 + N.wt p.2) (coFd M.Fd N.Fd)
    (coFd M.Ed N.Ed) where
  W_F p r q h := tensor_W M N (-2) (fun i r j h => M.isDP.W_F i r j (by intro h'; apply h; rw [h']; ring))
    (fun i r j h => N.isDP.W_F i r j (by intro h'; apply h; rw [h']; ring)) p r q
    (by intro h'; apply h; rw [h']; ring)
  W_E p r q h := tensor_W M N 2 (fun i r j h => M.isDP.W_E i r j h)
    (fun i r j h => N.isDP.W_E i r j h) p r q h
  P0_F := coFd_P0 M.isDP.P0_F N.isDP.P0_F
  P0_E := coFd_P0 M.isDP.P0_E N.isDP.P0_E
  P1_F := coFd_P1 M.isDP.P1_F N.isDP.P1_F
  P1_E := coFd_P1 M.isDP.P1_E N.isDP.P1_E
  K p r s := by
    obtain ⟨i, j⟩ := p
    exact tensor_K M N i j r s

/-- (P1) The tensor product `M ⊗ N` of two DP-lattices: basis `M.ι × N.ι`, weights
`wt (i, j) = M.wt i + N.wt j`, `F^{(r)} = Σ_{a=0}^{r} M.Fd a ⊠ N.Fd (r − a)` and
`E^{(r)} = Σ_{a=0}^{r} M.Ed a ⊠ N.Ed (r − a)`. That it is a DP-lattice is `tensor_isDP`. -/
def tensor : DPLattice A where
  ι := M.ι × N.ι
  wt p := M.wt p.1 + N.wt p.2
  Fd := coFd M.Fd N.Fd
  Ed := coFd M.Ed N.Ed
  isDP := tensor_isDP M N

/-- (P1) `F^{(r)}(m ⊗ n) = Σ_{a+b=r} F^{(a)} m ⊗ F^{(b)} n` on `M ⊗ N`. -/
theorem tensor_Fd_tprod (r : ℕ) (m : M.ι → A) (n : N.ι → A) :
    (tensor M N).Fd r (tprod m n) = ∑ a ∈ range (r + 1), tprod (M.Fd a m) (N.Fd (r - a) n) :=
  coFd_tprod _ _ r m n

/-- (P1) `E^{(r)}(m ⊗ n) = Σ_{a+b=r} E^{(a)} m ⊗ E^{(b)} n` on `M ⊗ N`. -/
theorem tensor_Ed_tprod (r : ℕ) (m : M.ι → A) (n : N.ι → A) :
    (tensor M N).Ed r (tprod m n) = ∑ a ∈ range (r + 1), tprod (M.Ed a m) (N.Ed (r - a) n) :=
  coFd_tprod _ _ r m n

/-- (P1) `H` on `M ⊗ N` is `H ⊠ 1 + 1 ⊠ H` (weights add). -/
theorem H_tensor : H (tensor M N) = kron (H M) 1 + kron 1 (H N) := (kron_Hop M.wt N.wt).symm

/-- (P1) the statement of the file: `M ⊗ N` has basis `M.ι × N.ι`, weights `M.wt i + N.wt j`,
`F^{(r)} = Σ_{a=0}^{r} M.Fd a ⊠ N.Fd (r − a)`, `E^{(r)} = Σ_{a=0}^{r} M.Ed a ⊠ N.Ed (r − a)`
(with `(f ⊠ g)(δ_{(i,j)}) (i', j') = f(δ_i)(i') · g(δ_j)(j')`), and these data satisfy `IsDP`,
(K) included. -/
theorem P1 :
    (tensor M N).ι = (M.ι × N.ι) ∧
    (∀ i j, (tensor M N).wt (i, j) = M.wt i + N.wt j) ∧
    (∀ r, (tensor M N).Fd r = ∑ a ∈ range (r + 1), kron (M.Fd a) (N.Fd (r - a))) ∧
    (∀ r, (tensor M N).Ed r = ∑ a ∈ range (r + 1), kron (M.Ed a) (N.Ed (r - a))) ∧
    IsDP (fun p : M.ι × N.ι => M.wt p.1 + N.wt p.2) (coFd M.Fd N.Fd) (coFd M.Ed N.Ed) :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, tensor_isDP M N⟩

end tensor

end Tensor2
