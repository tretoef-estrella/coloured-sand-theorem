module

public import Mathlib

/-!
# `C31_theorem_36_the_family_decomposition.md`: Part M — the multiplicities, and Part L — Lemma 3.7

Encodings (namespace `FamDec`):

* A formal sum `Σ_λ c_λ [λ]` of the paper (§1.2) is a `List ℕ`: the symbol `[λ]` with coefficient
  `c` is `c` copies of `λ` in the list; the order of the list does not matter (lists are compared
  up to `List.Perm`). The paper's `λ` is written `lam` (`λ` is reserved in Lean).
* `Vdot : ℕ → List ℕ` (the rule `V · [λ]`) is defined by well-founded recursion as
  `Vdot 0 = [1]`, `Vdot (n + 1) = [n + 2]` for even `n` and
  `Vdot (n + 1) = [n, n] ++ (Vdot (n / 2)).map (fun ν => 2ν + 1)` for odd `n`; the three equations
  of (M1) are the theorems `Vdot_zero`, `Vdot_odd`, `Vdot_even`.
* `L 0 = [0]`, `L (n + 1) = (L n).flatMap Vdot` (ordinary recursion), and
  `m lam n = (L n).count lam`.
-/

@[expose] public section

namespace FamDec

/-! ### (M1) -/

/-- **(M1)** the rule `V · [λ]` as a list: `Vdot 0 = [1]`, `Vdot (2l+1) = [2l+2]`,
`Vdot (2l+2) = [2l+1, 2l+1] ++ (Vdot l).map (2·+1)` (well-founded recursion, written with
`n + 1` and `n / 2`). -/
def Vdot : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => if n % 2 = 0 then [n + 2] else [n, n] ++ (Vdot (n / 2)).map (fun ν => 2 * ν + 1)
decreasing_by omega

/-- **(M1)** `Vdot 0 = [1]`. -/
theorem Vdot_zero : Vdot 0 = [1] := by rw [Vdot]

/-- **(M1)** `Vdot (2l + 1) = [2l + 2]`. -/
theorem Vdot_odd (l : ℕ) : Vdot (2 * l + 1) = [2 * l + 2] := by
  rw [Vdot, if_pos (by omega)]

/-- **(M1)** `Vdot (2l + 2) = [2l + 1, 2l + 1] ++ (Vdot l).map (fun ν => 2ν + 1)`. -/
theorem Vdot_even (l : ℕ) :
    Vdot (2 * l + 2) = [2 * l + 1, 2 * l + 1] ++ (Vdot l).map (fun ν => 2 * ν + 1) := by
  rw [show 2 * l + 2 = (2 * l + 1) + 1 by omega, Vdot, if_neg (by omega),
    show (2 * l + 1) / 2 = l by omega]

/-! ### (M2) -/

/-- **(M2)** the formal sums `L n = V^{⊗n} · [0]`: `L 0 = [0]`, `L (n+1) = (L n).flatMap Vdot`. -/
def L : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => (L n).flatMap Vdot

/-- **(M2)** `L 0 = [0]`. -/
theorem L_zero : L 0 = [0] := rfl

/-- **(M2)** `L (n + 1) = (L n).flatMap Vdot`. -/
theorem L_succ (n : ℕ) : L (n + 1) = (L n).flatMap Vdot := rfl

/-- **(M2)** the multiplicity `m_λ(n) = (L n).count λ`. -/
def m (lam n : ℕ) : ℕ := (L n).count lam

/-! ### Auxiliary facts on `Vdot` -/

/-- An even/odd case split used for the recursion of `Vdot` (auxiliary for Part M). -/
lemma nat_cases3 (n : ℕ) : n = 0 ∨ (∃ l, n = 2 * l + 1) ∨ ∃ l, n = 2 * l + 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rcases k with _ | k
    · left; rfl
    · right; right; exact ⟨k, by ring⟩
  · right; left; exact ⟨k, rfl⟩

/-- (M3), auxiliary: every `μ ∈ Vdot λ` has `1 ≤ μ ≤ λ + 1` and `μ ≡ λ + 1 (mod 2)`. -/
theorem mem_Vdot (lam : ℕ) : ∀ μ ∈ Vdot lam, 1 ≤ μ ∧ μ ≤ lam + 1 ∧ μ % 2 = (lam + 1) % 2 := by
  induction lam using Nat.strong_induction_on with
  | _ lam ih =>
    rcases nat_cases3 lam with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
    · simp [Vdot_zero]
    · simp only [Vdot_odd, List.mem_singleton]
      rintro μ rfl; omega
    · intro μ hμ
      rw [Vdot_even] at hμ
      rcases List.mem_append.mp hμ with h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> omega
      · obtain ⟨ν, hν, rfl⟩ := List.mem_map.mp h
        have := ih l (by omega) ν hν
        omega

/-- (L2), (L3), auxiliary: counting `2a + 1` in the image of a list under `ν ↦ 2ν + 1`. -/
lemma count_map_odd (l : List ℕ) (a : ℕ) :
    (l.map (fun ν => 2 * ν + 1)).count (2 * a + 1) = l.count a :=
  List.count_map_of_injective l (fun ν => 2 * ν + 1) (fun a b h => by simp at h; omega) a

/-- (L2), auxiliary: `λ + 1` occurs exactly once in `Vdot λ`. -/
theorem count_succ_Vdot (lam : ℕ) : (Vdot lam).count (lam + 1) = 1 := by
  induction lam using Nat.strong_induction_on with
  | _ lam ih =>
    rcases nat_cases3 lam with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
    · simp [Vdot_zero]
    · simp [Vdot_odd]
    · rw [Vdot_even, List.count_append, show 2 * l + 2 + 1 = 2 * (l + 1) + 1 by ring,
        count_map_odd, ih l (by omega)]
      simp

/-- (L4), auxiliary: `2` occurs in `Vdot λ` exactly once if `λ = 1`, and never otherwise. -/
theorem count_two_Vdot (lam : ℕ) : (Vdot lam).count 2 = if lam = 1 then 1 else 0 := by
  rcases nat_cases3 lam with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
  · simp [Vdot_zero]
  · rcases l with _ | l
    · rw [Vdot_odd]; simp
    · rw [Vdot_odd, if_neg (by omega)]; simp
  · rw [if_neg (by omega), List.count_eq_zero]
    intro h
    have := (mem_Vdot _ 2 h).2.2
    omega

/-- (L3), auxiliary: `1` occurs once in `Vdot 0`, twice in `Vdot 2`, and never in other `Vdot λ`. -/
theorem count_one_Vdot (lam : ℕ) :
    (Vdot lam).count 1 = (if lam = 0 then 1 else 0) + (if lam = 2 then 2 else 0) := by
  rcases nat_cases3 lam with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
  · simp [Vdot_zero]
  · rw [if_neg (by omega), if_neg (by omega), List.count_eq_zero]
    intro h
    have := (mem_Vdot _ 1 h).2.2
    omega
  · rw [if_neg (by omega), Vdot_even, List.count_append]
    rw [show List.count 1 (List.map (fun ν => 2 * ν + 1) (Vdot l)) = (Vdot l).count 0 from
      count_map_odd (Vdot l) 0]
    have h0 : (Vdot l).count 0 = 0 := by
      rw [List.count_eq_zero]
      intro h
      have := (mem_Vdot _ 0 h).1
      omega
    rw [h0]
    rcases l with _ | l
    · simp
    · simp

/-- (M4) and Part L, auxiliary: a sum over a list of a function supported at `a` with value `c` there. -/
lemma sum_map_eq_count_mul (l : List ℕ) (f : ℕ → ℕ) (a c : ℕ)
    (hf : ∀ x ∈ l, f x = if x = a then c else 0) : (l.map f).sum = l.count a * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih (fun y hy => hf y (by simp [hy])),
      hf x (by simp), List.count_cons]
    by_cases h : x = a
    · subst h; simp; ring
    · simp [h]

/-- Part L, auxiliary: `count x (L (n + 1))` is the sum over `λ ∈ L n` of `count x (Vdot λ)`. -/
lemma count_L_succ (x n : ℕ) :
    (L (n + 1)).count x = ((L n).map (fun lam => (Vdot lam).count x)).sum := by
  rw [L_succ, List.count_flatMap]
  rfl

/-! ### (M3) -/

/-- **(M3)** `λ ∈ L 0 ↔ λ = 0`. -/
theorem mem_L_zero (lam : ℕ) : lam ∈ L 0 ↔ lam = 0 := by simp [L_zero]

/-- **(M3)** support: for `n ≥ 1`, every `λ ∈ L n` has `1 ≤ λ ≤ n` and `λ ≡ n (mod 2)`. -/
theorem M3 (n : ℕ) (hn : 1 ≤ n) : ∀ lam ∈ L n, 1 ≤ lam ∧ lam ≤ n ∧ lam % 2 = n % 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro μ hμ
    rw [L_succ, List.mem_flatMap] at hμ
    obtain ⟨lam, hlam, hμ⟩ := hμ
    have h1 := mem_Vdot lam μ hμ
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [mem_L_zero] at hlam; subst hlam; omega
    · have h2 := ih hpos lam hlam
      omega

/-- (M3), consequence: every `λ ∈ L n` has `λ ≤ n` (for all `n`, including `n = 0`). -/
theorem le_of_mem_L (n : ℕ) : ∀ lam ∈ L n, lam ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · intro lam h; rw [mem_L_zero] at h; omega
  · intro lam h; exact (M3 n hpos lam h).2.1

/-! ### (M4) -/

/-- (M4), general form: a list of natural numbers all `< k` is a permutation of
`(List.range k).flatMap (fun a => List.replicate (l.count a) a)`. -/
theorem perm_flatMap_replicate (l : List ℕ) (k : ℕ) (hl : ∀ x ∈ l, x < k) :
    l.Perm ((List.range k).flatMap (fun a => List.replicate (l.count a) a)) := by
  rw [List.perm_iff_count]
  intro b
  rw [List.count_flatMap]
  have : ((List.range k).map (List.count b ∘ fun a => List.replicate (l.count a) a)).sum =
      (List.range k).count b * l.count b := by
    apply sum_map_eq_count_mul
    intro x _
    simp only [Function.comp_apply, List.count_replicate]
    by_cases h : x = b
    · subst h; simp
    · simp [h]
  rw [this]
  by_cases hb : b < k
  · rw [List.count_eq_one_of_mem (List.nodup_range) (List.mem_range.mpr hb), one_mul]
  · have hb' : l.count b = 0 := List.count_eq_zero.mpr (fun h => hb (hl b h))
    rw [hb', mul_zero]

/-- **(M4)** `L n` is a permutation of
`(List.range (n + 1)).flatMap (fun λ => List.replicate (m λ n) λ)`. -/
theorem M4 (n : ℕ) :
    (L n).Perm ((List.range (n + 1)).flatMap (fun lam => List.replicate (m lam n) lam)) :=
  perm_flatMap_replicate (L n) (n + 1) (fun x hx => Nat.lt_succ_of_le (le_of_mem_L n x hx))

/-! ### Part L — Lemma 3.7 -/

/-- **(L1)** (Lemma 3.7) `m 0 n = 0` for `n ≥ 1`. -/
theorem L1 (n : ℕ) (hn : 1 ≤ n) : m 0 n = 0 := by
  unfold m
  rw [List.count_eq_zero]
  intro h
  have := (M3 n hn 0 h).1
  omega

/-- (L2), general form: `m n n = 1` for every `n` (including `n = 0`). -/
theorem m_self (n : ℕ) : m n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold m at *
    rw [count_L_succ, sum_map_eq_count_mul (L n) _ n 1, ih]
    intro lam hlam
    have hle := le_of_mem_L n lam hlam
    by_cases h : lam = n
    · subst h; rw [if_pos rfl, count_succ_Vdot]
    · rw [if_neg h, List.count_eq_zero]
      intro hm
      have := (mem_Vdot lam _ hm).2.1
      omega

/-- **(L2)** (Lemma 3.7) `m n n = 1` for `n ≥ 1`. The hypothesis `1 ≤ n` is unused: `m_self`
proves it for every `n`. -/
theorem L2 (n : ℕ) (_hn : 1 ≤ n) : m n n = 1 := m_self n

/-- Lemma 3.7, auxiliary recursion: `m 2 (n + 1) = m 1 n`. -/
theorem m_two_succ (n : ℕ) : m 2 (n + 1) = m 1 n := by
  unfold m
  rw [count_L_succ, sum_map_eq_count_mul (L n) _ 1 1 (fun x _ => count_two_Vdot x), mul_one]

/-- Lemma 3.7, auxiliary recursion: `m 1 (n + 1) = m 0 n + 2 m 2 n`. -/
theorem m_one_succ (n : ℕ) : m 1 (n + 1) = m 0 n + 2 * m 2 n := by
  unfold m
  rw [count_L_succ]
  simp_rw [count_one_Vdot]
  rw [List.sum_map_add, sum_map_eq_count_mul (L n) _ 0 1 (fun _ _ => rfl),
    sum_map_eq_count_mul (L n) _ 2 2 (fun _ _ => rfl)]
  ring

/-- Lemma 3.7, auxiliary: `m 1 (2k + 1) = 2 ^ k`. -/
theorem m_one_odd (k : ℕ) : m 1 (2 * k + 1) = 2 ^ k := by
  induction k with
  | zero => rw [m_one_succ]; rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by ring, m_one_succ, L1 _ (by omega),
      m_two_succ, ih]
    ring

/-- **(L3)** (Lemma 3.7) `m 1 n = 2 ^ ((n − 1) / 2)` for odd `n ≥ 1`. The hypothesis `1 ≤ n`
is unused (it follows from oddness). -/
theorem L3 (n : ℕ) (_hn : 1 ≤ n) (hodd : n % 2 = 1) : m 1 n = 2 ^ ((n - 1) / 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  rw [m_one_odd]; congr 1; omega

/-- **(L4)** (Lemma 3.7) `m 2 n = 2 ^ ((n − 2) / 2)` for even `n ≥ 1`. -/
theorem L4 (n : ℕ) (hn : 1 ≤ n) (heven : n % 2 = 0) : m 2 n = 2 ^ ((n - 2) / 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨n / 2 - 1, by omega⟩
  rw [m_two_succ, m_one_odd]; congr 1; omega

end FamDec
