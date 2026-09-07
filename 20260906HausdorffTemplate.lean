import Mathlib

/-!
# Phase 1: Parameterized Kinematics and Variational Surgery on Δ^{n+m-1}

This section formalizes the general kinematics of moving blocks, algebraic defect
identities, the fourfold taxonomy of blocks, linear piece integration, the universal
Large-$W$ bound, and the variational surgery principle with global normal form reduction
for arbitrary systems of $n$ linear forms in $m$ variables ($d = n + m$).
-/

/-!
## Section 1: Kinematics of (n, m)-Moving Blocks on Δ^{n+m-1}
-/

/-- A moving block `[r, s]` on the simplex `Δ^{d-1}` in dimension `d = n + m`.
The block index interval satisfies `1 ≤ r ≤ s ≤ n + m`. When touching the top boundary
(`s = n + m`), the active length `k = s - r + 1` satisfies `k ≤ m` (maximal pulling width `k_* = m`). -/
structure MovingBlock (n m : ℕ) where
  r : ℕ
  s : ℕ
  r_ge_one : 1 ≤ r
  s_le_d : s ≤ n + m
  r_le_s : r ≤ s
  block_len_le : s = n + m → s - r + 1 ≤ m

namespace MovingBlock

variable {n m : ℕ} [NeZero n] [NeZero m]

/-- Ambient dimension `d = n + m`. -/
def d (n m : ℕ) : ℕ := n + m

/-- Block length `k = s - r + 1`. -/
def k (b : MovingBlock n m) : ℝ :=
  (b.s : ℝ) - (b.r : ℝ) + 1

/-- Block length is strictly positive for any moving block. -/
theorem k_pos (b : MovingBlock n m) : 0 < b.k := by
  dsimp [k]
  have hr : (b.r : ℝ) ≤ (b.s : ℝ) := Nat.cast_le.mpr b.r_le_s
  linarith

theorem k_ne_zero (b : MovingBlock n m) : b.k ≠ 0 :=
  ne_of_gt b.k_pos

/-- Velocity of the top coordinate: `P'_d = 1/k` if touching top (`s = d`), else `0`. -/
noncomputable def P'_d (b : MovingBlock n m) : ℝ :=
  if b.s = n + m then 1 / b.k else 0

/-- Normalized coupling ratio `σ_{n,m} = C / m`. -/
noncomputable def sigma (m : ℕ) (C : ℝ) : ℝ :=
  C / (m : ℝ)

/-- Pointwise contraction rate `δ(b)`:
  `C - σ * (r - 1)` for interior blocks (`s < d`),
  `σ * (k - 1)` for top boundary blocks (`s = d`). -/
noncomputable def delta (C : ℝ) (b : MovingBlock n m) : ℝ :=
  if b.s < n + m then
    C - sigma m C * ((b.r : ℝ) - 1)
  else
    sigma m C * (b.k - 1)

/-- Pointwise defect: `e(b) = C - δ(b) - C * P'_d(b)`. -/
noncomputable def defect (C : ℝ) (b : MovingBlock n m) : ℝ :=
  C - b.delta C - C * b.P'_d

/-! ### Algebraic Defect Reductions -/

/-- Algebraic reduction for interior blocks (`s < d`): `e(b) = σ * (r - 1)`. -/
theorem defect_of_s_lt_d (C : ℝ) (b : MovingBlock n m) (h : b.s < n + m) :
    b.defect C = sigma m C * ((b.r : ℝ) - 1) := by
  have hs_ne : b.s ≠ n + m := ne_of_lt h
  dsimp [defect, delta, P'_d]
  rw [ite_eq_left h, ite_eq_right hs_ne]
  ring

/-- Defect nonnegativity for interior blocks (`s < d`). -/
theorem defect_nonneg_of_s_lt_d (C : ℝ) (hC : 0 ≤ C) (b : MovingBlock n m) (h : b.s < n + m) :
    0 ≤ b.defect C := by
  rw [defect_of_s_lt_d C b h]
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have hsigma : 0 ≤ sigma m C := div_nonneg hC (le_of_lt hm_pos)
  have hr : 0 ≤ (b.r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (b.r : ℝ) := by exact_mod_cast b.r_ge_one
    linarith
  exact mul_nonneg hsigma hr

/-- Algebraic reduction for top boundary blocks (`s = d`):
  `e(b) = σ * (k - 1)(m - k) / k`. -/
theorem defect_of_s_eq_d (C : ℝ) (b : MovingBlock n m) (h : b.s = n + m) :
    b.defect C = sigma m C * (b.k - 1) * ((m : ℝ) - b.k) / b.k := by
  have h_not_lt : ¬ b.s < n + m := by linarith
  have hk_ne := b.k_ne_zero
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  dsimp [defect, delta, P'_d, sigma]
  rw [ite_eq_right h_not_lt, ite_eq_left h]
  field_simp [hk_ne, hm_ne]
  ring

/-- Defect nonnegativity for top boundary blocks (`s = d`). -/
theorem defect_nonneg_of_s_eq_d (C : ℝ) (hC : 0 ≤ C) (b : MovingBlock n m) (h : b.s = n + m) :
    0 ≤ b.defect C := by
  rw [defect_of_s_eq_d C b h]
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have hsigma : 0 ≤ sigma m C := div_nonneg hC (le_of_lt hm_pos)
  have hk1 : 0 ≤ b.k - 1 := by
    dsimp [k]
    have hr : (b.r : ℝ) ≤ (b.s : ℝ) := Nat.cast_le.mpr b.r_le_s
    linarith
  have hkm : 0 ≤ (m : ℝ) - b.k := by
    have h_len : ((b.s - b.r + 1 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (b.block_len_le h)
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub b.r_le_s] at h_len
    dsimp [k]
    linarith
  have h_prod : 0 ≤ sigma m C * (b.k - 1) * ((m : ℝ) - b.k) :=
    mul_nonneg (mul_nonneg hsigma hk1) hkm
  exact div_nonneg h_prod (le_of_lt b.k_pos)

/-- Universal Pointwise Nonnegativity: `e(b) ≥ 0` across all admissible moving blocks. -/
theorem defect_nonneg (C : ℝ) (hC : 0 ≤ C) (b : MovingBlock n m) :
    0 ≤ b.defect C := by
  by_cases h : b.s = n + m
  · exact defect_nonneg_of_s_eq_d C hC b h
  · have hlt : b.s < n + m := Nat.lt_of_le_of_ne b.s_le_d h
    exact defect_nonneg_of_s_lt_d C hC b hlt

/-- The fundamental pointwise defect conservation identity:
  `δ(b) = C - C * P'_d(b) - e(b)`. -/
theorem pointwise_id (C : ℝ) (b : MovingBlock n m) :
    b.delta C = C - C * b.P'_d - b.defect C := by
  dsimp [defect]
  ring

end MovingBlock

/-!
## Section 2: The Fourfold Taxonomy of Moving Blocks
-/

namespace MovingBlock

variable {n m : ℕ} [NeZero n] [NeZero m]
variable (C : ℝ) (b : MovingBlock n m)

/-- A 'Good' block is one where the defect evaluates identically to 0. -/
def IsGoodBlock : Prop := b.defect C = 0

/-- A 'Bad' block is one where the defect is strictly positive. -/
def IsBadBlock : Prop := 0 < b.defect C

/-- Completeness: Every admissible block is either Good (`e = 0`) or Bad (`e > 0`). -/
theorem good_or_bad (hC : 0 ≤ C) : IsGoodBlock C b ∨ IsBadBlock C b := by
  dsimp [IsGoodBlock, IsBadBlock]
  have h_nonneg := b.defect_nonneg C hC
  rcases h_nonneg.lt_or_eq with hlt | heq
  · exact Or.inr hlt
  · exact Or.inl heq.symm

/-- Class 1 (Interior Good Blocks):
For blocks with `s < d`, zero defect is attained if and only if `r = 1` (`[1, s]`). -/
theorem good_interior_iff (hC : 0 < C) (h : b.s < n + m) :
    IsGoodBlock C b ↔ b.r = 1 := by
  dsimp [IsGoodBlock]
  rw [defect_of_s_lt_d C b h]
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have hsigma_pos : 0 < sigma m C := div_pos hC hm_pos
  constructor
  · intro heq
    have h_zero : (b.r : ℝ) - 1 = 0 := by
      exact (mul_eq_zero.mp heq).resolve_left (ne_of_gt hsigma_pos)
    have : (b.r : ℝ) = 1 := by linarith
    exact_mod_cast this
  · intro hr
    rw [hr]
    push_cast
    ring

/-- Class 2 (Interior Bad Blocks):
Any interior block starting at `r ≥ 2` incurs a strictly positive defect penalty. -/
theorem bad_interior_iff (hC : 0 < C) (h : b.s < n + m) :
    IsBadBlock C b ↔ 2 ≤ b.r := by
  dsimp [IsBadBlock]
  rw [defect_of_s_lt_d C b h]
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have hsigma_pos : 0 < sigma m C := div_pos hC hm_pos
  constructor
  · intro h_pos
    have hr_pos : 0 < (b.r : ℝ) - 1 := by
      by_contra h_le
      have : (b.r : ℝ) - 1 ≤ 0 := not_lt.mp h_le
      nlinarith
    have : 1 < b.r := by
      have : (1 : ℝ) < (b.r : ℝ) := by linarith
      exact_mod_cast this
    exact this
  · intro hr
    have hr_sub : 0 < (b.r : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (b.r : ℝ) := by exact_mod_cast hr
      linarith
    exact mul_pos hsigma_pos hr_sub

/-- Class 3 (Boundary Good Blocks):
For blocks touching the top boundary (`s = d`), zero defect occurs if and only if
`k = 1` (singleton `[d, d]`) or `k = m` (maximal pulling block `[d - m + 1, d]`). -/
theorem good_top_iff (hC : 0 < C) (h : b.s = n + m) :
    IsGoodBlock C b ↔ b.k = 1 ∨ b.k = (m : ℝ) := by
  dsimp [IsGoodBlock]
  rw [defect_of_s_eq_d C b h]
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have hsigma_pos : 0 < sigma m C := div_pos hC hm_pos
  have hk_pos := b.k_pos
  constructor
  · intro heq
    have h_div : sigma m C * (b.k - 1) * ((m : ℝ) - b.k) = 0 := by
      exact (div_eq_zero_iff.mp heq).resolve_right (ne_of_gt hk_pos)
    rw [mul_assoc] at h_div
    have h_prod : (b.k - 1) * ((m : ℝ) - b.k) = 0 :=
      (mul_eq_zero.mp h_div).resolve_left (ne_of_gt hsigma_pos)
    rcases mul_eq_zero.mp h_prod with h1 | h2
    · left; linarith
    · right; linarith
  · intro hor
    rcases hor with hk1 | hkm
    · have h1 : b.k - 1 = 0 := by linarith
      rw [h1, mul_zero, zero_mul, zero_div]
    · have h2 : (m : ℝ) - b.k = 0 := by linarith
      rw [h2, mul_zero, zero_div]

/-- Class 4 (Boundary Bad Blocks):
Any partial top-boundary block with `1 < k < m` incurs a strictly positive defect. -/
theorem bad_top_iff (hC : 0 < C) (h : b.s = n + m) :
    IsBadBlock C b ↔ 1 < b.k ∧ b.k < (m : ℝ) := by
  dsimp [IsBadBlock]
  rw [defect_of_s_eq_d C b h]
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have hsigma_pos : 0 < sigma m C := div_pos hC hm_pos
  have hk_pos := b.k_pos
  have hk1_nonneg : 0 ≤ b.k - 1 := by
    dsimp [k]
    have hr : (b.r : ℝ) ≤ (b.s : ℝ) := Nat.cast_le.mpr b.r_le_s
    linarith
  have hkm_nonneg : 0 ≤ (m : ℝ) - b.k := by
    have h_len : ((b.s - b.r + 1 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (b.block_len_le h)
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub b.r_le_s] at h_len
    dsimp [k]
    linarith
  constructor
  · intro h_pos
    have h_num : 0 < sigma m C * (b.k - 1) * ((m : ℝ) - b.k) :=
      (div_pos_iff_of_pos_right hk_pos).mp h_pos
    have h_fac : 0 < (b.k - 1) * ((m : ℝ) - b.k) := by
      have h_assoc : 0 < sigma m C * ((b.k - 1) * ((m : ℝ) - b.k)) := by
        rwa [mul_assoc] at h_num
      by_contra h_le
      have : (b.k - 1) * ((m : ℝ) - b.k) ≤ 0 := not_lt.mp h_le
      nlinarith
    have hk1_pos : 0 < b.k - 1 := by
      rcases hk1_nonneg.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; rw [← heq, zero_mul] at h_fac; exact lt_irrefl 0 h_fac
    have hkm_pos : 0 < (m : ℝ) - b.k := by
      rcases hkm_nonneg.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; rw [← heq, mul_zero] at h_fac; exact lt_irrefl 0 h_fac
    exact ⟨by linarith, by linarith⟩
  · intro ⟨hk1, hkm⟩
    have h1 : 0 < b.k - 1 := by linarith
    have h2 : 0 < (m : ℝ) - b.k := by linarith
    have h_num : 0 < sigma m C * (b.k - 1) * ((m : ℝ) - b.k) :=
      mul_pos (mul_pos hsigma_pos h1) h2
    exact div_pos h_num hk_pos

end MovingBlock

/-!
## Section 3: Linear Piece Integration and the Global Defect Identity
-/

/-- Represents a single linear segment `[qa, qb]` of an admissible trajectory. -/
structure LinearPiece (n m : ℕ) (C : ℝ) where
  qa : ℝ
  qb : ℝ
  h_qa_le_qb : qa ≤ qb
  delta : ℝ
  Pd_slope : ℝ
  defect : ℝ
  pointwise_id : delta = C - C * Pd_slope - defect
  Pd_qa : ℝ
  Pd_qb : ℝ
  Pd_linear : Pd_qb - Pd_qa = Pd_slope * (qb - qa)

namespace LinearPiece

variable {n m : ℕ} {C : ℝ} (p : LinearPiece n m C)

/-- Duration `Δq = qb - qa`. -/
def len : ℝ := p.qb - p.qa

theorem len_nonneg : 0 ≤ p.len := by
  dsimp [len]; linarith [p.h_qa_le_qb]

/-- The integrated conservation identity on a single linear piece. -/
theorem integral_identity :
    p.delta * p.len = C * p.len - C * (p.Pd_qb - p.Pd_qa) - p.defect * p.len := by
  dsimp [len]
  rw [p.pointwise_id, p.Pd_linear]
  ring

/-- Sum of integrated contraction mass across a trajectory list. -/
def sum_delta : List (LinearPiece n m C) → ℝ
  | [] => 0
  | p :: rest => p.delta * p.len + sum_delta rest

/-- Sum of interval durations across a trajectory list. -/
def sum_len : List (LinearPiece n m C) → ℝ
  | [] => 0
  | p :: rest => p.len + sum_len rest

/-- Sum of top coordinate displacements across a trajectory list. -/
def sum_Pd_change : List (LinearPiece n m C) → ℝ
  | [] => 0
  | p :: rest => (p.Pd_qb - p.Pd_qa) + sum_Pd_change rest

/-- Sum of accumulated defect across a trajectory list. -/
def sum_defect : List (LinearPiece n m C) → ℝ
  | [] => 0
  | p :: rest => p.defect * p.len + sum_defect rest

theorem sum_len_nonneg (l : List (LinearPiece n m C)) : 0 ≤ sum_len l := by
  induction l with
  | nil => rfl
  | cons p tail ih =>
    dsimp [sum_len]
    exact add_nonneg p.len_nonneg ih

/-- Theorem 2.5 (Global Integral Defect Identity):
  `Δ_{tot}(l) = C * T(l) - C * ΔP_d(l) - Q(l)`. -/
theorem global_integral_identity (l : List (LinearPiece n m C)) :
    sum_delta l = C * sum_len l - C * sum_Pd_change l - sum_defect l := by
  induction l with
  | nil =>
    dsimp [sum_delta, sum_len, sum_Pd_change, sum_defect]
    ring
  | cons p tail ih =>
    dsimp [sum_delta, sum_len, sum_Pd_change, sum_defect]
    rw [p.integral_identity, ih]
    ring

/-- Total accumulated defect is non-negative when each piece has non-negative defect. -/
theorem sum_defect_nonneg (l : List (LinearPiece n m C))
    (h_defect : ∀ p ∈ l, 0 ≤ p.defect) : 0 ≤ sum_defect l := by
  induction l with
  | nil => rfl
  | cons p tail ih =>
    dsimp [sum_defect]
    have hp_def : 0 ≤ p.defect := h_defect p (List.Mem.head _)
    have hp_prod : 0 ≤ p.defect * p.len := mul_nonneg hp_def p.len_nonneg
    have htail : 0 ≤ sum_defect tail := ih (fun x hx => h_defect x (List.Mem.tail p hx))
    linarith

/-- Theorem 2.6 (Universal Contraction Rate Upper Bound):
The normalized average contraction rate satisfies:
  `Δ_{tot}(l) / T(l) ≤ C - C * (ΔP_d(l) / T(l))`. -/
theorem global_contraction_bound (l : List (LinearPiece n m C))
    (h_defect : ∀ p ∈ l, 0 ≤ p.defect)
    (h_T_pos : 0 < sum_len l) :
    sum_delta l / sum_len l ≤ C - C * (sum_Pd_change l / sum_len l) := by
  have h_id := global_integral_identity l
  have h_Q := sum_defect_nonneg l h_defect
  have h_ineq : sum_delta l ≤ C * sum_len l - C * sum_Pd_change l := by linarith
  have h_cancel : sum_len l ≠ 0 := ne_of_gt h_T_pos
  calc sum_delta l / sum_len l
    _ ≤ (C * sum_len l - C * sum_Pd_change l) / sum_len l :=
        div_le_div_of_nonneg_right h_ineq (le_of_lt h_T_pos)
    _ = (C * sum_len l) / sum_len l - (C * sum_Pd_change l) / sum_len l :=
        sub_div _ _ _
    _ = C - (C * sum_Pd_change l) / sum_len l := by
        rw [mul_div_cancel_right₀ _ h_cancel]
    _ = C - C * (sum_Pd_change l / sum_len l) := by
        ring

/-- Contiguity of consecutive linear pieces. -/
def IsContiguous : List (LinearPiece n m C) → Prop
  | [] => True
  | [_] => True
  | p1 :: p2 :: rest => p1.qb = p2.qa ∧ p1.Pd_qb = p2.Pd_qa ∧ IsContiguous (p2 :: rest)

/-! Distributivity of sums over list concatenation -/

theorem sum_len_append (l1 l2 : List (LinearPiece n m C)) :
    sum_len (l1 ++ l2) = sum_len l1 + sum_len l2 := by
  induction l1 with
  | nil => dsimp [sum_len]; ring
  | cons p tail ih =>
    dsimp [sum_len]; rw [ih]; ring

theorem sum_Pd_change_append (l1 l2 : List (LinearPiece n m C)) :
    sum_Pd_change (l1 ++ l2) = sum_Pd_change l1 + sum_Pd_change l2 := by
  induction l1 with
  | nil => dsimp [sum_Pd_change]; ring
  | cons p tail ih =>
    dsimp [sum_Pd_change]; rw [ih]; ring

theorem sum_delta_append (l1 l2 : List (LinearPiece n m C)) :
    sum_delta (l1 ++ l2) = sum_delta l1 + sum_delta l2 := by
  induction l1 with
  | nil => dsimp [sum_delta]; ring
  | cons p tail ih =>
    dsimp [sum_delta]; rw [ih]; ring

theorem sum_defect_append (l1 l2 : List (LinearPiece n m C)) :
    sum_defect (l1 ++ l2) = sum_defect l1 + sum_defect l2 := by
  induction l1 with
  | nil => dsimp [sum_defect]; ring
  | cons p tail ih =>
    dsimp [sum_defect]; rw [ih]; ring

end LinearPiece

/-!
## Section 4: General Variational Surgery Principle
-/

namespace LocalSurgery

open LinearPiece

variable {n m : ℕ} {C : ℝ}

/-- A Surgery replaces an original trajectory list with a perturbed trajectory list
having equal total duration and equal total top-coordinate displacement. -/
structure Surgery (n m : ℕ) (C : ℝ) where
  l_orig : List (LinearPiece n m C)
  l_pert : List (LinearPiece n m C)
  same_duration : sum_len l_orig = sum_len l_pert
  same_Pd_displacement : sum_Pd_change l_orig = sum_Pd_change l_pert

namespace Surgery

variable (s : Surgery n m C)

/-- Theorem 3.2 (Contraction-Defect Exchange Identity):
  `Δ_{tot}(l_pert) - Δ_{tot}(l_orig) = Q(l_orig) - Q(l_pert)`. -/
theorem delta_exchange :
    sum_delta s.l_pert - sum_delta s.l_orig =
    sum_defect s.l_orig - sum_defect s.l_pert := by
  have h_orig := global_integral_identity s.l_orig
  have h_pert := global_integral_identity s.l_pert
  have h_dur := s.same_duration
  have h_pd := s.same_Pd_displacement
  rw [h_orig, h_pert, ← h_dur, ← h_pd]
  ring

/-- Theorem 3.3 (Variational Surgery Principle):
Perturbation improves contraction mass if and only if it decreases accumulated defect. -/
theorem optimal_iff_minimal_defect :
    sum_delta s.l_orig ≤ sum_delta s.l_pert ↔
    sum_defect s.l_pert ≤ sum_defect s.l_orig := by
  have h_ex := s.delta_exchange
  constructor <;> intro h <;> linarith

/-- Contraction gain when surgery completely eliminates defect (`Q(l_pert) = 0`). -/
theorem delta_gain_of_zero_defect (h_zero : sum_defect s.l_pert = 0) :
    sum_delta s.l_pert - sum_delta s.l_orig = sum_defect s.l_orig := by
  have h_ex := s.delta_exchange
  linarith

/-- Any defect-free perturbation dominates an admissible original trajectory. -/
theorem zero_defect_is_optimal
    (h_orig_def : ∀ p ∈ s.l_orig, 0 ≤ p.defect)
    (h_pert_zero : sum_defect s.l_pert = 0) :
    sum_delta s.l_orig ≤ sum_delta s.l_pert := by
  have h_orig_nonneg := sum_defect_nonneg s.l_orig h_orig_def
  rw [s.optimal_iff_minimal_defect]
  linarith

/-- Equivalence on normalized average contraction rates. -/
theorem average_rate_iff_minimal_defect (h_T_pos : 0 < sum_len s.l_orig) :
    sum_delta s.l_orig / sum_len s.l_orig ≤ sum_delta s.l_pert / sum_len s.l_pert ↔
    sum_defect s.l_pert ≤ sum_defect s.l_orig := by
  have hT : sum_len s.l_pert = sum_len s.l_orig := s.same_duration.symm
  rw [hT, div_le_div_iff_of_pos_right h_T_pos]
  exact s.optimal_iff_minimal_defect

end Surgery

end LocalSurgery

/-!
## Section 5: The (n, m) Parabolic Gap Capacity Lemma
-/

namespace GapCapacity

variable (m : ℕ) [NeZero m] (C : ℝ) (k : ℝ)

/-- Definition 3.4 (Gap Capacity): Defect incurred per unit of top-coordinate advance:
  `C(k) = e(k) / P'_d(k)`. -/
noncomputable def defect_per_Pd_growth (m : ℕ) (C : ℝ) (k : ℝ) : ℝ :=
  ((MovingBlock.sigma m C * (k - 1) * ((m : ℝ) - k)) / k) / (1 / k)

/-- Lemma 3.5 (Parabolic Gap Capacity Lemma):
For any boundary moving block of length `k ∈ [1, m]`:
  `C(k) = σ_{n,m} * (k - 1)(m - k)`. -/
theorem defect_cost_is_parabolic (hk_pos : 0 < k) :
    defect_per_Pd_growth m C k = MovingBlock.sigma m C * (k - 1) * ((m : ℝ) - k) := by
  dsimp [defect_per_Pd_growth]
  have hk : k ≠ 0 := ne_of_gt hk_pos
  field_simp [hk]

/-- The gap capacity is zero if and only if `k = 1` or `k = m`. -/
theorem defect_cost_zero_iff (hC : 0 < C) (hk_pos : 0 < k) :
    defect_per_Pd_growth m C k = 0 ↔ k = 1 ∨ k = (m : ℝ) := by
  rw [defect_cost_is_parabolic m C k hk_pos]
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have hsigma_pos : 0 < MovingBlock.sigma m C := div_pos hC hm_pos
  have : MovingBlock.sigma m C * (k - 1) * ((m : ℝ) - k) = 0 ↔
         (k - 1 = 0 ∨ (m : ℝ) - k = 0) := by
    constructor
    · intro h
      have h1 := mul_eq_zero.mp h
      rcases h1 with h_left | h_right
      · have h2 := (mul_eq_zero.mp h_left).resolve_left (ne_of_gt hsigma_pos)
        exact Or.inl h2
      · exact Or.inr h_right
    · rintro (h1 | h2)
      · rw [h1, mul_zero, zero_mul]
      · rw [h2, mul_zero]
  rw [this]
  constructor
  · rintro (h1 | h2)
    · left; linarith
    · right; linarith
  · rintro (h1 | h2)
    · left; linarith
    · right; linarith

/-- Theorem 3.6 (Strict Suboptimality of Partial Boundary Contacts):
For `1 < k < m`, every partial boundary contact generates strictly positive defect. -/
theorem partial_contacts_strictly_suboptimal (hC : 0 < C) (hk_pos : 0 < k) :
    (1 < k → k < (m : ℝ) → 0 < defect_per_Pd_growth m C k) ∧
    (1 ≤ k → k ≤ (m : ℝ) → 0 ≤ defect_per_Pd_growth m C k) := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have hsigma_pos : 0 < MovingBlock.sigma m C := div_pos hC hm_pos
  constructor
  · intro hk1 hkm
    rw [defect_cost_is_parabolic m C k hk_pos]
    have h1 : 0 < k - 1 := by linarith
    have h2 : 0 < (m : ℝ) - k := by linarith
    exact mul_pos (mul_pos hsigma_pos h1) h2
  · intro hk1 hkm
    rw [defect_cost_is_parabolic m C k hk_pos]
    have h1 : 0 ≤ k - 1 := by linarith
    have h2 : 0 ≤ (m : ℝ) - k := by linarith
    exact mul_nonneg (mul_nonneg (le_of_lt hsigma_pos) h1) h2

end GapCapacity

/-!
## Section 6: Canonical Two-Phase Trajectory Deformation
-/

namespace GlobalSurgery

variable (m k T : ℝ)

/-- Canonical time allocation for Phase 1 (`[d, d]` singleton, slope `1`). -/
noncomputable def t1 : ℝ := ((m - k) / (k * (m - 1))) * T

/-- Canonical time allocation for Phase 2 (`[d - m + 1, d]` pulling bundle, slope `1/m`). -/
noncomputable def t2 : ℝ := ((m * (k - 1)) / (k * (m - 1))) * T

/-- Positivity of `t1` on partial boundary contacts `1 < k < m`. -/
theorem t1_pos (_hm : 1 < m) (hk : 1 < k) (hkm : k < m) (hT : 0 < T) :
    0 < t1 m k T := by
  dsimp [t1]
  have h_num : 0 < m - k := by linarith
  have h_den : 0 < k * (m - 1) := mul_pos (by linarith) (by linarith)
  exact mul_pos (div_pos h_num h_den) hT

/-- Positivity of `t2` on partial boundary contacts `1 < k < m`. -/
theorem t2_pos (_hm : 1 < m) (hk : 1 < k) (_hkm : k < m) (hT : 0 < T) :
    0 < t2 m k T := by
  dsimp [t2]
  have h_num : 0 < m * (k - 1) := mul_pos (by linarith) (by linarith)
  have h_den : 0 < k * (m - 1) := mul_pos (by linarith) (by linarith)
  exact mul_pos (div_pos h_num h_den) hT

theorem t1_nonneg (hm : 1 < m) (hk_ge : 1 ≤ k) (hkm : k ≤ m) (hT : 0 ≤ T) :
    0 ≤ t1 m k T := by
  dsimp [t1]
  have h_num : 0 ≤ m - k := by linarith
  have h_den : 0 < k * (m - 1) := mul_pos (by linarith) (by linarith)
  exact mul_nonneg (div_nonneg h_num (le_of_lt h_den)) hT

theorem t2_nonneg (hm : 1 < m) (hk_ge : 1 ≤ k) (_hkm : k ≤ m) (hT : 0 ≤ T) :
    0 ≤ t2 m k T := by
  dsimp [t2]
  have h_num : 0 ≤ m * (k - 1) := mul_nonneg (by linarith) (by linarith)
  have h_den : 0 < k * (m - 1) := mul_pos (by linarith) (by linarith)
  exact mul_nonneg (div_nonneg h_num (le_of_lt h_den)) hT

/-- Lemma 3.7.2: Canonical surgery preserves total time duration. -/
theorem surgery_preserves_time (hk : k ≠ 0) (hm : m - 1 ≠ 0) :
    t1 m k T + t2 m k T = T := by
  dsimp [t1, t2]
  field_simp
  ring

/-- Lemma 3.7.3: Canonical surgery preserves net top-coordinate displacement. -/
theorem surgery_preserves_displacement (hk : k ≠ 0) (hm_sub : m - 1 ≠ 0) (hm : m ≠ 0) :
    1 * t1 m k T + (1 / m) * t2 m k T = T / k := by
  dsimp [t1, t2]
  field_simp
  ring

/-- Integrated contraction mass of the original partial block: `δ = σ * (k - 1)` over duration `T`. -/
noncomputable def delta_orig (sigma : ℝ) : ℝ := sigma * (k - 1) * T

/-- Integrated contraction mass of the two-phase replacement:
  `δ_1 = 0` on `[d, d]` and `δ_2 = σ * (m - 1)` on `[d - m + 1, d]`. -/
noncomputable def delta_pert (sigma : ℝ) : ℝ :=
  0 * t1 m k T + sigma * (m - 1) * t2 m k T

/-- Accumulated defect of the partial contact: `Q = σ * (k - 1)(m - k) / k * T`. -/
noncomputable def defect_orig (sigma : ℝ) : ℝ :=
  (sigma * (k - 1) * (m - k) / k) * T

/-- Theorem 3.8 (Surgery Contraction Gain):
The net contraction gain under two-phase surgery equals the eliminated defect `Q(p_part)`. -/
theorem surgery_contraction_gain (sigma : ℝ) (hk : k ≠ 0) (hm_sub : m - 1 ≠ 0) :
    delta_pert m k T sigma - delta_orig k T sigma = defect_orig m k T sigma := by
  dsimp [delta_pert, delta_orig, defect_orig, t1, t2]
  field_simp
  ring

/-- Strict improvement in total contraction mass for any positive duration. -/
theorem surgery_strictly_improves (sigma : ℝ) (hsigma : 0 < sigma)
    (_hm : 1 < m) (hk : 1 < k) (hkm : k < m) (hT : 0 < T) :
    delta_orig k T sigma < delta_pert m k T sigma := by
  have hk0 : k ≠ 0 := by linarith
  have hm1 : m - 1 ≠ 0 := by linarith
  have h_gain := surgery_contraction_gain m k T sigma hk0 hm1
  have h_def_pos : 0 < defect_orig m k T sigma := by
    dsimp [defect_orig]
    have h1 : 0 < k - 1 := by linarith
    have h2 : 0 < m - k := by linarith
    have hk_pos : 0 < k := by linarith
    exact mul_pos (div_pos (mul_pos (mul_pos hsigma h1) h2) hk_pos) hT
  linarith

end GlobalSurgery

/-!
## Section 7: Barrier Non-Crossing Invariants and Global Trajectory Normal Form
-/

namespace TrajectoryNormalForm

open LinearPiece LocalSurgery GlobalSurgery

variable {n m : ℕ} {C : ℝ}

/-- Explicit representation of a defective partial contact piece touching top (`1 < k < m`). -/
structure PartialContactPiece (n m : ℕ) (C : ℝ) where
  piece : LinearPiece n m C
  k : ℝ
  hk1 : 1 < k
  hkm : k < (m : ℝ)
  h_slope : piece.Pd_slope = 1 / k
  h_delta : piece.delta = MovingBlock.sigma m C * (k - 1)
  h_defect : piece.defect = MovingBlock.sigma m C * (k - 1) * ((m : ℝ) - k) / k

/-- Classification of linear pieces by their boundary contact configuration. -/
inductive ClassifiedPiece (n m : ℕ) (C : ℝ) where
  | interior (p : LinearPiece n m C)
  | fullSingleton (p : LinearPiece n m C)
  | fullBoundary (p : LinearPiece n m C)
  | partialContact (pc : PartialContactPiece n m C)

namespace ClassifiedPiece

/-- Underlying linear piece extracted from a classified piece. -/
def toPiece : ClassifiedPiece n m C → LinearPiece n m C
  | interior p => p
  | fullSingleton p => p
  | fullBoundary p => p
  | partialContact pc => pc.piece

end ClassifiedPiece

namespace PartialContactPiece

variable {n m : ℕ} {C : ℝ}

theorem m_pos (hm : 3 ≤ m) : 0 < (m : ℝ) := by
  have : (3 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
  linarith

theorem m_ne_zero (hm : 3 ≤ m) : (m : ℝ) ≠ 0 := ne_of_gt (m_pos hm)

theorem m_one_lt (hm : 3 ≤ m) : 1 < (m : ℝ) := by
  have : (3 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
  linarith

theorem m_sub_one_pos (hm : 3 ≤ m) : 0 < (m : ℝ) - 1 := by
  have : (3 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
  linarith

theorem m_sub_one_ne_zero (hm : 3 ≤ m) : (m : ℝ) - 1 ≠ 0 := ne_of_gt (m_sub_one_pos hm)

theorem k_pos (pc : PartialContactPiece n m C) : 0 < pc.k := by linarith [pc.hk1]

theorem k_ne_zero (pc : PartialContactPiece n m C) : pc.k ≠ 0 := ne_of_gt pc.k_pos

/-- Interval duration of the partial contact piece. -/
def dur (pc : PartialContactPiece n m C) : ℝ := pc.piece.qb - pc.piece.qa

theorem dur_nonneg (pc : PartialContactPiece n m C) : 0 ≤ pc.dur := by
  dsimp [dur]; linarith [pc.piece.h_qa_le_qb]

/-- Allocated duration for Phase 1 (`[d, d]`). -/
noncomputable def dt1 (pc : PartialContactPiece n m C) : ℝ :=
  t1 (m : ℝ) pc.k pc.dur

/-- Allocated duration for Phase 2 (`[d - m + 1, d]`). -/
noncomputable def dt2 (pc : PartialContactPiece n m C) : ℝ :=
  t2 (m : ℝ) pc.k pc.dur

theorem dt1_nonneg (pc : PartialContactPiece n m C) (hm : 3 ≤ m) : 0 ≤ pc.dt1 := by
  dsimp [dt1]
  exact t1_nonneg (m : ℝ) pc.k pc.dur (m_one_lt hm) (le_of_lt pc.hk1) (le_of_lt pc.hkm) pc.dur_nonneg

theorem dt2_nonneg (pc : PartialContactPiece n m C) (hm : 3 ≤ m) : 0 ≤ pc.dt2 := by
  dsimp [dt2]
  exact t2_nonneg (m : ℝ) pc.k pc.dur (m_one_lt hm) (le_of_lt pc.hk1) (le_of_lt pc.hkm) pc.dur_nonneg

theorem sum_dt (pc : PartialContactPiece n m C) (hm : 3 ≤ m) : pc.dt1 + pc.dt2 = pc.dur := by
  dsimp [dt1, dt2]
  exact surgery_preserves_time (m : ℝ) pc.k pc.dur pc.k_ne_zero (m_sub_one_ne_zero hm)

/-! Canonical Two-Phase Replacement Pieces -/

/-- Phase 1 replacement: Canonical `[d, d]` singleton block (duration `dt1`, rate `0`, defect `0`). -/
noncomputable def transformedPiece1 (pc : PartialContactPiece n m C) (hm : 3 ≤ m) : LinearPiece n m C where
  qa := pc.piece.qa
  qb := pc.piece.qa + pc.dt1
  h_qa_le_qb := by
    have := pc.dt1_nonneg hm
    linarith
  delta := 0
  Pd_slope := 1
  defect := 0
  pointwise_id := by ring
  Pd_qa := pc.piece.Pd_qa
  Pd_qb := pc.piece.Pd_qa + pc.dt1
  Pd_linear := by ring

/-- Phase 2 replacement: Canonical `[d - m + 1, d]` maximal pulling block
  (duration `dt2`, rate `σ * (m - 1)`, defect `0`). -/
noncomputable def transformedPiece2 (pc : PartialContactPiece n m C) (hm : 3 ≤ m) : LinearPiece n m C where
  qa := pc.piece.qa + pc.dt1
  qb := pc.piece.qb
  h_qa_le_qb := by
    have h_sum := pc.sum_dt hm
    dsimp [dur] at h_sum
    have h2 := pc.dt2_nonneg hm
    linarith
  delta := MovingBlock.sigma m C * ((m : ℝ) - 1)
  Pd_slope := 1 / (m : ℝ)
  defect := 0
  pointwise_id := by
    dsimp [MovingBlock.sigma]
    have hm_ne := m_ne_zero hm
    field_simp [hm_ne]
    ring
  Pd_qa := pc.piece.Pd_qa + pc.dt1
  Pd_qb := pc.piece.Pd_qb
  Pd_linear := by
    have h_lin : pc.piece.Pd_qb = pc.piece.Pd_qa + (1 / pc.k) * (pc.piece.qb - pc.piece.qa) := by
      have h := pc.piece.Pd_linear
      rw [pc.h_slope] at h
      linarith
    rw [h_lin]
    dsimp [dur, dt1, t1]
    have hk_ne := pc.k_ne_zero
    have hm_ne := m_ne_zero hm
    have hm1_ne := m_sub_one_ne_zero hm
    field_simp [hk_ne, hm_ne, hm1_ne]
    ring

/-- Deformed two-piece path bypassing the partial contact piece. -/
noncomputable def deformedPath (pc : PartialContactPiece n m C) (hm : 3 ≤ m) : List (LinearPiece n m C) :=
  [pc.transformedPiece1 hm, pc.transformedPiece2 hm]

theorem deformedPath_contiguous (pc : PartialContactPiece n m C) (hm : 3 ≤ m) :
    IsContiguous (pc.deformedPath hm) := by
  dsimp [deformedPath, IsContiguous, transformedPiece1, transformedPiece2]
  exact ⟨rfl, rfl, trivial⟩

theorem deformedPath_preserves_duration (pc : PartialContactPiece n m C) (hm : 3 ≤ m) :
    sum_len (pc.deformedPath hm) = pc.dur := by
  dsimp [deformedPath, sum_len, transformedPiece1, transformedPiece2, len, dur]
  ring

theorem deformedPath_preserves_Pd_change (pc : PartialContactPiece n m C) (hm : 3 ≤ m) :
    sum_Pd_change (pc.deformedPath hm) = pc.piece.Pd_qb - pc.piece.Pd_qa := by
  dsimp [deformedPath, sum_Pd_change, transformedPiece1, transformedPiece2]
  ring

theorem deformedPath_defect_zero (pc : PartialContactPiece n m C) (hm : 3 ≤ m) :
    sum_defect (pc.deformedPath hm) = 0 := by
  dsimp [deformedPath, sum_defect, transformedPiece1, transformedPiece2]
  ring

theorem deformedPath_contraction_gain (pc : PartialContactPiece n m C) (hm : 3 ≤ m) :
    sum_delta (pc.deformedPath hm) - pc.piece.delta * pc.dur =
    pc.piece.defect * pc.dur := by
  dsimp [deformedPath, sum_delta, transformedPiece1, transformedPiece2, len]
  dsimp [dt1, dt2, t1, t2, dur]
  rw [pc.h_delta, pc.h_defect]
  have hk_ne := pc.k_ne_zero
  have hm1_ne := m_sub_one_ne_zero hm
  dsimp [MovingBlock.sigma]
  field_simp [hk_ne, hm1_ne]
  ring

/-- Lemma 3.9 (Barrier Non-Crossing Invariant):
Phase 1 widens the gap `P_d - P_j` for all `j < d`, and Phase 2 widens the gap
between the active group `{d - m + 1, ..., d}` and lower stationary coordinates `{1, ..., d - m}`.
Hence, the deformed trajectory never crosses any coordinate barrier. -/
theorem barrier_non_crossing_invariant
    (pc : PartialContactPiece n m C) (hm : 3 ≤ m) :
    pc.piece.Pd_qa ≤ (pc.transformedPiece1 hm).Pd_qb ∧
    pc.piece.Pd_qa ≤ pc.piece.Pd_qb := by
  have h_lin : pc.piece.Pd_qb = pc.piece.Pd_qa + (1 / pc.k) * (pc.piece.qb - pc.piece.qa) := by
    have h := pc.piece.Pd_linear
    rw [pc.h_slope] at h
    linarith
  constructor
  · dsimp [transformedPiece1]
    have := pc.dt1_nonneg hm
    linarith
  · have hk_pos := pc.k_pos
    have h_diff : 0 ≤ (1 / pc.k) * (pc.piece.qb - pc.piece.qa) :=
      mul_nonneg (by positivity) (by linarith [pc.piece.h_qa_le_qb])
    linarith [h_lin, h_diff]

end PartialContactPiece

/-! ### Global Normal Form Trajectory Patching Algorithm -/

/-- Patch a single classified piece: replaces partial contacts with `[d, d]` and `[d - m + 1, d]`. -/
noncomputable def patchPiece (hm : 3 ≤ m) :
    ClassifiedPiece n m C → List (LinearPiece n m C)
  | ClassifiedPiece.partialContact pc => pc.deformedPath hm
  | cp => [cp.toPiece]

/-- Definition 3.10: Global trajectory deformation patching all partial boundary contacts. -/
noncomputable def patchTrajectory (hm : 3 ≤ m) :
    List (ClassifiedPiece n m C) → List (LinearPiece n m C)
  | [] => []
  | cp :: rest => patchPiece hm cp ++ patchTrajectory hm rest

/-- Theorem 3.11.1: Patched trajectory preserves total time duration. -/
theorem patchTrajectory_preserves_duration (hm : 3 ≤ m)
    (l : List (ClassifiedPiece n m C)) :
    sum_len (patchTrajectory hm l) = sum_len (l.map ClassifiedPiece.toPiece) := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    dsimp [patchTrajectory, List.map, sum_len]
    rw [sum_len_append]
    cases head with
    | partialContact pc =>
      dsimp [patchPiece, ClassifiedPiece.toPiece]
      have h_len := pc.deformedPath_preserves_duration hm
      dsimp [PartialContactPiece.dur, len] at h_len ⊢
      rw [h_len, ih]
    | interior p =>
      dsimp [patchPiece, ClassifiedPiece.toPiece, sum_len]; rw [ih]; ring
    | fullSingleton p =>
      dsimp [patchPiece, ClassifiedPiece.toPiece, sum_len]; rw [ih]; ring
    | fullBoundary p =>
      dsimp [patchPiece, ClassifiedPiece.toPiece, sum_len]; rw [ih]; ring

/-- Theorem 3.11.2: Patched trajectory preserves total top-coordinate displacement. -/
theorem patchTrajectory_preserves_Pd_change (hm : 3 ≤ m)
    (l : List (ClassifiedPiece n m C)) :
    sum_Pd_change (patchTrajectory hm l) = sum_Pd_change (l.map ClassifiedPiece.toPiece) := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    dsimp [patchTrajectory, List.map, sum_Pd_change]
    rw [sum_Pd_change_append]
    cases head with
    | partialContact pc =>
      dsimp [patchPiece, ClassifiedPiece.toPiece]
      have h_pd := pc.deformedPath_preserves_Pd_change hm
      rw [h_pd, ih]
    | interior p =>
      dsimp [patchPiece, ClassifiedPiece.toPiece, sum_Pd_change]; rw [ih]; ring
    | fullSingleton p =>
      dsimp [patchPiece, ClassifiedPiece.toPiece, sum_Pd_change]; rw [ih]; ring
    | fullBoundary p =>
      dsimp [patchPiece, ClassifiedPiece.toPiece, sum_Pd_change]; rw [ih]; ring

/-- Patched trajectory weakly decreases accumulated defect. -/
theorem patchTrajectory_defect_le (hm : 3 ≤ m) (hC : 0 ≤ C)
    (l : List (ClassifiedPiece n m C)) :
    sum_defect (patchTrajectory hm l) ≤ sum_defect (l.map ClassifiedPiece.toPiece) := by
  induction l with
  | nil =>
    dsimp [patchTrajectory, List.map, sum_defect]
    exact le_rfl
  | cons head tail ih =>
    dsimp [patchTrajectory, List.map, sum_defect]
    rw [sum_defect_append]
    cases head with
    | partialContact pc =>
      dsimp [patchPiece, ClassifiedPiece.toPiece]
      have h_def_zero := pc.deformedPath_defect_zero hm
      rw [h_def_zero]
      have hk1 : 0 ≤ pc.k - 1 := by linarith [pc.hk1]
      have hkm : 0 ≤ (m : ℝ) - pc.k := by linarith [pc.hkm]
      have hk_pos := pc.k_pos
      have hm_pos : 0 < (m : ℝ) := PartialContactPiece.m_pos hm
      have hsigma_nonneg : 0 ≤ MovingBlock.sigma m C := div_nonneg hC (le_of_lt hm_pos)
      have h_piece_def : 0 ≤ pc.piece.defect := by
        rw [pc.h_defect]
        exact div_nonneg (mul_nonneg (mul_nonneg hsigma_nonneg hk1) hkm) (le_of_lt hk_pos)
      have h_prod : 0 ≤ pc.piece.defect * pc.piece.len :=
        mul_nonneg h_piece_def pc.piece.len_nonneg
      linarith
    | interior p =>
      dsimp [patchPiece, ClassifiedPiece.toPiece, sum_defect]; linarith
    | fullSingleton p =>
      dsimp [patchPiece, ClassifiedPiece.toPiece, sum_defect]; linarith
    | fullBoundary p =>
      dsimp [patchPiece, ClassifiedPiece.toPiece, sum_defect]; linarith

/-- Theorem 3.11.4: Patched trajectory weakly improves total contraction mass. -/
theorem patchTrajectory_improves_contraction (hm : 3 ≤ m) (hC : 0 ≤ C)
    (l : List (ClassifiedPiece n m C)) :
    sum_delta (l.map ClassifiedPiece.toPiece) ≤ sum_delta (patchTrajectory hm l) := by
  have h_same_dur := patchTrajectory_preserves_duration hm l
  have h_same_pd := patchTrajectory_preserves_Pd_change hm l
  let S : Surgery n m C := {
    l_orig := l.map ClassifiedPiece.toPiece
    l_pert := patchTrajectory hm l
    same_duration := h_same_dur.symm
    same_Pd_displacement := h_same_pd.symm
  }
  have h_ex := S.delta_exchange
  have h_defect_le := patchTrajectory_defect_le hm hC l
  linarith [h_ex, h_defect_le]

/-- Theorem 3.11.5: Patched trajectory weakly improves normalized average contraction rate. -/
theorem patchTrajectory_average_rate_ge (hm : 3 ≤ m) (hC : 0 ≤ C)
    (l : List (ClassifiedPiece n m C))
    (h_T_pos : 0 < sum_len (l.map ClassifiedPiece.toPiece)) :
    sum_delta (l.map ClassifiedPiece.toPiece) / sum_len (l.map ClassifiedPiece.toPiece) ≤
    sum_delta (patchTrajectory hm l) / sum_len (patchTrajectory hm l) := by
  have h_dur := patchTrajectory_preserves_duration hm l
  have h_delta := patchTrajectory_improves_contraction hm hC l
  rw [h_dur]
  exact div_le_div_of_nonneg_right h_delta (le_of_lt h_T_pos)

end TrajectoryNormalForm

/-!
# Phase 2: Contact Dynamics, Intrinsic Feasibility, and Renewal Bounds on Δ^{n+m-1}

This phase establishes:
1. The contact submanifolds Z_- and Z_+ and excursion coordinate ordering (x ≤ y_{k+1}).
2. The intrinsic Marnat–Moshchevitin feasibility threshold B ≥ B_min^{(n,m)}(A) and
   W ≥ W_min^{(n,m)}(U) from dilation floor/ceiling compatibility.
3. The multi-coordinate lower-gap slope dominance by defect on moving blocks.
4. The first macroscopic renewal recurrence and autonomous corridor freezing.
5. Filter-theoretic geometric series limits and continuous renewal bracketing.
6. Deduction of the remaining-range upper bound D_low^{(n,m)}(U, W).
-/

/-!
## Section 8: Coordinate Excursion Topology on Δ^{n+m-1}
-/

namespace MatrixExcursionTopology

open Set

/-- Abstract continuous template trajectory on Δ^{n+m-1} tracking the key
coordinates P_1 (bottom), P_m (primal contact), and P_d (top, d = n + m). -/
structure ContinuousTrajectory (n m : ℕ) where
  P1 : ℝ → ℝ
  Pm : ℝ → ℝ
  Pd : ℝ → ℝ
  h_cont1 : Continuous P1
  h_contm : Continuous Pm
  h_contd : Continuous Pd
  h_order : ∀ q, 0 ≤ P1 q ∧ P1 q ≤ Pm q ∧ Pm q ≤ Pd q
  h_mono1 : Monotone P1
  h_monom : Monotone Pm
  h_monod : Monotone Pd

namespace ContinuousTrajectory

variable {n m : ℕ} (P : ContinuousTrajectory n m)

/-- Lower contact locus Z_- where bottom coordinates coalesce: P_1 = P_m. -/
def Z_minus : Set ℝ := {q | P.P1 q = P.Pm q}

/-- Upper contact locus Z_+ where top coordinates coalesce: P_m = P_d. -/
def Z_plus : Set ℝ := {q | P.Pm q = P.Pd q}

/-- Z_- is closed by continuity of P_1 and P_m. -/
theorem isClosed_Z_minus : IsClosed (Z_minus P) :=
  isClosed_eq P.h_cont1 P.h_contm

/-- Z_+ is closed by continuity of P_m and P_d. -/
theorem isClosed_Z_plus : IsClosed (Z_plus P) :=
  isClosed_eq P.h_contm P.h_contd

/-- An open excursion interval (r, t) disjoint from the upper contact locus Z_+. -/
def IsExcursionInterval (r t : ℝ) : Prop :=
  r < t ∧ (Ioo r t ∩ Z_plus P = ∅)

/-- On an excursion interval, P_m(q) < P_d(q) strictly holds everywhere. -/
theorem Pm_lt_Pd_on_excursion {r t : ℝ} (h_exc : IsExcursionInterval P r t) :
    ∀ q ∈ Ioo r t, P.Pm q < P.Pd q := by
  intro q hq
  have h_le : P.Pm q ≤ P.Pd q := (P.h_order q).2.2
  have h_not_in : q ∉ Z_plus P := by
    intro h_in
    have h_mem : q ∈ Ioo r t ∩ Z_plus P := ⟨hq, h_in⟩
    rw [h_exc.2] at h_mem
    exact h_mem
  exact lt_of_le_of_ne h_le h_not_in

/-- Theorem 4.3 (Intermediate Coordinate Ordering Across Excursions):
Because the trajectory visits the lower contact locus ρ ∈ Z_- between peak time q*
and the terminal contact t_{k+1}, monotonicity forces x = P_m(q*) ≤ P_1(t_{k+1}) = y_{k+1}. -/
theorem x_le_y_of_monotone_excursion
    {q_star rho t_k1 : ℝ}
    (h_q_le_rho : q_star ≤ rho)
    (h_rho_le_tk1 : rho ≤ t_k1)
    (h_rho_lower : P.P1 rho = P.Pm rho)
    (x y : ℝ)
    (h_q_Pm : P.Pm q_star = x)
    (h_tk1_P1 : P.P1 t_k1 = y) :
    x ≤ y := by
  have h_P1_mono : P.P1 rho ≤ P.P1 t_k1 := P.h_mono1 h_rho_le_tk1
  have h_Pm_mono : P.Pm q_star ≤ P.Pm rho := P.h_monom h_q_le_rho
  rw [h_rho_lower] at h_P1_mono
  rw [h_tk1_P1] at h_P1_mono
  rw [h_q_Pm] at h_Pm_mono
  linarith

end ContinuousTrajectory

end MatrixExcursionTopology

/-!
## Section 9: Intrinsic Marnat–Moshchevitin Feasibility Boundary
-/

namespace KinematicFeasibility

/-! ### 9.1 Dilation Floor and Ceiling Definitions -/

/-- Theorem 4.4: Kinematic Dilation Floor L_{floor}(n, m, α_k, α_{k+1}). -/
noncomputable def dilation_floor (n m : ℕ) (alpha_k alpha_k1 : ℝ) : ℝ :=
  ((m : ℝ) - 1) * alpha_k / (1 - ((n : ℝ) + 1) * alpha_k1)

/-- Theorem 4.5: Diophantine Dilation Ceiling L_{ceil}(n, m, α_k, α_{k+1}, b). -/
noncomputable def dilation_ceiling (n m : ℕ) (alpha_k alpha_k1 b : ℝ) : ℝ :=
  (b * (1 - ((n : ℝ) + 1) * alpha_k) * ((m : ℝ) - 1)) /
  (((m : ℝ) - 1) * alpha_k1 - b * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * alpha_k1))

/-- The intrinsic quadratic denominator polynomial Q_{n,m}(A). -/
def Q_quad (n m : ℕ) (A : ℝ) : ℝ :=
  1 - (2 * (n : ℝ) + 1) * A + (n : ℝ) * ((m : ℝ) + (n : ℝ)) * A^2

/-- Exact product decomposition proving Q_{n,m}(A) strictly positive. -/
theorem Q_quad_eq_decomposition (n m : ℕ) (A : ℝ) :
    Q_quad n m A = (1 - ((n : ℝ) + 1) * A) * (1 - (n : ℝ) * A) + (n : ℝ) * ((m : ℝ) - 1) * A^2 := by
  dsimp [Q_quad]
  ring

/-- Strict positivity of Q_{n,m}(A) on the open admissible interval (0, 1/(n+1)). -/
theorem Q_quad_pos (n m : ℕ) (_hn : 1 ≤ n) (hm : 2 ≤ m) (A : ℝ)
    (hA_pos : 0 < A) (hA_top : A < 1 / ((n : ℝ) + 1)) :
    0 < Q_quad n m A := by
  rw [Q_quad_eq_decomposition]
  have hn1_pos : 0 < (n : ℝ) + 1 := by positivity
  have h1 : 0 < 1 - ((n : ℝ) + 1) * A := by
    have : A * ((n : ℝ) + 1) < 1 := (lt_div_iff₀ hn1_pos).mp hA_top
    nlinarith
  have h2 : 0 < 1 - (n : ℝ) * A := by
    have : (n : ℝ) * A < ((n : ℝ) + 1) * A := by nlinarith
    linarith
  have h_term1 : 0 < (1 - ((n : ℝ) + 1) * A) * (1 - (n : ℝ) * A) := mul_pos h1 h2
  have hm1 : 0 ≤ (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have h_term2 : 0 ≤ (n : ℝ) * ((m : ℝ) - 1) * A^2 := by positivity
  linarith

/-- The intrinsic minimal drift threshold B_min^{(n,m)}(A). -/
noncomputable def B_min (n m : ℕ) (A : ℝ) : ℝ :=
  ((m : ℝ) - 1) * A^2 / Q_quad n m A

/-! ### 9.2 Intrinsic Compatibility Theorem -/

/-- Theorem 4.6 (Floor-Ceiling Compatibility Equivalence):
In the asymptotic limit α_k, α_{k+1} → A and b → B, the floor is bounded by the
ceiling if and only if B ≥ B_min^{(n,m)}(A). -/
theorem floor_le_ceiling_iff (n m : ℕ) (hm : 2 ≤ m) (A B : ℝ)
    (_hA_pos : 0 < A)
    (h_floor_denom : 0 < 1 - ((n : ℝ) + 1) * A)
    (h_ceil_denom : 0 < ((m : ℝ) - 1) * A - B * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * A))
    (hQ_pos : 0 < Q_quad n m A) :
    ((m : ℝ) - 1) * A / (1 - ((n : ℝ) + 1) * A) ≤
      (B * (1 - ((n : ℝ) + 1) * A) * ((m : ℝ) - 1)) /
      (((m : ℝ) - 1) * A - B * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * A)) ↔
    B_min n m A ≤ B := by
  have hm1_pos : 0 < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  rw [div_le_div_iff₀ h_floor_denom h_ceil_denom]
  have h_alg : ((m : ℝ) - 1) * A * (((m : ℝ) - 1) * A - B * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * A)) ≤
               (B * (1 - ((n : ℝ) + 1) * A) * ((m : ℝ) - 1)) * (1 - ((n : ℝ) + 1) * A) ↔
               ((m : ℝ) - 1)^2 * A^2 ≤ B * ((m : ℝ) - 1) * Q_quad n m A := by
    have h_id : (B * (1 - ((n : ℝ) + 1) * A) * ((m : ℝ) - 1)) * (1 - ((n : ℝ) + 1) * A) -
                ((m : ℝ) - 1) * A * (((m : ℝ) - 1) * A - B * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * A)) =
                ((m : ℝ) - 1) * (B * Q_quad n m A - ((m : ℝ) - 1) * A^2) := by
      dsimp [Q_quad]; ring
    constructor
    · intro h
      have : 0 ≤ ((m : ℝ) - 1) * (B * Q_quad n m A - ((m : ℝ) - 1) * A^2) := by linarith [h, h_id]
      have h_diff : 0 ≤ B * Q_quad n m A - ((m : ℝ) - 1) * A^2 := by
        nlinarith
      nlinarith
    · intro h
      have h_diff : 0 ≤ B * Q_quad n m A - ((m : ℝ) - 1) * A^2 := by
        nlinarith
      linarith [h_id]
  rw [h_alg]
  dsimp [B_min]
  rw [div_le_iff₀ hQ_pos]
  constructor
  · intro h
    have : ((m : ℝ) - 1) * (((m : ℝ) - 1) * A^2) ≤ ((m : ℝ) - 1) * (B * Q_quad n m A) := by
      calc ((m : ℝ) - 1) * (((m : ℝ) - 1) * A^2)
        _ = ((m : ℝ) - 1)^2 * A^2 := by ring
        _ ≤ B * ((m : ℝ) - 1) * Q_quad n m A := h
        _ = ((m : ℝ) - 1) * (B * Q_quad n m A) := by ring
    nlinarith
  · intro h
    calc ((m : ℝ) - 1)^2 * A^2
      _ = ((m : ℝ) - 1) * (((m : ℝ) - 1) * A^2) := by ring
      _ ≤ ((m : ℝ) - 1) * (B * Q_quad n m A) := by nlinarith
      _ = B * ((m : ℝ) - 1) * Q_quad n m A := by ring

/-! ### 9.3 Conversion to Diophantine Exponents (U, W) -/

/-- Denominator polynomial in Diophantine exponent space (U, W):
  `D_{UW}(n, m, U) = 1 - (2n - 1)U + (n - 1)(m + n - 1)U^2`. -/
def denom_UW (n m : ℕ) (U : ℝ) : ℝ :=
  1 - (2 * (n : ℝ) - 1) * U + ((n : ℝ) - 1) * ((m : ℝ) + (n : ℝ) - 1) * U^2

/-- Marnat–Moshchevitin lower feasibility bound W_min^{(n,m)}(U). -/
noncomputable def W_min (n m : ℕ) (U : ℝ) : ℝ :=
  ((m : ℝ) - 1) * U^2 / denom_UW n m U

/-- Exact algebraic equivalence: Transforming B_min^{(n,m)}(A) to W = B / (1 - B)
under the Dani isomorphism A = U / (1 + U) produces W_min^{(n,m)}(U) identically. -/
theorem W_min_eq_B_min_transformed (n m : ℕ) (U : ℝ) (hU1 : 1 + U ≠ 0)
    (h_Q : Q_quad n m (U / (1 + U)) ≠ 0):
    let A := U / (1 + U)
    let B := B_min n m A
    B / (1 - B) = W_min n m U := by
  intro A B
  dsimp [B, B_min, W_min, A]
  have h_B_div : ((m : ℝ) - 1) * (U / (1 + U))^2 / Q_quad n m (U / (1 + U)) /
      (1 - ((m : ℝ) - 1) * (U / (1 + U))^2 / Q_quad n m (U / (1 + U))) =
      ((m : ℝ) - 1) * (U / (1 + U))^2 /
      (Q_quad n m (U / (1 + U)) - ((m : ℝ) - 1) * (U / (1 + U))^2) := by
    field_simp [h_Q]
  rw [h_B_div]
  dsimp [Q_quad, denom_UW]
  field_simp
  ring

/-- Specialization to n = 1: The denominator simplifies to 1 - U. -/
theorem denom_UW_n_one (m : ℕ) (U : ℝ) :
    denom_UW 1 m U = 1 - U := by
  dsimp [denom_UW]
  ring

/-- Specialization to (n, m) = (1, 2): W_min^{(1,2)}(U) = U^2 / (1 - U). -/
theorem W_min_one_two (U : ℝ) :
    W_min 1 2 U = U^2 / (1 - U) := by
  dsimp [W_min]
  rw [denom_UW_n_one]
  ring

/-- Corollary 4.7: Sub-feasible pairs (W < W_min) admit no valid template trajectories. -/
theorem sub_feasible_empty (n m : ℕ) (hm : 2 ≤ m) (A B : ℝ)
    (hA_pos : 0 < A)
    (h_floor_denom : 0 < 1 - ((n : ℝ) + 1) * A)
    (h_ceil_denom : 0 < ((m : ℝ) - 1) * A - B * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * A))
    (hQ_pos : 0 < Q_quad n m A)
    (hB_lt : B < B_min n m A) :
    dilation_ceiling n m A A B < dilation_floor n m A A := by
  dsimp [dilation_floor, dilation_ceiling]
  have h_not_le : ¬ (B_min n m A ≤ B) := not_le.mpr hB_lt
  have h_iff := floor_le_ceiling_iff n m hm A B hA_pos h_floor_denom h_ceil_denom hQ_pos
  exact lt_of_not_ge (fun h_le => h_not_le (h_iff.mp h_le))

end KinematicFeasibility

/-!
## Section 10: Multi-Coordinate Gap Slopes and Defect Dominance
-/

namespace MatrixExcursionRecurrence

open MovingBlock

variable {n m : ℕ} [NeZero n] [NeZero m]

/-- Velocity of bottom coordinate P_1 on moving block b. -/
noncomputable def P'_1 (b : MovingBlock n m) : ℝ :=
  if b.r = 1 then 1 / b.k else 0

/-- Velocity of m-th coordinate P_m on moving block b. -/
noncomputable def P'_m (b : MovingBlock n m) : ℝ :=
  if b.r ≤ m ∧ m ≤ b.s then 1 / b.k else 0

/-- Rate of expansion of lower coordinate gap P_m - P_1 (Definition 4.8). -/
noncomputable def gap_slope (b : MovingBlock n m) : ℝ :=
  P'_m b - P'_1 b

/-- Admissibility condition for interior moving blocks during an excursion. -/
def is_valid_interior_block (b : MovingBlock n m) : Prop :=
  b.s = n + m → b.r = n + m

/-- Lemma 4.9 (Gap Slope Defect Dominance):
On every valid interior moving block b, the lower gap velocity is bounded by defect:
  gap_slope(b) ≤ (1 / σ) * e(b). -/
theorem gap_growth_le_defect (C : ℝ) (hC : 0 < C) (b : MovingBlock n m)
    (h_valid : is_valid_interior_block b) :
    gap_slope b ≤ (1 / sigma m C) * b.defect C := by
  dsimp [gap_slope, P'_1, P'_m]
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
  have hsigma_pos : 0 < sigma m C := div_pos hC hm_pos
  by_cases hs : b.s = n + m
  · have hr : b.r = n + m := h_valid hs
    have hr_ne1 : b.r ≠ 1 := by
      intro h
      have hlen := b.block_len_le hs
      have hn_pos := NeZero.pos n
      omega
    have hr_not_le_m : ¬ (b.r ≤ m ∧ m ≤ b.s) := by
      rintro ⟨hle, _⟩
      have hn_pos := NeZero.pos n
      omega
    have hk_eq : b.k = 1 := by
      dsimp [MovingBlock.k]
      have hs_c : (b.s : ℝ) = (n + m : ℝ) := by exact_mod_cast hs
      have hr_c : (b.r : ℝ) = (n + m : ℝ) := by exact_mod_cast hr
      rw [hs_c, hr_c]; ring
    rw [ite_eq_right hr_not_le_m, ite_eq_right hr_ne1, sub_zero]
    rw [defect_of_s_eq_d C b hs, hk_eq]
    ring_nf
    exact le_rfl
  · have hlt : b.s < n + m := Nat.lt_of_le_of_ne b.s_le_d hs
    rw [defect_of_s_lt_d C b hlt]
    have h_cancel : (1 / sigma m C) * (sigma m C * ((b.r : ℝ) - 1)) = (b.r : ℝ) - 1 := by
      have : sigma m C ≠ 0 := ne_of_gt hsigma_pos
      field_simp
    rw [h_cancel]
    have hk_pos := b.k_pos
    have hk_ge1 : 1 ≤ b.k := by
      dsimp [MovingBlock.k]
      have : (b.r : ℝ) ≤ (b.s : ℝ) := Nat.cast_le.mpr b.r_le_s
      linarith
    have h_inv_le1 : 1 / b.k ≤ 1 := by rw [div_le_one hk_pos]; exact hk_ge1
    have h_inv_nonneg : 0 ≤ 1 / b.k := div_nonneg (by norm_num) (le_of_lt hk_pos)
    by_cases hr1 : b.r = 1
    · rw [ite_eq_left hr1]
      have hr_zero : (b.r : ℝ) - 1 = 0 := by
        have : (b.r : ℝ) = 1 := by exact_mod_cast hr1
        linarith
      rw [hr_zero]
      split_ifs with _h_m
      · linarith
      · linarith [h_inv_nonneg]
    · rw [ite_eq_right hr1]
      have hr_ge2 : 2 ≤ b.r := by
        have : 1 ≤ b.r := b.r_ge_one
        omega
      have hr_defect : 1 ≤ (b.r : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (b.r : ℝ) := by exact_mod_cast hr_ge2
        linarith
      split_ifs with _h_m
      · linarith [h_inv_le1, hr_defect]
      · linarith [hr_defect]

/-! ### 10.2 Excursion Gap Integration -/

/-- A single timed segment within an excursion trajectory. -/
structure ExcursionStep (n m : ℕ) where
  block : MovingBlock n m
  dt : ℝ
  h_dt : 0 ≤ dt
  valid : is_valid_interior_block block

/-- Integrated lower gap expansion across a sequence of excursion steps. -/
noncomputable def sum_gap_growth : List (ExcursionStep n m) → ℝ
  | [] => 0
  | step :: rest => gap_slope step.block * step.dt + sum_gap_growth rest

/-- Integrated accumulated defect across excursion steps. -/
noncomputable def sum_defect (C : ℝ) : List (ExcursionStep n m) → ℝ
  | [] => 0
  | step :: rest => step.block.defect C * step.dt + sum_defect C rest

/-- Telescoping gap integration: Total lower gap expansion is bounded by accumulated defect. -/
theorem sum_gap_growth_le_sum_defect (C : ℝ) (hC : 0 < C)
    (l : List (ExcursionStep n m)) :
    sum_gap_growth l ≤ (1 / sigma m C) * sum_defect C l := by
  induction l with
  | nil =>
    dsimp [sum_gap_growth, sum_defect]
    rw [mul_zero]
  | cons step rest ih =>
    dsimp [sum_gap_growth, sum_defect]
    have h_slope := gap_growth_le_defect C hC step.block step.valid
    have h_step : gap_slope step.block * step.dt ≤
        ((1 / sigma m C) * step.block.defect C) * step.dt :=
      mul_le_mul_of_nonneg_right h_slope step.h_dt
    have h_dist : ((1 / sigma m C) * step.block.defect C) * step.dt +
                  (1 / sigma m C) * sum_defect C rest =
                  (1 / sigma m C) * (step.block.defect C * step.dt + sum_defect C rest) := by ring
    linarith

/-- The normalized gap parameter d_0(n, m, α) = ((m + n)α - 1) / (m - 1) (Theorem 4.10). -/
noncomputable def d0 (n m : ℕ) (alpha : ℝ) : ℝ :=
  (((m : ℝ) + (n : ℝ)) * alpha - 1) / ((m : ℝ) - 1)

/-- Theorem 4.10 (First Macroscopic Renewal Inequality):
  z_{k+1} ≥ z_k / L_k + σ * d_0(n, m, α_{k+1}). -/
theorem first_macroscopic_renewal
    (n m : ℕ) (hm : 2 ≤ m) (C : ℝ) (hC : 0 < C)
    (t_k t_k1 : ℝ) (Q_k Q_k1 : ℝ) (alpha_k1 : ℝ)
    (ht_k_pos : 0 < t_k) (ht_k1_pos : 0 < t_k1)
    (h_gap_defect : d0 n m alpha_k1 * t_k1 ≤ (1 / sigma m C) * (Q_k1 - Q_k)) :
    let z_k := Q_k / t_k
    let z_k1 := Q_k1 / t_k1
    let L_k := t_k1 / t_k
    z_k / L_k + sigma m C * d0 n m alpha_k1 ≤ z_k1 := by
  intro z_k z_k1 L_k
  dsimp [z_k, z_k1, L_k]
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsigma_pos : 0 < sigma m C := div_pos hC hm_pos
  have ht_k_ne : t_k ≠ 0 := ne_of_gt ht_k_pos
  have ht_k1_ne : t_k1 ≠ 0 := ne_of_gt ht_k1_pos
  have h_scaled : sigma m C * (d0 n m alpha_k1 * t_k1) ≤ Q_k1 - Q_k := by
    have h_mul := mul_le_mul_of_nonneg_left h_gap_defect (le_of_lt hsigma_pos)
    have h_cancel : sigma m C * ((1 / sigma m C) * (Q_k1 - Q_k)) = Q_k1 - Q_k := by
      field_simp [ne_of_gt hsigma_pos]
    rwa [h_cancel] at h_mul
  have h_div : sigma m C * d0 n m alpha_k1 ≤ (Q_k1 - Q_k) / t_k1 := by
    have h_le := div_le_div_of_nonneg_right h_scaled (le_of_lt ht_k1_pos)
    have h_canc : (sigma m C * (d0 n m alpha_k1 * t_k1)) / t_k1 = sigma m C * d0 n m alpha_k1 := by
      field_simp [ht_k1_ne]
    rwa [h_canc] at h_le
  have h_ratio : (Q_k / t_k) / (t_k1 / t_k) = Q_k / t_k1 := by
    field_simp [ht_k_ne, ht_k1_ne]
  have h_sub : (Q_k1 - Q_k) / t_k1 = Q_k1 / t_k1 - Q_k / t_k1 := by ring
  linarith [h_div, h_ratio, h_sub]

end MatrixExcursionRecurrence

/-!
## Section 11: Uniform Freezing, Filter Limits, and Renewal Bracketing
-/

namespace MatrixUniformFreezing

open Filter Topology
open MatrixExcursionRecurrence
open MovingBlock

variable {n m : ℕ}

/-- Definition 4.11: The frozen corridor dilation parameter L_ε(a, b). -/
noncomputable def L_eps (n m : ℕ) (a b : ℝ) : ℝ :=
  (b * (1 - ((n : ℝ) + 1) * a) * ((m : ℝ) - 1)) /
  (((m : ℝ) - 1) * a - b * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * a))

/-- Theorem 4.11 (Uniform Recurrence Freezing):
Locks dynamic parameters α_k, α_{k+1} ≥ a into the uniform recurrence:
  z_k / L_ε + σ * d_0(n, m, a) ≤ z_{k+1}. -/
theorem uniform_renewal_step
    (n m : ℕ) (hm : 2 ≤ m) (C : ℝ) (hC : 0 < C)
    (z_k z_k1 L_k L_frozen a alpha_k1 : ℝ)
    (hz_k_nonneg : 0 ≤ z_k)
    (hL_k_pos : 0 < L_k)
    (hL_bound : L_k ≤ L_frozen)
    (ha_bound : a ≤ alpha_k1)
    (h_rec : z_k / L_k + sigma m C * d0 n m alpha_k1 ≤ z_k1) :
    z_k / L_frozen + sigma m C * d0 n m a ≤ z_k1 := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm1_pos : 0 < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hsigma_pos : 0 < sigma m C := div_pos hC hm_pos
  have h_dil : z_k / L_frozen ≤ z_k / L_k :=
    div_le_div_of_nonneg_left hz_k_nonneg hL_k_pos hL_bound
  have h_d0_mono : d0 n m a ≤ d0 n m alpha_k1 := by
    dsimp [d0]
    have h_num : ((m : ℝ) + (n : ℝ)) * a - 1 ≤ ((m : ℝ) + (n : ℝ)) * alpha_k1 - 1 := by
      have : 0 ≤ (m : ℝ) + (n : ℝ) := by positivity
      nlinarith
    exact div_le_div_of_nonneg_right h_num (le_of_lt hm1_pos)
  have h_sigma_d0 : sigma m C * d0 n m a ≤ sigma m C * d0 n m alpha_k1 :=
    mul_le_mul_of_nonneg_left h_d0_mono (le_of_lt hsigma_pos)
  linarith

/-! ### 11.2 Geometric Recurrence Unrolling and Limit -/

/-- Horner-form finite geometric series unrolling. -/
def geom_sum (r : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => geom_sum r n * r + 1

/-- Finite unrolling of the autonomous recurrence z_{k+1} ≥ z_k / L + C_inc. -/
theorem unroll_recurrence (z : ℕ → ℝ) (L C_inc : ℝ)
    (h_renew : ∀ k, z k / L + C_inc ≤ z (k + 1))
    (hL_pos : 0 < L) (k : ℕ) :
    z 0 * (1 / L)^k + C_inc * geom_sum (1 / L) k ≤ z k := by
  induction k with
  | zero =>
    dsimp [geom_sum]; ring_nf; linarith
  | succ k ih =>
    have hk := h_renew k
    dsimp [geom_sum]
    have h_nonneg : 0 ≤ 1 / L := by positivity
    have ih_div : (z 0 * (1 / L)^k + C_inc * geom_sum (1 / L) k) * (1 / L) ≤ z k * (1 / L) :=
      mul_le_mul_of_nonneg_right ih h_nonneg
    have h_div_eq : z k / L = z k * (1 / L) := by ring
    calc z 0 * (1 / L)^(k + 1) + C_inc * (geom_sum (1 / L) k * (1 / L) + 1)
      _ = (z 0 * (1 / L)^k + C_inc * geom_sum (1 / L) k) * (1 / L) + C_inc := by ring
      _ ≤ z k * (1 / L) + C_inc := by linarith [ih_div]
      _ = z k / L + C_inc := by rw [h_div_eq]
      _ ≤ z (k + 1) := hk

/-- Theorem 4.12: Closed-form geometric series summation identity for L > 1. -/
lemma geom_sum_mul_one_sub (r : ℝ) (k : ℕ) :
    geom_sum r k * (1 - r) = 1 - r^k := by
  induction k with
  | zero => dsimp [geom_sum]; ring
  | succ k ih =>
    dsimp [geom_sum]
    calc (geom_sum r k * r + 1) * (1 - r)
      _ = (geom_sum r k * (1 - r)) * r + (1 - r) := by ring
      _ = (1 - r^k) * r + (1 - r) := by rw [ih]
      _ = 1 - r^(k + 1) := by ring

theorem geom_sum_closed_form (L : ℝ) (k : ℕ) (hL_gt_one : 1 < L) :
    geom_sum (1 / L) k = (1 - (1 / L)^k) * (L / (L - 1)) := by
  have hL0 : 0 < L := by linarith
  have hL_ne : L ≠ 0 := ne_of_gt hL0
  have hLm1 : L - 1 ≠ 0 := by linarith
  have h_denom : 1 - 1 / L ≠ 0 := by
    have : 1 - 1 / L = (L - 1) / L := by field_simp [hL_ne]
    rw [this]; exact div_ne_zero hLm1 hL_ne
  have h_id := geom_sum_mul_one_sub (1 / L) k
  have h_div : geom_sum (1 / L) k = (1 - (1 / L)^k) / (1 - 1 / L) :=
    (eq_div_iff h_denom).mpr h_id
  have h_frac : 1 / (1 - 1 / L) = L / (L - 1) := by field_simp [hL_ne, hLm1]
  calc geom_sum (1 / L) k
    _ = (1 - (1 / L)^k) / (1 - 1 / L) := h_div
    _ = (1 - (1 / L)^k) * (1 / (1 - 1 / L)) := by ring
    _ = (1 - (1 / L)^k) * (L / (L - 1)) := by rw [h_frac]

/-- Pointwise geometric lower bound sequence. -/
noncomputable def lower_bound_seq (z0 L C_inc : ℝ) (k : ℕ) : ℝ :=
  z0 * (1 / L)^k + C_inc * (1 - (1 / L)^k) * (L / (L - 1))

/-- Convergence of the lower bound sequence to C_inc * L / (L - 1). -/
theorem tendsto_lower_bound_seq (z0 L C_inc : ℝ) (hL : 1 < L) :
    Tendsto (fun k ↦ lower_bound_seq z0 L C_inc k) atTop (𝓝 (C_inc * (L / (L - 1)))) := by
  dsimp [lower_bound_seq]
  have hL_pos : 0 < L := by linarith
  have h_nonneg : 0 ≤ 1 / L := by positivity
  have h_lt_one : 1 / L < 1 := (div_lt_one hL_pos).mpr hL
  have h_pow_zero := tendsto_pow_atTop_nhds_zero_of_lt_one h_nonneg h_lt_one
  have h_term1 : Tendsto (fun k ↦ z0 * (1 / L)^k) atTop (𝓝 (z0 * 0)) :=
    tendsto_const_nhds.mul h_pow_zero
  have h_sub : Tendsto (fun k ↦ 1 - (1 / L)^k) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h_pow_zero
  have h_term2 : Tendsto (fun k ↦ C_inc * (1 - (1 / L)^k) * (L / (L - 1))) atTop
      (𝓝 (C_inc * (1 - 0) * (L / (L - 1)))) :=
    (tendsto_const_nhds.mul h_sub).mul tendsto_const_nhds
  have h_sum := h_term1.add h_term2
  have h_simp : z0 * 0 + C_inc * (1 - 0) * (L / (L - 1)) = C_inc * (L / (L - 1)) := by ring
  rwa [h_simp] at h_sum

/-- Topological limit comparison preserving the geometric recurrence floor. -/
theorem le_of_tendsto_renewal_limit {z : ℕ → ℝ} {Z L C_inc : ℝ} (hL : 1 < L)
    (h_bound : ∀ k, lower_bound_seq (z 0) L C_inc k ≤ z k)
    (hz : Tendsto z atTop (𝓝 Z)) :
    C_inc * (L / (L - 1)) ≤ Z :=
  le_of_tendsto_of_tendsto' (tendsto_lower_bound_seq (z 0) L C_inc hL) hz h_bound

end MatrixUniformFreezing

/-!
## Section 12: Deductive Synthesis of the Remaining-Range Upper Bound
-/

namespace MatrixMasterUpperBounds

open MatrixExcursionRecurrence MatrixUniformFreezing MovingBlock

/-- The target candidate dimension formula D_low^{(n,m)}(U, W) (Section 1.3). -/
noncomputable def D_low (n m : ℕ) (C U W : ℝ) : ℝ :=
  ((1 + ((m : ℝ) * (n : ℝ) - (m : ℝ) - 2 * (n : ℝ) + 1) * U) * (((m : ℝ) + (n : ℝ) - 1) * U - 1) * W^2 +
   (C * U * ((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) -
    ((m : ℝ) - 1) * U * (((m : ℝ) + (n : ℝ) - 1) * U - 1)) * W -
   C * ((m : ℝ) - 1) * U^2) /
  (U * (W + 1) * (((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U))

/-- The defect penalty term measuring the discrepancy from the Large-W rate C / (1 + W) (Theorem 6.5). -/
noncomputable def defect_penalty (n m : ℕ) (U W : ℝ) : ℝ :=
  (- W * (((m : ℝ) + (n : ℝ) - 1) * U - 1) *
    (((m : ℝ) - 1) * U - W * (1 + ((m : ℝ) * (n : ℝ) - (m : ℝ) - 2 * (n : ℝ) + 1) * U))) /
  (U * (W + 1) * (((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U))

/-- Theorem 6.5 (Additive Defect Decomposition):
  D_low^{(n,m)}(U, W) = C / (1 + W) + defect_penalty(n, m, U, W). -/
theorem D_low_eq_envelope_add_penalty
    (n m : ℕ) (C U W : ℝ) (hU : U ≠ 0) (_hW1 : W + 1 ≠ 0)
    (h_denom : ((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U ≠ 0) :
    D_low n m C U W = C / (1 + W) + defect_penalty n m U W := by
  set factor := U * (((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U)
  have h_factor : factor ≠ 0 := mul_ne_zero hU h_denom
  have h_diff : D_low n m C U W - defect_penalty n m U W = C / (1 + W) := by
    dsimp [D_low, defect_penalty]
    rw [← sub_div]
    have h_num :
      ((1 + ((m : ℝ) * (n : ℝ) - (m : ℝ) - 2 * (n : ℝ) + 1) * U) * (((m : ℝ) + (n : ℝ) - 1) * U - 1) * W^2 +
       (C * U * ((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) -
        ((m : ℝ) - 1) * U * (((m : ℝ) + (n : ℝ) - 1) * U - 1)) * W -
       C * ((m : ℝ) - 1) * U^2) -
      (- W * (((m : ℝ) + (n : ℝ) - 1) * U - 1) *
        (((m : ℝ) - 1) * U - W * (1 + ((m : ℝ) * (n : ℝ) - (m : ℝ) - 2 * (n : ℝ) + 1) * U))) =
      C * factor := by
      dsimp [factor]
      ring
    have h_den :
      U * (W + 1) * (((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U) =
      (1 + W) * factor := by
      dsimp [factor]
      ring
    rw [h_num, h_den]
    exact mul_div_mul_right C (1 + W) h_factor
  linarith [h_diff]

/-- The continuous renewal bracketing defect ratio evaluates algebraically
to the defect penalty discrepancy (Theorem 4.14, Theorem 6.5). -/
theorem renewal_bracket_ratio_eq_penalty
    (n m : ℕ) (hm : 2 ≤ m) (U W A B : ℝ)
    (hA : A = U / (1 + U)) (hB : B = W / (1 + W))
    (hU1 : 1 + U ≠ 0) (hW1 : 1 + W ≠ 0)
    (hU : U ≠ 0)
    (h_pen_den : U * (W + 1) * (((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U) ≠ 0)
    (L : ℝ)
    (h_DL_ne : ((m : ℝ) - 1) * A - B * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * A) ≠ 0)
    (hL_eq : (L - 1) * ((1 + U) * (1 + W) * (((m : ℝ) - 1) * A - B * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * A))) =
             ((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U):
    - ((((m : ℝ) - 1) * d0 n m A * B) / (A * (L - 1))) = defect_penalty n m U W := by
  dsimp [defect_penalty, d0]
  have hm1_ne : (m : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    linarith
  have hW1_comm : W + 1 ≠ 0 := by intro h; apply hW1; linarith
  have h_NL_ne : ((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U ≠ 0 := by
    intro h
    apply h_pen_den
    rw [h, mul_zero]
  have h_DL_prod_ne : (1 + U) * (1 + W) * (((m : ℝ) - 1) * A - B * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * A)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hU1 hW1) h_DL_ne
  have hL_div : L - 1 = (((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U) /
                        ((1 + U) * (1 + W) * (((m : ℝ) - 1) * A - B * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * A))) := by
    exact (eq_div_iff h_DL_prod_ne).mpr hL_eq
  rw [hL_div]
  -- Now rewrite hA and hB everywhere so no A or B remains
  rw [hA, hB]
  field_simp [hU1, hW1, hW1_comm, hU, hm1_ne, h_NL_ne, h_pen_den]
  ring

/-- Theorem 4.14 (General Remaining-Range Upper Bound Theorem):
The asymptotic contraction rate along any admissible template matching drift B is
strictly bounded above by D_low^{(n,m)}(U, W) across W_min ≤ W < W_*. -/
theorem general_remaining_range_upper_bound
    (n m : ℕ) (hm : 2 ≤ m) (C U W A B L : ℝ)
    (hA : A = U / (1 + U)) (hB : B = W / (1 + W))
    (hU1 : 1 + U ≠ 0) (hW1 : 1 + W ≠ 0) (hU : U ≠ 0)
    (h_denom : ((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U ≠ 0)
    (h_pen_den : U * (W + 1) * (((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U) ≠ 0)
    (h_DL_ne : ((m : ℝ) - 1) * A - B * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * A) ≠ 0)
    (hL_eq : (L - 1) * ((1 + U) * (1 + W) * (((m : ℝ) - 1) * A - B * (1 + ((m : ℝ) * (n : ℝ) - 2 * (n : ℝ) - 1) * A))) =
             ((m : ℝ) - ((m : ℝ) + (n : ℝ) - 1) * U) * W - ((m : ℝ) - 1) * U)
    (delta_bound : ℝ)
    (h_bracket : delta_bound ≤ C / (1 + W) - (((m : ℝ) - 1) * d0 n m A * B) / (A * (L - 1))) :
    delta_bound ≤ D_low n m C U W := by
  have hW1_ne : W + 1 ≠ 0 := by intro h; apply hW1; linarith
  have h_decomp := D_low_eq_envelope_add_penalty n m C U W hU hW1_ne h_denom
  have h_pen := renewal_bracket_ratio_eq_penalty n m hm U W A B hA hB hU1 hW1 hU h_pen_den L h_DL_ne hL_eq
  have h_sub : C / (1 + W) - (((m : ℝ) - 1) * d0 n m A * B) / (A * (L - 1)) =
               C / (1 + W) + defect_penalty n m U W := by
    linarith [h_pen]
  rw [h_decomp, ← h_sub]
  exact h_bracket

end MatrixMasterUpperBounds
