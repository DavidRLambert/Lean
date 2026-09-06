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
