import Mathlib

/-!
# n = 1, m = 3 (equivalently transposed 1 x 3) template analysis

This is a self-contained checkpoint for the m = 3 investigation.
It is intentionally written so that most proofs are *polynomial certificates* proved by `ring`.
That is more robust in a single-file live.lean-lang.org workflow than repeatedly asking
`field_simp` to normalize large rational functions.

Conventions:
* transposed `1 x 3` generalized-system coordinates, so `d = 4`;
* `U` = uniform simultaneous exponent, `W` = ordinary exponent;
* `A = U/(1+U)`, `B = W/(1+W)`;
* the nontrivial uniform range is expected to be `1/3 < U < 1/2`.

Status discipline:
* exact algebraic identities are Lean theorems below;
* candidate template families are definitions;
* the length <= 8 exhaustiveness / dominance conclusions remain comments until the
  finite Roy-state enumeration is itself formalized.
-/

noncomputable section

namespace M3

/-! ## 1. Normalized exponent coordinates -/

def A (U : ℝ) : ℝ := U / (1 + U)
def B (W : ℝ) : ℝ := W / (1 + W)

theorem A_one_plus (U : ℝ) (h : 1 + U ≠ 0) :
    A U * (1 + U) = U := by
  unfold A
  field_simp [h]

theorem one_sub_A (U : ℝ) (h : 1 + U ≠ 0) :
    1 - A U = 1 / (1 + U) := by
  unfold A
  field_simp [h]
  ring

theorem one_sub_twoA (U : ℝ) (h : 1 + U ≠ 0) :
    1 - 2 * A U = (1 - U) / (1 + U) := by
  unfold A
  field_simp [h]
  ring

theorem one_sub_threeA (U : ℝ) (h : 1 + U ≠ 0) :
    1 - 3 * A U = (1 - 2 * U) / (1 + U) := by
  unfold A
  field_simp [h]
  ring

/-! ## 2. The regular-system (Marnat--Moshchevitin) quadratic -/

def rhoNum (U : ℝ) : ℝ := U + Real.sqrt (U * (4 - 3 * U))
def rhoDen (U : ℝ) : ℝ := 2 * (1 - U)

def rho (U : ℝ) : ℝ := rhoNum U / rhoDen U

def Wmm (U : ℝ) : ℝ := U * rho U

/-- Cleared-denominator quadratic for the regular-system root.
    This avoids division entirely. -/
theorem rhoNum_quadratic
    (U : ℝ)
    (hrad : 0 ≤ U * (4 - 3 * U)) :
    (1 - U) * (rhoNum U)^2
      - U * rhoNum U * rhoDen U
      - U * (rhoDen U)^2 = 0 := by
  have hs : (Real.sqrt (U * (4 - 3 * U))) ^ 2 = U * (4 - 3 * U) :=
    Real.sq_sqrt hrad
  unfold rhoNum rhoDen
  nlinarith [hs]

/-! ## 3. Threshold functions and their affine root polynomials -/

def Wc (U : ℝ) : ℝ := U / (2 - 3 * U)
def WT (U : ℝ) : ℝ := 2 * U^2 / (1 - U)
def WH (U : ℝ) : ℝ := U / (1 - U)
def WstarOld (U : ℝ) : ℝ := U / (2 * (1 - 2 * U))

def WxNum (U : ℝ) : ℝ := U * (4 * U - 1)
def WxDen (U : ℝ) : ℝ := -6 * U^2 + 6 * U - 1
def Wx (U : ℝ) : ℝ := WxNum U / WxDen U

def crossPoly (U W : ℝ) : ℝ :=
  6 * U^2 * W + 4 * U^2 - 6 * U * W - U + W

/-- `crossPoly U W = 0` is equivalent, after clearing the nonzero denominator,
    to `W = Wx U`. -/
theorem crossPoly_affine (U W : ℝ) :
    crossPoly U W = WxNum U - WxDen U * W := by
  unfold crossPoly WxNum WxDen
  ring

def WTNum (U : ℝ) : ℝ := 2 * U^2
def WTDen (U : ℝ) : ℝ := 1 - U

def birthPoly (U W : ℝ) : ℝ := 2 * U^2 + U * W - W

/-- `birthPoly U W = 0` is the cleared form of `W = WT U`. -/
theorem birthPoly_affine (U W : ℝ) :
    birthPoly U W = WTNum U - WTDen U * W := by
  unfold birthPoly WTNum WTDen
  ring

/-! ## 4. The nine active blocks in d = 4 -/

inductive Block where
  | b1   -- [1]
  | b2   -- [2]
  | b3   -- [3]
  | b4   -- [4]
  | b12  -- [1,2]
  | b23  -- [2,3]
  | b34  -- [3,4]
  | b13  -- [1,3]
  | b24  -- [2,4]
  deriving DecidableEq, Repr

namespace Block

def r : Block → ℕ
  | b1  => 1
  | b2  => 2
  | b3  => 3
  | b4  => 4
  | b12 => 1
  | b23 => 2
  | b34 => 3
  | b13 => 1
  | b24 => 2

def s : Block → ℕ
  | b1  => 1
  | b2  => 2
  | b3  => 3
  | b4  => 4
  | b12 => 2
  | b23 => 3
  | b34 => 4
  | b13 => 3
  | b24 => 4

/-- Pointwise contraction rate in the transposed `1 x 3` convention. -/
def delta : Block → ℝ
  | b1  => 3
  | b2  => 2
  | b3  => 1
  | b4  => 0
  | b12 => 3
  | b23 => 2
  | b34 => 1
  | b13 => 3
  | b24 => 2

/-- Slope of the top coordinate `P4`. -/
def topSlope : Block → ℝ
  | b4  => 1
  | b34 => 1 / 2
  | b24 => 1 / 3
  | _   => 0

end Block

/-- Small concrete vector type for d = 4 velocity vectors.
    We deliberately do not derive `Repr`: `Real.instRepr` is unsafe and caused
    a kernel error in the first live.lean pass. -/
structure Vec4 where
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  x4 : ℝ

namespace Vec4

def sum (v : Vec4) : ℝ := v.x1 + v.x2 + v.x3 + v.x4

end Vec4

namespace Block

def vel : Block → Vec4
  | b1  => ⟨1, 0, 0, 0⟩
  | b2  => ⟨0, 1, 0, 0⟩
  | b3  => ⟨0, 0, 1, 0⟩
  | b4  => ⟨0, 0, 0, 1⟩
  | b12 => ⟨1/2, 1/2, 0, 0⟩
  | b23 => ⟨0, 1/2, 1/2, 0⟩
  | b34 => ⟨0, 0, 1/2, 1/2⟩
  | b13 => ⟨1/3, 1/3, 1/3, 0⟩
  | b24 => ⟨0, 1/3, 1/3, 1/3⟩

theorem vel_sum_one (b : Block) : (vel b).sum = 1 := by
  cases b <;> norm_num [vel, Vec4.sum]

end Block

/-! ## 5. Short candidate words -/

def wordF6 : List Block :=
  [Block.b34, Block.b4, Block.b1, Block.b12, Block.b2, Block.b3]

def wordG6 : List Block :=
  [Block.b24, Block.b4, Block.b1, Block.b3, Block.b34, Block.b2]

def wordF4 : List Block :=
  [Block.b24, Block.b4, Block.b1, Block.b23]

def wordF7 : List Block :=
  [Block.b34, Block.b2, Block.b4, Block.b1, Block.b13, Block.b23, Block.b3]

theorem wordF6_length : wordF6.length = 6 := by rfl
theorem wordG6_length : wordG6.length = 6 := by rfl
theorem wordF4_length : wordF4.length = 4 := by rfl
theorem wordF7_length : wordF7.length = 7 := by rfl

/-! ## 6. F6: rational functions split into numerators and denominators -/

def D6Num (U W L : ℝ) : ℝ :=
  2 * L * U - 3 * U * W - 3 * U + 2 * W

def D6Den (U W L : ℝ) : ℝ := U * (L - 1) * (1 + W)
def D6 (U W L : ℝ) : ℝ := D6Num U W L / D6Den U W L

def L6mid (U W : ℝ) : ℝ := W / U

def L6high (U W : ℝ) : ℝ :=
  2 * W * (1 - U) / (2 * U - W * (1 - U))

def L6low (U W : ℝ) : ℝ :=
  (-1 + Real.sqrt (1 + 4 * W * (1 - U) / (U - W * (1 - U)))) / 2

def D6midNum (U W : ℝ) : ℝ := 3 * U * W + 3 * U - 4 * W
def D6midDen (U W : ℝ) : ℝ := (U - W) * (1 + W)
def D6midClosed (U W : ℝ) : ℝ := D6midNum U W / D6midDen U W

def D6highNum (U W : ℝ) : ℝ :=
  3 * U^2 * W^2 + 13 * U^2 * W + 6 * U^2
    - 5 * U * W^2 - 11 * U * W + 2 * W^2

def D6highDen (U W : ℝ) : ℝ :=
  U * (1 + W) * (3 * U * W + 2 * U - 3 * W)

def D6highClosed (U W : ℝ) : ℝ := D6highNum U W / D6highDen U W

/-- Polynomial certificate for the substitution `L = W/U`.
    If `L*U = W` and denominators are nonzero, this implies `D6 = D6midClosed`. -/
theorem D6_mid_substitution_certificate (U W L : ℝ) :
    D6Num U W L * D6midDen U W - D6midNum U W * D6Den U W L =
      -(1 + W) * (L * U - W) * (3 * U * W + U - 2 * W) := by
  unfold D6Num D6midDen D6midNum D6Den
  ring

/-- Residual equation defining the high F6 scale. -/
def L6highResidual (U W L : ℝ) : ℝ :=
  (2 * U - W * (1 - U)) * L - 2 * W * (1 - U)

/-- Polynomial certificate for the high F6 endpoint substitution. -/
theorem D6_high_substitution_certificate (U W L : ℝ) :
    D6Num U W L * D6highDen U W - D6highNum U W * D6Den U W L =
      -U * (1 + W) * (3 * U * W + U - 2 * W) * L6highResidual U W L := by
  unfold D6Num D6highDen D6highNum D6Den L6highResidual
  ring

/-! ## 7. G6 geometry: common-denominator duration algebra -/

/-- Finite G6 scale on the intermediate side of `WH`. -/
def LGNum (U W : ℝ) : ℝ := W * (1 - U)
def LGDen (U W : ℝ) : ℝ := 2 * (U * W + U - W)
def LG (U W : ℝ) : ℝ := LGNum U W / LGDen U W

def gCommonDen (U : ℝ) : ℝ := 1 + U

def g1Num (U L : ℝ) : ℝ := 3 * (L * (1 - 2 * U) - U)
def g2Num (U W L : ℝ) : ℝ := (1 - 2 * U) * (L * (2 * W - 1) + W)
def g3Num (U L : ℝ) : ℝ := (L - 1) * (1 - 2 * U)
def g4Num (U W L : ℝ) : ℝ := g2Num U W L
def g5Num (U W L : ℝ) : ℝ := 2 * (4 * L * U * W + L * U - 2 * L * W + 2 * U * W - W)
def g6Num (U L : ℝ) : ℝ := L * (3 * U - 1)

/-- Actual G6 durations. -/
def g1 (U L : ℝ) : ℝ := g1Num U L / gCommonDen U
def g2 (U W L : ℝ) : ℝ := g2Num U W L / gCommonDen U
def g3 (U L : ℝ) : ℝ := g3Num U L / gCommonDen U
def g4 (U W L : ℝ) : ℝ := g4Num U W L / gCommonDen U
def g5 (U W L : ℝ) : ℝ := g5Num U W L / gCommonDen U
def g6 (U L : ℝ) : ℝ := g6Num U L / gCommonDen U

/-- Cleared period-duration identity. -/
theorem g_duration_num_identity (U W L : ℝ) :
    g1Num U L + g2Num U W L + g3Num U L + g4Num U W L +
      g5Num U W L + g6Num U L = (L - 1) * (1 + U) := by
  simp [g1Num, g2Num, g3Num, g4Num, g5Num, g6Num]
  ring

/-- Cleared contraction-mass numerator; G6 rates are `(2,0,3,1,1,2)`. -/
def gMassNum (U W L : ℝ) : ℝ :=
  2 * g1Num U L + 3 * g3Num U L + g4Num U W L +
    g5Num U W L + 2 * g6Num U L

def gMassClosedNum (U W L : ℝ) : ℝ :=
  4 * L * U * W - 8 * L * U - 2 * L * W + 6 * L + 2 * U * W - W - 3

theorem gMass_num_identity (U W L : ℝ) :
    gMassNum U W L = gMassClosedNum U W L := by
  simp [gMassNum, gMassClosedNum, g1Num, g2Num, g3Num, g4Num, g5Num, g6Num]
  ring

/-- Numerator of the B-peak time, with common denominator `1+U`. -/
def gPeakQNum (U W L : ℝ) : ℝ := (1 + U) + g1Num U L + g2Num U W L

def gPeakQClosedNum (U W L : ℝ) : ℝ :=
  (2 * L + 1) * (1 - 2 * U) * (1 + W)

theorem gPeakQ_num_identity (U W L : ℝ) :
    gPeakQNum U W L = gPeakQClosedNum U W L := by
  simp [gPeakQNum, gPeakQClosedNum, g1Num, g2Num]
  ring

/-- Closed G6 peak-phase numerator and denominator. -/
def DGNum (U W L : ℝ) : ℝ :=
  6 * L^2 - 12 * L^2 * U + 4 * L * U * W - 2 * L * U - 2 * L * W
    + 2 * U * W + 6 * U - W - 3

def DGDen (U W L : ℝ) : ℝ :=
  (L - 1) * (2 * L + 1) * (1 - 2 * U) * (1 + W)

def DG (U W L : ℝ) : ℝ := DGNum U W L / DGDen U W L

/-- The numerator obtained from `gMass/(L-1) + 2*g1` is exactly `DGNum`. -/
theorem gPeakPhase_num_identity (U W L : ℝ) :
    gMassNum U W L + 2 * g1Num U L * (L - 1) = DGNum U W L := by
  simp [gMassNum, DGNum, g1Num, g2Num, g3Num, g4Num, g5Num, g6Num]
  ring

/-! ## 8. G6 finite endpoint and closed form -/

def DGclosedNum (U W : ℝ) : ℝ :=
  12 * U^3 * W^2 + 30 * U^3 * W + 12 * U^3
    - 25 * U^2 * W^2 - 40 * U^2 * W - 6 * U^2
    + 16 * U * W^2 + 12 * U * W - 3 * W^2

def DGclosedDen (U W : ℝ) : ℝ :=
  U * (2 * U - 1) * (1 + W) * (3 * U * W + 2 * U - 3 * W)

def DGclosed (U W : ℝ) : ℝ := DGclosedNum U W / DGclosedDen U W

def LGResidual (U W L : ℝ) : ℝ := LGDen U W * L - LGNum U W

def DGLGFactor (U W L : ℝ) : ℝ :=
  (2 * U - 1) * (1 + W) *
    (12 * L * U^2 * W - 13 * L * U * W + 3 * L * W
      - 6 * U^2 * W - 8 * U^2 + 10 * U * W + 3 * U - 3 * W)

/-- Cross-multiplied certificate for substituting the G6 finite endpoint `LG`. -/
theorem DG_LG_substitution_certificate (U W L : ℝ) :
    DGNum U W L * DGclosedDen U W - DGclosedNum U W * DGDen U W L =
      LGResidual U W L * DGLGFactor U W L := by
  unfold DGNum DGclosedDen DGclosedNum DGDen LGResidual LGDen LGNum DGLGFactor
  ring

/-! ## 9. Exact comparison certificates, without division -/

/-- F6--G6 comparison.  This is the cross-multiplied form of the rational
    difference used in the research analysis. -/
theorem DG_D6_cross_certificate (U W : ℝ) :
    DGclosedNum U W * D6highDen U W - D6highNum U W * DGclosedDen U W =
      U * W * (U - 1) * (1 + W) *
        (3 * U * W + 2 * U - 3 * W) * crossPoly U W := by
  unfold DGclosedNum D6highDen D6highNum DGclosedDen crossPoly
  ring

/-! ### Eliminated F7 candidate -/

def D7Num (U W : ℝ) : ℝ :=
  2 * (6 * U^2 * W + 6 * U^2 - 8 * U * W - 3 * U + 3 * W)

def D7Den (U W : ℝ) : ℝ :=
  (1 + W) * (4 * U^2 - U * W - 2 * U + W)

def D7closed (U W : ℝ) : ℝ := D7Num U W / D7Den U W

theorem DG_D7_cross_certificate (U W : ℝ) :
    DGclosedNum U W * D7Den U W - D7Num U W * DGclosedDen U W =
      -(W^2 * (U - 1) * (3 * U - 1) * (4 * U - 3) *
        (1 + W) * birthPoly U W) := by
  unfold DGclosedNum D7Den D7Num DGclosedDen birthPoly
  ring

/-! ### F4 bubble -/

def D4Num (U W : ℝ) : ℝ :=
  24 * U^2 * W^2 + 24 * U^2 * W + 3 * U^2
    - 20 * U * W^2 - 11 * U * W + 4 * W^2

def D4Den (U W : ℝ) : ℝ := U * (1 + W) * (6 * U * W + U - 3 * W)
def D4 (U W : ℝ) : ℝ := D4Num U W / D4Den U W

def bubblePoly (U W : ℝ) : ℝ :=
  3 * (U - 1) * (2 * U - 1) * (4 * U - 1) * W^2
    + U * (16 * U^2 - 13 * U + 2) * W
    + U^2 * (4 * U - 1)

theorem DG_D4_cross_certificate (U W : ℝ) :
    DGclosedNum U W * D4Den U W - D4Num U W * DGclosedDen U W =
      -U * W * (3 * U - 1) * (1 + W) * bubblePoly U W := by
  unfold DGclosedNum D4Den D4Num DGclosedDen bubblePoly
  ring

/-- Quartic whose sign is opposite to the normalized discriminant of `bubblePoly`. -/
def etaPoly (U : ℝ) : ℝ :=
  128 * U^4 - 352 * U^3 + 271 * U^2 - 80 * U + 8

theorem bubble_discriminant_identity (U : ℝ) :
    (U * (16 * U^2 - 13 * U + 2))^2
      - 4 * (3 * (U - 1) * (2 * U - 1) * (4 * U - 1))
          * (U^2 * (4 * U - 1))
    = -(U^2) * etaPoly U := by
  unfold etaPoly
  ring

def bubbleRad (U : ℝ) : ℝ :=
  -128 * U^4 + 352 * U^3 - 271 * U^2 + 80 * U - 8

def WbubbleMinus (U : ℝ) : ℝ :=
  U * (-(16 * U^2 - 13 * U + 2) - Real.sqrt (bubbleRad U)) /
    (6 * (U - 1) * (2 * U - 1) * (4 * U - 1))

def WbubblePlus (U : ℝ) : ℝ :=
  U * (-(16 * U^2 - 13 * U + 2) + Real.sqrt (bubbleRad U)) /
    (6 * (U - 1) * (2 * U - 1) * (4 * U - 1))

/-!
Numerically, the first root of `etaPoly` above `1/3` is approximately

  eta = 0.3386679178022999529...

For `1/3 < U < eta`, the current symbolic search indicates a small F4 dominance
bubble between `WbubbleMinus U` and `WbubblePlus U`.

We intentionally do not introduce `eta` as a chosen algebraic real root yet.
-/

/-! ## 10. Universal high-W target -/

def Dhigh (W : ℝ) : ℝ := 3 / (1 + W)

theorem DG_leading_identity (U L : ℝ) :
    (6 - 12 * U) * L^2 = 6 * (1 - 2 * U) * L^2 := by
  ring

/-!
## 11. Current search conclusions (NOT YET Lean theorems)

The current finite-state / symbolic search imposed:

* multiplicatively self-similar cycles;
* one distinguished A-minimum and one distinguished B-peak per fundamental cycle;
* legal Roy switch/contact conditions in d = 4;
* active-word length <= 8;
* repeated-state free parameters eliminated by linear-fractional endpoint / phase-tie
  reduction.

Under those constraints, the current upper envelope is:

(A) For most `U` in `(1/3,1/2)`:

      F6  -->  G6  -->  Dhigh

    with F6/G6 crossing controlled by `crossPoly`, i.e. formally by `Wx`, and
    candidate high-W transition `WH U = U/(1-U)`.

(B) For a very small interval just above `1/3`, ending numerically near

      eta ~= 0.3386679178022999529,

    the current envelope is

      F6 --> G6 --> F4 --> G6 --> Dhigh,

    with the bubble controlled by `bubblePoly`.

(C) F7 is symbolically dominated by G6 on the common relevant domain; the exact
    comparison polynomial is encoded in `DG_D7_cross_certificate`.

(D) Repeated-state words of length <= 8 produced no new payoff function in the
    current symbolic elimination.  They reduced to zero-duration degenerations,
    refinements tying F6/G6/F4, or phase-tie branches dominated by that envelope.

IMPORTANT: (A)--(D) are research conclusions, not yet machine-checked exhaustiveness
statements.  A next formal phase should add:

1. contact states and Roy-legal transitions;
2. finite word enumeration through length 8;
3. linear closure/contact equations for a word;
4. the Möbius elimination lemma for a one-dimensional free duration parameter;
5. word-by-word dominance certificates.
-/

/-! ## 12. Threshold cross-multiplication certificates

These identities are preferable to quotient manipulations.  Once denominator signs are
proved on `1/3 < U < 1/2`, they imply the ordering

    Wc < WT < Wx < WH.
-/

def WcNum (U : ℝ) : ℝ := U
def WcDen (U : ℝ) : ℝ := 2 - 3 * U

def WHNum (U : ℝ) : ℝ := U
def WHDen (U : ℝ) : ℝ := 1 - U

/-- Cross numerator for `WT - Wc`. -/
theorem WT_Wc_cross_identity (U : ℝ) :
    WTNum U * WcDen U - WcNum U * WTDen U =
      -U * (2 * U - 1) * (3 * U - 1) := by
  unfold WTNum WcDen WcNum WTDen
  ring

/-- Cross numerator for `Wx - WT`. -/
theorem Wx_WT_cross_identity (U : ℝ) :
    WxNum U * WTDen U - WTNum U * WxDen U =
      U * (2 * U - 1)^2 * (3 * U - 1) := by
  unfold WxNum WTDen WTNum WxDen
  ring

/-- Cross numerator for `WH - Wx`. -/
theorem WH_Wx_cross_identity (U : ℝ) :
    WHNum U * WxDen U - WxNum U * WHDen U =
      -U^2 * (2 * U - 1) := by
  unfold WHNum WxDen WxNum WHDen
  ring

/-- Cross numerator for `WH - WT`. -/
theorem WH_WT_cross_identity (U : ℝ) :
    WHNum U * WTDen U - WTNum U * WHDen U =
      U * (U - 1) * (2 * U - 1) := by
  unfold WHNum WTDen WTNum WHDen
  ring

/-- The denominator controlling the finite G6 endpoint vanishes exactly at the
    high-W affine barrier `U - W(1-U) = 0`. -/
def highBarrier (U W : ℝ) : ℝ := U - W * (1 - U)

theorem LGDen_highBarrier (U W : ℝ) :
    LGDen U W = 2 * highBarrier U W := by
  unfold LGDen highBarrier
  ring

/-! ## 13. G6 endpoint-admissibility certificates

When `LGResidual U W L = 0`, the following identities give the six duration numerators
at the finite G6 endpoint without performing division.  In particular `g1` is born at
`birthPoly = 0`, i.e. at `W = WT` after the appropriate denominator sign check.
-/

theorem g1_LG_certificate (U W L : ℝ) :
    g1Num U L * LGDen U W + 3 * birthPoly U W =
      -3 * (2 * U - 1) * LGResidual U W L := by
  simp only [g1Num, birthPoly, LGResidual, LGDen, LGNum]
  ring

theorem g2_LG_certificate (U W L : ℝ) :
    g2Num U W L * LGDen U W + W * (2 * U - 1) * (3 * U - 1) =
      -(2 * U - 1) * (2 * W - 1) * LGResidual U W L := by
  simp only [g2Num, LGResidual, LGDen, LGNum]
  ring

theorem g3_LG_certificate (U W L : ℝ) :
    g3Num U L * LGDen U W -
        (2 * U - 1) * (3 * U * W + 2 * U - 3 * W) =
      (1 - 2 * U) * LGResidual U W L := by
  simp only [g3Num, LGResidual, LGDen, LGNum]
  ring

theorem g5_LG_certificate (U W L : ℝ) :
    g5Num U W L * LGDen U W - 2 * U * W * (3 * U - 1) =
      2 * (4 * U * W + U - 2 * W) * LGResidual U W L := by
  simp only [g5Num, LGResidual, LGDen, LGNum]
  ring

theorem g6_LG_certificate (U W L : ℝ) :
    g6Num U L * LGDen U W + W * (U - 1) * (3 * U - 1) =
      (3 * U - 1) * LGResidual U W L := by
  simp only [g6Num, LGResidual, LGDen, LGNum]
  ring

/-! ## 14. Exact comparison with the universal high-W target -/

/-- Cross numerator of `DG(U,W,L) - 3/(1+W)`.
    Its degree drops from two to one in `L`, making the `L -> infinity` limit transparent. -/
theorem DG_Dhigh_cross_identity (U W L : ℝ) :
    DGNum U W L * (1 + W) - 3 * DGDen U W L =
      (1 + W) *
        (4 * L * U * W - 8 * L * U - 2 * L * W + 3 * L +
          2 * U * W - W) := by
  unfold DGNum DGDen
  ring

/-! ## 15. Algebraic core of repeated-state / Möbius elimination -/

/-- Numerator of a generic linear-fractional phase function. -/
def mobNum (a b t : ℝ) : ℝ := a + b * t

/-- Denominator of a generic linear-fractional phase function. -/
def mobDen (c d t : ℝ) : ℝ := c + d * t

/-- The cross-difference of a Möbius function at two parameter values factors into
    a constant determinant times `t₂ - t₁`.  Thus, wherever the two denominators
    have fixed positive sign, the function is monotone unless `b*c-a*d = 0`, in
    which case it is constant. -/
theorem mobius_cross_difference
    (a b c d t1 t2 : ℝ) :
    mobNum a b t2 * mobDen c d t1 - mobNum a b t1 * mobDen c d t2 =
      (b * c - a * d) * (t2 - t1) := by
  unfold mobNum mobDen
  ring

/-- A phase-tie equation between two affine-fractional expressions is polynomial
    after cross multiplication.  This is the algebraic reduction used when a free
    repeated-state parameter is stopped by equality of two vertex phase averages. -/
theorem mobius_phase_tie_cross
    (a1 b1 c1 d1 a2 b2 c2 d2 t : ℝ) :
    mobNum a1 b1 t * mobDen c2 d2 t -
        mobNum a2 b2 t * mobDen c1 d1 t =
      (a1 * c2 - a2 * c1) +
      (a1 * d2 + b1 * c2 - a2 * d1 - b2 * c1) * t +
      (b1 * d2 - b2 * d1) * t^2 := by
  unfold mobNum mobDen
  ring

/-!
## 16. Next formal layer

`v2` compiled cleanly on live.lean-lang.org.  Sections 12--15 are the next algebraic
layer and are deliberately still certificate-oriented.

Once this file compiles, the next useful additions are sign lemmas on the domain
`1/3 < U < 1/2`, followed by quotient-level corollaries such as

    Wc < WT < Wx < WH,
    F6 >= G6 for W <= Wx,
    G6 >= F6 for W >= Wx,
    G6 >= F7 for W >= WT.

Only after those scalar/domain facts are stable should we encode the finite Roy-state
transition graph and the length <= 8 enumeration itself.
-/

/-! ## 17. Ordered uniform-exponent domain and threshold signs

This section begins the first quotient-level layer.  The hypotheses

    1/3 < U < 1/2

are the natural nontrivial simultaneous-three-number range in the transposed
`1 x 3` coordinates.  We first isolate all denominator signs used later.
-/

theorem U_pos_of_domain {U : ℝ} (hUlo : (1 : ℝ) / 3 < U) : 0 < U := by
  nlinarith

theorem one_sub_U_pos_of_domain {U : ℝ} (_hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2) : 0 < 1 - U := by
  nlinarith

theorem one_sub_twoU_pos_of_domain {U : ℝ} (_hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2) : 0 < 1 - 2 * U := by
  nlinarith

theorem threeU_sub_one_pos_of_domain {U : ℝ} (hUlo : (1 : ℝ) / 3 < U)
    (_hUhi : U < (1 : ℝ) / 2) : 0 < 3 * U - 1 := by
  nlinarith

theorem WcDen_pos_of_domain {U : ℝ} (_hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2) : 0 < WcDen U := by
  unfold WcDen
  nlinarith

theorem WTDen_pos_of_domain {U : ℝ} (_hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2) : 0 < WTDen U := by
  unfold WTDen
  nlinarith

theorem WHDen_pos_of_domain {U : ℝ} (_hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2) : 0 < WHDen U := by
  unfold WHDen
  nlinarith

/-- Positivity of the denominator of `Wx` on `1/3 < U < 1/2`.
    We prove it from the positive interval product
    `(U-1/3)*(1/2-U) > 0`, avoiding a root computation. -/
theorem WxDen_pos_of_domain {U : ℝ} (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2) : 0 < WxDen U := by
  have hp : 0 < (U - (1 : ℝ) / 3) * ((1 : ℝ) / 2 - U) :=
    mul_pos (sub_pos.mpr hUlo) (sub_pos.mpr hUhi)
  have hU : 0 < U := U_pos_of_domain hUlo
  unfold WxDen
  nlinarith [hp]

/-! ### Exact threshold ordering -/

theorem Wc_lt_WT_of_domain {U : ℝ} (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2) : Wc U < WT U := by
  have hc : 0 < WcDen U := WcDen_pos_of_domain hUlo hUhi
  have ht : 0 < WTDen U := WTDen_pos_of_domain hUlo hUhi
  have hU : 0 < U := U_pos_of_domain hUlo
  have h12 : 0 < 1 - 2 * U := one_sub_twoU_pos_of_domain hUlo hUhi
  have h31 : 0 < 3 * U - 1 := threeU_sub_one_pos_of_domain hUlo hUhi
  have hp : 0 < U * (1 - 2 * U) * (3 * U - 1) :=
    mul_pos (mul_pos hU h12) h31
  change WcNum U / WcDen U < WTNum U / WTDen U
  rw [div_lt_div_iff₀ hc ht]
  have hid := WT_Wc_cross_identity U
  nlinarith [hid, hp]

theorem WT_lt_Wx_of_domain {U : ℝ} (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2) : WT U < Wx U := by
  have ht : 0 < WTDen U := WTDen_pos_of_domain hUlo hUhi
  have hx : 0 < WxDen U := WxDen_pos_of_domain hUlo hUhi
  have hU : 0 < U := U_pos_of_domain hUlo
  have h12 : 0 < 1 - 2 * U := one_sub_twoU_pos_of_domain hUlo hUhi
  have h31 : 0 < 3 * U - 1 := threeU_sub_one_pos_of_domain hUlo hUhi
  have hs : 0 < (1 - 2 * U)^2 := sq_pos_of_ne_zero (ne_of_gt h12)
  have hp : 0 < U * (1 - 2 * U)^2 * (3 * U - 1) :=
    mul_pos (mul_pos hU hs) h31
  change WTNum U / WTDen U < WxNum U / WxDen U
  rw [div_lt_div_iff₀ ht hx]
  have hid := Wx_WT_cross_identity U
  nlinarith [hid, hp]

theorem Wx_lt_WH_of_domain {U : ℝ} (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2) : Wx U < WH U := by
  have hx : 0 < WxDen U := WxDen_pos_of_domain hUlo hUhi
  have hh : 0 < WHDen U := WHDen_pos_of_domain hUlo hUhi
  have hU : 0 < U := U_pos_of_domain hUlo
  have h12 : 0 < 1 - 2 * U := one_sub_twoU_pos_of_domain hUlo hUhi
  have hp : 0 < U^2 * (1 - 2 * U) := by positivity
  change WxNum U / WxDen U < WHNum U / WHDen U
  rw [div_lt_div_iff₀ hx hh]
  have hid := WH_Wx_cross_identity U
  nlinarith [hid, hp]

/-- The basic candidate transition chain on the nontrivial U-domain. -/
theorem threshold_chain_of_domain {U : ℝ} (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2) :
    Wc U < WT U ∧ WT U < Wx U ∧ Wx U < WH U := by
  exact ⟨Wc_lt_WT_of_domain hUlo hUhi,
    WT_lt_Wx_of_domain hUlo hUhi,
    Wx_lt_WH_of_domain hUlo hUhi⟩

/-! ## 18. Threshold residual identities and sign corollaries -/

/-- `birthPoly` is exactly the cleared residual for `W <= WT`. -/
theorem birthPoly_residual (U W : ℝ) :
    birthPoly U W = WTNum U - W * WTDen U := by
  unfold birthPoly WTNum WTDen
  ring

/-- `crossPoly` is exactly the cleared residual for `W <= Wx`. -/
theorem crossPoly_residual (U W : ℝ) :
    crossPoly U W = WxNum U - W * WxDen U := by
  unfold crossPoly WxNum WxDen
  ring

/-- `highBarrier` is exactly the cleared residual for `W <= WH`. -/
theorem highBarrier_residual (U W : ℝ) :
    highBarrier U W = WHNum U - W * WHDen U := by
  unfold highBarrier WHNum WHDen
  ring

theorem birthPoly_nonneg_of_W_le_WT {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : W ≤ WT U) : 0 ≤ birthPoly U W := by
  have hd : 0 < WTDen U := WTDen_pos_of_domain hUlo hUhi
  have hfrac : W ≤ WTNum U / WTDen U := by
    simpa [WT, WTNum, WTDen] using hW
  have hc : W * WTDen U ≤ WTNum U := (le_div_iff₀ hd).mp hfrac
  rw [birthPoly_residual]
  linarith

theorem birthPoly_nonpos_of_W_ge_WT {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : WT U ≤ W) : birthPoly U W ≤ 0 := by
  have hd : 0 < WTDen U := WTDen_pos_of_domain hUlo hUhi
  have hfrac : WTNum U / WTDen U ≤ W := by
    simpa [WT, WTNum, WTDen] using hW
  have hc : WTNum U ≤ W * WTDen U := (div_le_iff₀ hd).mp hfrac
  rw [birthPoly_residual]
  linarith

theorem crossPoly_nonneg_of_W_le_Wx {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : W ≤ Wx U) : 0 ≤ crossPoly U W := by
  have hd : 0 < WxDen U := WxDen_pos_of_domain hUlo hUhi
  have hfrac : W ≤ WxNum U / WxDen U := by
    simpa [Wx] using hW
  have hc : W * WxDen U ≤ WxNum U := (le_div_iff₀ hd).mp hfrac
  rw [crossPoly_residual]
  linarith

theorem crossPoly_nonpos_of_W_ge_Wx {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : Wx U ≤ W) : crossPoly U W ≤ 0 := by
  have hd : 0 < WxDen U := WxDen_pos_of_domain hUlo hUhi
  have hfrac : WxNum U / WxDen U ≤ W := by
    simpa [Wx] using hW
  have hc : WxNum U ≤ W * WxDen U := (div_le_iff₀ hd).mp hfrac
  rw [crossPoly_residual]
  linarith

theorem highBarrier_nonneg_of_W_le_WH {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : W ≤ WH U) : 0 ≤ highBarrier U W := by
  have hd : 0 < WHDen U := WHDen_pos_of_domain hUlo hUhi
  have hfrac : W ≤ WHNum U / WHDen U := by
    simpa [WH, WHNum, WHDen] using hW
  have hc : W * WHDen U ≤ WHNum U := (le_div_iff₀ hd).mp hfrac
  rw [highBarrier_residual]
  linarith

theorem highBarrier_nonpos_of_W_ge_WH {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : WH U ≤ W) : highBarrier U W ≤ 0 := by
  have hd : 0 < WHDen U := WHDen_pos_of_domain hUlo hUhi
  have hfrac : WHNum U / WHDen U ≤ W := by
    simpa [WH, WHNum, WHDen] using hW
  have hc : WHNum U ≤ W * WHDen U := (div_le_iff₀ hd).mp hfrac
  rw [highBarrier_residual]
  linarith

/-!
## 19. Checkpoint after v4

Version v4 compiled successfully on live.lean-lang.org.

Sections 17--18 are intentionally the next small step: they move from polynomial
certificates to actual sign and ordering statements, but stop before quotient-level
F6/G6/F7 dominance.  If this checkpoint compiles, the next layer should prove the
relevant denominator signs in the common `(U,W)` regions and then convert the existing
cross certificates into inequalities between `D6highClosed`, `DGclosed`, and `D7closed`.
-/


/-! ## 20. Common denominator signs on the intermediate domain

The quotient-level dominance theorems below use only the region

    1/3 < U < 1/2,   WT U <= W.

On this region the common affine factor

    Q(U,W) = 3*U*W + 2*U - 3*W

is strictly negative.  Consequently `D6highDen < 0` while `DGclosedDen > 0`.
The sign flip comes from the additional factor `2*U-1 < 0` in `DGclosedDen`.
-/

def commonQ (U W : ℝ) : ℝ := 3 * U * W + 2 * U - 3 * W

theorem W_pos_of_W_ge_WT {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : WT U ≤ W) : 0 < W := by
  have hU : 0 < U := U_pos_of_domain hUlo
  have h1U : 0 < 1 - U := one_sub_U_pos_of_domain hUlo hUhi
  have hWT : 0 < WT U := by
    unfold WT
    positivity
  exact lt_of_lt_of_le hWT hW

theorem commonQ_neg_of_W_ge_WT {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : WT U ≤ W) : commonQ U W < 0 := by
  have hU : 0 < U := U_pos_of_domain hUlo
  have h1U : 0 < 1 - U := one_sub_U_pos_of_domain hUlo hUhi
  have h31 : 0 < 3 * U - 1 := threeU_sub_one_pos_of_domain hUlo hUhi
  have hfrac : 2 * U^2 / (1 - U) ≤ W := by
    simpa [WT] using hW
  have hmul : 2 * U^2 ≤ W * (1 - U) := (div_le_iff₀ h1U).mp hfrac
  have hprod : 0 < 2 * U * (3 * U - 1) := by positivity
  unfold commonQ
  nlinarith [hmul, hprod]

theorem D6highDen_neg_of_W_ge_WT {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : WT U ≤ W) : D6highDen U W < 0 := by
  have hU : 0 < U := U_pos_of_domain hUlo
  have hWp : 0 < W := W_pos_of_W_ge_WT hUlo hUhi hW
  have h1W : 0 < 1 + W := by linarith
  have hq : commonQ U W < 0 := commonQ_neg_of_W_ge_WT hUlo hUhi hW
  have hq' : 3 * U * W + 2 * U - 3 * W < 0 := by
    simpa [commonQ] using hq
  have hleft : 0 < U * (1 + W) := mul_pos hU h1W
  unfold D6highDen
  exact mul_neg_of_pos_of_neg hleft hq'

theorem DGclosedDen_pos_of_W_ge_WT {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : WT U ≤ W) : 0 < DGclosedDen U W := by
  have hU : 0 < U := U_pos_of_domain hUlo
  have h2U : 2 * U - 1 < 0 := by nlinarith
  have hWp : 0 < W := W_pos_of_W_ge_WT hUlo hUhi hW
  have h1W : 0 < 1 + W := by linarith
  have hq : commonQ U W < 0 := commonQ_neg_of_W_ge_WT hUlo hUhi hW
  have hq' : 3 * U * W + 2 * U - 3 * W < 0 := by
    simpa [commonQ] using hq
  have hneg1 : U * (2 * U - 1) < 0 := mul_neg_of_pos_of_neg hU h2U
  have hneg2 : U * (2 * U - 1) * (1 + W) < 0 :=
    mul_neg_of_neg_of_pos hneg1 h1W
  unfold DGclosedDen
  exact mul_pos_of_neg_of_neg hneg2 hq'

theorem D7Den_pos_of_W_ge_WT {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : WT U ≤ W) : 0 < D7Den U W := by
  have hU : 0 < U := U_pos_of_domain hUlo
  have h1U : 0 < 1 - U := one_sub_U_pos_of_domain hUlo hUhi
  have h31 : 0 < 3 * U - 1 := threeU_sub_one_pos_of_domain hUlo hUhi
  have hWp : 0 < W := W_pos_of_W_ge_WT hUlo hUhi hW
  have h1W : 0 < 1 + W := by linarith
  have hfrac : 2 * U^2 / (1 - U) ≤ W := by
    simpa [WT] using hW
  have hmul : 2 * U^2 ≤ W * (1 - U) := (div_le_iff₀ h1U).mp hfrac
  have hprod : 0 < 2 * U * (3 * U - 1) := by positivity
  have hinner : 0 < 4 * U^2 - U * W - 2 * U + W := by
    nlinarith [hmul, hprod]
  unfold D7Den
  exact mul_pos h1W hinner

/-! ## 21. Quotient-level F6--G6 dominance

`D6highDen` is negative in the common region, so we rewrite the F6 quotient with
both numerator and denominator negated before using `div_le_div_iff₀`.
-/

def D6highAltNum (U W : ℝ) : ℝ := -D6highNum U W

def D6highAltDen (U W : ℝ) : ℝ := -D6highDen U W

theorem D6highClosed_eq_alt (U W : ℝ) :
    D6highClosed U W = D6highAltNum U W / D6highAltDen U W := by
  unfold D6highClosed D6highAltNum D6highAltDen
  simp

theorem D6highAltDen_pos_of_W_ge_WT {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hW : WT U ≤ W) : 0 < D6highAltDen U W := by
  unfold D6highAltDen
  have h := D6highDen_neg_of_W_ge_WT hUlo hUhi hW
  linarith

/-- The common signed prefactor in the F6--G6 cross certificate is positive
    throughout the region `W >= WT`.  Writing the sign argument explicitly is more
    robust than asking `positivity` to discover the two negative factors. -/
theorem DG_D6_base_pos_of_W_ge_WT {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W) :
    0 < U * W * (U - 1) * (1 + W) *
      (3 * U * W + 2 * U - 3 * W) := by
  have hU : 0 < U := U_pos_of_domain hUlo
  have hWp : 0 < W := W_pos_of_W_ge_WT hUlo hUhi hWT
  have hUm1 : U - 1 < 0 := by nlinarith
  have h1W : 0 < 1 + W := by linarith
  have hq : commonQ U W < 0 := commonQ_neg_of_W_ge_WT hUlo hUhi hWT
  have hq' : 3 * U * W + 2 * U - 3 * W < 0 := by
    simpa [commonQ] using hq
  have hpos1 : 0 < U * W := mul_pos hU hWp
  have hneg1 : U * W * (U - 1) < 0 := mul_neg_of_pos_of_neg hpos1 hUm1
  have hneg2 : U * W * (U - 1) * (1 + W) < 0 :=
    mul_neg_of_neg_of_pos hneg1 h1W
  exact mul_pos_of_neg_of_neg hneg2 hq'

/-- Below the crossing `Wx`, the optimized high branch of F6 dominates G6. -/
theorem DGclosed_le_D6highClosed_of_W_le_Wx {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W) (hWx : W ≤ Wx U) :
    DGclosed U W ≤ D6highClosed U W := by
  have hDG : 0 < DGclosedDen U W := DGclosedDen_pos_of_W_ge_WT hUlo hUhi hWT
  have hD6 : 0 < D6highAltDen U W := D6highAltDen_pos_of_W_ge_WT hUlo hUhi hWT
  have hcp : 0 ≤ crossPoly U W :=
    crossPoly_nonneg_of_W_le_Wx hUlo hUhi hWx
  have hbase :
      0 < U * W * (U - 1) * (1 + W) *
        (3 * U * W + 2 * U - 3 * W) :=
    DG_D6_base_pos_of_W_ge_WT hUlo hUhi hWT
  have hcross :
      0 ≤ U * W * (U - 1) * (1 + W) *
        (3 * U * W + 2 * U - 3 * W) * crossPoly U W :=
    mul_nonneg (le_of_lt hbase) hcp
  have hcert := DG_D6_cross_certificate U W
  rw [D6highClosed_eq_alt]
  change DGclosedNum U W / DGclosedDen U W ≤
    D6highAltNum U W / D6highAltDen U W
  apply (div_le_div_iff₀ hDG hD6).2
  unfold D6highAltNum D6highAltDen
  nlinarith [hcert, hcross]

/-- Above the crossing `Wx`, G6 dominates the optimized high branch of F6. -/
theorem D6highClosed_le_DGclosed_of_W_ge_Wx {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hWx : Wx U ≤ W) :
    D6highClosed U W ≤ DGclosed U W := by
  have hchain := threshold_chain_of_domain hUlo hUhi
  have hWT : WT U ≤ W := le_trans (le_of_lt hchain.2.1) hWx
  have hDG : 0 < DGclosedDen U W := DGclosedDen_pos_of_W_ge_WT hUlo hUhi hWT
  have hD6 : 0 < D6highAltDen U W := D6highAltDen_pos_of_W_ge_WT hUlo hUhi hWT
  have hcp : crossPoly U W ≤ 0 :=
    crossPoly_nonpos_of_W_ge_Wx hUlo hUhi hWx
  have hbase :
      0 < U * W * (U - 1) * (1 + W) *
        (3 * U * W + 2 * U - 3 * W) :=
    DG_D6_base_pos_of_W_ge_WT hUlo hUhi hWT
  have hcross :
      U * W * (U - 1) * (1 + W) *
        (3 * U * W + 2 * U - 3 * W) * crossPoly U W ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hbase) hcp
  have hcert := DG_D6_cross_certificate U W
  rw [D6highClosed_eq_alt]
  change D6highAltNum U W / D6highAltDen U W ≤
    DGclosedNum U W / DGclosedDen U W
  apply (div_le_div_iff₀ hD6 hDG).2
  unfold D6highAltNum D6highAltDen
  nlinarith [hcert, hcross]

/-! ## 22. Quotient-level elimination of F7 -/

/-- On its natural birth domain `W >= WT`, the seven-piece candidate F7 never
    exceeds the finite-endpoint G6 value.  Equality occurs at the degeneration
    `birthPoly = 0`, i.e. `W = WT`, once the threshold equation is imposed. -/
theorem D7closed_le_DGclosed_of_W_ge_WT {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W) :
    D7closed U W ≤ DGclosed U W := by
  have hWp : 0 < W := W_pos_of_W_ge_WT hUlo hUhi hWT
  have hUm1 : U - 1 < 0 := by nlinarith
  have h31 : 0 < 3 * U - 1 := threeU_sub_one_pos_of_domain hUlo hUhi
  have h43 : 4 * U - 3 < 0 := by nlinarith
  have h1W : 0 < 1 + W := by linarith
  have hbirth : birthPoly U W ≤ 0 :=
    birthPoly_nonpos_of_W_ge_WT hUlo hUhi hWT
  have hDG : 0 < DGclosedDen U W := DGclosedDen_pos_of_W_ge_WT hUlo hUhi hWT
  have hD7 : 0 < D7Den U W := D7Den_pos_of_W_ge_WT hUlo hUhi hWT
  have hW2 : 0 < W^2 := by
    simpa [pow_two] using mul_pos hWp hWp
  have hneg1 : W^2 * (U - 1) < 0 := mul_neg_of_pos_of_neg hW2 hUm1
  have hneg2 : W^2 * (U - 1) * (3 * U - 1) < 0 :=
    mul_neg_of_neg_of_pos hneg1 h31
  have hpos1 : 0 < W^2 * (U - 1) * (3 * U - 1) * (4 * U - 3) :=
    mul_pos_of_neg_of_neg hneg2 h43
  have hbase :
      0 < W^2 * (U - 1) * (3 * U - 1) * (4 * U - 3) * (1 + W) :=
    mul_pos hpos1 h1W
  have hins :
      W^2 * (U - 1) * (3 * U - 1) * (4 * U - 3) *
        (1 + W) * birthPoly U W ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hbase) hbirth
  have hcross :
      0 ≤ -(W^2 * (U - 1) * (3 * U - 1) * (4 * U - 3) *
        (1 + W) * birthPoly U W) := by
    linarith
  have hcert := DG_D7_cross_certificate U W
  change D7Num U W / D7Den U W ≤ DGclosedNum U W / DGclosedDen U W
  apply (div_le_div_iff₀ hD7 hDG).2
  nlinarith [hcert, hcross]

/-! ## 23. Boundary equalities at the algebraic transition points -/

/-- The F6--G6 cross numerator vanishes whenever `crossPoly = 0`. -/
theorem DG_D6_cross_zero_of_crossPoly_zero {U W : ℝ}
    (hcross : crossPoly U W = 0) :
    DGclosedNum U W * D6highDen U W -
      D6highNum U W * DGclosedDen U W = 0 := by
  rw [DG_D6_cross_certificate, hcross]
  ring

/-- The G6--F7 cross numerator vanishes whenever `birthPoly = 0`. -/
theorem DG_D7_cross_zero_of_birthPoly_zero {U W : ℝ}
    (hbirth : birthPoly U W = 0) :
    DGclosedNum U W * D7Den U W -
      D7Num U W * DGclosedDen U W = 0 := by
  rw [DG_D7_cross_certificate, hbirth]
  ring

/-!
## 24. Checkpoint after v6

Version v5 compiled successfully on live.lean-lang.org.

Sections 20--23 are the first actual quotient-level dominance layer:

* denominator signs on `WT <= W`;
* F6 >= G6 below `Wx` and G6 >= F6 above `Wx`;
* G6 >= F7 on the whole F7 birth domain;
* exact cross-numerator vanishing at the two algebraic transition loci.

The next natural layer, once this compiles, is the F4 bubble.  That requires proving the
sign of `D4Den` on the relevant overlap and then converting `DG_D4_cross_certificate`
into the equivalence between `DGclosed >= D4` and `bubblePoly >= 0`.
-/


/-! ## 24. F4 denominator geometry

The four-piece top-triple family has denominator

    U * (1+W) * (6*U*W + U - 3*W).

The final affine factor changes sign at

    WD4(U) = U / (3*(1-2*U)).

The small F4 bubble found by the symbolic search lies strictly on the side where this
factor is negative.  We therefore record the sign condition explicitly rather than baking
an unproved global domain statement into the comparison theorem.
-/

def WD4 (U : ℝ) : ℝ := U / (3 * (1 - 2 * U))

def D4Affine (U W : ℝ) : ℝ := 6 * U * W + U - 3 * W

theorem WD4_den_pos_of_domain {U : ℝ}
    (hUhi : U < (1 : ℝ) / 2) :
    0 < 3 * (1 - 2 * U) := by
  have h : 0 < 1 - 2 * U := by nlinarith
  positivity

theorem D4Affine_neg_of_W_gt_WD4 {U W : ℝ}
    (hUhi : U < (1 : ℝ) / 2) (hW : WD4 U < W) :
    D4Affine U W < 0 := by
  have hden : 0 < 3 * (1 - 2 * U) := WD4_den_pos_of_domain hUhi
  have hfrac : U / (3 * (1 - 2 * U)) < W := by
    simpa [WD4] using hW
  have hmul : U < W * (3 * (1 - 2 * U)) :=
    (div_lt_iff₀ hden).mp hfrac
  unfold D4Affine
  nlinarith [hmul]

theorem D4Den_neg_of_W_gt_WD4 {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W) (hW : WD4 U < W) :
    D4Den U W < 0 := by
  have hU : 0 < U := U_pos_of_domain hUlo
  have hWp : 0 < W := W_pos_of_W_ge_WT hUlo hUhi hWT
  have h1W : 0 < 1 + W := by linarith
  have hq : D4Affine U W < 0 := D4Affine_neg_of_W_gt_WD4 hUhi hW
  have hpos : 0 < U * (1 + W) := mul_pos hU h1W
  change U * (1 + W) * D4Affine U W < 0
  exact mul_neg_of_pos_of_neg hpos hq

/-! ## 25. Quotient-level G6--F4 comparison -/

def D4AltNum (U W : ℝ) : ℝ := -D4Num U W

def D4AltDen (U W : ℝ) : ℝ := -D4Den U W

theorem D4_eq_alt (U W : ℝ) :
    D4 U W = D4AltNum U W / D4AltDen U W := by
  unfold D4 D4AltNum D4AltDen
  simp

theorem D4AltDen_pos_of_W_gt_WD4 {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W) (hW : WD4 U < W) :
    0 < D4AltDen U W := by
  unfold D4AltDen
  have h := D4Den_neg_of_W_gt_WD4 hUlo hUhi hWT hW
  linarith

/-- The G6--F4 cross certificate rewritten with the positive version of the F4 denominator. -/
theorem DG_D4_alt_cross_certificate (U W : ℝ) :
    DGclosedNum U W * D4AltDen U W -
      D4AltNum U W * DGclosedDen U W =
      U * W * (3 * U - 1) * (1 + W) * bubblePoly U W := by
  unfold DGclosedNum D4AltDen D4AltNum D4Den D4Num DGclosedDen bubblePoly
  ring

/-- The scalar prefactor in the positive-denominator G6--F4 certificate is positive. -/
theorem DG_D4_base_pos_of_W_ge_WT {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W) :
    0 < U * W * (3 * U - 1) * (1 + W) := by
  have hU : 0 < U := U_pos_of_domain hUlo
  have hWp : 0 < W := W_pos_of_W_ge_WT hUlo hUhi hWT
  have h31 : 0 < 3 * U - 1 := threeU_sub_one_pos_of_domain hUlo hUhi
  have h1W : 0 < 1 + W := by linarith
  have hUW : 0 < U * W := mul_pos hU hWp
  have hUW31 : 0 < U * W * (3 * U - 1) := mul_pos hUW h31
  exact mul_pos hUW31 h1W

/-- If `bubblePoly >= 0`, then G6 dominates F4 on the common denominator-sign domain. -/
theorem D4_le_DGclosed_of_bubble_nonneg {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W) (hWD4 : WD4 U < W)
    (hb : 0 ≤ bubblePoly U W) :
    D4 U W ≤ DGclosed U W := by
  have hDG : 0 < DGclosedDen U W := DGclosedDen_pos_of_W_ge_WT hUlo hUhi hWT
  have hD4 : 0 < D4AltDen U W := D4AltDen_pos_of_W_gt_WD4 hUlo hUhi hWT hWD4
  have hbase : 0 < U * W * (3 * U - 1) * (1 + W) :=
    DG_D4_base_pos_of_W_ge_WT hUlo hUhi hWT
  have hcross :
      0 ≤ U * W * (3 * U - 1) * (1 + W) * bubblePoly U W :=
    mul_nonneg (le_of_lt hbase) hb
  have hcert := DG_D4_alt_cross_certificate U W
  rw [D4_eq_alt]
  change D4AltNum U W / D4AltDen U W ≤
    DGclosedNum U W / DGclosedDen U W
  apply (div_le_div_iff₀ hD4 hDG).2
  nlinarith [hcert, hcross]

/-- If `bubblePoly <= 0`, then F4 dominates G6 on the common denominator-sign domain. -/
theorem DGclosed_le_D4_of_bubble_nonpos {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W) (hWD4 : WD4 U < W)
    (hb : bubblePoly U W ≤ 0) :
    DGclosed U W ≤ D4 U W := by
  have hDG : 0 < DGclosedDen U W := DGclosedDen_pos_of_W_ge_WT hUlo hUhi hWT
  have hD4 : 0 < D4AltDen U W := D4AltDen_pos_of_W_gt_WD4 hUlo hUhi hWT hWD4
  have hbase : 0 < U * W * (3 * U - 1) * (1 + W) :=
    DG_D4_base_pos_of_W_ge_WT hUlo hUhi hWT
  have hcross :
      U * W * (3 * U - 1) * (1 + W) * bubblePoly U W ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hbase) hb
  have hcert := DG_D4_alt_cross_certificate U W
  rw [D4_eq_alt]
  change DGclosedNum U W / DGclosedDen U W ≤
    D4AltNum U W / D4AltDen U W
  apply (div_le_div_iff₀ hDG hD4).2
  nlinarith [hcert, hcross]

/-! ## 26. The quartic discriminant mechanism

For fixed `U`, `bubblePoly U W` is a quadratic in `W`.  Instead of introducing the
algebraic root `eta` now, we prove the exact completed-square identity.  It implies:

    etaPoly U > 0  ==>  bubblePoly U W > 0 for every W,

throughout the geometric U-domain.  Hence in that region F4 cannot beat G6 anywhere on
the common denominator-sign domain.
-/

def bubbleA (U : ℝ) : ℝ :=
  3 * (U - 1) * (2 * U - 1) * (4 * U - 1)

def bubbleB (U : ℝ) : ℝ :=
  U * (16 * U^2 - 13 * U + 2)

def bubbleC (U : ℝ) : ℝ :=
  U^2 * (4 * U - 1)

theorem bubblePoly_coefficients (U W : ℝ) :
    bubblePoly U W = bubbleA U * W^2 + bubbleB U * W + bubbleC U := by
  unfold bubblePoly bubbleA bubbleB bubbleC
  ring

theorem bubble_complete_square_identity (U W : ℝ) :
    4 * bubbleA U * bubblePoly U W =
      (2 * bubbleA U * W + bubbleB U)^2 + U^2 * etaPoly U := by
  unfold bubbleA bubbleB bubblePoly etaPoly
  ring

theorem bubbleA_pos_of_domain {U : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2) :
    0 < bubbleA U := by
  have hUm1 : U - 1 < 0 := by nlinarith
  have h2 : 2 * U - 1 < 0 := by nlinarith
  have h4 : 0 < 4 * U - 1 := by nlinarith
  have h3 : (0 : ℝ) < 3 := by norm_num
  have h3Um1 : 3 * (U - 1) < 0 :=
    mul_neg_of_pos_of_neg h3 hUm1
  have h312 : 0 < (3 * (U - 1)) * (2 * U - 1) :=
    mul_pos_of_neg_of_neg h3Um1 h2
  unfold bubbleA
  exact mul_pos h312 h4

/-- Positive `etaPoly` forces the bubble quadratic to be strictly positive for every W. -/
theorem bubblePoly_pos_of_etaPoly_pos {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (heta : 0 < etaPoly U) :
    0 < bubblePoly U W := by
  have hA : 0 < bubbleA U := bubbleA_pos_of_domain hUlo hUhi
  have hU : 0 < U := U_pos_of_domain hUlo
  have hU2 : 0 < U^2 := by positivity
  have hetaTerm : 0 < U^2 * etaPoly U := mul_pos hU2 heta
  have hsq : 0 ≤ (2 * bubbleA U * W + bubbleB U)^2 := sq_nonneg _
  have hrhs :
      0 < (2 * bubbleA U * W + bubbleB U)^2 + U^2 * etaPoly U :=
    add_pos_of_nonneg_of_pos hsq hetaTerm
  have hid := bubble_complete_square_identity U W
  have hlhs : 0 < 4 * bubbleA U * bubblePoly U W := by
    rw [hid]
    exact hrhs
  have hfac : 0 < 4 * bubbleA U := by positivity
  nlinarith

/-- Consequently, whenever `etaPoly U > 0`, F4 is dominated by G6 throughout the
    common comparison region. -/
theorem D4_lt_DGclosed_of_etaPoly_pos {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W) (hWD4 : WD4 U < W)
    (heta : 0 < etaPoly U) :
    D4 U W < DGclosed U W := by
  have hb : 0 < bubblePoly U W :=
    bubblePoly_pos_of_etaPoly_pos hUlo hUhi heta
  have hDG : 0 < DGclosedDen U W := DGclosedDen_pos_of_W_ge_WT hUlo hUhi hWT
  have hD4 : 0 < D4AltDen U W := D4AltDen_pos_of_W_gt_WD4 hUlo hUhi hWT hWD4
  have hbase : 0 < U * W * (3 * U - 1) * (1 + W) :=
    DG_D4_base_pos_of_W_ge_WT hUlo hUhi hWT
  have hcross :
      0 < U * W * (3 * U - 1) * (1 + W) * bubblePoly U W :=
    mul_pos hbase hb
  have hcert := DG_D4_alt_cross_certificate U W
  rw [D4_eq_alt]
  change D4AltNum U W / D4AltDen U W <
    DGclosedNum U W / DGclosedDen U W
  apply (div_lt_div_iff₀ hD4 hDG).2
  nlinarith [hcert, hcross]

/-!
## 27. Checkpoint after v8 additions

Version v7 compiled successfully on live.lean-lang.org.

The new sections formalize the F4 comparison without yet selecting the algebraic constant
`eta`:

* the sign change of the F4 denominator at `WD4`;
* quotient-level equivalence of the G6/F4 ordering with the sign of `bubblePoly`;
* a completed-square identity for the bubble quadratic;
* the robust consequence `etaPoly U > 0 -> F4 < G6` on the common comparison domain.

A later version can isolate the first root of `etaPoly` above `1/3` and prove the actual
small F4 bubble between `WbubbleMinus` and `WbubblePlus`.  Before doing that, it may be
more valuable to encode the finite d=4 contact-state graph and Roy-legal transitions.
-/

/-!
## 28. Finite contact-state scaffolding in d = 4

A contact type records which adjacent coordinates are equal at a switching time.
There are exactly eight consecutive-coordinate partitions of four ordered coordinates.

For the first finite-state pass we record a state as

    (contact partition, outgoing active block).

The active block is required to be a suffix of one equality cluster.  At the full
contact `1234`, the forbidden width-four top block is omitted, leaving only the
three top suffixes of lengths 1, 2, 3.  Consequently there are 31 such active states.

This section intentionally encodes only:

* the 31-state universe;
* the suffix admissibility condition;
* Roy's S3 switching condition as a necessary edge test.

It does **not** yet claim that S3 alone characterizes physical reachability between
states.  That stronger directed graph will be added separately, so we do not bake an
unproved normal-form assumption into the formalization.
-/

inductive Contact where
  | none       -- 1|2|3|4
  | c12        -- 12|3|4
  | c23        -- 1|23|4
  | c34        -- 1|2|34
  | c12_34     -- 12|34
  | c123       -- 123|4
  | c234       -- 1|234
  | c1234      -- 1234
  deriving DecidableEq, Repr

namespace Contact

/-- Whether `P1 = P2` at this contact. -/
def e12 : Contact → Bool
  | c12 | c12_34 | c123 | c1234 => true
  | _ => false

/-- Whether `P2 = P3` at this contact. -/
def e23 : Contact → Bool
  | c23 | c123 | c234 | c1234 => true
  | _ => false

/-- Whether `P3 = P4` at this contact. -/
def e34 : Contact → Bool
  | c34 | c12_34 | c234 | c1234 => true
  | _ => false

/-- Equality of every coordinate in the consecutive range `[r,s]`, specialized to d=4.
    Invalid or reversed ranges are treated conservatively as `false`, except singletons. -/
def rangeEq (c : Contact) (r s : ℕ) : Bool :=
  match r, s with
  | 1, 1 | 2, 2 | 3, 3 | 4, 4 => true
  | 1, 2 => c.e12
  | 2, 3 => c.e23
  | 3, 4 => c.e34
  | 1, 3 => c.e12 && c.e23
  | 2, 4 => c.e23 && c.e34
  | 1, 4 => c.e12 && c.e23 && c.e34
  | _, _ => false

end Contact

/-- Outgoing active blocks allowed by the suffix-of-cluster rule at a contact. -/
def activeBlocks : Contact → List Block
  | Contact.none   => [Block.b1, Block.b2, Block.b3, Block.b4]
  | Contact.c12    => [Block.b2, Block.b12, Block.b3, Block.b4]
  | Contact.c23    => [Block.b1, Block.b3, Block.b23, Block.b4]
  | Contact.c34    => [Block.b1, Block.b2, Block.b4, Block.b34]
  | Contact.c12_34 => [Block.b2, Block.b12, Block.b4, Block.b34]
  | Contact.c123   => [Block.b3, Block.b23, Block.b13, Block.b4]
  | Contact.c234   => [Block.b1, Block.b4, Block.b34, Block.b24]
  | Contact.c1234  => [Block.b4, Block.b34, Block.b24]

structure State where
  contact : Contact
  block : Block
  deriving DecidableEq, Repr

/-- The eight contact types. -/
def allContacts : List Contact :=
  [Contact.none, Contact.c12, Contact.c23, Contact.c34,
   Contact.c12_34, Contact.c123, Contact.c234, Contact.c1234]

/-- All suffix-admissible outgoing states over one contact. -/
def statesAt (c : Contact) : List State :=
  (activeBlocks c).map (fun b => ⟨c, b⟩)

/-- The finite 31-state universe used by the d=4 search. -/
def allStates : List State :=
  allContacts.flatMap statesAt

/-- Boolean suffix-admissibility test. -/
def validState (s : State) : Bool :=
  decide (s.block ∈ activeBlocks s.contact)

/-- The state count is exactly 31. -/
theorem allStates_length : allStates.length = 31 := by
  decide

/-- Every state generated by `statesAt` is suffix-admissible. -/
theorem statesAt_valid (c : Contact) (s : State) (hs : s ∈ statesAt c) :
    validState s = true := by
  unfold statesAt at hs
  simp only [List.mem_map] at hs
  rcases hs with ⟨b, hb, rfl⟩
  unfold validState
  simp [hb]

/-!
### Roy S3 as a necessary switch condition

If the old active block has lower endpoint `r_old` and the new active block has upper
endpoint `s_new`, Roy's S3 condition requires equality of coordinates
`r_old, ..., s_new` whenever `r_old < s_new`.

`switchS3` is deliberately only a *necessary* switching test.  Reachability also depends
on the direction in which gaps evolve during the preceding piece.
-/

def switchS3 (old : Block) (next : State) : Bool :=
  if Block.r old < Block.s next.block then
    Contact.rangeEq next.contact (Block.r old) (Block.s next.block)
  else
    true

/-- Necessary finite-state edge test: both endpoint states are suffix-admissible and S3 holds. -/
def edgeNecessary (old next : State) : Bool :=
  validState old && validState next && switchS3 old.block next

/-! ### Candidate state cycles already found in the search -/

def statesF6 : List State :=
  [ ⟨Contact.c34, Block.b34⟩,
    ⟨Contact.c34, Block.b4⟩,
    ⟨Contact.none, Block.b1⟩,
    ⟨Contact.c12, Block.b12⟩,
    ⟨Contact.c12, Block.b2⟩,
    ⟨Contact.c23, Block.b3⟩ ]

def statesG6 : List State :=
  [ ⟨Contact.c234, Block.b24⟩,
    ⟨Contact.c234, Block.b4⟩,
    ⟨Contact.c23, Block.b1⟩,
    ⟨Contact.c123, Block.b3⟩,
    ⟨Contact.c12_34, Block.b34⟩,
    ⟨Contact.c12_34, Block.b2⟩ ]

def statesF4 : List State :=
  [ ⟨Contact.c234, Block.b24⟩,
    ⟨Contact.c234, Block.b4⟩,
    ⟨Contact.c23, Block.b1⟩,
    ⟨Contact.c123, Block.b23⟩ ]

def statesF7 : List State :=
  [ ⟨Contact.c34, Block.b34⟩,
    ⟨Contact.c34, Block.b2⟩,
    ⟨Contact.c234, Block.b4⟩,
    ⟨Contact.c23, Block.b1⟩,
    ⟨Contact.c123, Block.b13⟩,
    ⟨Contact.c123, Block.b23⟩,
    ⟨Contact.c23, Block.b3⟩ ]

theorem statesF6_length : statesF6.length = 6 := by rfl
theorem statesG6_length : statesG6.length = 6 := by rfl
theorem statesF4_length : statesF4.length = 4 := by rfl
theorem statesF7_length : statesF7.length = 7 := by rfl

/-- All contact/block pairs used by F6 are suffix-admissible. -/
theorem statesF6_valid : statesF6.map validState = [true, true, true, true, true, true] := by
  rfl

/-- All contact/block pairs used by G6 are suffix-admissible. -/
theorem statesG6_valid : statesG6.map validState = [true, true, true, true, true, true] := by
  rfl

/-- All contact/block pairs used by F4 are suffix-admissible. -/
theorem statesF4_valid : statesF4.map validState = [true, true, true, true] := by
  rfl

/-- All contact/block pairs used by F7 are suffix-admissible. -/
theorem statesF7_valid : statesF7.map validState = [true, true, true, true, true, true, true] := by
  rfl

/-!
For a first compiler-friendly check we spell out the cyclic S3 tests explicitly.  A later
version can replace these lists by a generic `cycleEdges` function once the full directed
reachability relation is fixed.
-/

def s3ChecksF6 : List Bool :=
  [ switchS3 Block.b34 ⟨Contact.c34, Block.b4⟩,
    switchS3 Block.b4  ⟨Contact.none, Block.b1⟩,
    switchS3 Block.b1  ⟨Contact.c12, Block.b12⟩,
    switchS3 Block.b12 ⟨Contact.c12, Block.b2⟩,
    switchS3 Block.b2  ⟨Contact.c23, Block.b3⟩,
    switchS3 Block.b3  ⟨Contact.c34, Block.b34⟩ ]

def s3ChecksG6 : List Bool :=
  [ switchS3 Block.b24 ⟨Contact.c234, Block.b4⟩,
    switchS3 Block.b4  ⟨Contact.c23, Block.b1⟩,
    switchS3 Block.b1  ⟨Contact.c123, Block.b3⟩,
    switchS3 Block.b3  ⟨Contact.c12_34, Block.b34⟩,
    switchS3 Block.b34 ⟨Contact.c12_34, Block.b2⟩,
    switchS3 Block.b2  ⟨Contact.c234, Block.b24⟩ ]

def s3ChecksF4 : List Bool :=
  [ switchS3 Block.b24 ⟨Contact.c234, Block.b4⟩,
    switchS3 Block.b4  ⟨Contact.c23, Block.b1⟩,
    switchS3 Block.b1  ⟨Contact.c123, Block.b23⟩,
    switchS3 Block.b23 ⟨Contact.c234, Block.b24⟩ ]

def s3ChecksF7 : List Bool :=
  [ switchS3 Block.b34 ⟨Contact.c34, Block.b2⟩,
    switchS3 Block.b2  ⟨Contact.c234, Block.b4⟩,
    switchS3 Block.b4  ⟨Contact.c23, Block.b1⟩,
    switchS3 Block.b1  ⟨Contact.c123, Block.b13⟩,
    switchS3 Block.b13 ⟨Contact.c123, Block.b23⟩,
    switchS3 Block.b23 ⟨Contact.c23, Block.b3⟩,
    switchS3 Block.b3  ⟨Contact.c34, Block.b34⟩ ]

theorem s3ChecksF6_all : s3ChecksF6 = [true, true, true, true, true, true] := by rfl
theorem s3ChecksG6_all : s3ChecksG6 = [true, true, true, true, true, true] := by rfl
theorem s3ChecksF4_all : s3ChecksF4 = [true, true, true, true] := by rfl
theorem s3ChecksF7_all : s3ChecksF7 = [true, true, true, true, true, true, true] := by rfl

/-!
## 29. Checkpoint after v10 additions

Version v9 compiled successfully on live.lean-lang.org.

The new section introduces the finite d=4 contact-state language without asserting a
premature normal-form theorem:

* 8 contact partitions;
* the suffix-of-cluster active-block lists;
* the resulting 31-state universe;
* a formalized necessary Roy-S3 switch test;
* state realizations of F6, G6, F4, F7;
* compiler-checkable suffix and S3 verification for those candidate cycles.

The next step, after this file compiles, is to formalize the **directed reachability** of a
piece: how an active block changes the adjacent gaps and which contact partitions can
actually occur at the next switch.  Only after that relation is verified should we count
all directed edges or enumerate cycles of length <= 8 inside Lean.
-/


/-!
## 30. Gap velocities and positive-time structural reachability

For d = 4 it is convenient to work with the three adjacent gaps

* `g12 = P2 - P1`,
* `g23 = P3 - P2`,
* `g34 = P4 - P3`.

To avoid fractions, `GapVelocity6` stores six times the gap derivative.  Thus all
entries are integers.  For example, on `[3,4]` the coordinate velocity is
`(0,0,1/2,1/2)`, so the scaled gap velocity is `(0,3,0)`.

The relation below is an **existence-level positive-time reachability test** for contact
patterns.  It remembers only signs of the gap derivatives and the exact zero/nonzero
pattern of the starting and ending contacts.  It does not fix the positive sizes of open
gaps.  Consequently, when an initially positive gap has negative derivative, it may either
remain positive (switch before collision) or become zero (switch at its collision); several
such gaps may be chosen to collide simultaneously by choosing their initial sizes.

This is the correct structural layer to combine with the Roy-S3 switch condition before
we impose the actual duration/exponent equations of a template word.
-/

structure GapVelocity6 where
  d12 : ℤ
  d23 : ℤ
  d34 : ℤ
  deriving DecidableEq, Repr

/-- Six times `(g12', g23', g34')` for each of the nine d=4 active blocks. -/
def gapVelocity6 : Block → GapVelocity6
  | Block.b1  => ⟨-6,  0,  0⟩
  | Block.b2  => ⟨ 6, -6,  0⟩
  | Block.b3  => ⟨ 0,  6, -6⟩
  | Block.b4  => ⟨ 0,  0,  6⟩
  | Block.b12 => ⟨ 0, -3,  0⟩
  | Block.b23 => ⟨ 3,  0, -3⟩
  | Block.b34 => ⟨ 0,  3,  0⟩
  | Block.b13 => ⟨ 0,  0, -2⟩
  | Block.b24 => ⟨ 2,  0,  0⟩

/-- The complete scaled gap-velocity table, compiler checked. -/
theorem gapVelocity6_table :
    [ gapVelocity6 Block.b1, gapVelocity6 Block.b2, gapVelocity6 Block.b3,
      gapVelocity6 Block.b4, gapVelocity6 Block.b12, gapVelocity6 Block.b23,
      gapVelocity6 Block.b34, gapVelocity6 Block.b13, gapVelocity6 Block.b24 ] =
    [ ⟨-6,0,0⟩, ⟨6,-6,0⟩, ⟨0,6,-6⟩,
      ⟨0,0,6⟩, ⟨0,-3,0⟩, ⟨3,0,-3⟩,
      ⟨0,3,0⟩, ⟨0,0,-2⟩, ⟨2,0,0⟩ ] := by
  rfl

namespace Contact

/-- Whether adjacent gap number `i` is zero (`i = 1,2,3`). -/
def gapZero (c : Contact) : ℕ → Bool
  | 1 => c.e12
  | 2 => c.e23
  | 3 => c.e34
  | _ => false

end Contact

/-- One-gap positive-time reachability rule.

If the derivative is negative, an already-zero gap would immediately violate ordering,
while a positive gap may remain positive or close at the endpoint.  If the derivative is
zero, its zero/nonzero status is preserved.  If the derivative is positive, the endpoint
gap must be positive. -/
def gapReachable (startZero : Bool) (d : ℤ) (endZero : Bool) : Bool :=
  if d < 0 then
    !startZero
  else if d = 0 then
    decide (startZero = endZero)
  else
    !endZero

/-- Infinitesimal order-safety for a single gap.

If a gap is already zero, its derivative must be nonnegative; a positive derivative is
perfectly safe and simply opens the contact immediately.  If the gap is initially positive,
any finite derivative is locally safe for sufficiently small positive time.

This is intentionally different from `gapReachable startZero d startZero`: the latter asks
that the *same contact status persist to the endpoint*, and therefore rejects the safe event
"zero gap + positive derivative", where the gap opens immediately. -/
def gapStartSafe (startZero : Bool) (d : ℤ) : Bool :=
  if startZero then decide (0 ≤ d) else true

/-- A moving state is infinitesimally order-safe if no zero gap has negative derivative. -/
def stateStartSafe (s : State) : Bool :=
  let d := gapVelocity6 s.block
  gapStartSafe (s.contact.gapZero 1) d.d12 &&
  gapStartSafe (s.contact.gapZero 2) d.d23 &&
  gapStartSafe (s.contact.gapZero 3) d.d34

/-- Every one of the 31 suffix-admissible states is infinitesimally order-safe. -/
theorem allStates_startSafe : allStates.all stateStartSafe = true := by
  native_decide

/-- Sanity check: singleton `[4]` at a `34` contact is safe because it opens gap 34. -/
theorem startSafe_c34_b4 :
    stateStartSafe ⟨Contact.c34, Block.b4⟩ = true := by
  native_decide

/-- Sanity check: singleton `[2]` at a `12` contact is safe because it opens gap 12. -/
theorem startSafe_c12_b2 :
    stateStartSafe ⟨Contact.c12, Block.b2⟩ = true := by
  native_decide

/-- Structural existence of positive-time motion from `old` to the exact contact pattern
`cnext`, before choosing the next active block. -/
def motionReachableContact (old : State) (cnext : Contact) : Bool :=
  let d := gapVelocity6 old.block
  gapReachable (old.contact.gapZero 1) d.d12 (cnext.gapZero 1) &&
  gapReachable (old.contact.gapZero 2) d.d23 (cnext.gapZero 2) &&
  gapReachable (old.contact.gapZero 3) d.d34 (cnext.gapZero 3)

/-- Directed positive-time structural edge: the old piece can evolve to the next contact,
the endpoint state is suffix-admissible, and the switch obeys Roy S3. -/
def edgePositive (old next : State) : Bool :=
  validState old && validState next &&
  motionReachableContact old next.contact &&
  switchS3 old.block next

/-- Positive-time successors of one finite state. -/
def positiveSuccessors (s : State) : List State :=
  allStates.filter (fun t => edgePositive s t)

/-- All directed structural positive-time edges in the 31-state graph. -/
def allPositiveEdges : List (State × State) :=
  allStates.flatMap (fun s =>
    (positiveSuccessors s).map (fun t => (s,t)))

/-- The sign-based positive-time/S3 graph has 150 directed edges.

This supersedes the earlier preliminary edge count quoted before the gap-motion relation
was formalized. -/
theorem allPositiveEdges_length : allPositiveEdges.length = 150 := by
  native_decide

/-! ### Small reachability sanity checks -/

/-- Moving `[4]` from a pure `34` contact opens exactly the top gap. -/
theorem reachable_c34_b4 :
    allContacts.filter (motionReachableContact ⟨Contact.c34, Block.b4⟩) =
      [Contact.none] := by
  native_decide

/-- From an interior state, `[1]` may switch early or exactly when gap 12 closes. -/
theorem reachable_none_b1 :
    allContacts.filter (motionReachableContact ⟨Contact.none, Block.b1⟩) =
      [Contact.none, Contact.c12] := by
  native_decide

/-- From `12`, singleton `[2]` opens gap 12 and may close gap 23. -/
theorem reachable_c12_b2 :
    allContacts.filter (motionReachableContact ⟨Contact.c12, Block.b2⟩) =
      [Contact.none, Contact.c23] := by
  native_decide

/-- `[2,4]` preserves the `234` contact while increasing the lower open gap. -/
theorem reachable_c234_b24 :
    allContacts.filter (motionReachableContact ⟨Contact.c234, Block.b24⟩) =
      [Contact.c234] := by
  native_decide

/-! ### Candidate cycles are genuine positive-time structural cycles -/

/-- Explicit cyclic positive-time edge checks for F6. -/
def positiveChecksF6 : List Bool :=
  [ edgePositive ⟨Contact.c34, Block.b34⟩ ⟨Contact.c34, Block.b4⟩,
    edgePositive ⟨Contact.c34, Block.b4⟩ ⟨Contact.none, Block.b1⟩,
    edgePositive ⟨Contact.none, Block.b1⟩ ⟨Contact.c12, Block.b12⟩,
    edgePositive ⟨Contact.c12, Block.b12⟩ ⟨Contact.c12, Block.b2⟩,
    edgePositive ⟨Contact.c12, Block.b2⟩ ⟨Contact.c23, Block.b3⟩,
    edgePositive ⟨Contact.c23, Block.b3⟩ ⟨Contact.c34, Block.b34⟩ ]

/-- Explicit cyclic positive-time edge checks for G6. -/
def positiveChecksG6 : List Bool :=
  [ edgePositive ⟨Contact.c234, Block.b24⟩ ⟨Contact.c234, Block.b4⟩,
    edgePositive ⟨Contact.c234, Block.b4⟩ ⟨Contact.c23, Block.b1⟩,
    edgePositive ⟨Contact.c23, Block.b1⟩ ⟨Contact.c123, Block.b3⟩,
    edgePositive ⟨Contact.c123, Block.b3⟩ ⟨Contact.c12_34, Block.b34⟩,
    edgePositive ⟨Contact.c12_34, Block.b34⟩ ⟨Contact.c12_34, Block.b2⟩,
    edgePositive ⟨Contact.c12_34, Block.b2⟩ ⟨Contact.c234, Block.b24⟩ ]

/-- Explicit cyclic positive-time edge checks for F4. -/
def positiveChecksF4 : List Bool :=
  [ edgePositive ⟨Contact.c234, Block.b24⟩ ⟨Contact.c234, Block.b4⟩,
    edgePositive ⟨Contact.c234, Block.b4⟩ ⟨Contact.c23, Block.b1⟩,
    edgePositive ⟨Contact.c23, Block.b1⟩ ⟨Contact.c123, Block.b23⟩,
    edgePositive ⟨Contact.c123, Block.b23⟩ ⟨Contact.c234, Block.b24⟩ ]

/-- Explicit cyclic positive-time edge checks for F7. -/
def positiveChecksF7 : List Bool :=
  [ edgePositive ⟨Contact.c34, Block.b34⟩ ⟨Contact.c34, Block.b2⟩,
    edgePositive ⟨Contact.c34, Block.b2⟩ ⟨Contact.c234, Block.b4⟩,
    edgePositive ⟨Contact.c234, Block.b4⟩ ⟨Contact.c23, Block.b1⟩,
    edgePositive ⟨Contact.c23, Block.b1⟩ ⟨Contact.c123, Block.b13⟩,
    edgePositive ⟨Contact.c123, Block.b13⟩ ⟨Contact.c123, Block.b23⟩,
    edgePositive ⟨Contact.c123, Block.b23⟩ ⟨Contact.c23, Block.b3⟩,
    edgePositive ⟨Contact.c23, Block.b3⟩ ⟨Contact.c34, Block.b34⟩ ]

theorem positiveChecksF6_all :
    positiveChecksF6 = [true, true, true, true, true, true] := by
  native_decide

theorem positiveChecksG6_all :
    positiveChecksG6 = [true, true, true, true, true, true] := by
  native_decide

theorem positiveChecksF4_all :
    positiveChecksF4 = [true, true, true, true] := by
  native_decide

theorem positiveChecksF7_all :
    positiveChecksF7 = [true, true, true, true, true, true, true] := by
  native_decide

/-!
## 31. Checkpoint after v12 correction

Versions v10 and v9 compiled successfully on live.lean-lang.org.

In v11, `stateStartSafe` incorrectly reused the endpoint predicate `gapReachable` with the
same contact at both ends.  That conflated "the contact persists" with "motion is locally
order-safe".  Version v12 separates these notions via `gapStartSafe`.

The new section adds the first geometric directed-edge relation rather than using Roy S3
alone:

* exact scaled derivatives of all three adjacent gaps for all nine active blocks;
* an infinitesimal order-safety check for all 31 states;
* a positive-time structural contact-reachability predicate;
* its combination with suffix admissibility and Roy S3 into `edgePositive`;
* a compiler-checked edge count for this structural graph;
* positive-time edge verification for F6, G6, F4, and F7.

The relation is intentionally existential at the level of open-gap sizes.  The next layer
will attach durations/linear constraints to a word.  Only then should cycle enumeration be
used as a certificate of admissible template geometry rather than merely combinatorial
reachability.
-/


/-!
## 32. Timed words, linear closure, and contact equations

The finite state graph records only combinatorics.  This section adds the continuous
variables needed to decide whether a structural word is realized by an actual
self-similar template.

A timed piece is an active block together with a real duration.  Its displacement is
`duration * velocity`.  All closure and contact conditions are therefore linear in the
durations once the scale `L` is fixed.

The key generic identity proved below is:

    normalized base + multiplicative closure  ==>  total duration = L - 1.

This is independent of any candidate family.
-/

namespace Vec4

def zero : Vec4 := ⟨0, 0, 0, 0⟩

def add (u v : Vec4) : Vec4 :=
  ⟨u.x1 + v.x1, u.x2 + v.x2, u.x3 + v.x3, u.x4 + v.x4⟩

def smul (a : ℝ) (v : Vec4) : Vec4 :=
  ⟨a * v.x1, a * v.x2, a * v.x3, a * v.x4⟩

theorem sum_zero : zero.sum = 0 := by
  unfold zero sum
  ring

/-- Coordinatewise extensionality for our lightweight four-vector structure. -/
theorem ext
    {u v : Vec4}
    (h1 : u.x1 = v.x1)
    (h2 : u.x2 = v.x2)
    (h3 : u.x3 = v.x3)
    (h4 : u.x4 = v.x4) :
    u = v := by
  cases u with
  | mk u1 u2 u3 u4 =>
    cases v with
    | mk v1 v2 v3 v4 =>
      simp_all

theorem sum_add (u v : Vec4) :
    (add u v).sum = u.sum + v.sum := by
  unfold add sum
  ring

theorem sum_smul (a : ℝ) (v : Vec4) :
    (smul a v).sum = a * v.sum := by
  unfold smul sum
  ring

end Vec4

structure TimedPiece where
  block : Block
  dur : ℝ

namespace TimedPiece

def disp (p : TimedPiece) : Vec4 :=
  Vec4.smul p.dur (Block.vel p.block)

theorem disp_sum (p : TimedPiece) :
    p.disp.sum = p.dur := by
  unfold disp
  rw [Vec4.sum_smul, Block.vel_sum_one]
  ring

end TimedPiece

/-- Total elapsed time of a finite timed word. -/
def wordDuration : List TimedPiece → ℝ
  | [] => 0
  | p :: ps => p.dur + wordDuration ps

/-- Total coordinate displacement of a finite timed word. -/
def wordDisplacement : List TimedPiece → Vec4
  | [] => Vec4.zero
  | p :: ps => Vec4.add p.disp (wordDisplacement ps)

/-- Total contraction mass of a finite timed word. -/
def wordMass : List TimedPiece → ℝ
  | [] => 0
  | p :: ps => Block.delta p.block * p.dur + wordMass ps

/-- Total top-coordinate growth of a finite timed word. -/
def wordTopGrowth : List TimedPiece → ℝ
  | [] => 0
  | p :: ps => Block.topSlope p.block * p.dur + wordTopGrowth ps

/-- Forget the durations and retain only the active-block word. -/
def timedBlocks (w : List TimedPiece) : List Block :=
  w.map TimedPiece.block

theorem wordDisplacement_sum (w : List TimedPiece) :
    (wordDisplacement w).sum = wordDuration w := by
  induction w with
  | nil =>
      simpa [wordDisplacement, wordDuration] using Vec4.sum_zero
  | cons p ps ih =>
      rw [wordDisplacement, wordDuration, Vec4.sum_add, TimedPiece.disp_sum, ih]

/-- Multiplicative closure: after all pieces, the endpoint is `L * base`. -/
def wordCloses (base : Vec4) (L : ℝ) (w : List TimedPiece) : Prop :=
  Vec4.add base (wordDisplacement w) = Vec4.smul L base

/-- For a normalized base point, multiplicative closure forces total duration `L - 1`. -/
theorem duration_eq_scale_sub_one_of_closure
    (base : Vec4) (L : ℝ) (w : List TimedPiece)
    (hnorm : base.sum = 1)
    (hclose : wordCloses base L w) :
    wordDuration w = L - 1 := by
  have hs := congrArg Vec4.sum hclose
  rw [Vec4.sum_add, wordDisplacement_sum, Vec4.sum_smul, hnorm] at hs
  linarith

/-- Coordinate position after the first `j` timed pieces. -/
def pointAfter (base : Vec4) (w : List TimedPiece) (j : ℕ) : Vec4 :=
  Vec4.add base (wordDisplacement (w.take j))

/-- Elapsed simplex time after the first `j` timed pieces, when the period starts at q=1. -/
def timeAfter (w : List TimedPiece) (j : ℕ) : ℝ :=
  1 + wordDuration (w.take j)

namespace Contact

/-- Linear equality equations associated with a contact partition.

This deliberately records only the equalities, not strict inequalities between distinct
clusters.  Ordering/exactness is a separate feasibility layer.
-/
def holdsEq (c : Contact) (p : Vec4) : Prop :=
  match c with
  | none => True
  | c12 => p.x1 = p.x2
  | c23 => p.x2 = p.x3
  | c34 => p.x3 = p.x4
  | c12_34 => p.x1 = p.x2 ∧ p.x3 = p.x4
  | c123 => p.x1 = p.x2 ∧ p.x2 = p.x3
  | c234 => p.x2 = p.x3 ∧ p.x3 = p.x4
  | c1234 => p.x1 = p.x2 ∧ p.x2 = p.x3 ∧ p.x3 = p.x4

end Contact

/-- The contact equations at a specified vertex of a timed word. -/
def contactAt (base : Vec4) (w : List TimedPiece) (j : ℕ) (c : Contact) : Prop :=
  c.holdsEq (pointAfter base w j)

/-- Ordered-simplex condition at a point. -/
def orderedPoint (p : Vec4) : Prop :=
  p.x1 ≤ p.x2 ∧ p.x2 ≤ p.x3 ∧ p.x3 ≤ p.x4

/-- Uniform exponent normalization at the beginning of a period. -/
def uniformBaseEq (U : ℝ) (base : Vec4) : Prop :=
  base.x4 = A U

/-- Cleared ordinary-exponent equation at a vertex: `P4(q) = B q`. -/
def ordinaryVertexEq
    (W : ℝ) (base : Vec4) (w : List TimedPiece) (j : ℕ) : Prop :=
  (pointAfter base w j).x4 = B W * timeAfter w j

/-!
### The G6 word as a timed cycle

This is our first nontrivial test of the generic encoding.  The six duration formulas were
already proved algebraically earlier in the file.  Here we attach them to the six active
blocks and verify the block skeleton, the normalized starting contact, and multiplicative
closure.
-/

def baseG6 (U : ℝ) : Vec4 :=
  ⟨1 - 3 * A U, A U, A U, A U⟩

def timedG6 (U W L : ℝ) : List TimedPiece :=
  [ ⟨Block.b24, g1 U L⟩,
    ⟨Block.b4,  g2 U W L⟩,
    ⟨Block.b1,  g3 U L⟩,
    ⟨Block.b3,  g4 U W L⟩,
    ⟨Block.b34, g5 U W L⟩,
    ⟨Block.b2,  g6 U L⟩ ]

theorem timedG6_blocks (U W L : ℝ) :
    timedBlocks (timedG6 U W L) = wordG6 := by
  rfl

theorem baseG6_sum (U : ℝ) :
    (baseG6 U).sum = 1 := by
  unfold baseG6 Vec4.sum
  ring

theorem baseG6_uniform (U : ℝ) :
    uniformBaseEq U (baseG6 U) := by
  rfl

theorem baseG6_contact :
    ∀ U : ℝ, Contact.holdsEq Contact.c234 (baseG6 U) := by
  intro U
  unfold Contact.holdsEq baseG6
  exact ⟨rfl, rfl⟩

/-- The six explicit G6 durations close at scale `L`.

The only denominator is `1+U`; no exponent-domain inequalities are needed for this
algebraic closure identity.
-/
theorem timedG6_closes
    (U W L : ℝ)
    (hden : 1 + U ≠ 0) :
    wordCloses (baseG6 U) L (timedG6 U W L) := by
  apply Vec4.ext <;>
    simp [timedG6, wordDisplacement, TimedPiece.disp,
      Vec4.zero, Vec4.add, Vec4.smul, Block.vel, baseG6,
      g1, g2, g3, g4, g5, g6, gCommonDen,
      g1Num, g2Num, g3Num, g4Num, g5Num, g6Num, A] <;>
    field_simp [hden] <;>
    ring

/-- As a corollary of generic closure, the actual G6 durations sum to `L - 1`. -/
theorem timedG6_duration
    (U W L : ℝ)
    (hden : 1 + U ≠ 0) :
    wordDuration (timedG6 U W L) = L - 1 := by
  exact duration_eq_scale_sub_one_of_closure
    (baseG6 U) L (timedG6 U W L) (baseG6_sum U)
    (timedG6_closes U W L hden)

/-- First nontrivial contact-equation test:
after the first G6 piece `[2,4]`, the top three coordinates remain equal. -/
theorem timedG6_contact_after_one
    (U W L : ℝ) :
    contactAt (baseG6 U) (timedG6 U W L) 1 Contact.c234 := by
  simp [contactAt, pointAfter, timedG6, wordDisplacement, TimedPiece.disp,
    Contact.holdsEq, Vec4.zero, Vec4.add, Vec4.smul, Block.vel, baseG6]

/-- After the second G6 piece `[4]`, only the `23` equality remains. -/
theorem timedG6_contact_after_two
    (U W L : ℝ) :
    contactAt (baseG6 U) (timedG6 U W L) 2 Contact.c23 := by
  simp [contactAt, pointAfter, timedG6, wordDisplacement, TimedPiece.disp,
    Contact.holdsEq, Vec4.zero, Vec4.add, Vec4.smul, Block.vel, baseG6]

/-!
The next version should add the genuinely constraining contacts after pieces 3, 4, and 6.
Those equations use the specific duration formulas rather than being preserved
tautologically by a block velocity.  Once those compile, the same machinery can be
abstracted to an arbitrary state word and used as the linear feasibility certificate in
the length-<=8 enumeration.
-/


/-!
## 33. Complete G6 vertex-contact and peak certificates

The previous section verified closure and the first two (kinematically preserved) contacts.
We now verify the genuinely constraining contacts at vertices 3 and 4, recover the final
`234` contact from multiplicative closure, and prove that vertex 2 realizes the prescribed
ordinary ratio `B = W/(1+W)`.
-/

/-- Under multiplicative closure, the vertex after the full word is exactly the scaled base. -/
theorem pointAfter_length_eq_scaled_of_closure
    (base : Vec4) (L : ℝ) (w : List TimedPiece)
    (hclose : wordCloses base L w) :
    pointAfter base w w.length = Vec4.smul L base := by
  unfold pointAfter
  rw [List.take_length]
  exact hclose

/-- After the third G6 piece `[1]`, the first three coordinates coalesce. -/
theorem timedG6_contact_after_three
    (U W L : ℝ)
    (hden : 1 + U ≠ 0) :
    contactAt (baseG6 U) (timedG6 U W L) 3 Contact.c123 := by
  unfold contactAt Contact.holdsEq
  constructor <;>
    simp [pointAfter, timedG6, wordDisplacement, TimedPiece.disp,
      Vec4.zero, Vec4.add, Vec4.smul, Block.vel, baseG6,
      g1, g2, g3, gCommonDen, g1Num, g2Num, g3Num, A] <;>
    field_simp [hden] <;>
    ring

/-- After the fourth G6 piece `[3]`, the contact is `12|34`. -/
theorem timedG6_contact_after_four
    (U W L : ℝ)
    (hden : 1 + U ≠ 0) :
    contactAt (baseG6 U) (timedG6 U W L) 4 Contact.c12_34 := by
  unfold contactAt Contact.holdsEq
  constructor <;>
    simp [pointAfter, timedG6, wordDisplacement, TimedPiece.disp,
      Vec4.zero, Vec4.add, Vec4.smul, Block.vel, baseG6,
      g1, g2, g3, g4, gCommonDen,
      g1Num, g2Num, g3Num, g4Num, A] <;>
    field_simp [hden] <;>
    ring

/-- The endpoint after all six G6 pieces is the scaled base point. -/
theorem timedG6_endpoint_scaled
    (U W L : ℝ)
    (hden : 1 + U ≠ 0) :
    pointAfter (baseG6 U) (timedG6 U W L) 6 =
      Vec4.smul L (baseG6 U) := by
  have hclose := timedG6_closes U W L hden
  have hlen : (timedG6 U W L).length = 6 := by
    rfl
  rw [← hlen]
  exact pointAfter_length_eq_scaled_of_closure
    (baseG6 U) L (timedG6 U W L) hclose

/-- Consequently the final G6 contact is again `234`, as required for renewal. -/
theorem timedG6_contact_after_six
    (U W L : ℝ)
    (hden : 1 + U ≠ 0) :
    contactAt (baseG6 U) (timedG6 U W L) 6 Contact.c234 := by
  unfold contactAt
  rw [timedG6_endpoint_scaled U W L hden]
  unfold Contact.holdsEq Vec4.smul baseG6
  exact ⟨rfl, rfl⟩

/-- Vertex 2 of G6 realizes the prescribed ordinary exponent ratio `B(W)`.

The hypotheses merely clear the coordinate-change denominators `1+U` and `1+W`.
-/
theorem timedG6_ordinary_peak_at_two
    (U W L : ℝ)
    (hU : 1 + U ≠ 0)
    (hW : 1 + W ≠ 0) :
    ordinaryVertexEq W (baseG6 U) (timedG6 U W L) 2 := by
  unfold ordinaryVertexEq
  simp [pointAfter, timeAfter, timedG6, wordDisplacement, wordDuration,
    TimedPiece.disp, Vec4.zero, Vec4.add, Vec4.smul, Block.vel, baseG6,
    g1, g2, gCommonDen, g1Num, g2Num, A, B] <;>
    field_simp [hU, hW] <;>
    ring

/-!
At this point the algebraic realization of the G6 skeleton is certified:

* normalized base at contact `234`;
* contacts `234 -> 23 -> 123 -> 12|34 -> ... -> 234`;
* multiplicative closure at scale `L`;
* the second vertex realizes the ordinary ratio `B(W)`.

The next useful layer is exact ordering and positivity of the six durations on the
candidate G6 parameter domain.  Those inequalities turn these equality certificates into
a genuine admissible template certificate.
-/


/-!
## 34. G6 finite-endpoint admissibility: scale and duration signs

We now specialize the G6 cycle to its finite optimizing endpoint

    L = LG(U,W) = W(1-U) / (2(UW+U-W)),

on the natural domain

    1/3 < U < 1/2,
    WT(U) <= W < WH(U).

The upper inequality is exactly the condition that the denominator of `LG` is positive.
The endpoint certificates from Section 13 then give the duration signs without expanding
the quotient `LG` directly.
-/

/-- Elementary cancellation helper used repeatedly below. -/
theorem nonneg_of_mul_nonneg_right_pos {a b : ℝ}
    (hb : 0 < b) (hab : 0 ≤ a * b) : 0 ≤ a := by
  by_contra h
  have ha : a < 0 := lt_of_not_ge h
  have hm : a * b < 0 := mul_neg_of_neg_of_pos ha hb
  linarith

/-- Strict version of the same cancellation helper. -/
theorem pos_of_mul_pos_right_pos {a b : ℝ}
    (hb : 0 < b) (hab : 0 < a * b) : 0 < a := by
  by_contra h
  have ha : a ≤ 0 := le_of_not_gt h
  have hm : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha (le_of_lt hb)
  linarith

theorem gCommonDen_pos_of_domain {U : ℝ}
    (hUlo : (1 : ℝ) / 3 < U) :
    0 < gCommonDen U := by
  unfold gCommonDen
  nlinarith

/-- Strict positivity of the finite G6 scale denominator below `WH`. -/
theorem LGDen_pos_of_W_lt_WH {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2)
    (hW : W < WH U) :
    0 < LGDen U W := by
  have hd : 0 < WHDen U := WHDen_pos_of_domain hUlo hUhi
  have hfrac : W < WHNum U / WHDen U := by
    simpa [WH] using hW
  have hc : W * WHDen U < WHNum U := (lt_div_iff₀ hd).mp hfrac
  rw [LGDen_highBarrier]
  unfold highBarrier WHNum WHDen at hc ⊢
  nlinarith

/-- The defining residual vanishes when `L` is instantiated by the quotient `LG`. -/
theorem LGResidual_at_LG {U W : ℝ}
    (hD : LGDen U W ≠ 0) :
    LGResidual U W (LG U W) = 0 := by
  unfold LGResidual LG
  field_simp [hD]

/-- On the finite G6 domain the first duration is nonnegative.
It vanishes at the birth boundary `W = WT`. -/
theorem g1Num_nonneg_at_LG {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W)
    (hWH : W < WH U) :
    0 ≤ g1Num U (LG U W) := by
  have hD : 0 < LGDen U W := LGDen_pos_of_W_lt_WH hUlo hUhi hWH
  have hR : LGResidual U W (LG U W) = 0 :=
    LGResidual_at_LG (ne_of_gt hD)
  have hb : birthPoly U W ≤ 0 :=
    birthPoly_nonpos_of_W_ge_WT hUlo hUhi hWT
  have hc := g1_LG_certificate U W (LG U W)
  rw [hR] at hc
  have hp : 0 ≤ g1Num U (LG U W) * LGDen U W := by
    nlinarith
  exact nonneg_of_mul_nonneg_right_pos hD hp

/-- The second duration is strictly positive on the finite G6 domain. -/
theorem g2Num_pos_at_LG {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W)
    (hWH : W < WH U) :
    0 < g2Num U W (LG U W) := by
  have hD : 0 < LGDen U W := LGDen_pos_of_W_lt_WH hUlo hUhi hWH
  have hR : LGResidual U W (LG U W) = 0 :=
    LGResidual_at_LG (ne_of_gt hD)
  have hW : 0 < W := W_pos_of_W_ge_WT hUlo hUhi hWT
  have h2 : 2 * U - 1 < 0 := by
    nlinarith
  have h3 : 0 < 3 * U - 1 := threeU_sub_one_pos_of_domain hUlo hUhi
  have ht1 : W * (2 * U - 1) < 0 :=
    mul_neg_of_pos_of_neg hW h2
  have ht : W * (2 * U - 1) * (3 * U - 1) < 0 :=
    mul_neg_of_neg_of_pos ht1 h3
  have hc := g2_LG_certificate U W (LG U W)
  rw [hR] at hc
  have hp : 0 < g2Num U W (LG U W) * LGDen U W := by
    nlinarith
  exact pos_of_mul_pos_right_pos hD hp

/-- The third duration is strictly positive on the finite G6 domain. -/
theorem g3Num_pos_at_LG {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W)
    (hWH : W < WH U) :
    0 < g3Num U (LG U W) := by
  have hD : 0 < LGDen U W := LGDen_pos_of_W_lt_WH hUlo hUhi hWH
  have hR : LGResidual U W (LG U W) = 0 :=
    LGResidual_at_LG (ne_of_gt hD)
  have h2 : 2 * U - 1 < 0 := by
    nlinarith
  have hq : commonQ U W < 0 :=
    commonQ_neg_of_W_ge_WT hUlo hUhi hWT
  have hp0 : 0 < (2 * U - 1) * commonQ U W :=
    mul_pos_of_neg_of_neg h2 hq
  have hc := g3_LG_certificate U W (LG U W)
  rw [hR] at hc
  have hp : 0 < g3Num U (LG U W) * LGDen U W := by
    unfold commonQ at hq hp0
    nlinarith
  exact pos_of_mul_pos_right_pos hD hp

/-- The fourth duration equals the second and is strictly positive. -/
theorem g4Num_pos_at_LG {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W)
    (hWH : W < WH U) :
    0 < g4Num U W (LG U W) := by
  simpa [g4Num] using g2Num_pos_at_LG hUlo hUhi hWT hWH

/-- The fifth duration is strictly positive on the finite G6 domain. -/
theorem g5Num_pos_at_LG {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W)
    (hWH : W < WH U) :
    0 < g5Num U W (LG U W) := by
  have hD : 0 < LGDen U W := LGDen_pos_of_W_lt_WH hUlo hUhi hWH
  have hR : LGResidual U W (LG U W) = 0 :=
    LGResidual_at_LG (ne_of_gt hD)
  have hU : 0 < U := U_pos_of_domain hUlo
  have hW : 0 < W := W_pos_of_W_ge_WT hUlo hUhi hWT
  have h3 : 0 < 3 * U - 1 := threeU_sub_one_pos_of_domain hUlo hUhi
  have hp0 : 0 < 2 * U * W * (3 * U - 1) := by
    have h2U : 0 < 2 * U := mul_pos (by norm_num) hU
    have h2UW : 0 < (2 * U) * W := mul_pos h2U hW
    exact mul_pos h2UW h3
  have hc := g5_LG_certificate U W (LG U W)
  rw [hR] at hc
  have hp : 0 < g5Num U W (LG U W) * LGDen U W := by
    nlinarith
  exact pos_of_mul_pos_right_pos hD hp

/-- The sixth duration is strictly positive on the finite G6 domain. -/
theorem g6Num_pos_at_LG {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W)
    (hWH : W < WH U) :
    0 < g6Num U (LG U W) := by
  have hD : 0 < LGDen U W := LGDen_pos_of_W_lt_WH hUlo hUhi hWH
  have hR : LGResidual U W (LG U W) = 0 :=
    LGResidual_at_LG (ne_of_gt hD)
  have hW : 0 < W := W_pos_of_W_ge_WT hUlo hUhi hWT
  have hUm1 : U - 1 < 0 := by
    nlinarith
  have h3 : 0 < 3 * U - 1 := threeU_sub_one_pos_of_domain hUlo hUhi
  have ht1 : W * (U - 1) < 0 :=
    mul_neg_of_pos_of_neg hW hUm1
  have ht : W * (U - 1) * (3 * U - 1) < 0 :=
    mul_neg_of_neg_of_pos ht1 h3
  have hc := g6_LG_certificate U W (LG U W)
  rw [hR] at hc
  have hp : 0 < g6Num U (LG U W) * LGDen U W := by
    nlinarith
  exact pos_of_mul_pos_right_pos hD hp

/-- Actual G6 duration signs after dividing by the positive common denominator `1+U`. -/
theorem g_durations_at_LG_signs {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W)
    (hWH : W < WH U) :
    0 ≤ g1 U (LG U W) ∧
    0 < g2 U W (LG U W) ∧
    0 < g3 U (LG U W) ∧
    0 < g4 U W (LG U W) ∧
    0 < g5 U W (LG U W) ∧
    0 < g6 U (LG U W) := by
  have hd : 0 < gCommonDen U := gCommonDen_pos_of_domain hUlo
  have h1n : 0 ≤ g1Num U (LG U W) :=
    g1Num_nonneg_at_LG hUlo hUhi hWT hWH
  have h2n : 0 < g2Num U W (LG U W) :=
    g2Num_pos_at_LG hUlo hUhi hWT hWH
  have h3n : 0 < g3Num U (LG U W) :=
    g3Num_pos_at_LG hUlo hUhi hWT hWH
  have h4n : 0 < g4Num U W (LG U W) :=
    g4Num_pos_at_LG hUlo hUhi hWT hWH
  have h5n : 0 < g5Num U W (LG U W) :=
    g5Num_pos_at_LG hUlo hUhi hWT hWH
  have h6n : 0 < g6Num U (LG U W) :=
    g6Num_pos_at_LG hUlo hUhi hWT hWH
  constructor
  · unfold g1
    exact div_nonneg h1n (le_of_lt hd)
  constructor
  · unfold g2
    exact div_pos h2n hd
  constructor
  · unfold g3
    exact div_pos h3n hd
  constructor
  · unfold g4
    exact div_pos h4n hd
  constructor
  · unfold g5
    exact div_pos h5n hd
  · unfold g6
    exact div_pos h6n hd

/-- The finite G6 endpoint scale is strictly larger than one. -/
theorem one_lt_LG {U W : ℝ}
    (hUlo : (1 : ℝ) / 3 < U)
    (hUhi : U < (1 : ℝ) / 2)
    (hWT : WT U ≤ W)
    (hWH : W < WH U) :
    1 < LG U W := by
  have hs := g_durations_at_LG_signs hUlo hUhi hWT hWH
  rcases hs with ⟨h1, h2, h3, h4, h5, h6⟩
  have hden : 1 + U ≠ 0 := by
    have hp : 0 < 1 + U := by nlinarith [U_pos_of_domain hUlo]
    exact ne_of_gt hp
  have hdur :
      0 < wordDuration (timedG6 U W (LG U W)) := by
    simp [wordDuration, timedG6]
    linarith
  have heq :=
    timedG6_duration U W (LG U W) hden
  rw [heq] at hdur
  linarith

/-!
The next admissibility layer should prove ordered coordinates and the normalized-top
barriers at every G6 vertex.  The duration-sign theorem above is the essential input:
within each active piece the only gap that can close does so at the certified endpoint,
while gaps with nonnegative derivative remain nonnegative.
-/

end M3
