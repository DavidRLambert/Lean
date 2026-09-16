/-
V11 -- FINITE-ORBIT POSITIVITY AND AUTOMATIC QUADRATIC-HEIGHT CUTOFF

VALIDATION RECORD (supersedes the historical headers retained below)
* The user's v10.1 log has 94 distinct axiom reports, matching all 94 checks
  in the delivered source. Every report contains only
  [propext, Classical.choice, Quot.sound]. No errors or linter warnings
  appear in that log. V10.1 is the fully validated baseline.
* This file retains the complete delivered v10.1 source byte-for-byte,
  between this header and the new V11 block. No old proof is edited.
* The V11 block adds one definition, 16 theorems, and 16 axiom checks.
  There are 110 axiom checks in this complete file.
* V11 HAS NOT BEEN COMPILED in this authoring environment. The live-editor
  check is required before treating the new statements as machine-validated.
* The new universal bound is 1/(2*(M+1)), not the sharp 1/(2*M) bound.
  It proves positivity for every nonempty orbit without irrationality.
* For hQ>0 and H>=0, floor(sqrt(H/hQ)) is proved to give the exact index
  cutoff. Eventual positivity is then derived and supplied to the existing
  limsup bridge. All arithmetic inclusion/multiplication assumptions remain.
* No new imports, axiom declarations, proof placeholders, native-evaluation
  admissions, linter suppressions, or external files are introduced.

Replace the ENTIRE editor contents with this complete single file.
The final check is AbelianLog.torsion_extension_logPowerLimsup_eq_of_pos_height.
-/

/-
REPAIR V10.1 -- EXPLICIT EXTENDED-REAL CASE PREDICATE

VALIDATION RECORD (this supersedes the historical headers below)
* The user's v10 log contains 94 axiom reports: 86 report only
  [propext, Classical.choice, Quot.sound]; eight also report sorryAx.
* There is one reported proof error, at apply EReal.forall.mpr in
  ereal_limsup_le_coe_iff. Seven later checks inherit its incomplete proof.
  No linter warnings are present in the supplied log.
* This revision replaces that one tactic with a term-mode refine and an
  explicit predicate p. The three existing case proofs are unchanged.
* Apart from this leading validation header and that tactic replacement,
  the delivered v10 source is unchanged. All definitions, theorem statements,
  hypotheses, other proof bodies, and all 94 axiom-print commands are intact.
  The embedded validated v9.1 source is preserved byte-for-byte.
* V10.1 has NOT been compiled in this authoring environment. A successful
  live-editor run remains necessary; v9.1 is the latest fully validated file.
* No axiom declarations, proof placeholders, native-evaluation admissions,
  imports, or linter suppressions are introduced. All positivity and
  arithmetic hypotheses are retained.

Replace the ENTIRE live-editor contents with this complete single file.
Only import Mathlib is required. The last check remains
AbelianLog.torsion_extension_logPowerLimsup_eq.
-/

/-
REPAIR V9.1 -- COUNTEREXAMPLE QUANTIFIER NORMALIZATION

VALIDATION RECORD
* The user's attached v9 live Lean/Mathlib report contains 78 axiom checks:
  77 report only [propext, Classical.choice, Quot.sound]. The only check
  reporting sorryAx is not_eventualLogPowerUpperBound_iff.
* That helper has one unused-simp-argument warning (not_imp) and an unsolved
  goal converting an existential over a proof into a conjunction.
* This revision replaces not_imp with exists_prop in that helper's simp-only
  proof. Apart from this header, that is the ONLY source change from v9.
* All theorem statements, hypotheses, definitions, other proof bodies, and
  all 78 axiom-print commands are unchanged. The embedded v8 code is intact.
* V9.1 has NOT been compiled in this authoring environment. A successful
  live-editor run is still required; v8 remains the latest whole-file
  validated baseline. This record supersedes older validation headers.
* No new axiom declarations, proof placeholders, imports, native-evaluation
  admissions, or linter suppressions are introduced. All arithmetic and
  analytic hypotheses remain explicit. No notebook results are changed.

Replace the ENTIRE live-editor contents with this complete single file.
Only import Mathlib is required. In particular, recheck
AbelianLog.not_eventualLogPowerUpperBound_iff. The final check remains
AbelianLog.torsion_extension_exactLogPowerEnvelope_iff.
-/

/-
CONTINUATION V8 -- ASYMPTOTIC POWER TRANSFER

VALIDATION RECORD
* The user's complete v7.2 live Lean/Mathlib report contains all 48 axiom
  checks, each reporting only [propext, Classical.choice, Quot.sound].
  No errors or linter warnings were included. V7.2 is the validated baseline.
* The entire delivered v7.2 source is preserved below, byte-for-byte.
  Its historical validation headers are superseded by this record.
* The NEW v8 extension at the end has NOT been compiled in this authoring
  environment. Its 12 new axiom checks bring the total to 60. None of the
  new proof scripts should be considered Lean-validated before testing.
* The extension proves drafts of fixed-power and coefficient-one epsilon
  transfer implications. It does not establish a particular asymptotic
  rate for the elliptic logarithm or for the curve's rational-point group.
* No new axiom declarations, explicit proof placeholders, native evaluation
  admissions, local helper imports, or linter suppressions are introduced.
* Arithmetic identification, rank/saturation, analytic interval membership,
  and actual canonical-height laws remain outside the new results.

Replace the ENTIRE live-editor contents with this complete single file.
Only import Mathlib is required. The final check is
AbelianLog.torsion_extension_epsilonPowerDecay_iff.
-/

/-
CLEANUP V7.2 -- WARNING-ONLY EDITS TO THE USER-VALIDATED V7.1

VALIDATION RECORD
* The user's complete v7.1 live Lean/Mathlib report contains all 48 axiom
  checks, each reporting only [propext, Classical.choice, Quot.sound].
  No proof errors or sorryAx dependencies are reported. In particular,
  the Nat.cast_one repair and all three dependent theorems passed.
* V7.1 is the latest version validated by that live-editor run.
* This v7.2 copy has NOT been compiled in the authoring environment.
  It addresses only the warning locations in the reported v7.1 run:
  - remove unreachable trailing ring at original lines 121 and 401;
  - replace <;> with ordinary tactic sequencing at original lines
    819, 828, 838, 880, 896, 1045, 1047, 1189, and 1368.
* All theorem statements, hypotheses, definitions, and 48 axiom-print
  commands are unchanged. The Nat.cast_one repair is retained.
  All other proof text is unchanged. No linters are disabled.
* No axiom declarations, proof placeholders, native computation
  admissions, or additional imports are introduced.
* Historical validation notes below describe earlier versions and are
  superseded by this record for v7.1. They do not validate this cleanup.
* Arithmetic inclusion, multiplication, interval membership, and height-law
  assumptions remain explicit. No new mathematical result is claimed.

This is a complete single file with only import Mathlib. Replace the entire
editor contents when testing it. The already validated v7.1 remains usable
without this optional cleanup.
-/

/-
CONTINUATION V6 -- SIGNED ORBITS AND QUADRATIC HEIGHT WINDOWS

VALIDATION RECORD
* The user has reported a successful live Lean/Mathlib run of the v5
  development, with all 20 displayed checks returning exactly
  [propext, Classical.choice, Quot.sound]. This includes the inherited
  inverse-square repair and the centered interval certificate.
* This supersedes the pending-user-validation notes in the historical
  headers retained below. No independent local Lean run is claimed.
* The previously delivered v5 source is preserved below, byte-for-byte.
  The user's unshared warning-only edits are not incorporated.
* The NEW v6 extension at the end is UNCOMPILED and awaits a live-editor
  test. It adds 15 axiom checks, for a total of 35. Proof drafts contain
  no explicit placeholders or newly declared axioms.
* Interval membership, an actual canonical-height law, the arithmetic
  logarithm identification, and rank/saturation are NOT proved here.

Replace the entire editor contents with this file, not just the new block.
The only import is Mathlib. No local helper files are required.
-/

import Mathlib

/-
CONTINUATION V5 -- CENTERED COVERING STABILITY

This is a complete single-file continuation. Replace the entire live-editor
contents with this file. No local helper imports are required; import Mathlib
is the only import. All original v4.1 proof bodies are preserved below.

Validation: the header inherited from v4.1 records the previous user's tests.
Neither the pending v4.1 repair nor the new v5 extension has been compiled
in this authoring environment. There are 20 axiom-print commands in total.
The final command checks small_centered_interval_certificate.

The companion Colab notebook tests the new finite inequalities in exact
rational arithmetic and replays the large certificates; those tests are
not a substitute for compiling this file or formalizing the analytic input.
-/


/-!
Abelian-logarithm project, v4.1: two-sided finite-orbit covering estimates.

VALIDATION STATUS
* In the user's v4 run, ten of the eleven displayed axiom checks returned
  exactly [propext, Classical.choice, Quot.sound]. This includes the
  two-sided covering theorem and the conditional interval certificate.
* Only inverse_square_approximation_covering_upper_bound had proof errors.
  This revision repairs its last two steps: add_le_add le_rfl hterm keeps
  the summands in the required order, and norm_num finishes the numerical
  equality left by field_simp.
* Apart from this header and those two proof steps, the v4 file is unchanged.
  All theorem statements and hypotheses are preserved.
* The revised proof has NOT been compiled in the authoring environment.
  The user's live Lean/Mathlib run is the pending validation step.
* No new axioms or explicit proof placeholders are introduced. Membership
  of the elliptic-logarithm ratio in the interval remains a hypothesis.

Replace the editor contents with this entire self-contained file; do not
append it to another version. All eleven axiom checks are retained.
-/

set_option autoImplicit false

namespace AbelianLog

/-- An integer is at least half a unit away from the midpoint 1/2. -/
theorem half_le_abs_int_sub_half (z : ℤ) :
    (1 / 2 : ℝ) ≤ |(z : ℝ) - 1 / 2| := by
  rcases le_or_gt z 0 with hz | hz
  · have hzR : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    have h := neg_le_abs ((z : ℝ) - 1 / 2)
    linarith
  · have hz1 : (1 : ℤ) ≤ z := by omega
    have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
    have h := le_abs_self ((z : ℝ) - 1 / 2)
    linarith

/-- Every point of a rational grid avoids the midpoint of its first cell. -/
theorem rational_grid_avoids_midpoint
    (p q k j : ℤ) (hq : 0 < q) :
    1 / (2 * (q : ℝ)) ≤
      |(k : ℝ) * ((p : ℝ) / (q : ℝ)) - (j : ℝ) -
        1 / (2 * (q : ℝ))| := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have heq :
      (k : ℝ) * ((p : ℝ) / (q : ℝ)) - (j : ℝ) -
          1 / (2 * (q : ℝ)) =
        (((k * p - j * q : ℤ) : ℝ) - 1 / 2) / (q : ℝ) := by
    push_cast
    field_simp [hq0]
  calc
    1 / (2 * (q : ℝ)) = (1 / 2 : ℝ) / (q : ℝ) := by
      field_simp [hq0]
    _ ≤ |(((k * p - j * q : ℤ) : ℝ) - 1 / 2)| / (q : ℝ) :=
      div_le_div_of_nonneg_right
        (half_le_abs_int_sub_half (k * p - j * q)) (le_of_lt hqR)
    _ = |(k : ℝ) * ((p : ℝ) / (q : ℝ)) - (j : ℝ) -
          1 / (2 * (q : ℝ))| := by
      rw [heq, abs_div, abs_of_pos hqR]

/--
Finite covering obstruction. If |alpha - p/q| <= delta and |k| <= B,
then the target 1/(2q) is at least 1/(2q) - B*delta away from k*alpha
modulo EVERY integer j. Hence the signed orbit {|k| <= B} has covering
radius at least that number, whenever the lower bound is positive.

For M one-sided orbit points, take B = M-1.
-/
theorem rational_approximation_forces_hole
    (alpha delta B : ℝ) (p q k j : ℤ)
    (hq : 0 < q) (hB : 0 ≤ B)
    (happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤ delta)
    (hk : |(k : ℝ)| ≤ B) :
    1 / (2 * (q : ℝ)) - B * delta ≤
      |(k : ℝ) * alpha - (j : ℝ) - 1 / (2 * (q : ℝ))| := by
  have hgrid := rational_grid_avoids_midpoint p q k j hq
  have hpert :
      |(k : ℝ) * alpha - (k : ℝ) * ((p : ℝ) / (q : ℝ))| ≤
        B * delta := by
    calc
      |(k : ℝ) * alpha - (k : ℝ) * ((p : ℝ) / (q : ℝ))| =
          |(k : ℝ)| * |alpha - (p : ℝ) / (q : ℝ)| := by
        rw [← mul_sub, abs_mul]
      _ ≤ B * delta := mul_le_mul hk happrox (abs_nonneg _) hB
  have htriangle :
      |(k : ℝ) * ((p : ℝ) / (q : ℝ)) - (j : ℝ) -
          1 / (2 * (q : ℝ))| ≤
      |(k : ℝ) * alpha - (j : ℝ) - 1 / (2 * (q : ℝ))| +
      |(k : ℝ) * alpha - (k : ℝ) * ((p : ℝ) / (q : ℝ))| := by
    calc
      |(k : ℝ) * ((p : ℝ) / (q : ℝ)) - (j : ℝ) -
          1 / (2 * (q : ℝ))| =
          |((k : ℝ) * alpha - (j : ℝ) - 1 / (2 * (q : ℝ))) +
            ((k : ℝ) * ((p : ℝ) / (q : ℝ)) - (k : ℝ) * alpha)| := by
        congr 1
        ring
      _ ≤ |(k : ℝ) * alpha - (j : ℝ) - 1 / (2 * (q : ℝ))| +
          |(k : ℝ) * ((p : ℝ) / (q : ℝ)) - (k : ℝ) * alpha| :=
        abs_add_le _ _
      _ = _ := by
        rw [abs_sub_comm ((k : ℝ) * ((p : ℝ) / (q : ℝ)))
          ((k : ℝ) * alpha)]
  linarith

/--
For each relative time-window size delta > 0, all sufficiently late trailing
windows contain a return to a bounded depth. The depth bound can depend on
delta. Asymptotic tightness of the continuous-time empirical measures implies
this property; the measure-theoretic implication is not formalized here.
-/
def RelativeBoundedReturns (f : ℝ → ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∃ R T0 : ℝ, 0 ≤ R ∧ 0 ≤ T0 ∧
      ∀ t : ℝ, T0 ≤ t →
        ∃ s : ℝ, 0 ≤ s ∧ s ≤ t ∧ t - s ≤ delta * t ∧ f s ≤ R

/-- Epsilon formulation of an eventual sublinear upper bound. -/
def SublinearUpperBound (f : ℝ → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps →
    ∃ T0 : ℝ, 0 ≤ T0 ∧ ∀ t : ℝ, T0 ≤ t → f t ≤ eps * t

/--
A function whose upward growth is at most L per time unit and which has
relative bounded returns has a sublinear upper bound. For a nonnegative
function, the conclusion is exactly f(t)/t -> 0 as t -> +infinity.
-/
theorem relative_returns_imply_sublinear
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hgrowth : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      f t ≤ f s + L * (t - s))
    (hreturns : RelativeBoundedReturns f) :
    SublinearUpperBound f := by
  intro eps heps
  let delta : ℝ := eps / (2 * (L + 1))
  have hden : 0 < 2 * (L + 1) := by linarith
  have hdelta : 0 < delta := div_pos heps hden
  obtain ⟨R, T0, _hR, hT0, hreturn⟩ := hreturns delta hdelta
  refine ⟨max T0 (2 * R / eps), le_trans hT0 (le_max_left _ _), ?_⟩
  intro t ht
  have ht0 : T0 ≤ t := le_trans (le_max_left _ _) ht
  have htR : 2 * R / eps ≤ t := le_trans (le_max_right _ _) ht
  have hRt : 2 * R ≤ t * eps := (div_le_iff₀ heps).mp htR
  obtain ⟨s, hs0, hst, hgap, hsR⟩ := hreturn t ht0
  have hLp : 0 ≤ L + 1 := by linarith
  have hL0 : L + 1 ≠ 0 := by linarith
  have hbound : L * (t - s) ≤ eps * t / 2 := by
    calc
      L * (t - s) ≤ (L + 1) * (t - s) :=
        mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr hst)
      _ ≤ (L + 1) * (delta * t) :=
        mul_le_mul_of_nonneg_left hgap hLp
      _ = eps * t / 2 := by
        dsimp [delta]
        field_simp [hL0]
  have hg := hgrowth s t hs0 hst
  nlinarith

#print axioms rational_approximation_forces_hole
#print axioms relative_returns_imply_sublinear

end AbelianLog

namespace AbelianLog

/-! ## V3 block: finite covering radii and interval certificates

The user has now validated this block as well as the preceding v2 block.
All declarations and proof bodies are retained without changes.
-/

/-- The M points 0, alpha, ..., (M-1)*alpha cover the circle with radius rho.
Integer translates encode the quotient by Z explicitly. -/
def FiniteOrbitCovers (alpha : ℝ) (M : ℕ) (rho : ℝ) : Prop :=
  ∀ y : ℝ, ∃ k j : ℤ,
    0 ≤ k ∧ k < (M : ℤ) ∧ |(k : ℝ) * alpha - (j : ℝ) - y| ≤ rho

/-- Infimum of all radii covering the finite orbit. We use this only for M > 0.
No geometric interpretation is assigned to the M = 0 value. -/
noncomputable def finiteOrbitCoveringRadius (alpha : ℝ) (M : ℕ) : ℝ :=
  sInf {rho : ℝ | FiniteOrbitCovers alpha M rho}

/-- A nonempty orbit has an admissible covering radius (the coarse bound 1). -/
theorem finiteOrbitCovers_one
    (alpha : ℝ) (M : ℕ) (hM : 0 < M) :
    FiniteOrbitCovers alpha M 1 := by
  intro y
  have hylo : (Int.floor y : ℝ) ≤ y := Int.floor_le y
  have hyhi : y < (Int.floor y : ℝ) + 1 :=
    Int.floor_le_iff.mp (le_refl (Int.floor y))
  have hnear : |(Int.floor y : ℝ) - y| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨0, -Int.floor y, by norm_num, ?_, ?_⟩
  · exact_mod_cast hM
  · simpa only [Int.cast_zero, Int.cast_neg, zero_mul,
      sub_neg_eq_add, zero_add] using hnear

/-- A covering radius cannot be negative. -/
theorem finiteOrbitCovers_nonneg
    (alpha rho : ℝ) (M : ℕ) (hcover : FiniteOrbitCovers alpha M rho) :
    0 ≤ rho := by
  obtain ⟨k, j, _hk0, _hkM, hdist⟩ := hcover 0
  exact le_trans (abs_nonneg _) hdist

/-- For a nonempty orbit, the infimum definition is nonnegative. -/
theorem finiteOrbitCoveringRadius_nonneg
    (alpha : ℝ) (M : ℕ) (hM : 0 < M) :
    0 ≤ finiteOrbitCoveringRadius alpha M := by
  unfold finiteOrbitCoveringRadius
  refine le_csInf ⟨1, finiteOrbitCovers_one alpha M hM⟩ ?_
  intro rho hcover
  exact finiteOrbitCovers_nonneg alpha rho M hcover

/-- The pointwise v2 obstruction implies a lower bound on the actual
infimum-defined covering radius, not merely on a selected orbit point. -/
theorem finite_covering_radius_lower_bound
    (alpha delta : ℝ) (M : ℕ) (p q : ℤ)
    (hM : 0 < M) (hq : 0 < q)
    (happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤ delta) :
    1 / (2 * (q : ℝ)) - ((M : ℝ) - 1) * delta ≤
      finiteOrbitCoveringRadius alpha M := by
  unfold finiteOrbitCoveringRadius
  refine le_csInf ⟨1, finiteOrbitCovers_one alpha M hM⟩ ?_
  intro rho hcover
  obtain ⟨k, j, hk0, hkM, hdist⟩ := hcover (1 / (2 * (q : ℝ)))
  have hM1 : (1 : ℕ) ≤ M := hM
  have hM1R : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hB : 0 ≤ (M : ℝ) - 1 := by linarith
  have hk0R : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
  have hkZ : k ≤ (M : ℤ) - 1 := by omega
  have hkR : (k : ℝ) ≤ (M : ℝ) - 1 := by exact_mod_cast hkZ
  have hkabs : |(k : ℝ)| ≤ (M : ℝ) - 1 := by
    rw [abs_of_nonneg hk0R]
    exact hkR
  exact le_trans
    (rational_approximation_forces_hole alpha delta ((M : ℝ) - 1)
      p q k j hq hB happrox hkabs) hdist

/-- Endpoint bounds on an enclosing interval are sufficient to produce
an exact lower bound for M times the covering radius. -/
theorem interval_certifies_normalized_covering_lower_bound
    (alpha lo hi delta C : ℝ) (M : ℕ) (p q : ℤ)
    (hM : 0 < M) (hq : 0 < q)
    (hlo : lo ≤ alpha) (hhi : alpha ≤ hi)
    (hleft : |lo - (p : ℝ) / (q : ℝ)| ≤ delta)
    (hright : |hi - (p : ℝ) / (q : ℝ)| ≤ delta)
    (hcert : C ≤ (M : ℝ) *
      (1 / (2 * (q : ℝ)) - ((M : ℝ) - 1) * delta)) :
    C ≤ (M : ℝ) * finiteOrbitCoveringRadius alpha M := by
  have hleftlo := (abs_le.mp hleft).1
  have hrightup := (abs_le.mp hright).2
  have happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤ delta :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hbound := finite_covering_radius_lower_bound alpha delta M p q
    hM hq happrox
  exact le_trans hcert
    (mul_le_mul_of_nonneg_left hbound (by positivity))

/-- Small certificate chosen from the numerical experiment.

This is a theorem for EVERY real alpha in the displayed rational interval.
The inclusion of the particular elliptic-logarithm ratio in that interval
is NOT proved or postulated as an axiom in this file: it is an explicit
hypothesis of this theorem. The two endpoint tests and the numerical
covering constant are checked by `norm_num`, not by floating-point code.
-/
theorem small_interval_certificate
    (alpha : ℝ)
    (hlo : (425071857 : ℝ) / 10000000000 ≤ alpha)
    (hhi : alpha ≤ (425071858 : ℝ) / 10000000000) :
    (17 / 10 : ℝ) ≤ (9480 : ℝ) * finiteOrbitCoveringRadius alpha 9480 := by
  exact interval_certifies_normalized_covering_lower_bound
    alpha (425071857 / 10000000000) (425071858 / 10000000000)
    (19 / 1000000000) (17 / 10) 9480 59 1388
    (by norm_num) (by norm_num) hlo hhi
    (by norm_num) (by norm_num) (by norm_num)

#print axioms finite_covering_radius_lower_bound
#print axioms interval_certifies_normalized_covering_lower_bound
#print axioms small_interval_certificate

end AbelianLog

/-! # V4 EXTENSION -- new draft, not yet compiled

The new upper bound requires IsCoprime p q. This hypothesis is essential:
without it, the first q multiples of p/q need not visit the full q-grid.
The lower bound from v3 does not require coprimality.
-/

namespace AbelianLog

/-- Choose an integer within half a unit of a prescribed real number. -/
theorem exists_int_within_half (x : ℝ) :
    ∃ m : ℤ, |(m : ℝ) - x| ≤ (1 / 2 : ℝ) := by
  let m : ℤ := Int.floor (x + 1 / 2)
  have hlo : (m : ℝ) ≤ x + 1 / 2 := Int.floor_le (x + 1 / 2)
  have hhi : x + 1 / 2 < (m : ℝ) + 1 :=
    Int.floor_le_iff.mp (le_refl (Int.floor (x + 1 / 2)))
  exact ⟨m, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- Bezout's identity gives a bounded representative of every residue:
for each m, k*p - j*q = m with 0 <= k < q. -/
theorem coprime_grid_representation
    (p q m : ℤ) (hq : 0 < q) (hcop : IsCoprime p q) :
    ∃ k j : ℤ, 0 ≤ k ∧ k < q ∧ k * p - j * q = m := by
  obtain ⟨a, b, hab⟩ := hcop
  let k : ℤ := (a * m) % q
  let t : ℤ := (a * m) / q
  have hk0 : 0 ≤ k := Int.emod_nonneg (a * m) (ne_of_gt hq)
  have hkq : k < q := Int.emod_lt_of_pos (a * m) hq
  have hdiv : k + q * t = a * m := Int.emod_add_mul_ediv (a * m) q
  refine ⟨k, -b * m - t * p, hk0, hkq, ?_⟩
  calc
    k * p - (-b * m - t * p) * q =
        m * (a * p + b * q) + (k + q * t - a * m) * p := by ring
    _ = m := by rw [hab, hdiv]; ring

/-- A target is within 1/(2q) of some point of the full rational q-grid. -/
theorem exists_near_rational_grid_point
    (q : ℤ) (hq : 0 < q) (y : ℝ) :
    ∃ m : ℤ, |(m : ℝ) / (q : ℝ) - y| ≤ 1 / (2 * (q : ℝ)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  obtain ⟨m, hm⟩ := exists_int_within_half ((q : ℝ) * y)
  refine ⟨m, ?_⟩
  calc
    |(m : ℝ) / (q : ℝ) - y| =
        |((m : ℝ) - (q : ℝ) * y) / (q : ℝ)| := by
      congr 1
      field_simp [hq0]
    _ = |(m : ℝ) - (q : ℝ) * y| / (q : ℝ) := by
      rw [abs_div, abs_of_pos hqR]
    _ ≤ (1 / 2 : ℝ) / (q : ℝ) :=
      div_le_div_of_nonneg_right hm (le_of_lt hqR)
    _ = 1 / (2 * (q : ℝ)) := by field_simp [hq0]

/-- Perturb the first q points of the rational orbit. When p and q are
coprime and q <= M, this proves coverage of EVERY target, using only k < q.
The perturbation cost is (q-1)*delta, not (M-1)*delta. -/
theorem finiteOrbitCovers_of_rational_approximation
    (alpha delta : ℝ) (M : ℕ) (p q : ℤ)
    (hq : 0 < q) (hcop : IsCoprime p q) (hqM : q ≤ (M : ℤ))
    (happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤ delta) :
    FiniteOrbitCovers alpha M
      (1 / (2 * (q : ℝ)) + ((q : ℝ) - 1) * delta) := by
  intro y
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hq1 : (1 : ℤ) ≤ q := by omega
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hB : 0 ≤ (q : ℝ) - 1 := by linarith
  obtain ⟨m, hm⟩ := exists_near_rational_grid_point q hq y
  obtain ⟨k, j, hk0, hkq, hrep⟩ := coprime_grid_representation p q m hq hcop
  have hrepR : (k : ℝ) * (p : ℝ) - (j : ℝ) * (q : ℝ) = (m : ℝ) := by
    exact_mod_cast hrep
  have heq : (k : ℝ) * ((p : ℝ) / (q : ℝ)) - (j : ℝ) =
      (m : ℝ) / (q : ℝ) := by
    field_simp [hq0]
    nlinarith [hrepR]
  have hgrid : |(k : ℝ) * ((p : ℝ) / (q : ℝ)) - (j : ℝ) - y| ≤
      1 / (2 * (q : ℝ)) := by
    rw [heq]
    exact hm
  have hk0R : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
  have hkZ : k ≤ q - 1 := by omega
  have hkR : (k : ℝ) ≤ (q : ℝ) - 1 := by exact_mod_cast hkZ
  have hkabs : |(k : ℝ)| ≤ (q : ℝ) - 1 := by
    rw [abs_of_nonneg hk0R]
    exact hkR
  have hpert : |(k : ℝ) * (alpha - (p : ℝ) / (q : ℝ))| ≤
      ((q : ℝ) - 1) * delta := by
    rw [abs_mul]
    exact mul_le_mul hkabs happrox (abs_nonneg _) hB
  refine ⟨k, j, hk0, lt_of_lt_of_le hkq hqM, ?_⟩
  calc
    |(k : ℝ) * alpha - (j : ℝ) - y| =
        |((k : ℝ) * ((p : ℝ) / (q : ℝ)) - (j : ℝ) - y) +
          (k : ℝ) * (alpha - (p : ℝ) / (q : ℝ))| := by
      congr 1
      ring
    _ ≤ |(k : ℝ) * ((p : ℝ) / (q : ℝ)) - (j : ℝ) - y| +
        |(k : ℝ) * (alpha - (p : ℝ) / (q : ℝ))| := abs_add_le _ _
    _ ≤ 1 / (2 * (q : ℝ)) + ((q : ℝ) - 1) * delta :=
      add_le_add hgrid hpert

/-- The complementary upper bound on the infimum-defined covering radius. -/
theorem finite_covering_radius_upper_bound
    (alpha delta : ℝ) (M : ℕ) (p q : ℤ)
    (hq : 0 < q) (hcop : IsCoprime p q) (hqM : q ≤ (M : ℤ))
    (happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤ delta) :
    finiteOrbitCoveringRadius alpha M ≤
      1 / (2 * (q : ℝ)) + ((q : ℝ) - 1) * delta := by
  unfold finiteOrbitCoveringRadius
  have hb : BddBelow {rho : ℝ | FiniteOrbitCovers alpha M rho} := by
    refine ⟨0, ?_⟩
    intro rho hcover
    exact finiteOrbitCovers_nonneg alpha rho M hcover
  exact csInf_le hb
    (finiteOrbitCovers_of_rational_approximation alpha delta M p q
      hq hcop hqM happrox)

/-- Two-sided perturbation estimate. Coprimality is used only for the upper
bound; the lower bound comes from the v3 theorem validated by the user. -/
theorem finite_covering_radius_two_sided
    (alpha delta : ℝ) (M : ℕ) (p q : ℤ)
    (hq : 0 < q) (hcop : IsCoprime p q) (hqM : q ≤ (M : ℤ))
    (happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤ delta) :
    (1 / (2 * (q : ℝ)) - ((M : ℝ) - 1) * delta ≤
      finiteOrbitCoveringRadius alpha M) ∧
    (finiteOrbitCoveringRadius alpha M ≤
      1 / (2 * (q : ℝ)) + ((q : ℝ) - 1) * delta) := by
  have hMZ : (0 : ℤ) < (M : ℤ) := lt_of_lt_of_le hq hqM
  have hM : 0 < M := by exact_mod_cast hMZ
  exact ⟨finite_covering_radius_lower_bound alpha delta M p q hM hq happrox,
    finite_covering_radius_upper_bound alpha delta M p q hq hcop hqM happrox⟩

/-- Exact rational-grid sanity check: after one full period, additional
points do not change the covering radius of a reduced rational rotation. -/
theorem rational_orbit_covering_radius_eq
    (M : ℕ) (p q : ℤ) (hq : 0 < q)
    (hcop : IsCoprime p q) (hqM : q ≤ (M : ℤ)) :
    finiteOrbitCoveringRadius ((p : ℝ) / (q : ℝ)) M =
      1 / (2 * (q : ℝ)) := by
  have h := finite_covering_radius_two_sided
    ((p : ℝ) / (q : ℝ)) 0 M p q hq hcop hqM (by simp)
  apply le_antisymm
  · simpa only [mul_zero, add_zero] using h.2
  · simpa only [mul_zero, sub_zero] using h.1

/-- A useful scale bound: a reduced inverse-square approximation yields
radius at most 3/(2q) whenever the orbit length is at least q.
This statement does not assume that p/q was generated by continued fractions. -/
theorem inverse_square_approximation_covering_upper_bound
    (alpha : ℝ) (M : ℕ) (p q : ℤ)
    (hq : 0 < q) (hcop : IsCoprime p q) (hqM : q ≤ (M : ℤ))
    (happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤
      1 / ((q : ℝ) * (q : ℝ))) :
    finiteOrbitCoveringRadius alpha M ≤ 3 / (2 * (q : ℝ)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqR
  have hterm : ((q : ℝ) - 1) * (1 / ((q : ℝ) * (q : ℝ))) ≤
      1 / (q : ℝ) := by
    calc
      ((q : ℝ) - 1) * (1 / ((q : ℝ) * (q : ℝ))) =
          ((q : ℝ) - 1) / ((q : ℝ) * (q : ℝ)) := by ring
      _ ≤ (q : ℝ) / ((q : ℝ) * (q : ℝ)) :=
        div_le_div_of_nonneg_right (by linarith)
          (mul_nonneg (le_of_lt hqR) (le_of_lt hqR))
      _ = 1 / (q : ℝ) := by field_simp [hq0]
  calc
    finiteOrbitCoveringRadius alpha M ≤
        1 / (2 * (q : ℝ)) +
          ((q : ℝ) - 1) * (1 / ((q : ℝ) * (q : ℝ))) :=
      finite_covering_radius_upper_bound alpha
        (1 / ((q : ℝ) * (q : ℝ))) M p q hq hcop hqM happrox
    _ ≤ 1 / (2 * (q : ℝ)) + 1 / (q : ℝ) := add_le_add le_rfl hterm
    _ = 3 / (2 * (q : ℝ)) := by
      field_simp [hq0]
      norm_num

/-- Endpoint inequalities can certify an upper bound just as they certify
a lower bound in v3. The coprimality and q <= M conditions are explicit. -/
theorem interval_certifies_normalized_covering_upper_bound
    (alpha lo hi delta U : ℝ) (M : ℕ) (p q : ℤ)
    (hq : 0 < q) (hcop : IsCoprime p q) (hqM : q ≤ (M : ℤ))
    (hlo : lo ≤ alpha) (hhi : alpha ≤ hi)
    (hleft : |lo - (p : ℝ) / (q : ℝ)| ≤ delta)
    (hright : |hi - (p : ℝ) / (q : ℝ)| ≤ delta)
    (hcert : (M : ℝ) *
      (1 / (2 * (q : ℝ)) + ((q : ℝ) - 1) * delta) ≤ U) :
    (M : ℝ) * finiteOrbitCoveringRadius alpha M ≤ U := by
  have hleftlo := (abs_le.mp hleft).1
  have hrightup := (abs_le.mp hright).2
  have happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤ delta :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hbound := finite_covering_radius_upper_bound alpha delta M p q
    hq hcop hqM happrox
  exact le_trans (mul_le_mul_of_nonneg_left hbound (by positivity)) hcert

/-- The same interval as the checked v3 example now gives both bounds.
The lower half is exactly the already-checked small_interval_certificate.
The upper half uses the explicit Bezout identity 447*59 - 19*1388 = 1.
The elliptic-logarithm ratio's membership in the interval is still NOT
proved here; hlo and hhi remain explicit hypotheses. -/
theorem small_interval_two_sided_certificate
    (alpha : ℝ)
    (hlo : (425071857 : ℝ) / 10000000000 ≤ alpha)
    (hhi : alpha ≤ (425071858 : ℝ) / 10000000000) :
    ((17 / 10 : ℝ) ≤ (9480 : ℝ) * finiteOrbitCoveringRadius alpha 9480) ∧
    ((9480 : ℝ) * finiteOrbitCoveringRadius alpha 9480 ≤ (37 / 10 : ℝ)) := by
  constructor
  · exact small_interval_certificate alpha hlo hhi
  · have hcop : IsCoprime (59 : ℤ) 1388 := by
      exact ⟨447, -19, by norm_num⟩
    exact interval_certifies_normalized_covering_upper_bound
      alpha (425071857 / 10000000000) (425071858 / 10000000000)
      (19 / 1000000000) (37 / 10) 9480 59 1388
      (by norm_num) hcop (by norm_num) hlo hhi
      (by norm_num) (by norm_num) (by norm_num)

#print axioms finite_covering_radius_upper_bound
#print axioms finite_covering_radius_two_sided
#print axioms rational_orbit_covering_radius_eq
#print axioms inverse_square_approximation_covering_upper_bound
#print axioms interval_certifies_normalized_covering_upper_bound
#print axioms small_interval_two_sided_certificate

end AbelianLog

/-!
# V5 EXTENSION: centered perturbations

The original v4.1 declarations above are unchanged. The new declarations
below have not been compiled in the authoring environment. They are proof
drafts for a complete-file test in the user's Lean/Mathlib live editor.

Main improvement:
  |R_alpha(M) - R_beta(M)| <= (M-1)/2 * |alpha-beta|.
Translate the comparison target by (M-1)/2 * (alpha-beta) before matching
orbit indices. This halves the earlier uncentered perturbation cost.

The upper-bound theorem below uses q : Nat to apply monotonicity at orbit
length q. The lower-bound theorem retains q : Int, as in v4.1. Coprimality
is still needed only for the upper bound.
-/

namespace AbelianLog

/-- Any admissible covering radius bounds the infimum from above. -/
theorem finiteOrbitCoveringRadius_le_of_covers
    (alpha rho : ℝ) (M : ℕ) (hcover : FiniteOrbitCovers alpha M rho) :
    finiteOrbitCoveringRadius alpha M ≤ rho := by
  unfold finiteOrbitCoveringRadius
  have hb : BddBelow {r : ℝ | FiniteOrbitCovers alpha M r} := by
    refine ⟨0, ?_⟩
    intro r hr
    exact finiteOrbitCovers_nonneg alpha r M hr
  exact csInf_le hb hcover

/-- Enlarging the orbit preserves coverage. -/
theorem finiteOrbitCovers_mono
    (alpha rho : ℝ) (M N : ℕ) (hMN : M ≤ N)
    (hcover : FiniteOrbitCovers alpha M rho) :
    FiniteOrbitCovers alpha N rho := by
  intro y
  obtain ⟨k, j, hk0, hkM, hdist⟩ := hcover y
  have hMNZ : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast hMN
  exact ⟨k, j, hk0, lt_of_lt_of_le hkM hMNZ, hdist⟩

/-- Covering radius is nonincreasing with the positive orbit length. -/
theorem finiteOrbitCoveringRadius_antitone
    (alpha : ℝ) (M N : ℕ) (hM : 0 < M) (hMN : M ≤ N) :
    finiteOrbitCoveringRadius alpha N ≤ finiteOrbitCoveringRadius alpha M := by
  change finiteOrbitCoveringRadius alpha N ≤
    sInf {rho : ℝ | FiniteOrbitCovers alpha M rho}
  refine le_csInf ⟨1, finiteOrbitCovers_one alpha M hM⟩ ?_
  intro rho hcover
  exact finiteOrbitCoveringRadius_le_of_covers alpha rho N
    (finiteOrbitCovers_mono alpha rho M N hMN hcover)

/-- Center the index range before comparing the two rotations.
The radius error is (M-1)*delta/2, rather than (M-1)*delta. -/
theorem finiteOrbitCovers_centered_perturbation
    (alpha beta delta rho : ℝ) (M : ℕ) (hM : 0 < M)
    (happrox : |alpha - beta| ≤ delta)
    (hcover : FiniteOrbitCovers beta M rho) :
    FiniteOrbitCovers alpha M (rho + ((M : ℝ) - 1) / 2 * delta) := by
  intro y
  let c : ℝ := ((M : ℝ) - 1) / 2
  obtain ⟨k, j, hk0, hkM, hnear⟩ := hcover (y - c * (alpha - beta))
  have hM1 : (1 : ℕ) ≤ M := hM
  have hM1R : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hk0R : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
  have hkZ : k ≤ (M : ℤ) - 1 := by omega
  have hkR : (k : ℝ) ≤ (M : ℝ) - 1 := by exact_mod_cast hkZ
  have hkc : |(k : ℝ) - c| ≤ c := by
    apply abs_le.mpr
    constructor <;> dsimp [c] <;> linarith
  have hpert : |((k : ℝ) - c) * (alpha - beta)| ≤ c * delta := by
    rw [abs_mul]
    exact mul_le_mul hkc happrox (abs_nonneg _) hc
  refine ⟨k, j, hk0, hkM, ?_⟩
  change |(k : ℝ) * alpha - (j : ℝ) - y| ≤ rho + c * delta
  calc
    |(k : ℝ) * alpha - (j : ℝ) - y| =
        |((k : ℝ) * beta - (j : ℝ) - (y - c * (alpha - beta))) +
          ((k : ℝ) - c) * (alpha - beta)| := by
      congr 1
      ring
    _ ≤ |(k : ℝ) * beta - (j : ℝ) - (y - c * (alpha - beta))| +
        |((k : ℝ) - c) * (alpha - beta)| := abs_add_le _ _
    _ ≤ rho + c * delta := add_le_add hnear hpert

/-- One direction of the centered comparison, without assuming attainment
of either infimum-defined covering radius. -/
theorem finiteOrbitCoveringRadius_centered_le
    (alpha beta delta : ℝ) (M : ℕ) (hM : 0 < M)
    (happrox : |alpha - beta| ≤ delta) :
    finiteOrbitCoveringRadius alpha M ≤ finiteOrbitCoveringRadius beta M +
      ((M : ℝ) - 1) / 2 * delta := by
  let c : ℝ := ((M : ℝ) - 1) / 2
  have h : finiteOrbitCoveringRadius alpha M - c * delta ≤
      finiteOrbitCoveringRadius beta M := by
    change finiteOrbitCoveringRadius alpha M - c * delta ≤
      sInf {rho : ℝ | FiniteOrbitCovers beta M rho}
    refine le_csInf ⟨1, finiteOrbitCovers_one beta M hM⟩ ?_
    intro rho hcover
    have hu := finiteOrbitCoveringRadius_le_of_covers alpha
      (rho + ((M : ℝ) - 1) / 2 * delta) M
      (finiteOrbitCovers_centered_perturbation alpha beta delta rho M hM
        happrox hcover)
    change finiteOrbitCoveringRadius alpha M ≤ rho + c * delta at hu
    linarith
  change finiteOrbitCoveringRadius alpha M ≤
    finiteOrbitCoveringRadius beta M + c * delta
  linarith

/-- Centered Lipschitz stability of the actual covering radius. -/
theorem finiteOrbitCoveringRadius_abs_sub_le
    (alpha beta delta : ℝ) (M : ℕ) (hM : 0 < M)
    (happrox : |alpha - beta| ≤ delta) :
    |finiteOrbitCoveringRadius alpha M - finiteOrbitCoveringRadius beta M| ≤
      ((M : ℝ) - 1) / 2 * delta := by
  have hsym : |beta - alpha| ≤ delta := by
    calc
      |beta - alpha| = |alpha - beta| := abs_sub_comm _ _
      _ ≤ delta := happrox
  have hf := finiteOrbitCoveringRadius_centered_le alpha beta delta M hM happrox
  have hb := finiteOrbitCoveringRadius_centered_le beta alpha delta M hM hsym
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The centered rational-grid lower bound needs no coprimality. -/
theorem finite_covering_radius_centered_lower_bound
    (alpha delta : ℝ) (M : ℕ) (p q : ℤ)
    (hM : 0 < M) (hq : 0 < q)
    (happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤ delta) :
    1 / (2 * (q : ℝ)) - ((M : ℝ) - 1) / 2 * delta ≤
      finiteOrbitCoveringRadius alpha M := by
  have hgrid0 := finite_covering_radius_lower_bound
    ((p : ℝ) / (q : ℝ)) 0 M p q hM hq (by simp)
  have hgrid : 1 / (2 * (q : ℝ)) ≤
      finiteOrbitCoveringRadius ((p : ℝ) / (q : ℝ)) M := by
    simpa only [mul_zero, sub_zero] using hgrid0
  have hstab := finiteOrbitCoveringRadius_abs_sub_le
    alpha ((p : ℝ) / (q : ℝ)) delta M hM happrox
  have hb := (abs_le.mp hstab).1
  linarith

/-- Perturb the full reduced q-grid at orbit length q, then use monotonicity.
This theorem uses a natural-number denominator q; p is still an integer. -/
theorem finite_covering_radius_centered_upper_bound
    (alpha delta : ℝ) (M q : ℕ) (p : ℤ)
    (hq : 0 < q) (hcop : IsCoprime p (q : ℤ)) (hqM : q ≤ M)
    (happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤ delta) :
    finiteOrbitCoveringRadius alpha M ≤
      1 / (2 * (q : ℝ)) + ((q : ℝ) - 1) / 2 * delta := by
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hrat : finiteOrbitCoveringRadius ((p : ℝ) / (q : ℝ)) q =
      1 / (2 * (q : ℝ)) := by
    simpa only [Int.cast_natCast] using
      (rational_orbit_covering_radius_eq q p (q : ℤ) hqZ hcop (le_refl (q : ℤ)))
  calc
    finiteOrbitCoveringRadius alpha M ≤ finiteOrbitCoveringRadius alpha q :=
      finiteOrbitCoveringRadius_antitone alpha q M hq hqM
    _ ≤ finiteOrbitCoveringRadius ((p : ℝ) / (q : ℝ)) q +
        ((q : ℝ) - 1) / 2 * delta :=
      finiteOrbitCoveringRadius_centered_le alpha ((p : ℝ) / (q : ℝ)) delta q
        hq happrox
    _ = 1 / (2 * (q : ℝ)) + ((q : ℝ) - 1) / 2 * delta := by rw [hrat]

/-- The same short interval used in v4.1 now certifies the tighter bounds
2.56 <= 9480 * R_alpha(9480) <= 3.54. Analytic interval membership is still
an explicit hypothesis, not an axiom or a proved elliptic-integral fact. -/
theorem small_centered_interval_certificate
    (alpha : ℝ)
    (hlo : (425071857 : ℝ) / 10000000000 ≤ alpha)
    (hhi : alpha ≤ (425071858 : ℝ) / 10000000000) :
    ((64 / 25 : ℝ) ≤ (9480 : ℝ) * finiteOrbitCoveringRadius alpha 9480) ∧
    ((9480 : ℝ) * finiteOrbitCoveringRadius alpha 9480 ≤ (177 / 50 : ℝ)) := by
  have hleft : |(425071857 : ℝ) / 10000000000 - 59 / 1388| ≤
      (19 : ℝ) / 1000000000 := by norm_num
  have hright : |(425071858 : ℝ) / 10000000000 - 59 / 1388| ≤
      (19 : ℝ) / 1000000000 := by norm_num
  have happrox : |alpha - (59 : ℝ) / 1388| ≤ (19 : ℝ) / 1000000000 :=
    abs_le.mpr ⟨by linarith [(abs_le.mp hleft).1],
      by linarith [(abs_le.mp hright).2]⟩
  have hcop : IsCoprime (59 : ℤ) 1388 := by
    exact ⟨447, -19, by norm_num⟩
  constructor
  · have hlower := finite_covering_radius_centered_lower_bound alpha
      (19 / 1000000000) 9480 59 1388 (by norm_num) (by norm_num) happrox
    have hscaled := mul_le_mul_of_nonneg_left hlower
      (show (0 : ℝ) ≤ 9480 by norm_num)
    exact le_trans (by norm_num) hscaled
  · have hupper := finite_covering_radius_centered_upper_bound alpha
      (19 / 1000000000) 9480 1388 59 (by norm_num) hcop (by norm_num) happrox
    have hscaled := mul_le_mul_of_nonneg_left hupper
      (show (0 : ℝ) ≤ 9480 by norm_num)
    exact le_trans hscaled (by norm_num)

#print axioms finiteOrbitCoveringRadius_le_of_covers
#print axioms finiteOrbitCovers_mono
#print axioms finiteOrbitCoveringRadius_antitone
#print axioms finiteOrbitCovers_centered_perturbation
#print axioms finiteOrbitCoveringRadius_centered_le
#print axioms finiteOrbitCoveringRadius_abs_sub_le
#print axioms finite_covering_radius_centered_lower_bound
#print axioms finite_covering_radius_centered_upper_bound
#print axioms small_centered_interval_certificate

end AbelianLog

/-!
# V6 EXTENSION: signed orbits and quadratic-height windows

NEW DRAFT: this block has not been compiled in the authoring environment.

The signed orbit is defined independently, with integer indices -B <= k <= B.
Its equality with the one-sided covering radius is proved by translation and
reindexing, not imposed as a definition. The quadratic-height model is also
an independent definition. Exact height windows avoid floor/square-root APIs.

No elliptic curve, elliptic logarithm, canonical height, rank, or saturation
fact is asserted by these definitions. In the final transfer theorem an
arbitrary height function must satisfy an explicit quadratic-law hypothesis.
-/

namespace AbelianLog

/-- Coverage by the signed orbit -B*alpha, ..., 0, ..., B*alpha. -/
def SignedOrbitCovers (alpha : ℝ) (B : ℕ) (rho : ℝ) : Prop :=
  ∀ y : ℝ, ∃ k j : ℤ,
    -(B : ℤ) ≤ k ∧ k ≤ (B : ℤ) ∧
      |(k : ℝ) * alpha - (j : ℝ) - y| ≤ rho

/-- Covering radius of the signed orbit, including B = 0. -/
noncomputable def signedOrbitCoveringRadius (alpha : ℝ) (B : ℕ) : ℝ :=
  sInf {rho : ℝ | SignedOrbitCovers alpha B rho}

/-- Translate the target and reindex by B. This proves equality of the sets
of admissible radii, not merely an inequality between their infima. -/
theorem signedOrbitCovers_iff_finiteOrbitCovers
    (alpha rho : ℝ) (B : ℕ) :
    SignedOrbitCovers alpha B rho ↔
      FiniteOrbitCovers alpha (2 * B + 1) rho := by
  have hsize : ((2 * B + 1 : ℕ) : ℤ) = 2 * (B : ℤ) + 1 := by
    push_cast
    ring
  constructor
  · intro h y
    obtain ⟨k, j, hklo, hkhi, hnear⟩ := h (y - (B : ℝ) * alpha)
    refine ⟨k + (B : ℤ), j, ?_, ?_, ?_⟩
    · omega
    · omega
    · have heq : (((k + (B : ℤ) : ℤ) : ℝ) * alpha - (j : ℝ) - y) =
          (k : ℝ) * alpha - (j : ℝ) - (y - (B : ℝ) * alpha) := by
        push_cast
        ring
      rw [heq]
      exact hnear
  · intro h y
    obtain ⟨k, j, hklo, hkhi, hnear⟩ := h (y + (B : ℝ) * alpha)
    refine ⟨k - (B : ℤ), j, ?_, ?_, ?_⟩
    · omega
    · omega
    · have heq : (((k - (B : ℤ) : ℤ) : ℝ) * alpha - (j : ℝ) - y) =
          (k : ℝ) * alpha - (j : ℝ) - (y + (B : ℝ) * alpha) := by
        push_cast
        ring
      rw [heq]
      exact hnear

/-- The signed and one-sided radii are exactly equal for every real alpha. -/
theorem signedOrbitCoveringRadius_eq_finite
    (alpha : ℝ) (B : ℕ) :
    signedOrbitCoveringRadius alpha B =
      finiteOrbitCoveringRadius alpha (2 * B + 1) := by
  have hsets : {rho : ℝ | SignedOrbitCovers alpha B rho} =
      {rho : ℝ | FiniteOrbitCovers alpha (2 * B + 1) rho} := by
    ext rho
    exact signedOrbitCovers_iff_finiteOrbitCovers alpha rho B
  unfold signedOrbitCoveringRadius finiteOrbitCoveringRadius
  rw [hsets]

/-- The signed radius is nonnegative, including at B = 0. -/
theorem signedOrbitCoveringRadius_nonneg
    (alpha : ℝ) (B : ℕ) :
    0 ≤ signedOrbitCoveringRadius alpha B := by
  rw [signedOrbitCoveringRadius_eq_finite]
  exact finiteOrbitCoveringRadius_nonneg alpha (2 * B + 1) (by omega)

/-- Increasing the signed cutoff cannot increase the covering radius. -/
theorem signedOrbitCoveringRadius_antitone
    (alpha : ℝ) (B C : ℕ) (hBC : B ≤ C) :
    signedOrbitCoveringRadius alpha C ≤ signedOrbitCoveringRadius alpha B := by
  rw [signedOrbitCoveringRadius_eq_finite, signedOrbitCoveringRadius_eq_finite]
  exact finiteOrbitCoveringRadius_antitone alpha (2 * B + 1) (2 * C + 1)
    (by omega) (by omega)

/-- The centered stability constant becomes exactly B for the signed orbit. -/
theorem signedOrbitCoveringRadius_abs_sub_le
    (alpha beta delta : ℝ) (B : ℕ)
    (happrox : |alpha - beta| ≤ delta) :
    |signedOrbitCoveringRadius alpha B - signedOrbitCoveringRadius beta B| ≤
      (B : ℝ) * delta := by
  rw [signedOrbitCoveringRadius_eq_finite, signedOrbitCoveringRadius_eq_finite]
  have h := finiteOrbitCoveringRadius_abs_sub_le alpha beta delta
    (2 * B + 1) (by omega) happrox
  have heq : (((2 * B + 1 : ℕ) : ℝ) - 1) / 2 * delta =
      (B : ℝ) * delta := by
    push_cast
    ring
  rw [heq] at h
  exact h

/-- Signed rational-grid lower bound; no coprimality is needed. -/
theorem signed_covering_radius_lower_bound
    (alpha delta : ℝ) (B : ℕ) (p q : ℤ)
    (hq : 0 < q)
    (happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤ delta) :
    1 / (2 * (q : ℝ)) - (B : ℝ) * delta ≤
      signedOrbitCoveringRadius alpha B := by
  rw [signedOrbitCoveringRadius_eq_finite]
  have h := finite_covering_radius_centered_lower_bound alpha delta
    (2 * B + 1) p q (by omega) hq happrox
  have heq : (((2 * B + 1 : ℕ) : ℝ) - 1) / 2 * delta =
      (B : ℝ) * delta := by
    push_cast
    ring
  rw [heq] at h
  exact h

/-- Signed rational-grid upper bound; the orbit must contain a full reduced
q-grid before perturbation. The denominator is natural, as in the v5 bound. -/
theorem signed_covering_radius_upper_bound
    (alpha delta : ℝ) (B q : ℕ) (p : ℤ)
    (hq : 0 < q) (hcop : IsCoprime p (q : ℤ)) (hqB : q ≤ 2 * B + 1)
    (happrox : |alpha - (p : ℝ) / (q : ℝ)| ≤ delta) :
    signedOrbitCoveringRadius alpha B ≤
      1 / (2 * (q : ℝ)) + ((q : ℝ) - 1) / 2 * delta := by
  rw [signedOrbitCoveringRadius_eq_finite]
  exact finite_covering_radius_centered_upper_bound alpha delta (2 * B + 1)
    q p hq hcop hqB happrox

/-- Coverage by precisely those indices whose model height hQ*k^2 is at most H.
This is an abstract quadratic height, not a definition of canonical height. -/
def QuadraticHeightOrbitCovers (alpha hQ H rho : ℝ) : Prop :=
  ∀ y : ℝ, ∃ k j : ℤ,
    hQ * (k : ℝ) ^ 2 ≤ H ∧ |(k : ℝ) * alpha - (j : ℝ) - y| ≤ rho

/-- Covering radius for the independently defined quadratic-height cutoff. -/
noncomputable def quadraticHeightCoveringRadius (alpha hQ H : ℝ) : ℝ :=
  sInf {rho : ℝ | QuadraticHeightOrbitCovers alpha hQ H rho}

/-- The exact cutoff is constant on hQ*B^2 <= H < hQ*(B+1)^2.
The upper endpoint must be strict: at equality, the indices ±(B+1) enter. -/
theorem quadratic_height_cutoff_iff
    (hQ H : ℝ) (B : ℕ) (k : ℤ)
    (hhQ : 0 < hQ)
    (hlo : hQ * (B : ℝ) ^ 2 ≤ H)
    (hhi : H < hQ * ((B : ℝ) + 1) ^ 2) :
    hQ * (k : ℝ) ^ 2 ≤ H ↔ -(B : ℤ) ≤ k ∧ k ≤ (B : ℤ) := by
  have hB : (0 : ℝ) ≤ (B : ℝ) := by positivity
  constructor
  · intro hk
    constructor
    · by_contra hn
      have hkZ : k ≤ -(B : ℤ) - 1 := by omega
      have hkR : (k : ℝ) ≤ -(B : ℝ) - 1 := by exact_mod_cast hkZ
      have hp : 0 ≤ (-(k : ℝ) - ((B : ℝ) + 1)) *
          (-(k : ℝ) + ((B : ℝ) + 1)) :=
        mul_nonneg (by linarith) (by linarith)
      have hs : ((B : ℝ) + 1) ^ 2 ≤ (k : ℝ) ^ 2 := by
        nlinarith only [hp]
      have hscaled := mul_le_mul_of_nonneg_left hs (le_of_lt hhQ)
      linarith
    · by_contra hn
      have hkZ : (B : ℤ) + 1 ≤ k := by omega
      have hkR : (B : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hkZ
      have hp : 0 ≤ ((k : ℝ) - ((B : ℝ) + 1)) *
          ((k : ℝ) + ((B : ℝ) + 1)) :=
        mul_nonneg (by linarith) (by linarith)
      have hs : ((B : ℝ) + 1) ^ 2 ≤ (k : ℝ) ^ 2 := by
        nlinarith only [hp]
      have hscaled := mul_le_mul_of_nonneg_left hs (le_of_lt hhQ)
      linarith
  · rintro ⟨hklo, hkhi⟩
    have hkloR : -(B : ℝ) ≤ (k : ℝ) := by exact_mod_cast hklo
    have hkhiR : (k : ℝ) ≤ (B : ℝ) := by exact_mod_cast hkhi
    have hp : 0 ≤ ((B : ℝ) - (k : ℝ)) * ((B : ℝ) + (k : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    have hs : (k : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 := by nlinarith only [hp]
    exact le_trans (mul_le_mul_of_nonneg_left hs (le_of_lt hhQ)) hlo

/-- Under the exact height window, the two coverage predicates agree. -/
theorem quadraticHeightOrbitCovers_iff_signed
    (alpha hQ H rho : ℝ) (B : ℕ)
    (hhQ : 0 < hQ)
    (hlo : hQ * (B : ℝ) ^ 2 ≤ H)
    (hhi : H < hQ * ((B : ℝ) + 1) ^ 2) :
    QuadraticHeightOrbitCovers alpha hQ H rho ↔ SignedOrbitCovers alpha B rho := by
  constructor
  · intro h y
    obtain ⟨k, j, hk, hdist⟩ := h y
    obtain ⟨hklo, hkhi⟩ := (quadratic_height_cutoff_iff hQ H B k hhQ hlo hhi).mp hk
    exact ⟨k, j, hklo, hkhi, hdist⟩
  · intro h y
    obtain ⟨k, j, hklo, hkhi, hdist⟩ := h y
    exact ⟨k, j, (quadratic_height_cutoff_iff hQ H B k hhQ hlo hhi).mpr
      ⟨hklo, hkhi⟩, hdist⟩

/-- Equality of the independently defined infima on every exact height window. -/
theorem quadraticHeightCoveringRadius_eq_signed
    (alpha hQ H : ℝ) (B : ℕ)
    (hhQ : 0 < hQ)
    (hlo : hQ * (B : ℝ) ^ 2 ≤ H)
    (hhi : H < hQ * ((B : ℝ) + 1) ^ 2) :
    quadraticHeightCoveringRadius alpha hQ H = signedOrbitCoveringRadius alpha B := by
  have hsets : {rho : ℝ | QuadraticHeightOrbitCovers alpha hQ H rho} =
      {rho : ℝ | SignedOrbitCovers alpha B rho} := by
    ext rho
    exact quadraticHeightOrbitCovers_iff_signed alpha hQ H rho B hhQ hlo hhi
  unfold quadraticHeightCoveringRadius signedOrbitCoveringRadius
  rw [hsets]

/-- Exact finite-scale bridge to the one-sided covering radius. -/
theorem quadraticHeightCoveringRadius_eq_finite
    (alpha hQ H : ℝ) (B : ℕ)
    (hhQ : 0 < hQ)
    (hlo : hQ * (B : ℝ) ^ 2 ≤ H)
    (hhi : H < hQ * ((B : ℝ) + 1) ^ 2) :
    quadraticHeightCoveringRadius alpha hQ H =
      finiteOrbitCoveringRadius alpha (2 * B + 1) := by
  rw [quadraticHeightCoveringRadius_eq_signed alpha hQ H B hhQ hlo hhi]
  exact signedOrbitCoveringRadius_eq_finite alpha B

/-- The new signed interval example uses B=4739, hence the ODD length 9479.
It does not identify an even-length orbit of size 9480 with a signed orbit. -/
theorem small_signed_interval_certificate
    (alpha : ℝ)
    (hlo : (425071857 : ℝ) / 10000000000 ≤ alpha)
    (hhi : alpha ≤ (425071858 : ℝ) / 10000000000) :
    ((64 / 25 : ℝ) ≤ (9479 : ℝ) * signedOrbitCoveringRadius alpha 4739) ∧
    ((9479 : ℝ) * signedOrbitCoveringRadius alpha 4739 ≤ (177 / 50 : ℝ)) := by
  have hleft : |(425071857 : ℝ) / 10000000000 - 59 / 1388| ≤
      (19 : ℝ) / 1000000000 := by norm_num
  have hright : |(425071858 : ℝ) / 10000000000 - 59 / 1388| ≤
      (19 : ℝ) / 1000000000 := by norm_num
  have happrox : |alpha - (59 : ℝ) / 1388| ≤ (19 : ℝ) / 1000000000 :=
    abs_le.mpr ⟨by linarith [(abs_le.mp hleft).1],
      by linarith [(abs_le.mp hright).2]⟩
  have hcop : IsCoprime (59 : ℤ) 1388 := by
    exact ⟨447, -19, by norm_num⟩
  constructor
  · have hlower := signed_covering_radius_lower_bound alpha
      (19 / 1000000000) 4739 59 1388 (by norm_num) happrox
    have hscaled := mul_le_mul_of_nonneg_left hlower
      (show (0 : ℝ) ≤ 9479 by norm_num)
    exact le_trans (by norm_num) hscaled
  · have hupper := signed_covering_radius_upper_bound alpha
      (19 / 1000000000) 4739 1388 59 (by norm_num) hcop (by norm_num) happrox
    have hscaled := mul_le_mul_of_nonneg_left hupper
      (show (0 : ℝ) ≤ 9479 by norm_num)
    exact le_trans hscaled (by norm_num)

/-- A conditional height-window certificate, uniform in the positive weight hQ.
Here 4739^2=22458121 and 4740^2=22467600. -/
theorem small_quadratic_height_interval_certificate
    (alpha hQ H : ℝ)
    (hhQ : 0 < hQ)
    (halphaLo : (425071857 : ℝ) / 10000000000 ≤ alpha)
    (halphaHi : alpha ≤ (425071858 : ℝ) / 10000000000)
    (hheightLo : hQ * 22458121 ≤ H)
    (hheightHi : H < hQ * 22467600) :
    ((64 / 25 : ℝ) ≤ (9479 : ℝ) * quadraticHeightCoveringRadius alpha hQ H) ∧
    ((9479 : ℝ) * quadraticHeightCoveringRadius alpha hQ H ≤ (177 / 50 : ℝ)) := by
  have hlow : hQ * (4739 : ℝ) ^ 2 ≤ H := by
    convert hheightLo using 1
    norm_num
  have hhigh : H < hQ * ((4739 : ℝ) + 1) ^ 2 := by
    convert hheightHi using 1
    norm_num
  rw [quadraticHeightCoveringRadius_eq_signed alpha hQ H 4739 hhQ hlow hhigh]
  exact small_signed_interval_certificate alpha halphaLo halphaHi

/-- Coverage using an arbitrary height function on integer orbit indices. -/
def HeightBoundOrbitCovers (alpha : ℝ) (height : ℤ → ℝ) (H rho : ℝ) : Prop :=
  ∀ y : ℝ, ∃ k j : ℤ,
    height k ≤ H ∧ |(k : ℝ) * alpha - (j : ℝ) - y| ≤ rho

/-- Height-bounded covering radius for an arbitrary specified index height. -/
noncomputable def heightBoundOrbitCoveringRadius
    (alpha : ℝ) (height : ℤ → ℝ) (H : ℝ) : ℝ :=
  sInf {rho : ℝ | HeightBoundOrbitCovers alpha height H rho}

/-- Transfer requires the quadratic law as an EXPLICIT hypothesis. It is not
proved here for any canonical height on an elliptic curve. -/
theorem heightBoundOrbitCoveringRadius_eq_quadratic
    (alpha hQ H : ℝ) (height : ℤ → ℝ)
    (hlaw : ∀ k : ℤ, height k = hQ * (k : ℝ) ^ 2) :
    heightBoundOrbitCoveringRadius alpha height H =
      quadraticHeightCoveringRadius alpha hQ H := by
  have hsets : {rho : ℝ | HeightBoundOrbitCovers alpha height H rho} =
      {rho : ℝ | QuadraticHeightOrbitCovers alpha hQ H rho} := by
    ext rho
    change (∀ y : ℝ, ∃ k j : ℤ, height k ≤ H ∧
      |(k : ℝ) * alpha - (j : ℝ) - y| ≤ rho) ↔
      (∀ y : ℝ, ∃ k j : ℤ, hQ * (k : ℝ) ^ 2 ≤ H ∧
      |(k : ℝ) * alpha - (j : ℝ) - y| ≤ rho)
    simp only [hlaw]
  unfold heightBoundOrbitCoveringRadius quadraticHeightCoveringRadius
  rw [hsets]

/-- The final bridge makes all height assumptions visible in its type. -/
theorem heightBoundOrbitCoveringRadius_eq_finite
    (alpha hQ H : ℝ) (height : ℤ → ℝ) (B : ℕ)
    (hlaw : ∀ k : ℤ, height k = hQ * (k : ℝ) ^ 2)
    (hhQ : 0 < hQ)
    (hlo : hQ * (B : ℝ) ^ 2 ≤ H)
    (hhi : H < hQ * ((B : ℝ) + 1) ^ 2) :
    heightBoundOrbitCoveringRadius alpha height H =
      finiteOrbitCoveringRadius alpha (2 * B + 1) := by
  rw [heightBoundOrbitCoveringRadius_eq_quadratic alpha hQ H height hlaw]
  exact quadraticHeightCoveringRadius_eq_finite alpha hQ H B hhQ hlo hhi

#print axioms signedOrbitCovers_iff_finiteOrbitCovers
#print axioms signedOrbitCoveringRadius_eq_finite
#print axioms signedOrbitCoveringRadius_nonneg
#print axioms signedOrbitCoveringRadius_antitone
#print axioms signedOrbitCoveringRadius_abs_sub_le
#print axioms signed_covering_radius_lower_bound
#print axioms signed_covering_radius_upper_bound
#print axioms quadratic_height_cutoff_iff
#print axioms quadraticHeightOrbitCovers_iff_signed
#print axioms quadraticHeightCoveringRadius_eq_signed
#print axioms quadraticHeightCoveringRadius_eq_finite
#print axioms small_signed_interval_certificate
#print axioms small_quadratic_height_interval_certificate
#print axioms heightBoundOrbitCoveringRadius_eq_quadratic
#print axioms heightBoundOrbitCoveringRadius_eq_finite

end AbelianLog

/-!
# V7 extension: finite-index transfer with the necessary height rescaling

For a nonempty circle phase set S, its radius is defined by an infimum,
not by an assumed largest-gap formula. If multiplication by d sends S
into T modulo integers, then R(T) <= d * R(S).

For height-bounded families, cyclic inclusion and an explicit multiplication
hypothesis give eta_cyclic(d^2 H)/d <= eta_ambient(H) <= eta_cyclic(H).
No rank, saturation, elliptic logarithm, or canonical-height assertion is
introduced as an axiom. The final concrete family is an abstract circle
model, not an identification with the rational points of a specific curve.
-/

namespace AbelianLog

/-- A set of real phase representatives covers the unit circle at radius rho.
There is no restriction to [0,1); integer translates are handled explicitly. -/
def CircleSetCovers (S : Set ℝ) (rho : ℝ) : Prop :=
  ∀ y : ℝ, ∃ x ∈ S, ∃ j : ℤ, |x - (j : ℝ) - y| ≤ rho

/-- Only nonempty phase sets are assigned a geometric interpretation. -/
noncomputable def circleSetCoveringRadius (S : Set ℝ) : ℝ :=
  sInf {rho : ℝ | CircleSetCovers S rho}

/-- Every nonempty phase set has the coarse covering bound 1. -/
theorem circleSetCovers_one
    (S : Set ℝ) (hS : S.Nonempty) : CircleSetCovers S 1 := by
  obtain ⟨x, hx⟩ := hS
  intro y
  have hlo : (Int.floor (x - y) : ℝ) ≤ x - y := Int.floor_le (x - y)
  have hhi : x - y < (Int.floor (x - y) : ℝ) + 1 :=
    Int.floor_le_iff.mp (le_refl (Int.floor (x - y)))
  refine ⟨x, hx, Int.floor (x - y), ?_⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Any admissible circle covering radius is nonnegative. -/
theorem circleSetCovers_nonneg
    (S : Set ℝ) (rho : ℝ) (hcover : CircleSetCovers S rho) :
    0 ≤ rho := by
  obtain ⟨x, _hx, j, hdist⟩ := hcover 0
  exact le_trans (abs_nonneg _) hdist

/-- Nonnegativity of the infimum for a nonempty phase set. -/
theorem circleSetCoveringRadius_nonneg
    (S : Set ℝ) (hS : S.Nonempty) : 0 ≤ circleSetCoveringRadius S := by
  unfold circleSetCoveringRadius
  refine le_csInf ⟨1, circleSetCovers_one S hS⟩ ?_
  intro rho hcover
  exact circleSetCovers_nonneg S rho hcover

/-- A covering radius bounds the infimum from above. -/
theorem circleSetCoveringRadius_le_of_covers
    (S : Set ℝ) (rho : ℝ) (hcover : CircleSetCovers S rho) :
    circleSetCoveringRadius S ≤ rho := by
  unfold circleSetCoveringRadius
  have hb : BddBelow {r : ℝ | CircleSetCovers S r} := by
    refine ⟨0, ?_⟩
    intro r hr
    exact circleSetCovers_nonneg S r hr
  exact csInf_le hb hcover

/-- Multiplication by d is surjective on the target circle and multiplies
this error bound by d. The phase map is required only modulo integers. -/
theorem circleSetCovers_integer_transfer
    (S T : Set ℝ) (d : ℕ) (rho : ℝ) (hd : 0 < d)
    (hmap : ∀ x ∈ S, ∃ z ∈ T, ∃ ell : ℤ,
      z = (d : ℝ) * x + (ell : ℝ))
    (hcover : CircleSetCovers S rho) :
    CircleSetCovers T ((d : ℝ) * rho) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdR
  intro y
  obtain ⟨x, hx, j, hnear⟩ := hcover (y / (d : ℝ))
  obtain ⟨z, hz, ell, hzEq⟩ := hmap x hx
  refine ⟨z, hz, (d : ℤ) * j + ell, ?_⟩
  have hident : z - (((d : ℤ) * j + ell : ℤ) : ℝ) - y =
      (d : ℝ) * (x - (j : ℝ) - y / (d : ℝ)) := by
    rw [hzEq]
    push_cast
    field_simp [hd0]
    ring
  rw [hident, abs_mul, abs_of_pos hdR]
  exact mul_le_mul_of_nonneg_left hnear (le_of_lt hdR)

/-- Infimum version of integer transfer, without an attainment assumption. -/
theorem circleSetCoveringRadius_integer_transfer
    (S T : Set ℝ) (d : ℕ) (hd : 0 < d) (hS : S.Nonempty)
    (hmap : ∀ x ∈ S, ∃ z ∈ T, ∃ ell : ℤ,
      z = (d : ℝ) * x + (ell : ℝ)) :
    circleSetCoveringRadius T ≤ (d : ℝ) * circleSetCoveringRadius S := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdiv : circleSetCoveringRadius T / (d : ℝ) ≤
      circleSetCoveringRadius S := by
    change circleSetCoveringRadius T / (d : ℝ) ≤
      sInf {rho : ℝ | CircleSetCovers S rho}
    refine le_csInf ⟨1, circleSetCovers_one S hS⟩ ?_
    intro rho hcover
    have hbound := circleSetCoveringRadius_le_of_covers T ((d : ℝ) * rho)
      (circleSetCovers_integer_transfer S T d rho hd hmap hcover)
    apply (div_le_iff₀ hdR).mpr
    calc
      circleSetCoveringRadius T ≤ (d : ℝ) * rho := hbound
      _ = rho * (d : ℝ) := mul_comm _ _
  calc
    circleSetCoveringRadius T ≤ circleSetCoveringRadius S * (d : ℝ) :=
      (div_le_iff₀ hdR).mp hdiv
    _ = (d : ℝ) * circleSetCoveringRadius S := mul_comm _ _

/-- Adding phase points can only decrease the radius. Inclusion is modulo
integers, so the theorem is independent of chosen phase representatives. -/
theorem circleSetCoveringRadius_modular_antitone
    (S T : Set ℝ) (hS : S.Nonempty)
    (hinclude : ∀ x ∈ S, ∃ z ∈ T, ∃ ell : ℤ, z = x + (ell : ℝ)) :
    circleSetCoveringRadius T ≤ circleSetCoveringRadius S := by
  have hmap : ∀ x ∈ S, ∃ z ∈ T, ∃ ell : ℤ,
      z = (1 : ℝ) * x + (ell : ℝ) := by
    intro x hx
    simpa only [one_mul] using hinclude x hx
  simpa using circleSetCoveringRadius_integer_transfer S T 1
    (by norm_num) hS (by simpa only [Nat.cast_one] using hmap)

/-- The actual set of real phases admitted by the quadratic cutoff. -/
def quadraticOrbitPhases (alpha hQ H : ℝ) : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H ∧ x = (k : ℝ) * alpha}

/-- The zero index is available at any nonnegative height budget. -/
theorem quadraticOrbitPhases_nonempty
    (alpha hQ H : ℝ) (hH : 0 ≤ H) :
    (quadraticOrbitPhases alpha hQ H).Nonempty := by
  refine ⟨0, ?_⟩
  change ∃ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H ∧ (0 : ℝ) = (k : ℝ) * alpha
  exact ⟨0, by simpa using hH, by norm_num⟩

/-- The set-based and previously defined index-based predicates agree. -/
theorem circleSetCovers_quadraticOrbitPhases_iff
    (alpha hQ H rho : ℝ) :
    CircleSetCovers (quadraticOrbitPhases alpha hQ H) rho ↔
      QuadraticHeightOrbitCovers alpha hQ H rho := by
  constructor
  · intro h y
    obtain ⟨x, ⟨k, hk, hx⟩, j, hdist⟩ := h y
    refine ⟨k, j, hk, ?_⟩
    simpa only [hx] using hdist
  · intro h y
    obtain ⟨k, j, hk, hdist⟩ := h y
    exact ⟨(k : ℝ) * alpha, ⟨k, hk, rfl⟩, j, hdist⟩

/-- Exact compatibility with the v6 quadratic-height covering radius. -/
theorem circleSetCoveringRadius_quadraticOrbitPhases
    (alpha hQ H : ℝ) :
    circleSetCoveringRadius (quadraticOrbitPhases alpha hQ H) =
      quadraticHeightCoveringRadius alpha hQ H := by
  have hsets : {rho : ℝ | CircleSetCovers (quadraticOrbitPhases alpha hQ H) rho} =
      {rho : ℝ | QuadraticHeightOrbitCovers alpha hQ H rho} := by
    ext rho
    exact circleSetCovers_quadraticOrbitPhases_iff alpha hQ H rho
  unfold circleSetCoveringRadius quadraticHeightCoveringRadius
  rw [hsets]

/-- Finite-index-style comparison at a fixed height budget.

hinclude expresses cyclic inclusion at height H, modulo integers.
hmultiply expresses that multiplication by d sends every admitted ambient
point to a cyclic point of height at most d^2*H, again modulo integers.
These are hypotheses, not an assertion of rank or finite index for a curve.
No finiteness, density, or positivity of hQ is needed for this comparison;
positive hQ is needed to interpret the cyclic cutoff as a finite set.
-/
theorem finite_index_height_covering_sandwich
    (alpha hQ H : ℝ) (d : ℕ) (ambient : ℝ → Set ℝ)
    (hd : 0 < d) (hH : 0 ≤ H)
    (hinclude : ∀ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H →
      ∃ x ∈ ambient H, ∃ j : ℤ, x = (k : ℝ) * alpha + (j : ℝ))
    (hmultiply : ∀ x ∈ ambient H, ∃ k j : ℤ,
      hQ * (k : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * H ∧
      (k : ℝ) * alpha = (d : ℝ) * x + (j : ℝ)) :
    (quadraticHeightCoveringRadius alpha hQ ((d : ℝ) ^ 2 * H) / (d : ℝ) ≤
      circleSetCoveringRadius (ambient H)) ∧
    (circleSetCoveringRadius (ambient H) ≤ quadraticHeightCoveringRadius alpha hQ H) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hambient : (ambient H).Nonempty := by
    obtain ⟨x, hx, _j, _heq⟩ := hinclude 0 (by simpa using hH)
    exact ⟨x, hx⟩
  constructor
  · have hmap : ∀ x ∈ ambient H,
        ∃ z ∈ quadraticOrbitPhases alpha hQ ((d : ℝ) ^ 2 * H),
        ∃ j : ℤ, z = (d : ℝ) * x + (j : ℝ) := by
      intro x hx
      obtain ⟨k, j, hk, heq⟩ := hmultiply x hx
      exact ⟨(k : ℝ) * alpha, ⟨k, hk, rfl⟩, j, heq⟩
    have hbound := circleSetCoveringRadius_integer_transfer (ambient H)
      (quadraticOrbitPhases alpha hQ ((d : ℝ) ^ 2 * H)) d hd hambient hmap
    rw [circleSetCoveringRadius_quadraticOrbitPhases] at hbound
    apply (div_le_iff₀ hdR).mpr
    calc
      quadraticHeightCoveringRadius alpha hQ ((d : ℝ) ^ 2 * H) ≤
          (d : ℝ) * circleSetCoveringRadius (ambient H) := hbound
      _ = circleSetCoveringRadius (ambient H) * (d : ℝ) := mul_comm _ _
  · have hmap : ∀ x ∈ quadraticOrbitPhases alpha hQ H,
        ∃ z ∈ ambient H, ∃ j : ℤ, z = x + (j : ℝ) := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := hx
      exact hinclude k hk
    have hbound := circleSetCoveringRadius_modular_antitone
      (quadraticOrbitPhases alpha hQ H) (ambient H)
      (quadraticOrbitPhases_nonempty alpha hQ H hH) hmap
    simpa only [circleSetCoveringRadius_quadraticOrbitPhases] using hbound

/-- Abstract rank-one-plus-torsion phase model. The offset j/t is taken for
all integers j; modulo 1 this gives exactly t offsets when t>0. This definition
is NOT an identification with an actual elliptic curve's rational points. -/
def torsionExtendedPhases (beta h0 H : ℝ) (t : ℕ) : Set ℝ :=
  {x : ℝ | ∃ n j : ℤ, h0 * (n : ℝ) ^ 2 ≤ H ∧
    x = (n : ℝ) * beta + (j : ℝ) / (t : ℝ)}

/-- In the explicit circle model, alpha=m*beta and hQ=m^2*h0.
Multiplication by d=m*t kills all torsion offsets and lands in the cyclic
subgroup. This proves the two required hypotheses rather than assuming them.
For the intended finite-height interpretation take h0>0; the inequalities
also hold without that additional restriction. d need not be minimal. -/
theorem torsion_extension_height_covering_sandwich
    (beta h0 H : ℝ) (m t : ℕ) (hm : 0 < m) (ht : 0 < t) (hH : 0 ≤ H) :
    (quadraticHeightCoveringRadius ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0)
        (((m * t : ℕ) : ℝ) ^ 2 * H) / ((m * t : ℕ) : ℝ) ≤
      circleSetCoveringRadius (torsionExtendedPhases beta h0 H t)) ∧
    (circleSetCoveringRadius (torsionExtendedPhases beta h0 H t) ≤
      quadraticHeightCoveringRadius ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0) H) := by
  refine finite_index_height_covering_sandwich
    ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0) H (m * t)
    (fun K => torsionExtendedPhases beta h0 K t)
    (Nat.mul_pos hm ht) hH ?_ ?_
  · intro k hk
    refine ⟨((((m : ℤ) * k : ℤ) : ℝ) * beta), ?_, 0, ?_⟩
    · change ∃ n j : ℤ, h0 * (n : ℝ) ^ 2 ≤ H ∧
        (((m : ℤ) * k : ℤ) : ℝ) * beta =
          (n : ℝ) * beta + (j : ℝ) / (t : ℝ)
      refine ⟨(m : ℤ) * k, 0, ?_, ?_⟩
      · calc
          h0 * ((((m : ℤ) * k : ℤ) : ℝ)) ^ 2 =
              (m : ℝ) ^ 2 * h0 * (k : ℝ) ^ 2 := by push_cast; ring
          _ ≤ H := hk
      · simp
    · push_cast
      ring
  · intro x hx
    obtain ⟨n, j, hn, hxEq⟩ := hx
    refine ⟨(t : ℤ) * n, -((m : ℤ) * j), ?_, ?_⟩
    · have hscaled := mul_le_mul_of_nonneg_left hn
        (sq_nonneg (((m * t : ℕ) : ℝ)))
      calc
        (m : ℝ) ^ 2 * h0 * ((((t : ℤ) * n : ℤ) : ℝ)) ^ 2 =
            (((m * t : ℕ) : ℝ)) ^ 2 * (h0 * (n : ℝ) ^ 2) := by
          push_cast
          ring
        _ ≤ (((m * t : ℕ) : ℝ)) ^ 2 * H := hscaled
    · have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
      have ht0 : (t : ℝ) ≠ 0 := ne_of_gt htR
      rw [hxEq]
      push_cast
      field_simp [ht0]
      ring

/-- Transfer of the v6 small lower certificate. Its height window must be
checked at d^2*H, not at H. The conclusion retains the necessary factor d.
Analytic interval membership and the ambient arithmetic model stay explicit. -/
theorem small_finite_index_lower_certificate
    (alpha hQ H : ℝ) (d : ℕ) (ambient : ℝ → Set ℝ)
    (hd : 0 < d) (hhQ : 0 < hQ) (hH : 0 ≤ H)
    (halphaLo : (425071857 : ℝ) / 10000000000 ≤ alpha)
    (halphaHi : alpha ≤ (425071858 : ℝ) / 10000000000)
    (hheightLo : hQ * 22458121 ≤ (d : ℝ) ^ 2 * H)
    (hheightHi : (d : ℝ) ^ 2 * H < hQ * 22467600)
    (hinclude : ∀ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H →
      ∃ x ∈ ambient H, ∃ j : ℤ, x = (k : ℝ) * alpha + (j : ℝ))
    (hmultiply : ∀ x ∈ ambient H, ∃ k j : ℤ,
      hQ * (k : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * H ∧
      (k : ℝ) * alpha = (d : ℝ) * x + (j : ℝ)) :
    (64 / 25 : ℝ) ≤ ((9479 : ℝ) * (d : ℝ)) *
      circleSetCoveringRadius (ambient H) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcyclic := (small_quadratic_height_interval_certificate alpha hQ
    ((d : ℝ) ^ 2 * H) hhQ halphaLo halphaHi hheightLo hheightHi).1
  have hsandwich := (finite_index_height_covering_sandwich alpha hQ H d
    ambient hd hH hinclude hmultiply).1
  have hscaled := (div_le_iff₀ hdR).mp hsandwich
  calc
    (64 / 25 : ℝ) ≤ (9479 : ℝ) *
        quadraticHeightCoveringRadius alpha hQ ((d : ℝ) ^ 2 * H) := hcyclic
    _ ≤ (9479 : ℝ) * (circleSetCoveringRadius (ambient H) * (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hscaled (by norm_num)
    _ = ((9479 : ℝ) * (d : ℝ)) * circleSetCoveringRadius (ambient H) := by ring

#print axioms circleSetCovers_one
#print axioms circleSetCovers_nonneg
#print axioms circleSetCoveringRadius_nonneg
#print axioms circleSetCoveringRadius_le_of_covers
#print axioms circleSetCovers_integer_transfer
#print axioms circleSetCoveringRadius_integer_transfer
#print axioms circleSetCoveringRadius_modular_antitone
#print axioms quadraticOrbitPhases_nonempty
#print axioms circleSetCovers_quadraticOrbitPhases_iff
#print axioms circleSetCoveringRadius_quadraticOrbitPhases
#print axioms finite_index_height_covering_sandwich
#print axioms torsion_extension_height_covering_sandwich
#print axioms small_finite_index_lower_certificate

end AbelianLog

/-!
# V8 extension: eventual power bounds under fixed height rescaling

For real functions c and a, positive K and D, suppose for every H > 0 that
  c (K * H) / D <= a H <= c H.
Then c and a have exactly the same eventual upper power bounds, INCLUDING
whether a bound holds at any specified endpoint exponent s.

These are one-sided inequalities for arbitrary real functions, not a
redefinition of Mathlib's absolute-value Big O. For nonnegative radii they
have the usual upper-bound interpretation.

The epsilon property below has coefficient ONE. The equivalence with
bounds having an arbitrary positive constant is proved using half of the
epsilon allowance to absorb that constant.

No liminf/limsup identity, continued-fraction theorem, arithmetic enclosure,
rank/saturation result, or particular decay rate is assumed or proved here.
-/

namespace AbelianLog

/-- A fixed exponent upper bound, valid at EVERY sufficiently large real
height. The constant and starting height are strictly positive. -/
def EventualPowerUpperBound (f : ℝ → ℝ) (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ H0 : ℝ, 0 < H0 ∧
    ∀ H : ℝ, H0 ≤ H → f H ≤ C * H ^ (-s)

/-- A coefficient-one upper bound with an arbitrary positive exponent loss.
For target b, the right side is H^(-b + epsilon). -/
def EpsilonPowerDecay (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ H0 : ℝ, 0 < H0 ∧ ∀ H : ℝ, H0 ≤ H →
      f H ≤ H ^ (-(b - epsilon))

/-- Exact bookkeeping for the reverse transfer. If f(K*H) <= D*g(H)
and g(H) <= C*H^(-s) beyond H0, the transferred constant is
D*C/K^(-s), and the new starting height is K*H0. -/
theorem scaled_transfer_power_bound
    (f g : ℝ → ℝ) (K D C H0 s : ℝ)
    (hK : 0 < K) (hD : 0 ≤ D) (hH0 : 0 < H0)
    (htransfer : ∀ H : ℝ, 0 < H → f (K * H) ≤ D * g H)
    (hbound : ∀ H : ℝ, H0 ≤ H → g H ≤ C * H ^ (-s)) :
    ∀ H : ℝ, K * H0 ≤ H →
      f H ≤ (D * C / K ^ (-s)) * H ^ (-s) := by
  intro H hH
  have hHpos : 0 < H := lt_of_lt_of_le (mul_pos hK hH0) hH
  have hquot : H0 ≤ H / K := by
    apply (le_div_iff₀ hK).mpr
    simpa only [mul_comm] using hH
  have hquotpos : 0 < H / K := div_pos hHpos hK
  have hident : K * (H / K) = H := by
    calc
      K * (H / K) = (K / K) * H := by ring
      _ = H := by rw [div_self (ne_of_gt hK), one_mul]
  calc
    f H = f (K * (H / K)) := congrArg f hident.symm
    _ ≤ D * g (H / K) := htransfer (H / K) hquotpos
    _ ≤ D * (C * (H / K) ^ (-s)) :=
      mul_le_mul_of_nonneg_left (hbound (H / K) hquot) hD
    _ = (D * C / K ^ (-s)) * H ^ (-s) := by
      rw [Real.div_rpow (le_of_lt hHpos) (le_of_lt hK) (-s)]
      ring

/-- Pointwise upper comparison on positive heights preserves an eventual
power upper bound. No positivity of the two functions is required. -/
theorem eventualPowerUpperBound_mono
    (f g : ℝ → ℝ) (s : ℝ)
    (hle : ∀ H : ℝ, 0 < H → f H ≤ g H)
    (hg : EventualPowerUpperBound g s) :
    EventualPowerUpperBound f s := by
  obtain ⟨C, hC, H0, hH0, hbound⟩ := hg
  refine ⟨C, hC, H0, hH0, ?_⟩
  intro H hH
  exact le_trans (hle H (lt_of_lt_of_le hH0 hH)) (hbound H hH)

/-- A fixed positive height dilation and positive multiplicative loss
preserve every eventual upper power exponent. -/
theorem eventualPowerUpperBound_of_scaled_transfer
    (f g : ℝ → ℝ) (K D s : ℝ) (hK : 0 < K) (hD : 0 < D)
    (htransfer : ∀ H : ℝ, 0 < H → f (K * H) ≤ D * g H)
    (hg : EventualPowerUpperBound g s) :
    EventualPowerUpperBound f s := by
  obtain ⟨C, hC, H0, hH0, hbound⟩ := hg
  refine ⟨D * C / K ^ (-s),
    div_pos (mul_pos hD hC) (Real.rpow_pos_of_pos hK (-s)),
    K * H0, mul_pos hK hH0, ?_⟩
  exact scaled_transfer_power_bound f g K D C H0 s hK (le_of_lt hD)
    hH0 htransfer hbound

/-- The abstract sandwich preserves a bound at each specified real exponent.
In particular this statement does not merely compare suprema of exponents. -/
theorem eventualPowerUpperBound_iff_of_sandwich
    (c a : ℝ → ℝ) (K D s : ℝ) (hK : 0 < K) (hD : 0 < D)
    (hsandwich : ∀ H : ℝ, 0 < H →
      c (K * H) / D ≤ a H ∧ a H ≤ c H) :
    EventualPowerUpperBound c s ↔ EventualPowerUpperBound a s := by
  constructor
  · intro hc
    exact eventualPowerUpperBound_mono a c s
      (fun H hH => (hsandwich H hH).2) hc
  · intro ha
    apply eventualPowerUpperBound_of_scaled_transfer c a K D s hK hD ?_ ha
    intro H hH
    have h := (div_le_iff₀ hD).mp (hsandwich H hH).1
    simpa only [mul_comm] using h

/-- Absorb a positive constant into any positive loss in exponent.
The explicit new cutoff is max H0 (C^(1/epsilon)), written with inverse.
No assumption s>0 is needed. -/
theorem power_upper_bound_absorb_constant
    (f : ℝ → ℝ) (C H0 s epsilon : ℝ)
    (hC : 0 < C) (hH0 : 0 < H0) (hepsilon : 0 < epsilon)
    (hbound : ∀ H : ℝ, H0 ≤ H → f H ≤ C * H ^ (-s)) :
    ∀ H : ℝ, max H0 (C ^ epsilon⁻¹) ≤ H →
      f H ≤ H ^ (-(s - epsilon)) := by
  intro H hH
  have hbase : H0 ≤ H := le_trans (le_max_left _ _) hH
  have hHpos : 0 < H := lt_of_lt_of_le hH0 hbase
  have hroot : C ^ epsilon⁻¹ ≤ H := le_trans (le_max_right _ _) hH
  have hcancel : (C ^ epsilon⁻¹) ^ epsilon = C :=
    Real.rpow_inv_rpow (le_of_lt hC) (ne_of_gt hepsilon)
  have hconstant : C ≤ H ^ epsilon := by
    calc
      C = (C ^ epsilon⁻¹) ^ epsilon := hcancel.symm
      _ ≤ H ^ epsilon := Real.rpow_le_rpow
        (le_of_lt (Real.rpow_pos_of_pos hC epsilon⁻¹)) hroot (le_of_lt hepsilon)
  calc
    f H ≤ C * H ^ (-s) := hbound H hbase
    _ ≤ H ^ epsilon * H ^ (-s) := mul_le_mul_of_nonneg_right hconstant
      (le_of_lt (Real.rpow_pos_of_pos hHpos (-s)))
    _ = H ^ (epsilon + (-s)) := (Real.rpow_add hHpos epsilon (-s)).symm
    _ = H ^ (-(s - epsilon)) := by congr 1; ring

/-- The coefficient-one epsilon statement is equivalent to allowing an
arbitrary positive constant separately for each epsilon. The reverse proof
uses epsilon/2 twice, so it does not assume a uniform constant in epsilon. -/
theorem epsilonPowerDecay_iff_eventualPowerUpperBounds
    (f : ℝ → ℝ) (b : ℝ) :
    EpsilonPowerDecay f b ↔
      ∀ epsilon : ℝ, 0 < epsilon → EventualPowerUpperBound f (b - epsilon) := by
  constructor
  · intro hf epsilon hepsilon
    obtain ⟨H0, hH0, hbound⟩ := hf epsilon hepsilon
    refine ⟨1, by norm_num, H0, hH0, ?_⟩
    intro H hH
    simpa only [one_mul] using hbound H hH
  · intro hf epsilon hepsilon
    have hhalf : 0 < epsilon / 2 := by linarith
    obtain ⟨C, hC, H0, hH0, hbound⟩ := hf (epsilon / 2) hhalf
    refine ⟨max H0 (C ^ (epsilon / 2)⁻¹),
      lt_of_lt_of_le hH0 (le_max_left _ _), ?_⟩
    intro H hH
    have h := power_upper_bound_absorb_constant f C H0
      (b - epsilon / 2) (epsilon / 2) hC hH0 hhalf hbound H hH
    have hexponent : (b - epsilon / 2) - epsilon / 2 = b - epsilon := by ring
    simpa only [hexponent] using h

/-- The same sandwich preserves the coefficient-one epsilon property. -/
theorem epsilonPowerDecay_iff_of_sandwich
    (c a : ℝ → ℝ) (K D b : ℝ) (hK : 0 < K) (hD : 0 < D)
    (hsandwich : ∀ H : ℝ, 0 < H →
      c (K * H) / D ≤ a H ∧ a H ≤ c H) :
    EpsilonPowerDecay c b ↔ EpsilonPowerDecay a b := by
  rw [epsilonPowerDecay_iff_eventualPowerUpperBounds,
    epsilonPowerDecay_iff_eventualPowerUpperBounds]
  constructor
  · intro hc epsilon hepsilon
    exact (eventualPowerUpperBound_iff_of_sandwich c a K D
      (b - epsilon) hK hD hsandwich).mp (hc epsilon hepsilon)
  · intro ha epsilon hepsilon
    exact (eventualPowerUpperBound_iff_of_sandwich c a K D
      (b - epsilon) hK hD hsandwich).mpr (ha epsilon hepsilon)

/-- Equality of the full sets of admissible upper power exponents.
This is a set equality, not a liminf/limsup theorem. -/
theorem scaled_sandwich_power_spectrum_eq
    (c a : ℝ → ℝ) (K D : ℝ) (hK : 0 < K) (hD : 0 < D)
    (hsandwich : ∀ H : ℝ, 0 < H →
      c (K * H) / D ≤ a H ∧ a H ≤ c H) :
    {s : ℝ | EventualPowerUpperBound c s} =
      {s : ℝ | EventualPowerUpperBound a s} := by
  ext s
  exact eventualPowerUpperBound_iff_of_sandwich c a K D s hK hD hsandwich

/-- Apply the abstract result to the v7.2 finite-index sandwich.
IMPORTANT: the SAME integer d works at EVERY nonnegative height. The two
arithmetic transfer hypotheses are not conclusions about a specific curve. -/
theorem finite_index_eventualPowerUpperBound_iff
    (alpha hQ s : ℝ) (d : ℕ) (ambient : ℝ → Set ℝ) (hd : 0 < d)
    (hinclude : ∀ H : ℝ, 0 ≤ H → ∀ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H →
      ∃ x ∈ ambient H, ∃ j : ℤ, x = (k : ℝ) * alpha + (j : ℝ))
    (hmultiply : ∀ H : ℝ, 0 ≤ H → ∀ x ∈ ambient H, ∃ k j : ℤ,
      hQ * (k : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * H ∧
      (k : ℝ) * alpha = (d : ℝ) * x + (j : ℝ)) :
    EventualPowerUpperBound (fun H => quadraticHeightCoveringRadius alpha hQ H) s ↔
      EventualPowerUpperBound (fun H => circleSetCoveringRadius (ambient H)) s := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  apply eventualPowerUpperBound_iff_of_sandwich
    (fun H => quadraticHeightCoveringRadius alpha hQ H)
    (fun H => circleSetCoveringRadius (ambient H))
    ((d : ℝ) ^ 2) (d : ℝ) s (sq_pos_of_pos hdR) hdR
  intro H hH
  exact finite_index_height_covering_sandwich alpha hQ H d ambient hd
    (le_of_lt hH) (hinclude H (le_of_lt hH)) (hmultiply H (le_of_lt hH))

/-- The finite-index comparison preserves the coefficient-one epsilon
covering property at any target exponent b. It does not prove that property
for either family without an additional input. -/
theorem finite_index_epsilonPowerDecay_iff
    (alpha hQ b : ℝ) (d : ℕ) (ambient : ℝ → Set ℝ) (hd : 0 < d)
    (hinclude : ∀ H : ℝ, 0 ≤ H → ∀ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H →
      ∃ x ∈ ambient H, ∃ j : ℤ, x = (k : ℝ) * alpha + (j : ℝ))
    (hmultiply : ∀ H : ℝ, 0 ≤ H → ∀ x ∈ ambient H, ∃ k j : ℤ,
      hQ * (k : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * H ∧
      (k : ℝ) * alpha = (d : ℝ) * x + (j : ℝ)) :
    EpsilonPowerDecay (fun H => quadraticHeightCoveringRadius alpha hQ H) b ↔
      EpsilonPowerDecay (fun H => circleSetCoveringRadius (ambient H)) b := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  apply epsilonPowerDecay_iff_of_sandwich
    (fun H => quadraticHeightCoveringRadius alpha hQ H)
    (fun H => circleSetCoveringRadius (ambient H))
    ((d : ℝ) ^ 2) (d : ℝ) b (sq_pos_of_pos hdR) hdR
  intro H hH
  exact finite_index_height_covering_sandwich alpha hQ H d ambient hd
    (le_of_lt hH) (hinclude H (le_of_lt hH)) (hmultiply H (le_of_lt hH))

/-- The explicit rank-one-plus-torsion circle model has exactly the same
upper power bounds as its m-fold cyclic subgroup. The model-to-curve
identification remains outside this statement. -/
theorem torsion_extension_eventualPowerUpperBound_iff
    (beta h0 s : ℝ) (m t : ℕ) (hm : 0 < m) (ht : 0 < t) :
    EventualPowerUpperBound
        (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta)
          ((m : ℝ) ^ 2 * h0) H) s ↔
      EventualPowerUpperBound
        (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t)) s := by
  have hdR : (0 : ℝ) < ((m * t : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hm ht
  apply eventualPowerUpperBound_iff_of_sandwich
    (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0) H)
    (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t))
    ((((m * t : ℕ) : ℝ)) ^ 2) ((m * t : ℕ) : ℝ) s (sq_pos_of_pos hdR) hdR
  intro H hH
  exact torsion_extension_height_covering_sandwich beta h0 H m t hm ht (le_of_lt hH)

/-- Coefficient-one epsilon equivalence for the explicit torsion model.
For the intended finite-height interpretation, use h0>0. No positivity of
h0 is needed for the abstract comparison inherited from v7.2. -/
theorem torsion_extension_epsilonPowerDecay_iff
    (beta h0 b : ℝ) (m t : ℕ) (hm : 0 < m) (ht : 0 < t) :
    EpsilonPowerDecay
        (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta)
          ((m : ℝ) ^ 2 * h0) H) b ↔
      EpsilonPowerDecay
        (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t)) b := by
  have hdR : (0 : ℝ) < ((m * t : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hm ht
  apply epsilonPowerDecay_iff_of_sandwich
    (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0) H)
    (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t))
    ((((m * t : ℕ) : ℝ)) ^ 2) ((m * t : ℕ) : ℝ) b (sq_pos_of_pos hdR) hdR
  intro H hH
  exact torsion_extension_height_covering_sandwich beta h0 H m t hm ht (le_of_lt hH)

#print axioms scaled_transfer_power_bound
#print axioms eventualPowerUpperBound_mono
#print axioms eventualPowerUpperBound_of_scaled_transfer
#print axioms eventualPowerUpperBound_iff_of_sandwich
#print axioms power_upper_bound_absorb_constant
#print axioms epsilonPowerDecay_iff_eventualPowerUpperBounds
#print axioms epsilonPowerDecay_iff_of_sandwich
#print axioms scaled_sandwich_power_spectrum_eq
#print axioms finite_index_eventualPowerUpperBound_iff
#print axioms finite_index_epsilonPowerDecay_iff
#print axioms torsion_extension_eventualPowerUpperBound_iff
#print axioms torsion_extension_epsilonPowerDecay_iff

end AbelianLog

/-!
# V9 extension: logarithmic bounds and exact envelopes

A fixed scaled sandwich c(K*H)/D <= a(H) <= c(H), with K,D>0,
preserves every eventual upper bound C*H^(-b)*(log H)^ell, for arbitrary
real b and ell. The logarithmic exponent is preserved exactly, not just
up to an epsilon loss. Coefficient-one epsilon bounds are also preserved.

An exact envelope is expressed by eventual upper bounds above ell and
failure of every constant upper bound below ell. This is NOT a formal
identification with Mathlib's limsup. The continued-fraction dictionary
and the arithmetic value of the envelope remain outside this extension.

All functions here may be real-valued; the statements are upper inequalities,
not absolute-value Big O. For the intended application they are radii.
-/

namespace AbelianLog

/-- A logarithmically corrected upper bound at EVERY sufficiently large
real height. The cutoff exceeds 1, so every logarithmic base is positive. -/
def EventualLogPowerUpperBound (f : ℝ → ℝ) (b ell : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ H0 : ℝ, 1 < H0 ∧
    ∀ H : ℝ, H0 ≤ H →
      f H ≤ C * H ^ (-b) * (Real.log H) ^ ell

/-- Coefficient-one epsilon allowance in the LOGARITHMIC exponent only.
The height exponent -b is unchanged. -/
def EpsilonLogPowerBound (f : ℝ → ℝ) (b ell : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ H0 : ℝ, 1 < H0 ∧ ∀ H : ℝ, H0 ≤ H →
      f H ≤ H ^ (-b) * (Real.log H) ^ (ell + epsilon)

/-- A finite exact logarithmic envelope, specified without a limsup:
upper bounds with every positive logarithmic loss, and failure of every
constant upper bound with every positive logarithmic improvement.
No two-sided estimate at every height is asserted. -/
def ExactLogPowerEnvelope (f : ℝ → ℝ) (b ell : ℝ) : Prop :=
  EpsilonLogPowerBound f b ell ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      ¬ EventualLogPowerUpperBound f b (ell - epsilon)

/-- At logarithmic exponent zero, the new bound agrees with the validated
v8 power-bound definition. Raising the old cutoff above 1 is harmless. -/
theorem eventualLogPowerUpperBound_zero_iff (f : ℝ → ℝ) (b : ℝ) :
    EventualLogPowerUpperBound f b 0 ↔ EventualPowerUpperBound f b := by
  constructor
  · rintro ⟨C, hC, H0, hH0, hbound⟩
    refine ⟨C, hC, H0, lt_trans (by norm_num : (0 : ℝ) < 1) hH0, ?_⟩
    intro H hH
    simpa only [Real.rpow_zero, mul_one] using hbound H hH
  · rintro ⟨C, hC, H0, _hH0, hbound⟩
    refine ⟨C, hC, max H0 2,
      lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
    intro H hH
    simpa only [Real.rpow_zero, mul_one] using
      hbound H (le_trans (le_max_left _ _) hH)

/-- Explicit control of a logarithm under any positive fixed dilation.
At H >= exp(2*|log K|+1), log(H/K) is between (log H)/2 and 2*log H.
The factor 2^|ell| is valid for positive, zero, AND negative ell. -/
theorem log_div_rpow_le
    (K H ell : ℝ) (hK : 0 < K)
    (hH : Real.exp (2 * |Real.log K| + 1) ≤ H) :
    (Real.log (H / K)) ^ ell ≤ (2 : ℝ) ^ |ell| * (Real.log H) ^ ell := by
  have hHpos : 0 < H := lt_of_lt_of_le (Real.exp_pos _) hH
  have hlogH : 2 * |Real.log K| + 1 ≤ Real.log H := by
    have h := Real.log_le_log (Real.exp_pos (2 * |Real.log K| + 1)) hH
    simpa only [Real.log_exp] using h
  have hlogpos : 0 < Real.log H := by
    linarith [abs_nonneg (Real.log K)]
  have hdiv : Real.log (H / K) = Real.log H - Real.log K :=
    Real.log_div (ne_of_gt hHpos) (ne_of_gt hK)
  have hlower : Real.log H / 2 ≤ Real.log (H / K) := by
    rw [hdiv]
    linarith [le_abs_self (Real.log K)]
  have hupper : Real.log (H / K) ≤ 2 * Real.log H := by
    rw [hdiv]
    linarith [neg_le_abs (Real.log K)]
  have hlogdivpos : 0 < Real.log (H / K) :=
    lt_of_lt_of_le (div_pos hlogpos (by norm_num)) hlower
  rcases le_total 0 ell with hell | hell
  · calc
      (Real.log (H / K)) ^ ell ≤ (2 * Real.log H) ^ ell :=
        Real.rpow_le_rpow (le_of_lt hlogdivpos) hupper hell
      _ = (2 : ℝ) ^ |ell| * (Real.log H) ^ ell := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hlogpos),
          abs_of_nonneg hell]
  · calc
      (Real.log (H / K)) ^ ell ≤ (Real.log H / 2) ^ ell :=
        Real.rpow_le_rpow_of_nonpos (div_pos hlogpos (by norm_num)) hlower hell
      _ = (2 : ℝ) ^ |ell| * (Real.log H) ^ ell := by
        rw [Real.div_rpow (le_of_lt hlogpos) (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonpos hell, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) ell]
        ring

/-- The reverse transfer with an explicit constant and cutoff. The new
constant is (D*C/K^(-b))*2^|ell|. The maximum in the cutoff enforces both
the original bound at H/K and the logarithm comparison. -/
theorem scaled_transfer_logPower_bound
    (f g : ℝ → ℝ) (K D C H0 b ell : ℝ)
    (hK : 0 < K) (hD : 0 ≤ D) (hC : 0 ≤ C) (hH0 : 1 < H0)
    (htransfer : ∀ H : ℝ, 0 < H → f (K * H) ≤ D * g H)
    (hbound : ∀ H : ℝ, H0 ≤ H →
      g H ≤ C * H ^ (-b) * (Real.log H) ^ ell) :
    ∀ H : ℝ, max (K * H0) (Real.exp (2 * |Real.log K| + 1)) ≤ H →
      f H ≤ ((D * C / K ^ (-b)) * (2 : ℝ) ^ |ell|) *
        H ^ (-b) * (Real.log H) ^ ell := by
  intro H hH
  have hscale : K * H0 ≤ H := le_trans (le_max_left _ _) hH
  have hlarge : Real.exp (2 * |Real.log K| + 1) ≤ H :=
    le_trans (le_max_right _ _) hH
  have hHpos : 0 < H := lt_of_lt_of_le (Real.exp_pos _) hlarge
  have hquot : H0 ≤ H / K := by
    apply (le_div_iff₀ hK).mpr
    simpa only [mul_comm] using hscale
  have hquotpos : 0 < H / K :=
    lt_trans (by norm_num : (0 : ℝ) < 1) (lt_of_lt_of_le hH0 hquot)
  have hident : K * (H / K) = H := by
    calc
      K * (H / K) = (K / K) * H := by ring
      _ = H := by rw [div_self (ne_of_gt hK), one_mul]
  have hcoefficient : 0 ≤ (D * C / K ^ (-b)) * H ^ (-b) :=
    mul_nonneg
      (div_nonneg (mul_nonneg hD hC) (le_of_lt (Real.rpow_pos_of_pos hK (-b))))
      (le_of_lt (Real.rpow_pos_of_pos hHpos (-b)))
  calc
    f H = f (K * (H / K)) := congrArg f hident.symm
    _ ≤ D * g (H / K) := htransfer (H / K) hquotpos
    _ ≤ D * (C * (H / K) ^ (-b) * (Real.log (H / K)) ^ ell) :=
      mul_le_mul_of_nonneg_left (hbound (H / K) hquot) hD
    _ = ((D * C / K ^ (-b)) * H ^ (-b)) * (Real.log (H / K)) ^ ell := by
      rw [Real.div_rpow (le_of_lt hHpos) (le_of_lt hK) (-b)]
      ring
    _ ≤ ((D * C / K ^ (-b)) * H ^ (-b)) *
        ((2 : ℝ) ^ |ell| * (Real.log H) ^ ell) :=
      mul_le_mul_of_nonneg_left (log_div_rpow_le K H ell hK hlarge) hcoefficient
    _ = ((D * C / K ^ (-b)) * (2 : ℝ) ^ |ell|) *
        H ^ (-b) * (Real.log H) ^ ell := by ring

/-- A pointwise upper comparison transfers the same corrected bound. -/
theorem eventualLogPowerUpperBound_mono
    (f g : ℝ → ℝ) (b ell : ℝ)
    (hle : ∀ H : ℝ, 0 < H → f H ≤ g H)
    (hg : EventualLogPowerUpperBound g b ell) :
    EventualLogPowerUpperBound f b ell := by
  obtain ⟨C, hC, H0, hH0, hbound⟩ := hg
  refine ⟨C, hC, H0, hH0, ?_⟩
  intro H hH
  have hHpos : 0 < H :=
    lt_trans (by norm_num : (0 : ℝ) < 1) (lt_of_lt_of_le hH0 hH)
  exact le_trans (hle H hHpos) (hbound H hH)

/-- A fixed positive dilation preserves b and ell exactly. -/
theorem eventualLogPowerUpperBound_of_scaled_transfer
    (f g : ℝ → ℝ) (K D b ell : ℝ) (hK : 0 < K) (hD : 0 < D)
    (htransfer : ∀ H : ℝ, 0 < H → f (K * H) ≤ D * g H)
    (hg : EventualLogPowerUpperBound g b ell) :
    EventualLogPowerUpperBound f b ell := by
  obtain ⟨C, hC, H0, hH0, hbound⟩ := hg
  have hexp : 1 < Real.exp (2 * |Real.log K| + 1) := by
    apply Real.lt_exp_of_log_lt
    rw [Real.log_one]
    linarith [abs_nonneg (Real.log K)]
  refine ⟨(D * C / K ^ (-b)) * (2 : ℝ) ^ |ell|,
    mul_pos (div_pos (mul_pos hD hC) (Real.rpow_pos_of_pos hK (-b)))
      (Real.rpow_pos_of_pos (by norm_num) |ell|),
    max (K * H0) (Real.exp (2 * |Real.log K| + 1)),
    lt_of_lt_of_le hexp (le_max_right _ _), ?_⟩
  exact scaled_transfer_logPower_bound f g K D C H0 b ell hK (le_of_lt hD)
    (le_of_lt hC) hH0 htransfer hbound

/-- Full equivalence of corrected bounds, including any endpoint ell. -/
theorem eventualLogPowerUpperBound_iff_of_sandwich
    (c a : ℝ → ℝ) (K D b ell : ℝ) (hK : 0 < K) (hD : 0 < D)
    (hsandwich : ∀ H : ℝ, 0 < H →
      c (K * H) / D ≤ a H ∧ a H ≤ c H) :
    EventualLogPowerUpperBound c b ell ↔ EventualLogPowerUpperBound a b ell := by
  constructor
  · intro hc
    exact eventualLogPowerUpperBound_mono a c b ell
      (fun H hH => (hsandwich H hH).2) hc
  · intro ha
    apply eventualLogPowerUpperBound_of_scaled_transfer c a K D b ell hK hD ?_ ha
    intro H hH
    have h := (div_le_iff₀ hD).mp (hsandwich H hH).1
    simpa only [mul_comm] using h

/-- Absorb a positive constant into a positive LOGARITHMIC exponent loss.
The explicit extra cutoff is exp(C^(1/epsilon)); the power exponent b
is not changed. -/
theorem logPower_upper_bound_absorb_constant
    (f : ℝ → ℝ) (C H0 b ell epsilon : ℝ)
    (hC : 0 < C) (hH0 : 1 < H0) (hepsilon : 0 < epsilon)
    (hbound : ∀ H : ℝ, H0 ≤ H →
      f H ≤ C * H ^ (-b) * (Real.log H) ^ ell) :
    ∀ H : ℝ, max H0 (Real.exp (C ^ epsilon⁻¹)) ≤ H →
      f H ≤ H ^ (-b) * (Real.log H) ^ (ell + epsilon) := by
  intro H hH
  have hbase : H0 ≤ H := le_trans (le_max_left _ _) hH
  have hHgt : 1 < H := lt_of_lt_of_le hH0 hbase
  have hHpos : 0 < H := lt_trans (by norm_num : (0 : ℝ) < 1) hHgt
  have hlogpos : 0 < Real.log H := Real.log_pos hHgt
  have hroot : C ^ epsilon⁻¹ ≤ Real.log H := by
    apply (Real.le_log_iff_exp_le hHpos).mpr
    exact le_trans (le_max_right _ _) hH
  have hconstant : C ≤ (Real.log H) ^ epsilon := by
    calc
      C = (C ^ epsilon⁻¹) ^ epsilon :=
        (Real.rpow_inv_rpow (le_of_lt hC) (ne_of_gt hepsilon)).symm
      _ ≤ (Real.log H) ^ epsilon := Real.rpow_le_rpow
        (le_of_lt (Real.rpow_pos_of_pos hC epsilon⁻¹)) hroot (le_of_lt hepsilon)
  calc
    f H ≤ C * H ^ (-b) * (Real.log H) ^ ell := hbound H hbase
    _ = H ^ (-b) * (C * (Real.log H) ^ ell) := by ring
    _ ≤ H ^ (-b) * ((Real.log H) ^ epsilon * (Real.log H) ^ ell) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hconstant
          (le_of_lt (Real.rpow_pos_of_pos hlogpos ell)))
        (le_of_lt (Real.rpow_pos_of_pos hHpos (-b)))
    _ = H ^ (-b) * (Real.log H) ^ (epsilon + ell) := by
      rw [Real.rpow_add hlogpos epsilon ell]
    _ = H ^ (-b) * (Real.log H) ^ (ell + epsilon) := by
      rw [add_comm epsilon ell]

/-- Epsilon-logarithmic upper bounds can be stated with coefficient one
or with an arbitrary positive constant for each epsilon. The converse
uses epsilon/2; no uniformity in epsilon is required. -/
theorem epsilonLogPowerBound_iff_eventualLogPowerUpperBounds
    (f : ℝ → ℝ) (b ell : ℝ) :
    EpsilonLogPowerBound f b ell ↔
      ∀ epsilon : ℝ, 0 < epsilon →
        EventualLogPowerUpperBound f b (ell + epsilon) := by
  constructor
  · intro hf epsilon hepsilon
    obtain ⟨H0, hH0, hbound⟩ := hf epsilon hepsilon
    refine ⟨1, by norm_num, H0, hH0, ?_⟩
    intro H hH
    simpa only [one_mul] using hbound H hH
  · intro hf epsilon hepsilon
    have hhalf : 0 < epsilon / 2 := by linarith
    obtain ⟨C, hC, H0, hH0, hbound⟩ := hf (epsilon / 2) hhalf
    refine ⟨max H0 (Real.exp (C ^ (epsilon / 2)⁻¹)),
      lt_of_lt_of_le hH0 (le_max_left _ _), ?_⟩
    intro H hH
    have h := logPower_upper_bound_absorb_constant f C H0 b
      (ell + epsilon / 2) (epsilon / 2) hC hH0 hhalf hbound H hH
    have hexponent : (ell + epsilon / 2) + epsilon / 2 = ell + epsilon := by ring
    simpa only [hexponent] using h

/-- Coefficient-one logarithmic epsilon bounds are invariant under the
scaled sandwich. This does not assert that either family has such a bound. -/
theorem epsilonLogPowerBound_iff_of_sandwich
    (c a : ℝ → ℝ) (K D b ell : ℝ) (hK : 0 < K) (hD : 0 < D)
    (hsandwich : ∀ H : ℝ, 0 < H →
      c (K * H) / D ≤ a H ∧ a H ≤ c H) :
    EpsilonLogPowerBound c b ell ↔ EpsilonLogPowerBound a b ell := by
  rw [epsilonLogPowerBound_iff_eventualLogPowerUpperBounds,
    epsilonLogPowerBound_iff_eventualLogPowerUpperBounds]
  constructor
  · intro hc epsilon hepsilon
    exact (eventualLogPowerUpperBound_iff_of_sandwich c a K D b
      (ell + epsilon) hK hD hsandwich).mp (hc epsilon hepsilon)
  · intro ha epsilon hepsilon
    exact (eventualLogPowerUpperBound_iff_of_sandwich c a K D b
      (ell + epsilon) hK hD hsandwich).mpr (ha epsilon hepsilon)

/-- The entire set of logarithmic upper-bound exponents agrees, at fixed b.
In particular, membership of its endpoint is preserved when applicable. -/
theorem scaled_sandwich_logPower_spectrum_eq
    (c a : ℝ → ℝ) (K D b : ℝ) (hK : 0 < K) (hD : 0 < D)
    (hsandwich : ∀ H : ℝ, 0 < H →
      c (K * H) / D ≤ a H ∧ a H ≤ c H) :
    {ell : ℝ | EventualLogPowerUpperBound c b ell} =
      {ell : ℝ | EventualLogPowerUpperBound a b ell} := by
  ext ell
  exact eventualLogPowerUpperBound_iff_of_sandwich c a K D b ell hK hD hsandwich

/-- Failure of an eventual bound gives a strict counterexample beyond
EVERY starting height, for EVERY positive constant. This is the exact
quantifier content used in the lower side of the envelope definition. -/
theorem not_eventualLogPowerUpperBound_iff (f : ℝ → ℝ) (b ell : ℝ) :
    (¬ EventualLogPowerUpperBound f b ell) ↔
      ∀ C : ℝ, 0 < C → ∀ H0 : ℝ, 1 < H0 →
        ∃ H : ℝ, H0 ≤ H ∧ C * H ^ (-b) * (Real.log H) ^ ell < f H := by
  classical
  simp only [EventualLogPowerUpperBound, not_exists, not_and, not_forall,
    not_le, exists_prop]

/-- Both sides of a finite exact logarithmic envelope transfer. This is
a statement about explicit quantified bounds, not a Mathlib limsup theorem. -/
theorem exactLogPowerEnvelope_iff_of_sandwich
    (c a : ℝ → ℝ) (K D b ell : ℝ) (hK : 0 < K) (hD : 0 < D)
    (hsandwich : ∀ H : ℝ, 0 < H →
      c (K * H) / D ≤ a H ∧ a H ≤ c H) :
    ExactLogPowerEnvelope c b ell ↔ ExactLogPowerEnvelope a b ell := by
  constructor
  · rintro ⟨hupper, hlower⟩
    refine ⟨(epsilonLogPowerBound_iff_of_sandwich c a K D b ell
      hK hD hsandwich).mp hupper, ?_⟩
    intro epsilon hepsilon hbound
    exact hlower epsilon hepsilon
      ((eventualLogPowerUpperBound_iff_of_sandwich c a K D b (ell - epsilon)
        hK hD hsandwich).mpr hbound)
  · rintro ⟨hupper, hlower⟩
    refine ⟨(epsilonLogPowerBound_iff_of_sandwich c a K D b ell
      hK hD hsandwich).mpr hupper, ?_⟩
    intro epsilon hepsilon hbound
    exact hlower epsilon hepsilon
      ((eventualLogPowerUpperBound_iff_of_sandwich c a K D b (ell - epsilon)
        hK hD hsandwich).mp hbound)

/-- Finite-index logarithmic-bound transfer under the SAME multiplier d
at EVERY nonnegative height. The arithmetic hypotheses remain explicit. -/
theorem finite_index_eventualLogPowerUpperBound_iff
    (alpha hQ b ell : ℝ) (d : ℕ) (ambient : ℝ → Set ℝ) (hd : 0 < d)
    (hinclude : ∀ H : ℝ, 0 ≤ H → ∀ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H →
      ∃ x ∈ ambient H, ∃ j : ℤ, x = (k : ℝ) * alpha + (j : ℝ))
    (hmultiply : ∀ H : ℝ, 0 ≤ H → ∀ x ∈ ambient H, ∃ k j : ℤ,
      hQ * (k : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * H ∧
      (k : ℝ) * alpha = (d : ℝ) * x + (j : ℝ)) :
    EventualLogPowerUpperBound (fun H => quadraticHeightCoveringRadius alpha hQ H)
        b ell ↔
      EventualLogPowerUpperBound (fun H => circleSetCoveringRadius (ambient H)) b ell := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  apply eventualLogPowerUpperBound_iff_of_sandwich
    (fun H => quadraticHeightCoveringRadius alpha hQ H)
    (fun H => circleSetCoveringRadius (ambient H))
    ((d : ℝ) ^ 2) (d : ℝ) b ell (sq_pos_of_pos hdR) hdR
  intro H hH
  exact finite_index_height_covering_sandwich alpha hQ H d ambient hd
    (le_of_lt hH) (hinclude H (le_of_lt hH)) (hmultiply H (le_of_lt hH))

/-- The finite-index comparison preserves coefficient-one epsilon losses
in the logarithmic exponent, with no loss in the power exponent. -/
theorem finite_index_epsilonLogPowerBound_iff
    (alpha hQ b ell : ℝ) (d : ℕ) (ambient : ℝ → Set ℝ) (hd : 0 < d)
    (hinclude : ∀ H : ℝ, 0 ≤ H → ∀ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H →
      ∃ x ∈ ambient H, ∃ j : ℤ, x = (k : ℝ) * alpha + (j : ℝ))
    (hmultiply : ∀ H : ℝ, 0 ≤ H → ∀ x ∈ ambient H, ∃ k j : ℤ,
      hQ * (k : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * H ∧
      (k : ℝ) * alpha = (d : ℝ) * x + (j : ℝ)) :
    EpsilonLogPowerBound (fun H => quadraticHeightCoveringRadius alpha hQ H) b ell ↔
      EpsilonLogPowerBound (fun H => circleSetCoveringRadius (ambient H)) b ell := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  apply epsilonLogPowerBound_iff_of_sandwich
    (fun H => quadraticHeightCoveringRadius alpha hQ H)
    (fun H => circleSetCoveringRadius (ambient H))
    ((d : ℝ) ^ 2) (d : ℝ) b ell (sq_pos_of_pos hdR) hdR
  intro H hH
  exact finite_index_height_covering_sandwich alpha hQ H d ambient hd
    (le_of_lt hH) (hinclude H (le_of_lt hH)) (hmultiply H (le_of_lt hH))

/-- Exact finite logarithmic envelopes transfer under finite index.
No particular value of the envelope is supplied by this implication. -/
theorem finite_index_exactLogPowerEnvelope_iff
    (alpha hQ b ell : ℝ) (d : ℕ) (ambient : ℝ → Set ℝ) (hd : 0 < d)
    (hinclude : ∀ H : ℝ, 0 ≤ H → ∀ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H →
      ∃ x ∈ ambient H, ∃ j : ℤ, x = (k : ℝ) * alpha + (j : ℝ))
    (hmultiply : ∀ H : ℝ, 0 ≤ H → ∀ x ∈ ambient H, ∃ k j : ℤ,
      hQ * (k : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * H ∧
      (k : ℝ) * alpha = (d : ℝ) * x + (j : ℝ)) :
    ExactLogPowerEnvelope (fun H => quadraticHeightCoveringRadius alpha hQ H) b ell ↔
      ExactLogPowerEnvelope (fun H => circleSetCoveringRadius (ambient H)) b ell := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  apply exactLogPowerEnvelope_iff_of_sandwich
    (fun H => quadraticHeightCoveringRadius alpha hQ H)
    (fun H => circleSetCoveringRadius (ambient H))
    ((d : ℝ) ^ 2) (d : ℝ) b ell (sq_pos_of_pos hdR) hdR
  intro H hH
  exact finite_index_height_covering_sandwich alpha hQ H d ambient hd
    (le_of_lt hH) (hinclude H (le_of_lt hH)) (hmultiply H (le_of_lt hH))

/-- Corrected-bound equivalence for the explicit rank-one-plus-torsion
circle model. Use h0>0 for its intended finite-height interpretation. -/
theorem torsion_extension_eventualLogPowerUpperBound_iff
    (beta h0 b ell : ℝ) (m t : ℕ) (hm : 0 < m) (ht : 0 < t) :
    EventualLogPowerUpperBound
        (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta)
          ((m : ℝ) ^ 2 * h0) H) b ell ↔
      EventualLogPowerUpperBound
        (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t)) b ell := by
  have hdR : (0 : ℝ) < ((m * t : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hm ht
  apply eventualLogPowerUpperBound_iff_of_sandwich
    (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0) H)
    (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t))
    ((((m * t : ℕ) : ℝ)) ^ 2) ((m * t : ℕ) : ℝ) b ell (sq_pos_of_pos hdR) hdR
  intro H hH
  exact torsion_extension_height_covering_sandwich beta h0 H m t hm ht (le_of_lt hH)

/-- Coefficient-one logarithmic epsilon equivalence for the torsion model. -/
theorem torsion_extension_epsilonLogPowerBound_iff
    (beta h0 b ell : ℝ) (m t : ℕ) (hm : 0 < m) (ht : 0 < t) :
    EpsilonLogPowerBound
        (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta)
          ((m : ℝ) ^ 2 * h0) H) b ell ↔
      EpsilonLogPowerBound
        (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t)) b ell := by
  have hdR : (0 : ℝ) < ((m * t : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hm ht
  apply epsilonLogPowerBound_iff_of_sandwich
    (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0) H)
    (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t))
    ((((m * t : ℕ) : ℝ)) ^ 2) ((m * t : ℕ) : ℝ) b ell (sq_pos_of_pos hdR) hdR
  intro H hH
  exact torsion_extension_height_covering_sandwich beta h0 H m t hm ht (le_of_lt hH)

/-- Final exact-envelope equivalence for the explicit torsion model.
This proves neither a numerical value of ell nor a curve identification. -/
theorem torsion_extension_exactLogPowerEnvelope_iff
    (beta h0 b ell : ℝ) (m t : ℕ) (hm : 0 < m) (ht : 0 < t) :
    ExactLogPowerEnvelope
        (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta)
          ((m : ℝ) ^ 2 * h0) H) b ell ↔
      ExactLogPowerEnvelope
        (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t)) b ell := by
  have hdR : (0 : ℝ) < ((m * t : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hm ht
  apply exactLogPowerEnvelope_iff_of_sandwich
    (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0) H)
    (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t))
    ((((m * t : ℕ) : ℝ)) ^ 2) ((m * t : ℕ) : ℝ) b ell (sq_pos_of_pos hdR) hdR
  intro H hH
  exact torsion_extension_height_covering_sandwich beta h0 H m t hm ht (le_of_lt hH)

#print axioms eventualLogPowerUpperBound_zero_iff
#print axioms log_div_rpow_le
#print axioms scaled_transfer_logPower_bound
#print axioms eventualLogPowerUpperBound_mono
#print axioms eventualLogPowerUpperBound_of_scaled_transfer
#print axioms eventualLogPowerUpperBound_iff_of_sandwich
#print axioms logPower_upper_bound_absorb_constant
#print axioms epsilonLogPowerBound_iff_eventualLogPowerUpperBounds
#print axioms epsilonLogPowerBound_iff_of_sandwich
#print axioms scaled_sandwich_logPower_spectrum_eq
#print axioms not_eventualLogPowerUpperBound_iff
#print axioms exactLogPowerEnvelope_iff_of_sandwich
#print axioms finite_index_eventualLogPowerUpperBound_iff
#print axioms finite_index_epsilonLogPowerBound_iff
#print axioms finite_index_exactLogPowerEnvelope_iff
#print axioms torsion_extension_eventualLogPowerUpperBound_iff
#print axioms torsion_extension_epsilonLogPowerBound_iff
#print axioms torsion_extension_exactLogPowerEnvelope_iff

end AbelianLog

/-!
# V10 extension: the actual extended-real logarithmic limsup

The new definition uses Mathlib's Filter.limsup, not a substitute predicate.
The real profile is interpreted on a tail where H>exp(1) and f(H)>0.
Eventual positivity is an EXPLICIT hypothesis of all semantic bridges.

The EReal codomain retains both infinite outcomes. It does not change the
meaning of Real.log at nonpositive inputs; eventual positivity is still
necessary. No finite-cardinality positivity result, continued-fraction
identity, rank/saturation fact, analytic enclosure, or arithmetic value
of the limsup is introduced in this extension.

The v9.1 source above is retained verbatim. Only this appended extension
and the leading validation record are new. All proofs below are DRAFTS
pending the user's live Lean/Mathlib compilation.
-/

namespace AbelianLog

open Filter

/-- The logarithmic profile. On its intended positive tail this equals
log(H^b*f(H))/log(log(H)). Behavior off that tail is not interpreted. -/
noncomputable def logPowerProfile (f : ℝ → ℝ) (b H : ℝ) : ℝ :=
  (Real.log (f H) + b * Real.log H) / Real.log (Real.log H)

/-- Mathlib's genuine limsup in the complete ordered extended real line.
This retains both infinities and needs no boundedness assumption. -/
noncomputable def logPowerLimsup (f : ℝ → ℝ) (b : ℝ) : EReal :=
  Filter.limsup (fun H : ℝ => (logPowerProfile f b H : EReal)) Filter.atTop

/-- The additive numerator is exactly the logarithm of the normalized
radius whenever both factors are positive. -/
theorem logPowerProfile_eq_log_product
    (f : ℝ → ℝ) (b H : ℝ) (hH : 0 < H) (hf : 0 < f H) :
    logPowerProfile f b H =
      Real.log (H ^ b * f H) / Real.log (Real.log H) := by
  unfold logPowerProfile
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hH b)) (ne_of_gt hf),
    Real.log_rpow hH b]
  congr 1
  ring

/-- On H>exp(1), a profile cutoff is exactly the coefficient-one
logarithmically corrected radius bound. Every logarithm used is positive
where required, and the profile denominator is strictly positive. -/
theorem logPowerProfile_le_iff
    (f : ℝ → ℝ) (b s H : ℝ)
    (hH : Real.exp 1 < H) (hf : 0 < f H) :
    logPowerProfile f b H ≤ s ↔
      f H ≤ H ^ (-b) * (Real.log H) ^ s := by
  have hHpos : 0 < H := lt_trans (Real.exp_pos 1) hH
  have hloggt : 1 < Real.log H := by
    have h := Real.log_lt_log (Real.exp_pos 1) hH
    simpa only [Real.log_exp] using h
  have hlogpos : 0 < Real.log H := by linarith
  have hloglog : 0 < Real.log (Real.log H) := Real.log_pos hloggt
  have hpow : 0 < H ^ (-b) := Real.rpow_pos_of_pos hHpos (-b)
  have hlogpow : 0 < (Real.log H) ^ s := Real.rpow_pos_of_pos hlogpos s
  have hlogbound :
      Real.log (H ^ (-b) * (Real.log H) ^ s) =
        (-b) * Real.log H + s * Real.log (Real.log H) := by
    rw [Real.log_mul (ne_of_gt hpow) (ne_of_gt hlogpow),
      Real.log_rpow hHpos (-b), Real.log_rpow hlogpos s]
  have hcompare := Real.log_le_log_iff hf (mul_pos hpow hlogpow)
  rw [hlogbound] at hcompare
  unfold logPowerProfile
  rw [div_le_iff₀ hloglog]
  constructor
  · intro h
    exact hcompare.mp (by linarith)
  · intro h
    have hlog := hcompare.mpr h
    linarith

/-- Eventual profile bounds and eventual coefficient-one corrected bounds
coincide. The finite initial segment of heights is discarded explicitly. -/
theorem eventually_logPowerProfile_le_iff
    (f : ℝ → ℝ) (b s : ℝ)
    (hpos : ∀ᶠ H : ℝ in Filter.atTop, 0 < f H) :
    (∀ᶠ H : ℝ in Filter.atTop, logPowerProfile f b H ≤ s) ↔
      ∃ H0 : ℝ, 1 < H0 ∧ ∀ H : ℝ, H0 ≤ H →
        f H ≤ H ^ (-b) * (Real.log H) ^ s := by
  constructor
  · intro hprofile
    have hbound : ∀ᶠ H : ℝ in Filter.atTop,
        f H ≤ H ^ (-b) * (Real.log H) ^ s := by
      filter_upwards [hprofile, hpos, Filter.eventually_gt_atTop (Real.exp 1)]
        with H hp hf hH
      exact (logPowerProfile_le_iff f b s H hH hf).mp hp
    obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hbound
    refine ⟨max A 2,
      lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
    intro H hH
    exact hA H (le_trans (le_max_left _ _) hH)
  · rintro ⟨H0, _hH0, hbound⟩
    filter_upwards [hpos, Filter.eventually_ge_atTop H0,
      Filter.eventually_gt_atTop (Real.exp 1)] with H hf hbase hH
    exact (logPowerProfile_le_iff f b s H hH hf).mpr (hbound H hbase)

/-- A real cut characterizes the upper side of an EReal limsup. Unlike a
real-valued limsup, the two infinite cases remain meaningful automatically. -/
theorem ereal_limsup_le_coe_iff
    (u : ℝ → ℝ) (ell : ℝ) :
    Filter.limsup (fun H : ℝ => (u H : EReal)) Filter.atTop ≤ (ell : EReal) ↔
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ H : ℝ in Filter.atTop, u H ≤ ell + epsilon := by
  constructor
  · intro h epsilon hepsilon
    have hstrict :
        Filter.limsup (fun H : ℝ => (u H : EReal)) Filter.atTop <
          ((ell + epsilon : ℝ) : EReal) :=
      lt_of_le_of_lt h (EReal.coe_lt_coe (by linarith))
    have hevent : ∀ᶠ H : ℝ in Filter.atTop,
        (u H : EReal) < ((ell + epsilon : ℝ) : EReal) :=
      Filter.eventually_lt_of_limsup_lt hstrict
    filter_upwards [hevent] with H hH
    exact le_of_lt (EReal.coe_lt_coe_iff.mp hH)
  · intro h
    apply (Filter.limsup_le_iff'
      (u := fun H : ℝ => (u H : EReal)) (f := Filter.atTop)).mpr
    refine (EReal.forall (p := fun y : EReal =>
      (ell : EReal) < y →
        ∀ᶠ H : ℝ in Filter.atTop, (u H : EReal) ≤ y)).mpr ?_
    refine ⟨?_, ?_, ?_⟩
    · intro hbot
      exact False.elim ((not_lt_of_ge (bot_le : (⊥ : EReal) ≤ (ell : EReal))) hbot)
    · intro _
      exact Filter.Eventually.of_forall (fun _ => le_top)
    · intro s hs
      have hsR : ell < s := EReal.coe_lt_coe_iff.mp hs
      filter_upwards [h (s - ell) (sub_pos.mpr hsR)] with H hH
      apply EReal.coe_le_coe
      linarith

/-- The coefficient-one epsilon upper property is precisely the upper
inequality for the actual extended-real limsup, under eventual positivity. -/
theorem epsilonLogPowerBound_iff_logPowerLimsup_le
    (f : ℝ → ℝ) (b ell : ℝ)
    (hpos : ∀ᶠ H : ℝ in Filter.atTop, 0 < f H) :
    EpsilonLogPowerBound f b ell ↔ logPowerLimsup f b ≤ (ell : EReal) := by
  unfold logPowerLimsup
  rw [ereal_limsup_le_coe_iff]
  constructor
  · intro h epsilon hepsilon
    exact (eventually_logPowerProfile_le_iff f b (ell + epsilon) hpos).mpr
      (h epsilon hepsilon)
  · intro h epsilon hepsilon
    exact (eventually_logPowerProfile_le_iff f b (ell + epsilon) hpos).mp
      (h epsilon hepsilon)

/-- Any eventual corrected bound implies the coefficient-one epsilon
version at the same logarithmic exponent, by the validated absorption lemma. -/
theorem eventualLogPowerUpperBound_imp_epsilonLogPowerBound
    (f : ℝ → ℝ) (b ell : ℝ)
    (hbound : EventualLogPowerUpperBound f b ell) :
    EpsilonLogPowerBound f b ell := by
  obtain ⟨C, hC, H0, hH0, hbound⟩ := hbound
  intro epsilon hepsilon
  refine ⟨max H0 (Real.exp (C ^ epsilon⁻¹)),
    lt_of_lt_of_le hH0 (le_max_left _ _), ?_⟩
  exact logPower_upper_bound_absorb_constant f C H0 b ell epsilon
    hC hH0 hepsilon hbound

/-- Constants in eventual upper bounds disappear in the logarithmic limsup. -/
theorem logPowerLimsup_le_of_eventualLogPowerUpperBound
    (f : ℝ → ℝ) (b ell : ℝ)
    (hpos : ∀ᶠ H : ℝ in Filter.atTop, 0 < f H)
    (hbound : EventualLogPowerUpperBound f b ell) :
    logPowerLimsup f b ≤ (ell : EReal) :=
  (epsilonLogPowerBound_iff_logPowerLimsup_le f b ell hpos).mp
    (eventualLogPowerUpperBound_imp_epsilonLogPowerBound f b ell hbound)

/-- Main bridge: the v9 exact envelope is equivalent to a genuine finite
limsup value. Eventual positivity is not inferred or silently assumed. -/
theorem exactLogPowerEnvelope_iff_logPowerLimsup_eq
    (f : ℝ → ℝ) (b ell : ℝ)
    (hpos : ∀ᶠ H : ℝ in Filter.atTop, 0 < f H) :
    ExactLogPowerEnvelope f b ell ↔ logPowerLimsup f b = (ell : EReal) := by
  constructor
  · rintro ⟨hupper, hlower⟩
    apply le_antisymm
    · exact (epsilonLogPowerBound_iff_logPowerLimsup_le f b ell hpos).mp hupper
    · unfold logPowerLimsup
      apply Filter.le_limsup_of_le (by isBoundedDefault)
      intro y hy
      induction y using EReal.rec with
      | bot =>
          obtain ⟨H, hH⟩ := hy.exists
          exact False.elim ((not_le_of_gt (EReal.bot_lt_coe (logPowerProfile f b H))) hH)
      | coe s =>
          apply EReal.coe_le_coe
          by_contra hn
          have hs : s < ell := lt_of_not_ge hn
          have hprofile : ∀ᶠ H : ℝ in Filter.atTop, logPowerProfile f b H ≤ s := by
            filter_upwards [hy] with H hH
            exact EReal.coe_le_coe_iff.mp hH
          obtain ⟨H0, hH0, hbound⟩ :=
            (eventually_logPowerProfile_le_iff f b s hpos).mp hprofile
          have hconstant : EventualLogPowerUpperBound f b s := by
            refine ⟨1, by norm_num, H0, hH0, ?_⟩
            intro H hH
            simpa only [one_mul] using hbound H hH
          have hnot := hlower (ell - s) (sub_pos.mpr hs)
          have hexponent : ell - (ell - s) = s := by ring
          rw [hexponent] at hnot
          exact hnot hconstant
      | top => exact le_top
  · intro hlim
    refine ⟨(epsilonLogPowerBound_iff_logPowerLimsup_le f b ell hpos).mpr
      (le_of_eq hlim), ?_⟩
    intro epsilon hepsilon hbound
    have hle := logPowerLimsup_le_of_eventualLogPowerUpperBound
      f b (ell - epsilon) hpos hbound
    rw [hlim] at hle
    have hreal : ell ≤ ell - epsilon := EReal.coe_le_coe_iff.mp hle
    linarith

/-- The profile limsup agrees with the workbench's product-log expression.
This equality uses eventual agreement, so the initial range is irrelevant. -/
theorem logPowerLimsup_eq_log_product_limsup
    (f : ℝ → ℝ) (b : ℝ)
    (hpos : ∀ᶠ H : ℝ in Filter.atTop, 0 < f H) :
    logPowerLimsup f b =
      Filter.limsup (fun H : ℝ =>
        ((Real.log (H ^ b * f H) / Real.log (Real.log H) : ℝ) : EReal))
        Filter.atTop := by
  unfold logPowerLimsup
  apply Filter.limsup_congr
  filter_upwards [hpos, Filter.eventually_gt_atTop (0 : ℝ)] with H hf hH
  exact congrArg (fun x : ℝ => (x : EReal))
    (logPowerProfile_eq_log_product f b H hH hf)

/-- A finite exact logarithmic envelope has a unique exponent. -/
theorem exactLogPowerEnvelope_unique
    (f : ℝ → ℝ) (b ell₁ ell₂ : ℝ)
    (hpos : ∀ᶠ H : ℝ in Filter.atTop, 0 < f H)
    (h₁ : ExactLogPowerEnvelope f b ell₁)
    (h₂ : ExactLogPowerEnvelope f b ell₂) : ell₁ = ell₂ := by
  have hlim₁ := (exactLogPowerEnvelope_iff_logPowerLimsup_eq f b ell₁ hpos).mp h₁
  have hlim₂ := (exactLogPowerEnvelope_iff_logPowerLimsup_eq f b ell₂ hpos).mp h₂
  exact EReal.coe_eq_coe_iff.mp (hlim₁.symm.trans hlim₂)

/-- Real upper cuts determine order in EReal, including the infinite cases. -/
theorem ereal_le_of_real_upper_bounds
    (x y : EReal)
    (h : ∀ r : ℝ, y ≤ (r : EReal) → x ≤ (r : EReal)) : x ≤ y := by
  induction y using EReal.rec with
  | bot =>
      induction x using EReal.rec with
      | bot => exact le_rfl
      | coe r =>
          have hreal : r ≤ r - 1 := EReal.coe_le_coe_iff.mp (h (r - 1) bot_le)
          exfalso
          linarith
      | top =>
          exact False.elim ((not_le_of_gt (EReal.coe_lt_top (0 : ℝ))) (h 0 bot_le))
  | coe r => exact h r le_rfl
  | top => exact le_top

/-- Equality of all real upper cuts implies actual EReal equality. -/
theorem ereal_eq_of_real_upper_bounds
    (x y : EReal)
    (h : ∀ r : ℝ, x ≤ (r : EReal) ↔ y ≤ (r : EReal)) : x = y := by
  apply le_antisymm
  · exact ereal_le_of_real_upper_bounds x y (fun r hr => (h r).mpr hr)
  · exact ereal_le_of_real_upper_bounds y x (fun r hr => (h r).mp hr)

/-- Positivity of the cyclic radius on a tail implies positivity of the
ambient radius on a tail, by the lower half of the scaled sandwich. -/
theorem eventually_positive_of_scaled_sandwich
    (c a : ℝ → ℝ) (K D : ℝ) (hK : 0 < K) (hD : 0 < D)
    (hsandwich : ∀ H : ℝ, 0 < H → c (K * H) / D ≤ a H ∧ a H ≤ c H)
    (hcpos : ∀ᶠ H : ℝ in Filter.atTop, 0 < c H) :
    ∀ᶠ H : ℝ in Filter.atTop, 0 < a H := by
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.mp hcpos
  apply Filter.eventually_atTop.mpr
  refine ⟨max (P / K) 1, ?_⟩
  intro H hH
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_trans (le_max_right _ _) hH)
  have hPH : P / K ≤ H := le_trans (le_max_left _ _) hH
  have hscaled : P ≤ K * H := by
    have h := (div_le_iff₀ hK).mp hPH
    simpa only [mul_comm] using h
  exact lt_of_lt_of_le (div_pos (hP (K * H) hscaled) hD) (hsandwich H hHpos).1

/-- Full equality of the actual logarithmic limsups under a scaled sandwich.
The equality is in EReal: finite, +infinity, and -infinity are all covered.
Only cyclic eventual positivity is requested; ambient positivity is derived. -/
theorem logPowerLimsup_eq_of_sandwich
    (c a : ℝ → ℝ) (K D b : ℝ) (hK : 0 < K) (hD : 0 < D)
    (hsandwich : ∀ H : ℝ, 0 < H → c (K * H) / D ≤ a H ∧ a H ≤ c H)
    (hcpos : ∀ᶠ H : ℝ in Filter.atTop, 0 < c H) :
    logPowerLimsup c b = logPowerLimsup a b := by
  have hapos := eventually_positive_of_scaled_sandwich c a K D hK hD hsandwich hcpos
  apply ereal_eq_of_real_upper_bounds
  intro ell
  exact ((epsilonLogPowerBound_iff_logPowerLimsup_le c b ell hcpos).symm.trans
    (epsilonLogPowerBound_iff_of_sandwich c a K D b ell hK hD hsandwich)).trans
      (epsilonLogPowerBound_iff_logPowerLimsup_le a b ell hapos)

/-- Finite-index equality of genuine limsups. Arithmetic inclusion and
multiplication remain hypotheses, uniform in height for a fixed d.
Positivity of the cyclic radius is also retained explicitly. -/
theorem finite_index_logPowerLimsup_eq
    (alpha hQ b : ℝ) (d : ℕ) (ambient : ℝ → Set ℝ)
    (hd : 0 < d)
    (hinclude : ∀ H : ℝ, 0 ≤ H → ∀ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H →
      ∃ x ∈ ambient H, ∃ j : ℤ, x = (k : ℝ) * alpha + (j : ℝ))
    (hmultiply : ∀ H : ℝ, 0 ≤ H → ∀ x ∈ ambient H, ∃ k j : ℤ,
      hQ * (k : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * H ∧
      (k : ℝ) * alpha = (d : ℝ) * x + (j : ℝ))
    (hcpos : ∀ᶠ H : ℝ in Filter.atTop,
      0 < quadraticHeightCoveringRadius alpha hQ H) :
    logPowerLimsup (fun H => quadraticHeightCoveringRadius alpha hQ H) b =
      logPowerLimsup (fun H => circleSetCoveringRadius (ambient H)) b := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  apply logPowerLimsup_eq_of_sandwich
    (fun H => quadraticHeightCoveringRadius alpha hQ H)
    (fun H => circleSetCoveringRadius (ambient H))
    ((d : ℝ) ^ 2) (d : ℝ) b (sq_pos_of_pos hdR) hdR ?_ hcpos
  intro H hH
  exact finite_index_height_covering_sandwich alpha hQ H d ambient hd
    (le_of_lt hH) (hinclude H (le_of_lt hH)) (hmultiply H (le_of_lt hH))

/-- Genuine limsup equality for the explicit torsion phase model.
This does not identify that model with the curve's rational-point group. -/
theorem torsion_extension_logPowerLimsup_eq
    (beta h0 b : ℝ) (m t : ℕ) (hm : 0 < m) (ht : 0 < t)
    (hcpos : ∀ᶠ H : ℝ in Filter.atTop,
      0 < quadraticHeightCoveringRadius ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0) H) :
    logPowerLimsup
        (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0) H) b =
      logPowerLimsup
        (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t)) b := by
  have hdR : (0 : ℝ) < ((m * t : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hm ht
  apply logPowerLimsup_eq_of_sandwich
    (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0) H)
    (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t))
    ((((m * t : ℕ) : ℝ)) ^ 2) ((m * t : ℕ) : ℝ) b
    (sq_pos_of_pos hdR) hdR ?_ hcpos
  intro H hH
  exact torsion_extension_height_covering_sandwich beta h0 H m t hm ht (le_of_lt hH)

#print axioms logPowerProfile_eq_log_product
#print axioms logPowerProfile_le_iff
#print axioms eventually_logPowerProfile_le_iff
#print axioms ereal_limsup_le_coe_iff
#print axioms epsilonLogPowerBound_iff_logPowerLimsup_le
#print axioms eventualLogPowerUpperBound_imp_epsilonLogPowerBound
#print axioms logPowerLimsup_le_of_eventualLogPowerUpperBound
#print axioms exactLogPowerEnvelope_iff_logPowerLimsup_eq
#print axioms logPowerLimsup_eq_log_product_limsup
#print axioms exactLogPowerEnvelope_unique
#print axioms ereal_le_of_real_upper_bounds
#print axioms ereal_eq_of_real_upper_bounds
#print axioms eventually_positive_of_scaled_sandwich
#print axioms logPowerLimsup_eq_of_sandwich
#print axioms finite_index_logPowerLimsup_eq
#print axioms torsion_extension_logPowerLimsup_eq

end AbelianLog

/-!
# V11 extension: positivity from finite geometry and the exact height cutoff

This block supplies, rather than assumes, positivity of finite-orbit radii.
The elementary pigeonhole estimate is 1/(2*(M+1)); it is deliberately NOT
claimed to be the sharp largest-gap bound 1/(2*M).

For hQ>0 and H>=0, B=floor(sqrt(H/hQ)) gives the exact signed cutoff.
Consequently the quadratic-height covering radius is positive at EVERY
nonnegative height. The new limsup wrappers replace the old abstract
positivity hypothesis by hQ>0 (or h0>0 in the torsion model).

No irrationality, elliptic-integral enclosure, rank, saturation, or actual
canonical-height identification is introduced. All earlier statements and
proof bodies are retained unchanged.
-/

namespace AbelianLog

/-- An integer grid has no two distinct residues less than one unit apart
once the denominator has been cleared. Integer translates are allowed. -/
theorem integer_grid_residues_eq_of_abs_lt_one
    (q i l j : ℤ) (hq : 0 < q)
    (hi0 : 0 ≤ i) (hiq : i < q) (hl0 : 0 ≤ l) (hlq : l < q)
    (hnear : |(i : ℝ) - (l : ℝ) - (j : ℝ) * (q : ℝ)| < 1) :
    i = l := by
  have hlo : (-1 : ℤ) < i - l - j * q := by
    exact_mod_cast (abs_lt.mp hnear).1
  have hhi : i - l - j * q < (1 : ℤ) := by
    exact_mod_cast (abs_lt.mp hnear).2
  have heq : i - l - j * q = 0 := by omega
  rcases lt_trichotomy j 0 with hj | hj | hj
  · have hj1 : j ≤ -1 := by omega
    have hp : j * q ≤ -q := by
      calc
        j * q ≤ (-1) * q := mul_le_mul_of_nonneg_right hj1 (le_of_lt hq)
        _ = -q := by ring
    omega
  · subst j
    omega
  · have hj1 : 1 ≤ j := by omega
    have hp : q ≤ j * q := by
      calc
        q = 1 * q := by ring
        _ ≤ j * q := mul_le_mul_of_nonneg_right hj1 (le_of_lt hq)
    omega

/-- Pigeonhole lower bound for an arbitrary indexed family of N circle
phases, allowing repeated phases. N+1 evenly spaced targets cannot all be
covered with radius strictly less than 1/(2*(N+1)). -/
theorem finite_phase_covering_lower_bound
    (N : ℕ) (x : Fin N → ℝ) (rho : ℝ)
    (hcover : ∀ y : ℝ, ∃ k : Fin N, ∃ j : ℤ, |x k - (j : ℝ) - y| ≤ rho) :
    1 / (2 * ((N : ℝ) + 1)) ≤ rho := by
  classical
  by_contra hn
  have hrho : rho < 1 / (2 * ((N : ℝ) + 1)) := lt_of_not_ge hn
  let Q : ℝ := (N : ℝ) + 1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hQ0 : Q ≠ 0 := ne_of_gt hQ
  have hsmall : 2 * rho * Q < 1 := by
    have h := (lt_div_iff₀ (show 0 < 2 * Q by positivity)).mp hrho
    nlinarith only [h]
  have hex : ∀ a : Fin (N + 1), ∃ k : Fin N, ∃ j : ℤ,
      |x k - (j : ℝ) - (a.val : ℝ) / Q| ≤ rho := by
    intro a
    exact hcover ((a.val : ℝ) / Q)
  choose k j hk using hex
  have hinj : Function.Injective k := by
    intro a b hab
    have ha := hk a
    have hb := hk b
    rw [hab] at ha
    have hdifference :
        |(x (k b) - (j b : ℝ) - (b.val : ℝ) / Q) -
          (x (k b) - (j a : ℝ) - (a.val : ℝ) / Q)| ≤ 2 * rho := by
      apply abs_le.mpr
      constructor
      · linarith [(abs_le.mp hb).1, (abs_le.mp ha).2]
      · linarith [(abs_le.mp hb).2, (abs_le.mp ha).1]
    have hid :
        (a.val : ℝ) - (b.val : ℝ) - ((j b - j a : ℤ) : ℝ) * Q =
          ((x (k b) - (j b : ℝ) - (b.val : ℝ) / Q) -
            (x (k b) - (j a : ℝ) - (a.val : ℝ) / Q)) * Q := by
      push_cast
      simp only [sub_mul, div_mul_cancel₀ (a.val : ℝ) hQ0,
        div_mul_cancel₀ (b.val : ℝ) hQ0]
      ring
    have hnear :
        |(a.val : ℝ) - (b.val : ℝ) - ((j b - j a : ℤ) : ℝ) * Q| < 1 := by
      calc
        _ = |(x (k b) - (j b : ℝ) - (b.val : ℝ) / Q) -
            (x (k b) - (j a : ℝ) - (a.val : ℝ) / Q)| * Q := by
          rw [hid, abs_mul, abs_of_pos hQ]
        _ ≤ (2 * rho) * Q :=
          mul_le_mul_of_nonneg_right hdifference (le_of_lt hQ)
        _ < 1 := hsmall
    have hgrid : |((a.val : ℤ) : ℝ) - ((b.val : ℤ) : ℝ) -
        ((j b - j a : ℤ) : ℝ) * (((N + 1 : ℕ) : ℤ) : ℝ)| < 1 := by
      simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_one,
        Int.cast_add, Int.cast_one, Q] using hnear
    have heq := integer_grid_residues_eq_of_abs_lt_one
      ((N + 1 : ℕ) : ℤ) (a.val : ℤ) (b.val : ℤ) (j b - j a)
      (by omega) (by positivity) (by exact_mod_cast a.isLt)
      (by positivity) (by exact_mod_cast b.isLt) hgrid
    apply Fin.ext
    exact_mod_cast heq
  have hcard : N + 1 ≤ N := Fin.le_of_injective k hinj
  omega

/-- A universal, nonsharp positive lower bound. No irrationality or
rational approximation hypothesis is needed. The M=0 case is excluded. -/
theorem finiteOrbitCoveringRadius_card_lower_bound
    (alpha : ℝ) (M : ℕ) (hM : 0 < M) :
    1 / (2 * ((M : ℝ) + 1)) ≤ finiteOrbitCoveringRadius alpha M := by
  unfold finiteOrbitCoveringRadius
  refine le_csInf ⟨1, finiteOrbitCovers_one alpha M hM⟩ ?_
  intro rho hcover
  apply finite_phase_covering_lower_bound M (fun k => (k.val : ℝ) * alpha) rho
  intro y
  obtain ⟨k, j, hk0, hkM, hdist⟩ := hcover y
  have hknat : k.toNat < M := by omega
  have hkcast : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk0
  refine ⟨⟨k.toNat, hknat⟩, j, ?_⟩
  change |(k.toNat : ℝ) * alpha - (j : ℝ) - y| ≤ rho
  simpa only [hkcast] using hdist

/-- Every nonempty finite orbit has strictly positive covering radius. -/
theorem finiteOrbitCoveringRadius_pos
    (alpha : ℝ) (M : ℕ) (hM : 0 < M) :
    0 < finiteOrbitCoveringRadius alpha M := by
  exact lt_of_lt_of_le (by positivity)
    (finiteOrbitCoveringRadius_card_lower_bound alpha M hM)

/-- For 2*B+1 signed indices, the elementary lower bound is 1/(4*(B+1)). -/
theorem signedOrbitCoveringRadius_card_lower_bound
    (alpha : ℝ) (B : ℕ) :
    1 / (4 * ((B : ℝ) + 1)) ≤ signedOrbitCoveringRadius alpha B := by
  rw [signedOrbitCoveringRadius_eq_finite]
  have h := finiteOrbitCoveringRadius_card_lower_bound alpha (2 * B + 1) (by omega)
  have hden : 2 * (((2 * B + 1 : ℕ) : ℝ) + 1) = 4 * ((B : ℝ) + 1) := by
    push_cast
    ring
  rwa [hden] at h

/-- Signed-orbit positivity includes the singleton case B=0. -/
theorem signedOrbitCoveringRadius_pos (alpha : ℝ) (B : ℕ) :
    0 < signedOrbitCoveringRadius alpha B := by
  exact lt_of_lt_of_le (by positivity)
    (signedOrbitCoveringRadius_card_lower_bound alpha B)

/-- The natural floor is used only under hQ>0 and H>=0 in the results below. -/
noncomputable def quadraticHeightCutoff (hQ H : ℝ) : ℕ :=
  Nat.floor (Real.sqrt (H / hQ))

/-- The floor-of-square-root cutoff belongs to exactly the correct half-open
height window, including the boundary H=0. -/
theorem quadraticHeightCutoff_spec
    (hQ H : ℝ) (hhQ : 0 < hQ) (hH : 0 ≤ H) :
    hQ * (quadraticHeightCutoff hQ H : ℝ) ^ 2 ≤ H ∧
      H < hQ * ((quadraticHeightCutoff hQ H : ℝ) + 1) ^ 2 := by
  let B := quadraticHeightCutoff hQ H
  have hx : 0 ≤ Real.sqrt (H / hQ) := Real.sqrt_nonneg _
  have hB : (0 : ℝ) ≤ (B : ℝ) := by positivity
  have hlo : (B : ℝ) ≤ Real.sqrt (H / hQ) := Nat.floor_le hx
  have hhi : Real.sqrt (H / hQ) < (B : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsq : (Real.sqrt (H / hQ)) ^ 2 = H / hQ :=
    Real.sq_sqrt (div_nonneg hH (le_of_lt hhQ))
  have hloSq : (B : ℝ) ^ 2 ≤ (Real.sqrt (H / hQ)) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hlo) (add_nonneg hx hB)
    nlinarith only [hp]
  have hhiSq : (Real.sqrt (H / hQ)) ^ 2 < ((B : ℝ) + 1) ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hhi)
      (show 0 < (B : ℝ) + 1 + Real.sqrt (H / hQ) by positivity)
    nlinarith only [hp]
  have hid : hQ * (H / hQ) = H := by
    field_simp [ne_of_gt hhQ]
  constructor
  · change hQ * (B : ℝ) ^ 2 ≤ H
    calc
      _ ≤ hQ * (Real.sqrt (H / hQ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hloSq (le_of_lt hhQ)
      _ = H := by rw [hsq, hid]
  · change H < hQ * ((B : ℝ) + 1) ^ 2
    calc
      H = hQ * (Real.sqrt (H / hQ)) ^ 2 := by rw [hsq, hid]
      _ < _ := mul_lt_mul_of_pos_left hhiSq hhQ

/-- Exact index membership with no separately supplied height-window witness. -/
theorem quadratic_height_cutoff_floor_iff
    (hQ H : ℝ) (k : ℤ) (hhQ : 0 < hQ) (hH : 0 ≤ H) :
    hQ * (k : ℝ) ^ 2 ≤ H ↔
      -(quadraticHeightCutoff hQ H : ℤ) ≤ k ∧ k ≤ (quadraticHeightCutoff hQ H : ℤ) := by
  obtain ⟨hlo, hhi⟩ := quadraticHeightCutoff_spec hQ H hhQ hH
  exact quadratic_height_cutoff_iff hQ H (quadraticHeightCutoff hQ H) k hhQ hlo hhi

/-- Global-in-height version of the validated exact finite-orbit bridge. -/
theorem quadraticHeightCoveringRadius_eq_finite_floor
    (alpha hQ H : ℝ) (hhQ : 0 < hQ) (hH : 0 ≤ H) :
    quadraticHeightCoveringRadius alpha hQ H =
      finiteOrbitCoveringRadius alpha (2 * quadraticHeightCutoff hQ H + 1) := by
  obtain ⟨hlo, hhi⟩ := quadraticHeightCutoff_spec hQ H hhQ hH
  exact quadraticHeightCoveringRadius_eq_finite alpha hQ H
    (quadraticHeightCutoff hQ H) hhQ hlo hhi

/-- Explicit elementary lower bound at every nonnegative real height. -/
theorem quadraticHeightCoveringRadius_card_lower_bound
    (alpha hQ H : ℝ) (hhQ : 0 < hQ) (hH : 0 ≤ H) :
    1 / (4 * ((quadraticHeightCutoff hQ H : ℝ) + 1)) ≤
      quadraticHeightCoveringRadius alpha hQ H := by
  obtain ⟨hlo, hhi⟩ := quadraticHeightCutoff_spec hQ H hhQ hH
  rw [quadraticHeightCoveringRadius_eq_signed alpha hQ H
    (quadraticHeightCutoff hQ H) hhQ hlo hhi]
  exact signedOrbitCoveringRadius_card_lower_bound alpha (quadraticHeightCutoff hQ H)

/-- Positivity is proved from hQ>0 and finiteness, not from irrationality. -/
theorem quadraticHeightCoveringRadius_pos
    (alpha hQ H : ℝ) (hhQ : 0 < hQ) (hH : 0 ≤ H) :
    0 < quadraticHeightCoveringRadius alpha hQ H := by
  exact lt_of_lt_of_le (by positivity)
    (quadraticHeightCoveringRadius_card_lower_bound alpha hQ H hhQ hH)

/-- The positivity hypothesis needed by the limsup bridge is now discharged. -/
theorem quadraticHeightCoveringRadius_eventually_pos
    (alpha hQ : ℝ) (hhQ : 0 < hQ) :
    ∀ᶠ H : ℝ in Filter.atTop, 0 < quadraticHeightCoveringRadius alpha hQ H := by
  apply Filter.eventually_atTop.mpr
  exact ⟨0, fun H hH => quadraticHeightCoveringRadius_pos alpha hQ H hhQ hH⟩

/-- Exact logarithmic envelope versus genuine limsup, with positivity derived. -/
theorem quadraticHeight_exactLogPowerEnvelope_iff_limsup
    (alpha hQ b ell : ℝ) (hhQ : 0 < hQ) :
    ExactLogPowerEnvelope (fun H => quadraticHeightCoveringRadius alpha hQ H) b ell ↔
      logPowerLimsup (fun H => quadraticHeightCoveringRadius alpha hQ H) b = (ell : EReal) := by
  exact exactLogPowerEnvelope_iff_logPowerLimsup_eq
    (fun H => quadraticHeightCoveringRadius alpha hQ H) b ell
    (quadraticHeightCoveringRadius_eventually_pos alpha hQ hhQ)

/-- At each nonnegative height, the ambient radius is positive under the
same inclusion and multiplication hypotheses as the finite-index sandwich. -/
theorem finite_index_circleSetCoveringRadius_pos
    (alpha hQ H : ℝ) (d : ℕ) (ambient : ℝ → Set ℝ)
    (hhQ : 0 < hQ) (hd : 0 < d) (hH : 0 ≤ H)
    (hinclude : ∀ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H →
      ∃ x ∈ ambient H, ∃ j : ℤ, x = (k : ℝ) * alpha + (j : ℝ))
    (hmultiply : ∀ x ∈ ambient H, ∃ k j : ℤ,
      hQ * (k : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * H ∧
      (k : ℝ) * alpha = (d : ℝ) * x + (j : ℝ)) :
    0 < circleSetCoveringRadius (ambient H) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hp := quadraticHeightCoveringRadius_pos alpha hQ ((d : ℝ) ^ 2 * H)
    hhQ (mul_nonneg (sq_nonneg _) hH)
  exact lt_of_lt_of_le (div_pos hp hdR)
    (finite_index_height_covering_sandwich alpha hQ H d ambient hd hH
      hinclude hmultiply).1

/-- Finite-index equality of EReal limsups with no separate eventual-positivity
assumption. The arithmetic transfer hypotheses are still uniform in height. -/
theorem finite_index_logPowerLimsup_eq_of_pos_height
    (alpha hQ b : ℝ) (d : ℕ) (ambient : ℝ → Set ℝ)
    (hhQ : 0 < hQ) (hd : 0 < d)
    (hinclude : ∀ H : ℝ, 0 ≤ H → ∀ k : ℤ, hQ * (k : ℝ) ^ 2 ≤ H →
      ∃ x ∈ ambient H, ∃ j : ℤ, x = (k : ℝ) * alpha + (j : ℝ))
    (hmultiply : ∀ H : ℝ, 0 ≤ H → ∀ x ∈ ambient H, ∃ k j : ℤ,
      hQ * (k : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * H ∧
      (k : ℝ) * alpha = (d : ℝ) * x + (j : ℝ)) :
    logPowerLimsup (fun H => quadraticHeightCoveringRadius alpha hQ H) b =
      logPowerLimsup (fun H => circleSetCoveringRadius (ambient H)) b := by
  exact finite_index_logPowerLimsup_eq alpha hQ b d ambient hd hinclude hmultiply
    (quadraticHeightCoveringRadius_eventually_pos alpha hQ hhQ)

/-- The explicit rank-one-plus-torsion model now needs only h0>0 for
positivity. No identification with an actual Mordell-Weil group is asserted. -/
theorem torsion_extension_logPowerLimsup_eq_of_pos_height
    (beta h0 b : ℝ) (m t : ℕ) (hh0 : 0 < h0) (hm : 0 < m) (ht : 0 < t) :
    logPowerLimsup
        (fun H => quadraticHeightCoveringRadius ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0) H) b =
      logPowerLimsup
        (fun H => circleSetCoveringRadius (torsionExtendedPhases beta h0 H t)) b := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  exact torsion_extension_logPowerLimsup_eq beta h0 b m t hm ht
    (quadraticHeightCoveringRadius_eventually_pos ((m : ℝ) * beta) ((m : ℝ) ^ 2 * h0)
      (mul_pos (sq_pos_of_pos hmR) hh0))

#print axioms integer_grid_residues_eq_of_abs_lt_one
#print axioms finite_phase_covering_lower_bound
#print axioms finiteOrbitCoveringRadius_card_lower_bound
#print axioms finiteOrbitCoveringRadius_pos
#print axioms signedOrbitCoveringRadius_card_lower_bound
#print axioms signedOrbitCoveringRadius_pos
#print axioms quadraticHeightCutoff_spec
#print axioms quadratic_height_cutoff_floor_iff
#print axioms quadraticHeightCoveringRadius_eq_finite_floor
#print axioms quadraticHeightCoveringRadius_card_lower_bound
#print axioms quadraticHeightCoveringRadius_pos
#print axioms quadraticHeightCoveringRadius_eventually_pos
#print axioms quadraticHeight_exactLogPowerEnvelope_iff_limsup
#print axioms finite_index_circleSetCoveringRadius_pos
#print axioms finite_index_logPowerLimsup_eq_of_pos_height
#print axioms torsion_extension_logPowerLimsup_eq_of_pos_height

end AbelianLog
