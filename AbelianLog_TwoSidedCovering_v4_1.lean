import Mathlib

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
    field_simp [hq0] <;> ring
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
      field_simp [hq0] <;> ring
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
