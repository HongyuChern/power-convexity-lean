import PowerConvexity.Analysis.ActualFlatPerturbationDataFour
import PowerConvexity.Calculus.ActualFlatHalfRadiusTaylorFour
import Mathlib.Analysis.SpecificLimits.Basic

/-! # One actual boundary-compatible quadratic improvement
The smallness threshold is chosen before the actual coefficient, source and
solution. The polynomial vanishes on the entire fixed flat boundary.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_elliptic_quadratic_improvement_four
    {lam Lambda Ka Kf alpha : ℝ} (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (halpha : 0 < alpha) :
    ∃ M > 0, ∀ eta > 0, ∀ Rmax > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r ≤ Rmax ∧
      ∀ N : E, ‖N‖=1 → ∃ delta > 0, delta ≤ 1 ∧
      ∀ D : ActualFlatPerturbationDataFour N lam Lambda Ka Kf alpha delta,
      ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
        (∀ x : E, inner ℝ N x=0 → q x=0) ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace=0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ x ∈ actualFlatClosedUpperBallFour N r, |D.solution x-q x| ≤ eta*r^2 := by
  classical
  obtain ⟨M,hM,happrox⟩ := actual_harmonic_flat_half_boundary_quadratic_below_radius_four
  refine ⟨M,hM,?_⟩
  intro eta heta Rmax hRmax
  obtain ⟨r,hr,hr8,hrmax,ha⟩ := happrox (eta/2) (half_pos heta) Rmax hRmax
  refine ⟨r,hr,hr8,hrmax,?_⟩
  intro N hN
  let Q : (E → ℝ) → Prop := fun u => ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
    (∀ x : E, inner ℝ N x=0 → q x=0) ∧
    (∀ x, (realBlockHessian realDirections imagDirections q x).trace=0) ∧
    (∀ x, ‖realHessian q x‖ ≤ M) ∧
    ∀ x ∈ actualFlatClosedUpperBallFour N r, |u x-q x| ≤ eta*r^2
  change ∃ delta > 0, delta ≤ 1 ∧
    ∀ D : ActualFlatPerturbationDataFour N lam Lambda Ka Kf alpha delta, Q D.solution
  by_contra hnone
  have hcounter (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1) :
      ∃ D : ActualFlatPerturbationDataFour N lam Lambda Ka Kf alpha delta, ¬ Q D.solution := by
    by_contra hn
    apply hnone
    refine ⟨delta,hd,hd1,?_⟩
    intro D
    by_contra hq
    exact hn ⟨D,hq⟩
  let eps : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hepspos (n : ℕ) : 0 < eps n := by dsimp only [eps]; positivity
  have heps1 (n : ℕ) : eps n ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ)<(n : ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have heps0 : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose D hnot using (fun n : ℕ => hcounter (eps n) (hepspos n) (heps1 n))
  have hcoeff (i j : Fin (2+2)) : TendstoUniformlyOn (fun n x => (D n).coeff.a x i j)
      (fun _ => (1 : Mat) i j) atTop (actualFlatUpperBallFour N 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro tau htau
    filter_upwards [heps0 (Iio_mem_nhds htau)] with n hn x hx
    have hh := ((D n).near_identity x hx i j).trans_lt hn
    simpa only [Real.dist_eq,abs_sub_comm] using hh
  obtain ⟨phi,hphi,g,hgc,hunif,hgH,hgb,hg0⟩ :=
    actual_flat_elliptic_harmonic_subsequence_four hN hlam hLambda hKa hKf
      (by norm_num : (0 : ℝ) ≤ 1) halpha (fun n => (D n).coeff)
      (fun n => (D n).lower) (fun n => (D n).upper) (fun n => (D n).positive)
      (fun n => (D n).regular) (fun n => (D n).divergence) (fun n => (D n).holder)
      (fun n => (D n).source) (fun n => (D n).solution)
      (fun n => (D n).source_regular) (fun n => (D n).source_holder)
      (fun n x hx => ((D n).source_bound x hx).trans (heps1 n))
      (fun n => (D n).solution_regular) (fun n => (D n).solution_continuous)
      (fun n => (D n).solution_zero) (fun n => (D n).solution_bound)
      (fun n => (D n).equation) hcoeff heps0 (fun n => (D n).source_bound)
  obtain ⟨q,hq,hq0,hqt,hqH,hqa⟩ := ha N hN g hgc hgH
    (fun x hx hx0 => hg0 x ⟨hx,hx0.ge⟩ hx0) hgb
  have htol : 0 < (eta/2)*r^2 := mul_pos (half_pos heta) (sq_pos_of_pos hr)
  obtain ⟨k,hk⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hunif) _ htol)
  apply hnot (phi k)
  refine ⟨q,hq,hq0,hqt,hqH,?_⟩
  intro x hx
  have hxC : x ∈ actualFlatClosedUpperBallFour N (1/2) :=
    ⟨closedBall_subset_closedBall (hr8.trans (by norm_num)) hx.1,hx.2⟩
  have he : |(D (phi k)).solution x-g x| ≤ (eta/2)*r^2 := by
    simpa only [Real.dist_eq,abs_sub_comm] using (hk k le_rfl x hxC).le
  calc
    |(D (phi k)).solution x-q x| ≤ |(D (phi k)).solution x-g x|+|g x-q x| := by
      simpa only [sub_add_sub_cancel] using abs_add_le ((D (phi k)).solution x-g x) (g x-q x)
    _ ≤ (eta/2)*r^2+(eta/2)*r^2 := add_le_add he (hqa x hx)
    _ = eta*r^2 := by ring

end PowerConvexity
