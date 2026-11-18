import PowerConvexity.Analysis.ActualFlatDriftPerturbationDataFour
import PowerConvexity.Calculus.ActualFlatPrescribedHolderTaylorFour
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Actual boundary improvement at a prescribed Holder exponent -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_prescribed_holder_quadratic_improvement_four
    {lam Lambda : ℝ} (hlam : 0 < lam) (hLambda : 0 < Lambda) :
    ∃ M > 0, ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
      ∀ eta > 0, ∀ Rmax > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r ≤ Rmax ∧
      r^alpha ≤ (1/2 : ℝ) ∧
      ∀ N : E, ‖N‖=1 → ∃ delta > 0, delta ≤ 1 ∧
      ∀ D : ActualFlatDriftPerturbationDataFour N lam Lambda delta,
      ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
        (∀ x : E, inner ℝ N x=0 → q x=0) ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace=0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ x ∈ actualFlatClosedUpperBallFour N r, |D.solution x-q x| ≤ eta*r^alpha*r^2 := by
  classical
  obtain ⟨M,hM,happrox⟩ := actual_harmonic_flat_prescribed_holder_taylor_four
  refine ⟨M,hM,?_⟩
  intro alpha halpha halpha1 eta heta Rmax hRmax
  obtain ⟨r,hr,hr8,hrmax,hrpow,ha⟩ :=
    happrox alpha halpha halpha1 (eta/2) (half_pos heta) Rmax hRmax
  refine ⟨r,hr,hr8,hrmax,hrpow,?_⟩
  intro N hN
  let Q : (E → ℝ) → Prop := fun u => ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
    (∀ x : E, inner ℝ N x=0 → q x=0) ∧
    (∀ x, (realBlockHessian realDirections imagDirections q x).trace=0) ∧
    (∀ x, ‖realHessian q x‖ ≤ M) ∧
    ∀ x ∈ actualFlatClosedUpperBallFour N r, |u x-q x| ≤ eta*r^alpha*r^2
  change ∃ delta > 0, delta ≤ 1 ∧ ∀ D : ActualFlatDriftPerturbationDataFour N lam Lambda delta, Q D.solution
  by_contra hnone
  have hcounter (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1) :
      ∃ D : ActualFlatDriftPerturbationDataFour N lam Lambda delta, ¬ Q D.solution := by
    by_contra hn
    apply hnone
    refine ⟨delta,hd,hd1,?_⟩
    intro D
    by_contra hq
    exact hn ⟨D,hq⟩
  let K := 3*(4*(Lambda/lam)+(1/lam)/4+1)+3
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let B := min 1 (lam/(K+1))
  have hB : 0 < B := lt_min (by norm_num) (div_pos hlam (by positivity))
  have hB1 : B ≤ 1 := min_le_left _ _
  have hsmall : K*(B/lam) ≤ 2 := by
    have hh : B*(K+1) ≤ lam := (le_div_iff₀ (by positivity : 0 < K+1)).mp (min_le_right 1 (lam/(K+1)))
    have hb : K*B ≤ lam := by nlinarith
    calc
      K*(B/lam)=(K*B)/lam := by ring
      _ ≤ 1 := (div_le_one hlam).mpr hb
      _ ≤ 2 := by norm_num
  let eps : ℕ → ℝ := fun n => B*(1/((n : ℝ)+1))
  have hepspos (n : ℕ) : 0 < eps n := by dsimp only [eps]; positivity
  have hepsB (n : ℕ) : eps n ≤ B := by
    have hh : (1 : ℝ)/((n : ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact (mul_le_mul_of_nonneg_left hh hB.le).trans_eq (mul_one B)
  have heps1 (n : ℕ) : eps n ≤ 1 := (hepsB n).trans hB1
  have heps0 : Tendsto eps atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul B
  choose D hnot using (fun n : ℕ => hcounter (eps n) (hepspos n) (heps1 n))
  have hcoeff (i j : Fin (2+2)) : TendstoUniformlyOn (fun n x => (D n).coeff.a x i j)
      (fun _ => (1 : Mat) i j) atTop (actualFlatUpperBallFour N 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro tau htau
    filter_upwards [heps0 (Iio_mem_nhds htau)] with n hn x hx
    have hh := ((D n).near_identity x hx i j).trans_lt hn
    simpa only [Real.dist_eq,abs_sub_comm] using hh
  have hbd : TendstoUniformlyOn (fun n => (D n).drift) (fun _ => 0) atTop (actualFlatUpperBallFour N 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro tau htau
    filter_upwards [heps0 (Iio_mem_nhds htau)] with n hn x hx
    simpa only [dist_zero_left] using ((D n).drift_bound x hx).trans_lt hn
  obtain ⟨phi,hphi,g,hgc,hunif,hgH,hgb,hg0⟩ := actual_flat_drift_harmonic_subsequence_four hN
    (fun n => (D n).coeff) hlam (fun n => (D n).lower) (fun n => (D n).upper)
    hB.le (by norm_num : (0 : ℝ) ≤ 1) hsmall
    (fun n => (D n).positive) (fun n => (D n).regular) (fun n => (D n).drift)
    (fun n => (D n).drift_continuous) (fun n => (D n).divergence)
    (fun n x hx => ((D n).drift_bound x hx).trans (hepsB n))
    (fun n => (D n).source) (fun n => (D n).solution) (fun n => (D n).source_continuous)
    (fun n => (D n).solution_regular) (fun n => (D n).solution_continuous)
    (fun n => (D n).solution_zero) (fun n => (D n).solution_bound)
    (fun n x hx => ((D n).source_bound x hx).trans (heps1 n))
    (fun n => (D n).equation) hcoeff hbd heps0 (fun n => (D n).source_bound)
  obtain ⟨q,hq,hq0,hqt,hqH,hqa⟩ := ha N hN g hgc hgH
    (fun x hx hx0 => hg0 x ⟨hx,hx0.ge⟩ hx0) hgb
  have htol : 0 < (eta/2)*r^alpha*r^2 := mul_pos (mul_pos (half_pos heta) (Real.rpow_pos_of_pos hr _)) (sq_pos_of_pos hr)
  obtain ⟨k,hk⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hunif) _ htol)
  apply hnot (phi k)
  refine ⟨q,hq,hq0,hqt,hqH,?_⟩
  intro x hx
  have hxC : x ∈ actualFlatClosedUpperBallFour N (1/2) :=
    ⟨closedBall_subset_closedBall (hr8.trans (by norm_num)) hx.1,hx.2⟩
  have he : |(D (phi k)).solution x-g x| ≤ (eta/2)*r^alpha*r^2 := by
    simpa only [Real.dist_eq,abs_sub_comm] using (hk k le_rfl x hxC).le
  calc
    |(D (phi k)).solution x-q x| ≤ |(D (phi k)).solution x-g x|+|g x-q x| := by
      simpa only [sub_add_sub_cancel] using abs_add_le ((D (phi k)).solution x-g x) (g x-q x)
    _ ≤ (eta/2)*r^alpha*r^2+(eta/2)*r^alpha*r^2 := add_le_add he (hqa x hx)
    _ = eta*r^alpha*r^2 := by ring

end PowerConvexity
