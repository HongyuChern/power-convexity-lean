import PowerConvexity.Analysis.ActualGraphShearFluxFour

/-! # A genuine physical scale makes the chart drift small -/
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

theorem actual_small_scale_operator_drift_four {A : E → (E →L[ℝ] E)} {b : E → E}
    (hA : ContinuousAt A 0) (hAI : A 0=ContinuousLinearMap.id ℝ E) (hb : ContinuousAt b 0)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ r > 0, r ≤ 1 ∧ ∀ z : E, ‖z‖ ≤ 1 →
      ‖A (r • z)-ContinuousLinearMap.id ℝ E‖ ≤ delta ∧ r*‖b (r • z)‖ ≤ delta := by
  have hnearA : ∀ᶠ y in 𝓝 (0 : E), ‖A y-ContinuousLinearMap.id ℝ E‖ < delta := by
    have hnorm : Tendsto (fun y => ‖A y-ContinuousLinearMap.id ℝ E‖) (𝓝 (0 : E)) (𝓝 0) := by
      have hc : ContinuousAt (fun y => A y-ContinuousLinearMap.id ℝ E) 0 :=
        hA.sub continuousAt_const
      simpa only [hAI,sub_self,norm_zero] using hc.norm.tendsto
    exact (tendsto_order.1 hnorm).2 delta hdelta
  have hnearB : ∀ᶠ y in 𝓝 (0 : E), ‖b y‖ < ‖b 0‖+1 :=
    (tendsto_order.1 hb.norm.tendsto).2 _ (by linarith)
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (hnearA.and hnearB)
  let K := ‖b 0‖+1
  have hK : 0 < K := by dsimp only [K]; positivity
  let r := min 1 (min (R/2) (delta/(2*K)))
  have hr : 0 < r := lt_min (by norm_num) (lt_min (half_pos hR) (div_pos hdelta (by positivity)))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrR : r ≤ R/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrD : r ≤ delta/(2*K) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,hr1,?_⟩
  intro z hz
  have hy : r • z ∈ ball (0 : E) R := by
    simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    have hh := mul_le_mul_of_nonneg_left hz hr.le
    nlinarith
  refine ⟨(hball hy).1.le,?_⟩
  have hbK : ‖b (r • z)‖ ≤ K := (hball hy).2.le
  have hmul : r*K ≤ delta/2 := by
    calc
      _ ≤ (delta/(2*K))*K := mul_le_mul_of_nonneg_right hrD hK.le
      _ = delta/2 := by field_simp
  exact (mul_le_mul_of_nonneg_left hbK hr.le).trans (hmul.trans (by linarith))

def actualGraphShearDriftFieldFour (N : E) (rho : E → ℝ) (a : E → Mat) (x : E) : E :=
  -(∑ k, ∑ l, a (actualGraphShearFour N rho x) l k*euclideanHessian rho x l k) • N

theorem actual_graph_shear_drift_field_continuousAt_four {N x : E} {rho : E → ℝ} {a : E → Mat}
    (hrho : ContDiffAt ℝ 2 rho x)
    (ha : ∀ i j, ContinuousAt (fun y => a y i j) (actualGraphShearFour N rho x)) :
    ContinuousAt (actualGraphShearDriftFieldFour N rho a) x := by
  have hH : ContinuousAt (realHessian rho) x :=
    ((hrho.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hPhi := (actual_graph_shear_contDiffAt_four (N := N) hrho).continuousAt
  change ContinuousAt ((fun y => -(∑ k, ∑ l, a (actualGraphShearFour N rho y) l k*euclideanHessian rho y l k)) • (fun _ : E => N)) x
  apply ContinuousAt.smul _ continuousAt_const
  apply ContinuousAt.neg
  apply tendsto_finsetSum
  intro k _
  apply tendsto_finsetSum
  intro l _
  exact ((ha l k).comp hPhi).mul ((hH.clm_apply continuousAt_const).clm_apply continuousAt_const)

end PowerConvexity
