import PowerConvexity.Analysis.ActualCompactJointPhysicalChartsFour
import PowerConvexity.Analysis.ActualCommonNonlinearBoundaryGeometryFour

/-! # Constructing common nonlinear boundary geometry from actual joint data

One true jointly C4 defining function, the compact actual closure and boundary
graphs, and the actual inner/outer balls supply every field of the quantitative
moving-domain geometry. No solution derivative modulus occurs in the input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
local instance ajcbgTripleGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ajcbgTripleSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance ajcbgTripleModule : Module ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance ajcbgTripleTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.toNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem actual_joint_common_boundary_geometry_four
    {V : ℝ → Set E}
    (hgeometry : ∀ t ∈ Icc (0 : ℝ) 1,
      IsOpen (V t) ∧ Convex ℝ (V t) ∧ IsCompact (closure (V t)))
    (hclosure : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    (hfrontier : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)})
    {s d rho0 Dout : ℝ} (hd : 0 < d)
    (hinner : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (0 : E) rho0 ⊆ V t)
    (houter : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closure (V t), ‖x‖ ≤ Dout)
    {f : ℝ × E → ℝ} (hf : ContDiffOn ℝ 4 f (ball s (2*d) ×ˢ (univ : Set E)))
    (hfb : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ frontier (V t),
      f (t,x)=0 ∧ fderiv ℝ (fun y => f (t,y)) x≠0 ∧
      (∀ᶠ q in 𝓝 (t,x), q.1 ∈ Icc (0 : ℝ) 1 → (q.2 ∈ V q.1 ↔ f q<0))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ Hchart > 0, ∃ F > 0, ∃ delta > 0,
      ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∃ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
        Geo.domain=V t ∧ Geo.defining=(fun x => f (t,x)) := by
  let Kc : Set (ℝ × E) :=
    {q | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)} ∩ Prod.fst ⁻¹' closedBall s d
  let Kb : Set (ℝ × E) :=
    {q | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)} ∩ Prod.fst ⁻¹' closedBall s d
  let S : Set ℝ := closedBall s d ∩ Icc (0 : ℝ) 1
  have hKc : IsCompact Kc := hclosure.inter_right (isClosed_closedBall.preimage continuous_fst)
  have hKb : IsCompact Kb := hfrontier.inter_right (isClosed_closedBall.preimage continuous_fst)
  have hC3 (q : ℝ × E) (hq : q.1 ∈ closedBall s d) : ContDiffAt ℝ 3 f q :=
    (hf.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      ⟨closedBall_subset_ball (by linarith : d < 2*d) hq,mem_univ q.2⟩)).of_le (by norm_num)
  have hDc (q : ℝ × E) (hq : q.1 ∈ closedBall s d) : ContDiffAt ℝ 2
      (fun p : ℝ × E => fderiv ℝ (fun y => f (p.1,y)) p.2) q :=
    parameter_fiber_fderiv_contDiffAt (n := 2) (hC3 q hq)
  have hHc (q : ℝ × E) (hq : q.1 ∈ closedBall s d) : ContDiffAt ℝ 1
      (fun p : ℝ × E => realHessian (fun y => f (p.1,y)) p.2) q :=
    parameter_fiber_fderiv_contDiffAt (n := 1) (hDc q hq)
  have hTc (q : ℝ × E) (hq : q.1 ∈ closedBall s d) : ContDiffAt ℝ 0
      (fun p : ℝ × E => fderiv ℝ (realHessian (fun y => f (p.1,y))) p.2) q :=
    parameter_fiber_fderiv_contDiffAt (n := 0) (hHc q hq)
  have hDcont : ContinuousOn (fun q : ℝ × E => fderiv ℝ (fun y => f (q.1,y)) q.2) Kc :=
    fun q hq => (hDc q hq.2).continuousAt.continuousWithinAt
  have hHcont : ContinuousOn (fun q : ℝ × E => realHessian (fun y => f (q.1,y)) q.2) Kc :=
    fun q hq => (hHc q hq.2).continuousAt.continuousWithinAt
  have hTcont : ContinuousOn
      (fun q : ℝ × E => fderiv ℝ (realHessian (fun y => f (q.1,y))) q.2) Kc :=
    fun q hq => (hTc q hq.2).continuousAt.continuousWithinAt
  obtain ⟨B1,hB1⟩ := (hKc.image_of_continuousOn hDcont).isBounded.exists_norm_le
  obtain ⟨B2,hB2⟩ := (hKc.image_of_continuousOn hHcont).isBounded.exists_norm_le
  obtain ⟨B3,hB3⟩ := (hKc.image_of_continuousOn hTcont).isBounded.exists_norm_le
  let F := |B1|+|B2|+|B3|+1
  have hF : 0 < F := by dsimp only [F]; positivity
  have hB1F : B1 ≤ F := by dsimp only [F]; linarith [le_abs_self B1,abs_nonneg B2,abs_nonneg B3]
  have hB2F : B2 ≤ F := by dsimp only [F]; linarith [le_abs_self B2,abs_nonneg B1,abs_nonneg B3]
  have hB3F : B3 ≤ F := by dsimp only [F]; linarith [le_abs_self B3,abs_nonneg B1,abs_nonneg B2]
  have hDncont : ContinuousOn (fun q : ℝ × E => ‖fderiv ℝ (fun y => f (q.1,y)) q.2‖) Kb :=
    fun q hq => (hDc q hq.2).continuousAt.norm.continuousWithinAt
  have hDn (q : ℝ × E) (hq : q ∈ Kb) : 0 < ‖fderiv ℝ (fun y => f (q.1,y)) q.2‖ :=
    norm_pos_iff.mpr (hfb q.1 hq.2 hq.1.1 q.2 hq.1.2).2.1
  obtain ⟨delta,hdelta,hmargin⟩ := hKb.exists_forall_le' hDncont hDn
  obtain ⟨r,hr,hr1,Hchart,hHchart,hcharts⟩ := actual_compact_joint_unit_boundary_charts_four
    (V := V) (S := S) hKb
    (fun t ht x hx => ⟨⟨ht.2,hx⟩,ht.1⟩)
    (fun q hq => hC3 q hq.2)
    (fun q hq => (hfb q.1 hq.2 hq.1.1 q.2 hq.1.2).1)
    (fun q hq => (hfb q.1 hq.2 hq.1.1 q.2 hq.1.2).2.1)
    (fun q hq => ((hfb q.1 hq.2 hq.1.1 q.2 hq.1.2).2.2).mono
      (fun _ hp ht => hp ht.2))
  refine ⟨r,hr,hr1,Hchart,hHchart,F,hF,delta,hdelta,?_⟩
  intro t ht hI
  have hreg : ContDiff ℝ 3 (fun x => f (t,x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hC3 (t,x) ht).comp x (contDiffAt_const.prodMk contDiffAt_id)
  let Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout := {
    domain := V t
    defining := fun x => f (t,x)
    isOpen := (hgeometry t hI).1
    convex := (hgeometry t hI).2.1
    compactClosure := (hgeometry t hI).2.2
    charts := hcharts t ⟨ht,hI⟩
    regular := hreg
    boundary := fun x hx => ⟨(hfb t ht hI x hx).1,(hfb t ht hI x hx).2.1⟩
    side := by
      intro x hx
      have hin : Tendsto (fun y : E => (t,y)) (𝓝 x) (𝓝 (t,x)) :=
        (continuousAt_const.prodMk continuousAt_id).tendsto
      filter_upwards [hin.eventually (hfb t ht hI x hx).2.2] with y hy
      exact hy hI
    firstBound := fun x hx => (hB1 _ (mem_image_of_mem _ (show (t,x) ∈ Kc from ⟨⟨hI,hx⟩,ht⟩))).trans hB1F
    secondBound := fun x hx => (hB2 _ (mem_image_of_mem _ (show (t,x) ∈ Kc from ⟨⟨hI,hx⟩,ht⟩))).trans hB2F
    thirdBound := fun x hx => (hB3 _ (mem_image_of_mem _ (show (t,x) ∈ Kc from ⟨⟨hI,hx⟩,ht⟩))).trans hB3F
    normalMargin := fun x hx => hmargin (t,x) ⟨⟨hI,hx⟩,ht⟩
    center := 0
    innerBall := hinner t hI
    boundaryRadius := fun c hc => by simpa only [zero_sub,norm_neg] using houter t hI c (frontier_subset_closure hc)
  }
  exact ⟨Geo,rfl,rfl⟩

end PowerConvexity
