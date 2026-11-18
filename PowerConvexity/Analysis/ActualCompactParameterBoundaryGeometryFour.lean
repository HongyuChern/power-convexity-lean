import PowerConvexity.Analysis.ActualJointCommonBoundaryGeometryFour
import PowerConvexity.Analysis.ActualCommonBoundaryGeometryMonotoneFour
import PowerConvexity.Analysis.CompactLocalMonotoneBounds

/-! # One genuine geometric scale before the entire compact parameter interval

Actual local charts are rescaled, not reused at a different physical radius.
This permits compactness to choose one common radius, graph and defining-jet
bound, and positive normal margin for all actual domains in the family.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_compact_parameter_common_geometry_of_local_four
    {V : ℝ → Set E} {rho0 Dout : ℝ}
    (hlocal : ∀ s ∈ Icc (0 : ℝ) 1,
      ∃ d > 0, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ Hchart > 0, ∃ F > 0, ∃ delta > 0,
        ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
        ∃ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
          Geo.domain=V t) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ Hchart > 0, ∃ F > 0, ∃ delta > 0,
      ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
        Geo.domain=V t := by
  let P : ℝ → ℝ → Prop := fun t B => 0 ≤ B ∧
    (t ∈ Icc (0 : ℝ) 1 →
      ∃ Geo : ActualCommonNonlinearBoundaryGeometryFour (1/(B+1)) (B+1) (B+1) (1/(B+1)) rho0 Dout,
        Geo.domain=V t)
  have hmono : ∀ t a b, a ≤ b → P t a → P t b := by
    intro t a b hab hpa
    have hb : 0 ≤ b := hpa.1.trans hab
    refine ⟨hb,?_⟩
    intro ht
    obtain ⟨Geo,hGeo⟩ := hpa.2 ht
    have hrad : 1/(b+1) ≤ 1/(a+1) :=
      one_div_le_one_div_of_le (by linarith [hpa.1]) (by linarith)
    exact ⟨Geo.enlarge (by positivity) hrad (by linarith [hpa.1])
      (by linarith) (by linarith) hrad le_rfl,hGeo⟩
  have hnear : ∀ s ∈ Icc (0 : ℝ) 1, ∃ B ≥ 0, ∀ᶠ t in 𝓝 s, P t B := by
    intro s hs
    obtain ⟨d,hd,r,hr,_,Hchart,hHchart,F,hF,delta,hdelta,hGeo⟩ := hlocal s hs
    let B := max Hchart (max F (max (1/r) (1/delta)))
    have hHB : Hchart ≤ B := le_max_left _ _
    have hFB : F ≤ B := (le_max_left _ _).trans (le_max_right _ _)
    have hrB : 1/r ≤ B := (le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
    have hdB : 1/delta ≤ B := (le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
    have hB : 0 ≤ B := hHchart.le.trans hHB
    have hrad : 1/(B+1) ≤ r := by
      apply (div_le_iff₀ (by linarith : 0 < B+1)).mpr
      have hh := (div_le_iff₀ hr).mp hrB
      nlinarith
    have hmargin : 1/(B+1) ≤ delta := by
      apply (div_le_iff₀ (by linarith : 0 < B+1)).mpr
      have hh := (div_le_iff₀ hdelta).mp hdB
      nlinarith
    refine ⟨B,hB,?_⟩
    filter_upwards [ball_mem_nhds s hd] with t ht
    refine ⟨hB,?_⟩
    intro hI
    obtain ⟨Geo,hG⟩ := hGeo t (ball_subset_closedBall ht) hI
    exact ⟨Geo.enlarge (by positivity) hrad hHchart.le
      (by linarith) (by linarith) hmargin le_rfl,hG⟩
  obtain ⟨B,hB,hall⟩ := compact_uniform_monotone_bound_of_local isCompact_Icc P hmono hnear
  have hr : 0 < 1/(B+1) := by positivity
  refine ⟨1/(B+1),hr,?_,B+1,by positivity,B+1,by positivity,1/(B+1),hr,?_⟩
  · exact (div_le_one (by linarith : 0 < B+1)).mpr (by linarith)
  · intro t ht
    exact (hall t ht).2 ht

theorem actual_compact_joint_common_boundary_geometry_four
    {V : ℝ → Set E}
    (hgeometry : ∀ t ∈ Icc (0 : ℝ) 1,
      IsOpen (V t) ∧ Convex ℝ (V t) ∧ IsCompact (closure (V t)))
    (hclosure : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    (hfrontier : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)})
    {rho0 Dout : ℝ}
    (hinner : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (0 : E) rho0 ⊆ V t)
    (houter : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closure (V t), ‖x‖ ≤ Dout)
    (hjoint : ∀ s ∈ Icc (0 : ℝ) 1, ∃ d > 0, ∃ f : ℝ × E → ℝ,
      ContDiffOn ℝ 4 f (ball s (2*d) ×ˢ (univ : Set E)) ∧
      ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ frontier (V t),
        f (t,x)=0 ∧ fderiv ℝ (fun y => f (t,y)) x≠0 ∧
        (∀ᶠ q in 𝓝 (t,x), q.1 ∈ Icc (0 : ℝ) 1 → (q.2 ∈ V q.1 ↔ f q<0))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ Hchart > 0, ∃ F > 0, ∃ delta > 0,
      ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ Geo : ActualCommonNonlinearBoundaryGeometryFour r Hchart F delta rho0 Dout,
        Geo.domain=V t := by
  apply actual_compact_parameter_common_geometry_of_local_four
  intro s hs
  obtain ⟨d,hd,f,hf,hfb⟩ := hjoint s hs
  obtain ⟨r,hr,hr1,Hchart,hHchart,F,hF,delta,hdelta,hGeo⟩ :=
    actual_joint_common_boundary_geometry_four hgeometry hclosure hfrontier hd hinner houter hf hfb
  refine ⟨d,hd,r,hr,hr1,Hchart,hHchart,F,hF,delta,hdelta,?_⟩
  intro t ht hI
  obtain ⟨Geo,hG,_⟩ := hGeo t ht hI
  exact ⟨Geo,hG⟩

end PowerConvexity
