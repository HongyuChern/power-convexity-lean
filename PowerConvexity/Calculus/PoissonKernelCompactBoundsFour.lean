import PowerConvexity.Calculus.PoissonMassFour
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Universal actual Hessian bounds and modulus for the Poisson kernel.
The compact product is the actual closed half unit ball times the actual
unit sphere. Constants and radii do not depend on boundary data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : E) 1
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE

theorem poissonKernelFour_hessian_continuousOn_halfBall_sphere :
    ContinuousOn (fun p : E × S => realHessian (poissonKernelFour p.2) p.1)
      (closedBall (0 : E) (1/2 : ℝ) ×ˢ univ) := by
  intro p hp
  have hx : p.1 ∈ ball (0 : E) 1 := by
    exact mem_ball.mpr ((mem_closedBall.mp hp.1).trans_lt (by norm_num))
  have hm : ContinuousAt (fun q : E × S => (q.1,(q.2 : E))) p :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt
  exact ((poissonKernelFour_hessian_joint_contDiffAt
    (z := (p.1,(p.2 : E))) (unitBall_point_ne_unitSphere_four hx p.2) 0).continuousAt.comp
      (f := fun q : E × S => (q.1,(q.2 : E))) hm).continuousWithinAt

theorem poissonKernelFour_hessian_universal_bound :
    ∃ M > 0, ∀ x ∈ closedBall (0 : E) (1/2 : ℝ), ∀ ξ : S,
      ‖realHessian (poissonKernelFour ξ) x‖ ≤ M := by
  have hK := (isCompact_closedBall (0 : E) (1/2 : ℝ)).prod
    (isCompact_univ : IsCompact (univ : Set S))
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun p : E × S => realHessian (poissonKernelFour p.2) p.1)
    poissonKernelFour_hessian_continuousOn_halfBall_sphere
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x hx ξ
  exact (hC (x,ξ) ⟨hx,mem_univ ξ⟩).trans (le_max_left _ _)

theorem poissonKernelFour_hessian_universal_modulus {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, δ ≤ (1/2 : ℝ) ∧
      ∀ x ∈ closedBall (0 : E) (1/2 : ℝ), ∀ y ∈ closedBall (0 : E) (1/2 : ℝ),
        dist x y < δ → ∀ ξ : S,
          ‖realHessian (poissonKernelFour ξ) x-realHessian (poissonKernelFour ξ) y‖ ≤ η := by
  have hK := (isCompact_closedBall (0 : E) (1/2 : ℝ)).prod
    (isCompact_univ : IsCompact (univ : Set S))
  obtain ⟨d,hd,hdiff⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous poissonKernelFour_hessian_continuousOn_halfBall_sphere) η hη
  refine ⟨min d (1/2),lt_min hd (by norm_num),min_le_right _ _,?_⟩
  intro x hx y hy hxy ξ
  have hp : dist (x,ξ) (y,ξ) < d := by
    simpa only [Prod.dist_eq,dist_self,max_eq_left (dist_nonneg : 0 ≤ dist x y)] using
      hxy.trans_le (min_le_left _ _)
  have h := hdiff (x,ξ) ⟨hx,mem_univ ξ⟩ (y,ξ) ⟨hy,mem_univ ξ⟩ hp
  simpa only [dist_eq_norm] using h.le

end PowerConvexity
