import PowerConvexity.Analysis.ActualFlatDriftPerturbationDataFour
import PowerConvexity.Analysis.ActualFlatCenteredGeometryFour

/-! # Monotonicity and actual boundary values of the drift perturbation data -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualFlatDriftPerturbationDataFour_weaken {N : E} {lam Lambda delta tau : ℝ}
    (D : ActualFlatDriftPerturbationDataFour N lam Lambda delta) (h : delta ≤ tau) :
    ActualFlatDriftPerturbationDataFour N lam Lambda tau :=
  { D with
    near_identity := fun x hx i j => (D.near_identity x hx i j).trans h
    drift_bound := fun x hx => (D.drift_bound x hx).trans h
    source_bound := fun x hx => (D.source_bound x hx).trans h }

theorem actual_flat_drift_data_boundary_bounds_four {N : E} (hN : ‖N‖=1)
    {lam Lambda delta : ℝ} (D : ActualFlatDriftPerturbationDataFour N lam Lambda delta)
    (hb : ContinuousOn D.drift (actualFlatClosedUpperBallFour N 1))
    (hf : ContinuousOn D.source (actualFlatClosedUpperBallFour N 1)) :
    ‖D.drift 0‖ ≤ delta ∧ |D.source 0| ≤ delta := by
  have h0 : (0 : E) ∈ closure (actualFlatUpperBallFour N 1) :=
    actual_flat_boundary_point_mem_closure_four hN (by simp) (by simp)
  have hbc : ContinuousOn (fun x => ‖D.drift x‖) (closure (actualFlatUpperBallFour N 1)) :=
    hb.norm.mono (actualFlatUpperBallFour_closure_subset N 1)
  have hfc : ContinuousOn (fun x => |D.source x|) (closure (actualFlatUpperBallFour N 1)) :=
    hf.abs.mono (actualFlatUpperBallFour_closure_subset N 1)
  exact ⟨le_on_closure D.drift_bound hbc continuousOn_const h0,
    le_on_closure D.source_bound hfc continuousOn_const h0⟩

end PowerConvexity
