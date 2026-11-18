import PowerConvexity.Calculus.SmallContactTraceBarrierTwo
import CHS.Analysis.LinearizedFlux
import CHS.Analysis.WeakHarnackMean

/-! # The actual deviation is subharmonic on its positive branch.
The identity coefficient is constructed with ellipticity constants one.
The local weak supersolution uses all H01 tests through the checked
classical-flux theorem; no global extension hypothesis is imposed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra DeGiorgi
local notation "E" => AmbientSpace (2+2)

def identityNormalizedEllipticCoeffTwo (D : Set E) : NormalizedEllipticCoeff (2+2) D :=
  ⟨{ a := fun _ => 1
     lam := 1
     Λ := 1
     measurable_comp := fun _ _ => measurable_const
     hlam := zero_lt_one
     hΛ := le_rfl
     coercive := Filter.Eventually.of_forall fun _ ξ => by
       simp [matMulE,real_inner_self_eq_norm_sq]
     coercive_inv := Filter.Eventually.of_forall fun _ ξ => by
       simp [matMulE,real_inner_self_eq_norm_sq] }, rfl⟩

theorem actual_shifted_CMA_laplacian_nonnegative_two
    {w : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x)
    (hpsh : (1+complexHessian realDirections imagDirections w x).PosSemidef)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1) :
    0 ≤ ∑ i : Fin (2+2), realHessian w x
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  have ht := two_sqrt_det_re_le_trace hpsh
  rw [hdet] at ht
  norm_num [Matrix.trace_add,Matrix.trace_one] at ht
  have hp := four_complexProjection_trace_re
    (realBlockHessian realDirections imagDirections w x)
  rw [complexProjection_realBlockHessian hw] at hp
  have htr : 0 ≤ (realBlockHessian realDirections imagDirections w x).trace := by
    linarith only [ht,hp]
  rw [← Equiv.sum_comp finSumFinEquiv]
  simpa only [Matrix.trace,Matrix.diag,realBlockHessian,blockDirection_eq_single] using htr

theorem actual_shifted_CMA_negative_local_supersolution_two
    {U : Set E} (hU : IsOpen U) {w : E → ℝ} (hw : ContDiffOn ℝ 2 w U)
    (hpsh : ∀ x ∈ U, (1+complexHessian realDirections imagDirections w x).PosSemidef)
    (hdet : ∀ x ∈ U, (1+complexHessian realDirections imagDirections w x).det = 1)
    {x₀ : E} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hclosed : closedBall x₀ R ⊆ U) :
    IsSupersolution (identityNormalizedEllipticCoeffTwo (ball x₀ r)).1 (fun x => -w x) := by
  let F : E → E := fun y => matMulE (1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ)
    (smoothGradField (fun z => -w z) y)
  have hn : ContDiffOn ℝ 2 (fun x => -w x) U := hw.neg
  have hF (i : Fin (2+2)) : ContDiffOn ℝ 1 (fun x => F x i) U := by
    intro x hx
    have hh := (((hn.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1)
      (by norm_num)).clm_apply (contDiffAt_const (c := EuclideanSpace.single i (1 : ℝ))))
    simpa only [F,matMulE_apply,Matrix.one_mulVec,smoothGradField,PiLp.toLp_apply] using
      hh.contDiffWithinAt
  apply supersolution_of_local_classical_flux hU hr hrR hclosed _
    (hn.of_le (by norm_num)) hF
  · intro x hx
    rfl
  · intro x hx
    have hxU := hclosed (closedBall_subset_closedBall hrR.le (ball_subset_closedBall hx))
    have htrace := actual_shifted_CMA_laplacian_nonnegative_two
      (hw.contDiffAt (hU.mem_nhds hxU)) (hpsh x hxU) (hdet x hxU)
    rw [show F = fun y => matMulE (1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ)
      (smoothGradField (fun z => -w z) y) by rfl,
      classicalDivergence_matMulE_gradient
        (A := fun _ : E => (1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ))
        (fun _ _ => differentiableAt_const _)
        (hn.contDiffAt (hU.mem_nhds hxU)) (fun _ => by simp)]
    simpa [PowerConvexity.realHessian_neg,Matrix.one_apply] using neg_nonpos.mpr htrace

end PowerConvexity
