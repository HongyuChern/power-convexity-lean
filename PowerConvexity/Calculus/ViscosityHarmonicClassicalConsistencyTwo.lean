import PowerConvexity.Calculus.SmallCMAUniformLimitLocalTestsTwo
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-! # Agreement with the actual Euclidean Laplacian.
The block trace is exactly the locked library Laplacian, with no missing
normalization factor. With actual C2 regularity, the local-test definition
is equivalent to classical harmonicity on an open set. This is a
consistency result, not a regularity theorem for continuous viscosity limits.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem actual_block_trace_eq_laplacian_two (p : E → ℝ) (x : E) :
    (realBlockHessian realDirections imagDirections p x).trace =
      Laplacian.laplacian p x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis p
    (EuclideanSpace.basisFun (Fin (2+2)) ℝ)]
  simp only [iteratedFDeriv_two_apply,EuclideanSpace.basisFun_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp only [Matrix.trace,Matrix.diag_apply,realBlockHessian,blockDirection_eq_single,realHessian]

theorem IsViscosityHarmonicTwo.actual_trace_zero_of_C2
    {g : E → ℝ} {U : Set E} (hg : IsViscosityHarmonicTwo g U)
    {x : E} (hx : x ∈ U) (hC2 : ContDiffAt ℝ 2 g x) :
    (realBlockHessian realDirections imagDirections g x).trace = 0 := by
  have hz : IsLocalMin (fun y => g y-g y) x := by
    simpa only [sub_self] using (isLocalMin_const : IsLocalMin (fun _ : E => (0 : ℝ)) x)
  obtain ⟨hl,hu⟩ := hg.2 x hx g hC2
  exact le_antisymm (hl hz) (hu hz)

theorem IsViscosityHarmonicTwo.classical_harmonic_of_C2
    {g : E → ℝ} {U : Set E} (hg : IsViscosityHarmonicTwo g U)
    (hU : IsOpen U) (hC2 : ContDiffOn ℝ 2 g U) :
    InnerProductSpace.HarmonicOnNhd g U := by
  intro x hx
  refine ⟨hC2.contDiffAt (hU.mem_nhds hx),?_⟩
  filter_upwards [hU.mem_nhds hx] with y hy
  change Laplacian.laplacian g y = 0
  rw [← actual_block_trace_eq_laplacian_two]
  exact hg.actual_trace_zero_of_C2 hy (hC2.contDiffAt (hU.mem_nhds hy))

theorem classical_harmonic_isViscosityHarmonicTwo
    {g : E → ℝ} {U : Set E} (hg : InnerProductSpace.HarmonicOnNhd g U) :
    IsViscosityHarmonicTwo g U := by
  refine ⟨hg.continuousOn,?_⟩
  intro x hx p hp
  have hg2 := (hg x hx).1
  have hzero : (realBlockHessian realDirections imagDirections g x).trace = 0 := by
    rw [actual_block_trace_eq_laplacian_two]
    exact (hg x hx).2.self_of_nhds
  constructor
  · intro hm
    have ho := realHessian_le_of_isLocalMin_sub hg2 hp hm
    have ht : (realBlockHessian realDirections imagDirections p x).trace ≤
        (realBlockHessian realDirections imagDirections g x).trace := by
      exact Finset.sum_le_sum (fun i _ => ho (Sum.elim realDirections imagDirections i))
    simpa only [hzero] using ht
  · intro hm
    have ho := realHessian_le_of_isLocalMin_sub hp hg2 hm
    have ht : (realBlockHessian realDirections imagDirections g x).trace ≤
        (realBlockHessian realDirections imagDirections p x).trace := by
      exact Finset.sum_le_sum (fun i _ => ho (Sum.elim realDirections imagDirections i))
    simpa only [hzero] using ht

end PowerConvexity
