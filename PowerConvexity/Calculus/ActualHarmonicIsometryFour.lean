import PowerConvexity.Calculus.CMAJetsIsometricTransport
import PowerConvexity.Calculus.ViscosityHarmonicClassicalConsistencyTwo

/-! # Actual Euclidean Laplacian and harmonicity under a real isometry -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem actual_laplacian_comp_linearIsometry_four
    (T : E ≃ₗᵢ[ℝ] E) {p : E → ℝ} {x : E}
    (hp : ContDiffAt ℝ 2 p (T x)) :
    Laplacian.laplacian (fun y => p (T y)) x = Laplacian.laplacian p (T x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fun y => p (T y)) (EuclideanSpace.basisFun (Fin (2+2)) ℝ),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis p
      ((EuclideanSpace.basisFun (Fin (2+2)) ℝ).map T)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    OrthonormalBasis.map_apply]
  exact realHessian_comp_linearIsometry T hp _ _

theorem actual_harmonic_comp_linearIsometry_four
    (T : E ≃ₗᵢ[ℝ] E) {p : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hp : InnerProductSpace.HarmonicOnNhd p U) :
    InnerProductSpace.HarmonicOnNhd (fun y => p (T y)) (T ⁻¹' U) := by
  intro x hx
  refine ⟨(hp (T x) hx).1.comp x T.contDiff.contDiffAt,?_⟩
  filter_upwards [(hU.preimage T.continuous).mem_nhds hx] with y hy
  change Laplacian.laplacian (fun z => p (T z)) y = 0
  rw [actual_laplacian_comp_linearIsometry_four T (hp (T y) hy).1]
  exact (hp (T y) hy).2.self_of_nhds

end PowerConvexity
