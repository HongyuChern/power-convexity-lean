import PowerConvexity.Analysis.ActualQuadraticScaleNormalizationTwo
import PowerConvexity.Analysis.ActualScalarHolderNormalizationTwo
import PowerConvexity.Analysis.ActualConcentricWeakScalingTwo

/-! # Polynomial weak sources without differentiating the coefficients

The hypothesis is the actual full H01 weak equation for every quadratic.
For continuous distributionally divergence-free coefficients this is the
appropriate replacement for a pointwise C1 column-divergence assumption.
The residual identities retain the original weak function and source.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

def ActualWeakQuadraticSourcesTwo {U : Set E} (A : EllipticCoeff (2+2) U) : Prop :=
  ∀ q : E → ℝ, IsQuadraticPolynomial q →
    ActualScalarWeakEquationTwo A (quadraticScalarSourceTwo A.a q) q

theorem actual_weak_quadratic_sources_of_C1_two
    {c : E} {r : ℝ} {V : Set E} (hV : IsOpen V) (hclosed : closedBall c r ⊆ V)
    (A : EllipticCoeff (2+2) (ball c r))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V)
    (hdiv : ∀ x ∈ ball c r, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1))=0) :
    ActualWeakQuadraticSourcesTwo A := by
  intro q hq
  exact actual_divergenceFree_quadratic_source_two hV hclosed A hA hdiv hq

theorem actual_quadratic_source_memLp_on_bounded_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {a : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ}
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) (closure U))
    {q : E → ℝ} (hq : IsQuadraticPolynomial q) :
    MemLp (quadraticScalarSourceTwo a q) 2 (volume.restrict U) := by
  apply continuousOn_memLp_two_of_subset_compact hU.measurableSet hUb.isCompact_closure subset_closure
  have he : quadraticScalarSourceTwo a q =
      fun x => -(∑ i, ∑ j, a x i j*euclideanHessian q 0 i j) := by
    funext x
    simp only [quadraticScalarSourceTwo,euclideanHessian,quadratic_realHessian_from_jet_zero hq x]
  rw [he]
  apply ContinuousOn.neg
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact (ha i j).mul continuousOn_const

theorem actual_weak_quadratic_residual_rescale_two
    {c : E} {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (A : EllipticCoeff (2+2) (ball c R)) {u f q : E → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball c R)))
    (hqf : MemLp (quadraticScalarSourceTwo A.a q) 2 (volume.restrict (ball c R)))
    (hu : ActualScalarWeakEquationTwo A f u)
    (hq : ActualScalarWeakEquationTwo A (quadraticScalarSourceTwo A.a q) q) :
    ActualScalarWeakEquationTwo (rescaleCoeffToUnitBall hR A)
      (fun z => a⁻¹*(f (c+R • z)-quadraticScalarSourceTwo A.a q (c+R • z)))
      (fun z => a⁻¹*(R^2)⁻¹*(u (c+R • z)-q (c+R • z))) := by
  have hr := actual_scalar_weak_sub_two isOpen_ball hf hqf hu hq
  have hs := actual_scalar_weak_smul_two isOpen_ball
    (actual_scalar_weak_rescale_to_unitBall_two hR A hr) (a⁻¹*(R^2)⁻¹)
  apply actual_scalar_weak_source_congr_ae_two (hu := hs)
  exact Filter.Eventually.of_forall (fun z => by field_simp)

end PowerConvexity
