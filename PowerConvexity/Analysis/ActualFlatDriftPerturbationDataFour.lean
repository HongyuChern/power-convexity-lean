import PowerConvexity.Analysis.ActualFlatDriftHarmonicCompactnessFour

/-! # Fixed actual perturbation data retaining the generated drift -/
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

structure ActualFlatDriftPerturbationDataFour (N : E) (lam Lambda delta : ℝ) where
  coeff : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)
  drift : E → E
  source : E → ℝ
  solution : E → ℝ
  lower : coeff.lam=lam
  upper : coeff.Λ ≤ Lambda
  positive : ∀ x ∈ actualFlatUpperBallFour N 1, (coeff.a x).PosDef
  regular : ∀ i j, ContDiffOn ℝ 1 (fun x => coeff.a x i j) (actualFlatUpperBallFour N 1)
  divergence : ∀ x ∈ actualFlatUpperBallFour N 1, actualCoefficientColumnDivergenceFour coeff.a x=drift x
  near_identity : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ i j, |coeff.a x i j-(1 : Mat) i j| ≤ delta
  drift_continuous : ContinuousOn drift (actualFlatUpperBallFour N 1)
  drift_bound : ∀ x ∈ actualFlatUpperBallFour N 1, ‖drift x‖ ≤ delta
  source_continuous : ContinuousOn source (actualFlatUpperBallFour N 1)
  source_bound : ∀ x ∈ actualFlatUpperBallFour N 1, |source x| ≤ delta
  solution_regular : ContDiffOn ℝ 2 solution (actualFlatUpperBallFour N 1)
  solution_continuous : ContinuousOn solution (actualFlatClosedUpperBallFour N 1)
  solution_zero : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → solution x=0
  solution_bound : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |solution x| ≤ 1
  equation : ∀ x ∈ actualFlatUpperBallFour N 1,
    (∑ i, ∑ j, coeff.a x i j*euclideanHessian solution x i j)+fderiv ℝ solution x (drift x) = -source x

end PowerConvexity
