import PowerConvexity.Analysis.ActualFlatHarmonicCompactnessFour

/-! # Fixed representation of the actual normalized flat elliptic data -/
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

structure ActualFlatPerturbationDataFour (N : E) (lam Lambda Ka Kf alpha delta : ℝ) where
  coeff : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)
  source : E → ℝ
  solution : E → ℝ
  lower : lam ≤ coeff.lam
  upper : coeff.Λ ≤ Lambda
  positive : ∀ x ∈ actualFlatUpperBallFour N 1, (coeff.a x).PosDef
  regular : ∀ i j, ContDiffOn ℝ 1 (fun x => coeff.a x i j) (actualFlatUpperBallFour N 1)
  divergence : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ j,
    (∑ i, fderiv ℝ (fun y => coeff.a y i j) x (EuclideanSpace.single i 1))=0
  holder : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
    ‖actualMatrixOperatorTwo (coeff.a x)-actualMatrixOperatorTwo (coeff.a y)‖ ≤ Ka*‖x-y‖^alpha
  near_identity : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ i j,
    |coeff.a x i j-(1 : Mat) i j| ≤ delta
  source_regular : ContDiffOn ℝ 1 source (actualFlatUpperBallFour N 1)
  source_holder : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ y ∈ actualFlatUpperBallFour N 1,
    |source x-source y| ≤ Kf*‖x-y‖^alpha
  source_bound : ∀ x ∈ actualFlatUpperBallFour N 1, |source x| ≤ delta
  solution_regular : ContDiffOn ℝ 2 solution (actualFlatUpperBallFour N 1)
  solution_continuous : ContinuousOn solution (actualFlatClosedUpperBallFour N 1)
  solution_zero : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → solution x=0
  solution_bound : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |solution x| ≤ 1
  equation : ∀ x ∈ actualFlatUpperBallFour N 1,
    (∑ i, ∑ j, coeff.a x i j*euclideanHessian solution x i j) = -source x

end PowerConvexity
