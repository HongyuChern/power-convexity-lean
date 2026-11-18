import PowerConvexity.Analysis.ActualUniformDefiningTangentialDirichletFour
import PowerConvexity.Analysis.ActualAffineScalarBoundsFour

/-! # The actual rough Dirichlet equation and its physical affine pullback

The data records only the genuine interior coefficient, divergence identity,
bounded continuous load, and actual continuous zero-boundary response. No
coefficient modulus, boundary derivative or boundary expansion is an input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

structure ActualRoughDomainDirichletDataFour (U : Set E) (lam Lambda F M : ℝ) where
  coeff : EllipticCoeff (2+2) U
  source : E → ℝ
  solution : E → ℝ
  lower : lam ≤ coeff.lam
  upper : coeff.Λ ≤ Lambda
  positive : ∀ x ∈ U, (coeff.a x).PosDef
  regular : ∀ i j, ContDiffOn ℝ 1 (fun x => coeff.a x i j) U
  divergence : ∀ x ∈ U, ∀ j,
    (∑ i, fderiv ℝ (fun y => coeff.a y i j) x (EuclideanSpace.single i 1))=0
  source_continuous : ContinuousOn source U
  source_bound : ∀ x ∈ U, |source x| ≤ F
  solution_regular : ContDiffOn ℝ 2 solution U
  solution_continuous : ContinuousOn solution (closure U)
  solution_zero : ∀ x ∈ frontier U, solution x=0
  solution_bound : ∀ x ∈ closure U, |solution x| ≤ M
  equation : ∀ x ∈ U,
    (∑ i, ∑ j, coeff.a x i j*euclideanHessian solution x i j) = -source x

def ActualRoughDomainDirichletDataFour.affinePullback
    {U : Set E} (hU : IsOpen U) {lam Lambda F M r B I : ℝ}
    (D : ActualRoughDomainDirichletDataFour U lam Lambda F M)
    (c : E) (G : E ≃L[ℝ] E) (hr : 0 < r)
    (hG : ‖G.toContinuousLinearMap‖ ≤ B) (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ I) :
    ActualRoughDomainDirichletDataFour ((fun z : E => c+G (r • z)) ⁻¹' U)
      (lam/(max 1 B)^2) (Lambda*(max 1 I)^2) (r^2*F) M := by
  let phi : E → E := fun z => c+G (r • z)
  let V := phi ⁻¹' U
  have hphi : Continuous phi := by fun_prop
  have hphiD : ContDiff ℝ 2 phi := by fun_prop
  have hmap : MapsTo phi V U := fun _ hx => hx
  have hmapC : MapsTo phi (closure V) (closure U) := hmap.closure hphi
  let A := actualAffineNormalizedCoeffFour c G hr D.coeff hmap
  have hlo : lam/(max 1 B)^2 ≤ A.lam := by
    rw [show A.lam=D.coeff.lam/(max 1 ‖G.toContinuousLinearMap‖)^2 from rfl]
    apply div_le_div₀ D.coeff.hlam.le D.lower (by positivity)
    exact pow_le_pow_left₀ (by positivity) (max_le_max_left 1 hG) 2
  have hhi : A.Λ ≤ Lambda*(max 1 I)^2 := by
    change D.coeff.Λ*(max 1 ‖G.symm.toContinuousLinearMap‖)^2 ≤ Lambda*(max 1 I)^2
    exact mul_le_mul D.upper (pow_le_pow_left₀ (by positivity) (max_le_max_left 1 hInv) 2)
      (sq_nonneg _) (D.coeff.Λ_pos.le.trans D.upper)
  refine {
    coeff := A
    source := fun z => r^2*D.source (phi z)
    solution := fun z => D.solution (phi z)
    lower := hlo
    upper := hhi
    positive := actual_affine_normalized_coeff_posDef_four c G hr D.coeff hmap D.positive
    regular := actual_affine_normalized_coeff_regular_four c G hr D.coeff hmap D.regular
    divergence := actual_affine_normalized_coeff_divergence_four hU c G hr D.coeff hmap D.regular D.divergence
    source_continuous := continuousOn_const.mul (D.source_continuous.comp hphi.continuousOn hmap)
    source_bound := actual_affine_source_bound_four G hmap D.source_bound
    solution_regular := D.solution_regular.comp hphiD.contDiffOn hmap
    solution_continuous := D.solution_continuous.comp hphi.continuousOn hmapC
    solution_zero := fun x hx => D.solution_zero _ (hphi.frontier_preimage_subset U hx)
    solution_bound := fun x hx => D.solution_bound _ (hmapC hx)
    equation := ?_
  }
  intro x hx
  exact actual_affine_classical_equation_transport_four G c r
    (D.solution_regular.contDiffAt (hU.mem_nhds (hmap hx))) (D.equation _ (hmap hx))

def ActualRoughDomainDirichletDataFour.enlarge
    {U : Set E} {lam Lambda F M lam' Lambda' F' M' : ℝ}
    (D : ActualRoughDomainDirichletDataFour U lam Lambda F M)
    (hl : lam' ≤ lam) (hL : Lambda ≤ Lambda') (hF : F ≤ F') (hM : M ≤ M') :
    ActualRoughDomainDirichletDataFour U lam' Lambda' F' M' := {
  D with
  lower := hl.trans D.lower
  upper := D.upper.trans hL
  source_bound := fun x hx => (D.source_bound x hx).trans hF
  solution_bound := fun x hx => (D.solution_bound x hx).trans hM
}

end PowerConvexity
