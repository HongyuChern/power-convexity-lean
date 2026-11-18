import PowerConvexity.Analysis.ActualClosureCofactorHolderCoefficientTwo
import PowerConvexity.Analysis.ActualClosureCofactorCoefficientFactsTwo
import PowerConvexity.Analysis.VariableDensityCofactorEllipticity
import PowerConvexity.Calculus.ActualHolderC2JetIdentificationTwo
import PowerConvexity.Calculus.ActualHolderResponseLiftTwo

/-! # An actual Holder jet supplies its own true Holder cofactor coefficient

The complete jet norm gives the real Hessian bound and Holder seminorm.
Uniform cofactor ellipticity is constructed from the actual determinant
lower bound; the true closure coefficient then supplies all required data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] holderResponseJetSeminormedGroup

theorem actual_holder_jet_cofactor_coefficient_two
    {U : Set E} [CompactSpace (closure U)] (hU : IsOpen U) (alpha : ℝ)
    (p : actualHolderC2JetSpaceTwo U alpha)
    (hu : ContDiffOn ℝ 4 (actualClosureExtensionTwo U p.1.1) U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections
      (actualClosureExtensionTwo U p.1.1) x).PosDef)
    (hdet : ∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections
      (actualClosureExtensionTwo U p.1.1) x).det.re) :
    ∃ c : ℝ, 0 < c ∧ ∃ Ka : ℝ, 0 ≤ Ka ∧ ∃ A : EllipticCoeff (2+2) U,
      A.lam=1 ∧
      (∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff (actualClosureExtensionTwo U p.1.1) x) ∧
      ∀ x ∈ closure U, ∀ y ∈ closure U,
        ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤ Ka*‖x-y‖^alpha := by
  obtain ⟨hu2,J,hJD,hJH⟩ := actualHolderC2JetSpaceTwo_regular U hU alpha p
  let Hv : C(closure U,E →L[ℝ] E →L[ℝ] ℝ) := actualHolderLoadSpaceTwo_value _ _ alpha p.1.2.2
  have hJvalue (x : E) (hx : x ∈ closure U) : J.hessian x=Hv ⟨x,hx⟩ :=
    (congrFun hJH x).trans (actualClosureExtensionTwo_apply U Hv hx)
  have hnorm : ∀ x ∈ closure U, ‖J.hessian x‖ ≤ ‖p‖ := by
    intro x hx
    rw [hJvalue x hx]
    exact (((actualHolderLoadSpaceTwo_value _ _ alpha p.1.2.2).norm_coe_le_norm ⟨x,hx⟩).trans
      (actualHolderLoadSpaceTwo_value_norm_le _ _ alpha p.1.2.2)).trans
      (actualHolderC2JetSpaceTwo_norm_bounds U alpha p).2.2
  have hhold : ∀ x ∈ closure U, ∀ y ∈ closure U,
      ‖J.hessian x-J.hessian y‖ ≤ ‖p‖*‖x-y‖^alpha := by
    intro x hx y hy
    rw [hJvalue x hx,hJvalue y hy]
    simpa only [Subtype.dist_eq,dist_eq_norm] using
      actualHolderC2JetSpaceTwo_hessian_holder U alpha p ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨c,hc,Lambda,hLambda,hcoeff⟩ := exists_uniform_variable_density_cofactor_coefficients (n := 2) ‖p‖
  have hentry : ∀ x ∈ U, ∀ i j,
      |euclideanHessian (actualClosureExtensionTwo U p.1.1) x i j| ≤ ‖p‖ := by
    intro x hx i j
    have h := (realHessian (actualClosureExtensionTwo U p.1.1) x).le_opNorm₂
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    have h' : |euclideanHessian (actualClosureExtensionTwo U p.1.1) x i j| ≤
        ‖realHessian (actualClosureExtensionTwo U p.1.1) x‖ := by
      simpa only [euclideanHessian,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs] using h
    apply h'.trans
    have he : realHessian (actualClosureExtensionTwo U p.1.1) x=J.hessian x :=
      (J.hessian_eq hx).symm
    exact (congrArg norm he).trans_le (hnorm x (subset_closure hx))
  obtain ⟨A,hAL,hA⟩ := hcoeff U hU _ hu hdet hpos hentry
  let B := actualClosureCofactorEllipticCoeffTwo hU hu2 J A.1 hA
  let Ka := c⁻¹*‖actualCofactorOperatorFormTwo‖*‖p‖
  refine ⟨c,hc,Ka,by dsimp only [Ka]; positivity,B,
    (actual_closure_cofactor_coefficient_lower_two hU hu2 J A.1 hA).trans A.property,?_,?_⟩
  · intro x hx
    exact actual_closure_cofactor_coefficient_interior_two hU hu2 J A.1 hA hx
  · exact actual_closure_cofactor_coefficient_holder_two hU hu2 J hc A.1 hA hhold

end PowerConvexity
