import PowerConvexity.Analysis.ActualCofactorFirstVariationTwo
import PowerConvexity.Analysis.ActualUniformVariableDirectionalJetsFour
import PowerConvexity.Analysis.ActualUniformClosureTangentialResponseFour

/-! # The actual cofactor equation for a variable tangential field

The third derivatives produced by differentiating the genuine response Du(T)
are eliminated by the actual first variation of the same determinant equation.
The remaining load is bounded using only Du, D²u, DT and D²T. Boundary values
are taken from the actual closure jet, and tangency to a regular defining
function gives its true zero trace. No boundary Holder estimate is asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi

local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ

def actualTangentialCofactorCommutatorFour (u : E → ℝ) (T : E → E) (a : E → Mat)
    (x : E) : ℝ :=
  ∑ i, ∑ j, a x i j *
    (realHessian u x (EuclideanSpace.single j 1) (fderiv ℝ T x (EuclideanSpace.single i 1))+
      realHessian u x (EuclideanSpace.single i 1) (fderiv ℝ T x (EuclideanSpace.single j 1))+
      fderiv ℝ u x (fderiv ℝ (fderiv ℝ T) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)))

theorem actual_scaled_cofactor_variable_field_equation_four
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ} {T : E → E}
    (hu : ContDiffOn ℝ 4 u U) (hrho : ContDiffOn ℝ 1 rho U)
    (hT : ContDiffOn ℝ 2 T U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (rho x : ℂ))
    {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff u x) :
    ∀ x ∈ U,
      (∑ i, ∑ j, A.a x i j*euclideanHessian (fun y => fderiv ℝ u y (T y)) x i j) =
        c⁻¹*fderiv ℝ rho x (T x)+actualTangentialCofactorCommutatorFour u T A.a x := by
  intro x hx
  have hux : ContDiffAt ℝ 3 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hTx := hT.contDiffAt (hU.mem_nhds hx)
  have hh (i j : Fin (2+2)) := actual_hessian_variable_directional_difference_four hux hTx
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have heq := actual_scaled_cofactor_first_variation_equation_two hU hu hrho hpos hdet A hA (T x) x hx
  simp only [euclideanHessian] at heq
  simp only [euclideanHessian,actualTangentialCofactorCommutatorFour]
  simp_rw [hh,mul_add,Finset.sum_add_distrib]
  rw [heq]

theorem actual_tangential_cofactor_commutator_bound_four
    {u : E → ℝ} {T : E → E} {a : E → Mat} {x : E} {A G H D K : ℝ}
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hH : 0 ≤ H) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (ha : ∀ i j, |a x i j| ≤ A)
    (hu1 : ‖fderiv ℝ u x‖ ≤ G) (hu2 : ‖realHessian u x‖ ≤ H)
    (hT1 : ‖fderiv ℝ T x‖ ≤ D) (hT2 : ‖fderiv ℝ (fderiv ℝ T) x‖ ≤ K) :
    |actualTangentialCofactorCommutatorFour u T a x| ≤ 16*A*(2*H*D+G*K) := by
  have hunit (i : Fin (2+2)) : ‖(EuclideanSpace.single i 1 : E)‖ = 1 := by
    simp only [EuclideanSpace.norm_single,norm_one]
  have hDT (i : Fin (2+2)) : ‖fderiv ℝ T x (EuclideanSpace.single i 1)‖ ≤ D := by
    exact ((fderiv ℝ T x).le_opNorm _).trans (by rw [hunit,mul_one]; exact hT1)
  have hHterm (i j : Fin (2+2)) :
      |realHessian u x (EuclideanSpace.single j 1) (fderiv ℝ T x (EuclideanSpace.single i 1))| ≤ H*D := by
    calc
      _ ≤ ‖realHessian u x‖*‖EuclideanSpace.single j 1‖*
          ‖fderiv ℝ T x (EuclideanSpace.single i 1)‖ :=
        (realHessian u x).le_opNorm₂ _ _
      _ ≤ H*D := by rw [hunit,mul_one]; exact mul_le_mul hu2 (hDT i) (norm_nonneg _) hH
  have hKterm (i j : Fin (2+2)) :
      |fderiv ℝ u x (fderiv ℝ (fderiv ℝ T) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1))| ≤ G*K := by
    apply ((fderiv ℝ u x).le_opNorm _).trans
    apply mul_le_mul hu1 _ (norm_nonneg _) hG
    exact ((fderiv ℝ (fderiv ℝ T) x).le_opNorm₂ _ _).trans
      (by rw [hunit,hunit,mul_one,mul_one]; exact hT2)
  unfold actualTangentialCofactorCommutatorFour
  calc
    _ ≤ ∑ i, |∑ j, a x i j *
        (realHessian u x (EuclideanSpace.single j 1) (fderiv ℝ T x (EuclideanSpace.single i 1))+
          realHessian u x (EuclideanSpace.single i 1) (fderiv ℝ T x (EuclideanSpace.single j 1))+
          fderiv ℝ u x (fderiv ℝ (fderiv ℝ T) x (EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (2+2), ∑ _j : Fin (2+2), A*(2*H*D+G*K) := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul (ha i j) _ (abs_nonneg _) hA
      calc
        _ ≤ |realHessian u x (EuclideanSpace.single j 1) (fderiv ℝ T x (EuclideanSpace.single i 1))|+
            |realHessian u x (EuclideanSpace.single i 1) (fderiv ℝ T x (EuclideanSpace.single j 1))|+
            |fderiv ℝ u x (fderiv ℝ (fderiv ℝ T) x (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1))| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ H*D+H*D+G*K := add_le_add (add_le_add (hHterm i j) (hHterm j i)) (hKterm i j)
        _ = _ := by ring
    _ = _ := by simp; ring


theorem actual_scaled_cofactor_closure_tangential_equation_four
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ} {T : E → E}
    (hu : ContDiffOn ℝ 4 u U) (hrho : ContDiffOn ℝ 1 rho U)
    (hT : ContDiffOn ℝ 2 T U) (J : ClosureC2Jet u U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (rho x : ℂ))
    {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff u x) :
    ∀ x ∈ U,
      (∑ i, ∑ j, A.a x i j*euclideanHessian (actualClosureTangentialResponseFour J T) x i j) =
        c⁻¹*fderiv ℝ rho x (T x)+actualTangentialCofactorCommutatorFour u T A.a x := by
  intro x hx
  have he := actual_closure_tangential_response_eventually_eq_four hU J T hx
  have hH : realHessian (actualClosureTangentialResponseFour J T) x =
      realHessian (fun y => fderiv ℝ u y (T y)) x := he.fderiv.fderiv_eq
  simpa only [euclideanHessian,hH] using
    actual_scaled_cofactor_variable_field_equation_four hU hu hrho hT hpos hdet A hA x hx

theorem actual_tangential_cofactor_commutator_continuous_four
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} {T : E → E} {a : E → Mat}
    (hu : ContDiffOn ℝ 2 u U) (hT : ContDiffOn ℝ 2 T U)
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) U) :
    ContinuousOn (actualTangentialCofactorCommutatorFour u T a) U := by
  have hu1 := (hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn
  have hu2 : ContinuousOn (realHessian u) U :=
    ((hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).fderiv_of_isOpen hU
      (m := 0) (by norm_num)).continuousOn
  have hT1 := (hT.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn
  have hT2 := ((hT.fderiv_of_isOpen hU (m := 1) (by norm_num)).fderiv_of_isOpen hU
      (m := 0) (by norm_num)).continuousOn
  unfold actualTangentialCofactorCommutatorFour
  apply continuousOn_finsetSum _
  intro i _
  apply continuousOn_finsetSum _
  intro j _
  exact (ha i j).mul (((hu2.clm_apply continuousOn_const).clm_apply
    (hT1.clm_apply continuousOn_const)).add
    ((hu2.clm_apply continuousOn_const).clm_apply (hT1.clm_apply continuousOn_const)) |>.add
    (hu1.clm_apply ((hT2.clm_apply continuousOn_const).clm_apply continuousOn_const)))

theorem actual_variable_density_tangential_closure_weak_ball_four
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ} {T : E → E}
    (hu : ContDiffOn ℝ 4 u U) (hrho : ContDiffOn ℝ 1 rho U)
    (hT : ContDiffOn ℝ 2 T U) (J : ClosureC2Jet u U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (rho x : ℂ))
    {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff u x)
    {x₀ : E} {r : ℝ} (hclosed : closedBall x₀ r ⊆ U) :
    ActualScalarWeakEquationTwo (A.restrict (ball_subset_closedBall.trans hclosed))
      (fun x => -(c⁻¹*fderiv ℝ rho x (T x)+actualTangentialCofactorCommutatorFour u T A.a x))
      (actualClosureTangentialResponseFour J T) := by
  have hsub : ball x₀ r ⊆ U := ball_subset_closedBall.trans hclosed
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hu hpos hA
  have hp := actual_closure_tangential_response_regular_four hU J (hu.of_le (by norm_num)) hT
  have hfC : ContinuousOn (fun x => -(c⁻¹*fderiv ℝ rho x (T x)+
      actualTangentialCofactorCommutatorFour u T A.a x)) U := ((continuousOn_const.mul
    ((hrho.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn.clm_apply hT.continuousOn)).add
    (actual_tangential_cofactor_commutator_continuous_four hU
      (hu.of_le (by norm_num)) hT (fun i j => (hreg i j).continuousOn))).neg
  have hf := continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall x₀ r) ball_subset_closedBall (hfC.mono hclosed)
  apply actual_local_classical_scalar_weak_two hU hp hclosed
    (A.restrict hsub) (fun i j => (hreg i j).mono hsub)
    (fun x hx j => hdiv x (hsub hx) j) hf
  intro x hx
  simpa only [EllipticCoeff.restrict_a,neg_neg] using
    actual_scaled_cofactor_closure_tangential_equation_four hU hu hrho hT J hpos hdet A hA x (hsub hx)

theorem actual_det_one_tangential_closure_weak_ball_four
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} {T : E → E}
    (hu : ContDiffOn ℝ 4 u U) (hT : ContDiffOn ℝ 2 T U) (J : ClosureC2Jet u U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = 1)
    {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = c⁻¹ • complexCofactorCoeff u x)
    {x₀ : E} {r : ℝ} (hclosed : closedBall x₀ r ⊆ U) :
    ActualScalarWeakEquationTwo (A.restrict (ball_subset_closedBall.trans hclosed))
      (fun x => -actualTangentialCofactorCommutatorFour u T A.a x)
      (actualClosureTangentialResponseFour J T) := by
  have hsub : ball x₀ r ⊆ U := ball_subset_closedBall.trans hclosed
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hu hpos hA
  have hp := actual_closure_tangential_response_regular_four hU J (hu.of_le (by norm_num)) hT
  have hfC := (actual_tangential_cofactor_commutator_continuous_four hU
    (hu.of_le (by norm_num)) hT (fun i j => (hreg i j).continuousOn)).neg
  have hf := continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall x₀ r) ball_subset_closedBall (hfC.mono hclosed)
  apply actual_local_classical_scalar_weak_two hU hp hclosed
    (A.restrict hsub) (fun i j => (hreg i j).mono hsub)
    (fun x hx j => hdiv x (hsub hx) j) hf
  intro x hx
  have hdet' : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).det = ((1 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_one] using hdet
  simpa [EllipticCoeff.restrict_a] using
    actual_scaled_cofactor_closure_tangential_equation_four hU hu contDiffOn_const hT J
      hpos hdet' A hA x (hsub hx)

end PowerConvexity
