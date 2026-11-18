import PowerConvexity.Analysis.ActualFlatDriftPhysicalInputFour
import PowerConvexity.Analysis.ActualAffineEllipticCoeffFour
import PowerConvexity.Analysis.ActualLinearCongruenceHolderFour

/-! # Exact orthogonal transport of actual physical boundary data

The same coefficient, source, solution and drift are transported by one
orthogonal map. All ellipticity and Holder constants are preserved. This is
the input needed to choose boundary expansion constants before the normal.
-/
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

theorem actual_isometry_flat_maps_four (O : E ≃ₗᵢ[ℝ] E) {N M : E}
    (hinner : ∀ x : E, inner ℝ N (O x)=inner ℝ M x) {R : ℝ} :
    MapsTo O (actualFlatUpperBallFour M R) (actualFlatUpperBallFour N R) ∧
      MapsTo O (actualFlatClosedUpperBallFour M R) (actualFlatClosedUpperBallFour N R) := by
  constructor
  · intro x hx
    refine ⟨?_,?_⟩
    · simpa only [mem_ball,dist_zero_right,O.norm_map] using hx.1
    · change 0 < inner ℝ N (O x)
      rw [hinner]
      exact hx.2
  · intro x hx
    refine ⟨?_,?_⟩
    · simpa only [mem_closedBall,dist_zero_right,O.norm_map] using hx.1
    · change 0 ≤ inner ℝ N (O x)
      rw [hinner]
      exact hx.2

theorem actual_linear_congruence_column_vector_four (G : E ≃L[ℝ] E)
    {a : E → Mat} {x : E}
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) (G x)) :
    actualCoefficientColumnDivergenceFour
      (fun y => actualLinearCongruenceMatrixTwo G (a (G y))) x =
        G.symm (actualCoefficientColumnDivergenceFour a (G x)) := by
  ext j
  change (∑ i, fderiv ℝ (fun y => actualLinearCongruenceMatrixTwo G (a (G y)) i j) x
    (EuclideanSpace.single i 1)) = _
  rw [actual_linear_congruence_column_divergence_two G ha]
  rw [← actual_linear_matrix_action_two G.symm]
  rfl

theorem actual_linear_drift_equation_transport_four (G : E ≃L[ℝ] E)
    {a : E → Mat} {b : E → E} {f u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u (G x))
    (heq : (∑ i, ∑ j, a (G x) i j*euclideanHessian u (G x) i j)+
      fderiv ℝ u (G x) (b (G x)) = -f (G x)) :
    (∑ i, ∑ j, actualLinearCongruenceMatrixTwo G (a (G x)) i j*
      euclideanHessian (u ∘ G) x i j)+
        fderiv ℝ (u ∘ G) x (G.symm (b (G x))) = -f (G x) := by
  have hu' : ContDiffAt ℝ 2 u (0+G ((1 : ℝ) • x)) := by simpa only [one_smul,zero_add] using hu
  have hs : (∑ i, ∑ j, a (0+G ((1 : ℝ) • x)) i j*
      euclideanHessian u (0+G ((1 : ℝ) • x)) i j) =
        -(f (0+G ((1 : ℝ) • x))+fderiv ℝ u (0+G ((1 : ℝ) • x)) (b (0+G ((1 : ℝ) • x)))) := by
    simpa only [one_smul,zero_add] using (show
      (∑ i, ∑ j, a (G x) i j*euclideanHessian u (G x) i j) =
        -(f (G x)+fderiv ℝ u (G x) (b (G x))) by linarith)
  have ht := actual_affine_classical_equation_transport_four G (0 : E) 1
    (A := a) (f := fun y => f y+fderiv ℝ u y (b y)) hu' hs
  simp only [one_smul,zero_add,one_pow,one_mul] at ht
  have hd : fderiv ℝ (u ∘ G) x (G.symm (b (G x)))=fderiv ℝ u (G x) (b (G x)) := by
    rw [fderiv_comp x (hu.differentiableAt (by norm_num)) G.differentiableAt,
      G.fderiv]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,G.apply_symm_apply]
  change (∑ i, ∑ j, actualLinearCongruenceMatrixTwo G (a (G x)) i j*
    euclideanHessian (u ∘ G) x i j) = -(f (G x)+fderiv ℝ u (G x) (b (G x))) at ht
  rw [hd]
  linarith

def actualFlatDriftRotateInputFour {N M : E} (O : E ≃ₗᵢ[ℝ] E)
    (hinner : ∀ x : E, inner ℝ N (O x)=inner ℝ M x)
    {lam Lambda alpha Ka Kb Kf Bd B : ℝ}
    (D : ActualFlatDriftPhysicalInputFour N lam Lambda alpha Ka Kb Kf Bd B) :
    ActualFlatDriftPhysicalInputFour M lam Lambda alpha Ka Kb Kf Bd B := by
  let G := O.toContinuousLinearEquiv
  have hmap := (actual_isometry_flat_maps_four O hinner (R := 1)).1
  have hmapC := (actual_isometry_flat_maps_four O hinner (R := 1)).2
  have hmap' : MapsTo (fun x : E => 0+G ((1 : ℝ) • x))
      (actualFlatUpperBallFour M 1) (actualFlatUpperBallFour N 1) := by
    intro x hx
    simpa only [one_smul,zero_add,G,LinearIsometryEquiv.coe_toContinuousLinearEquiv] using hmap hx
  let A := actualAffineNormalizedCoeffFour (0 : E) G zero_lt_one D.coeff hmap'
  have hA (x : E) : A.a x=actualLinearCongruenceMatrixTwo G (D.coeff.a (O x)) := by
    simp only [A,actualAffineNormalizedCoeffFour_a,one_smul,zero_add]
    rfl
  have hG : ‖G.toContinuousLinearMap‖=1 := O.norm_toContinuousLinearMap
  have hInv : ‖G.symm.toContinuousLinearMap‖=1 := O.symm.norm_toContinuousLinearMap
  have hU := actualFlatUpperBallFour_isOpen N 1
  have hAc (i j : Fin (2+2)) : ContinuousOn (fun x => A.a x i j)
      (actualFlatClosedUpperBallFour M 1) := by
    simp only [hA,actualLinearCongruenceMatrixTwo,Matrix.mul_apply]
    apply continuousOn_finsetSum _
    intro k _
    apply ContinuousOn.mul _ continuousOn_const
    apply continuousOn_finsetSum _
    intro l _
    exact continuousOn_const.mul ((D.continuous l k).comp O.continuous.continuousOn hmapC)
  refine {
    coeff := A
    drift := fun x => O.symm (D.drift (O x))
    source := D.source ∘ O
    solution := D.solution ∘ O
    lower := by simp only [A,actualAffineNormalizedCoeffFour_lam,hG,max_self,one_pow,div_one]; exact D.lower
    upper := by simp only [A,actualAffineNormalizedCoeffFour_Lambda,hInv,max_self,one_pow,mul_one]; exact D.upper
    positive := actual_affine_normalized_coeff_posDef_four (0 : E) G zero_lt_one D.coeff hmap' D.positive
    frozen := by rw [hA,map_zero,D.frozen]; exact actual_linear_isometry_congruence_identity_four O
    regular := by
      intro i j
      exact (actual_affine_normalized_coeff_regular_four (0 : E) G zero_lt_one D.coeff hmap' D.regular i j)
    continuous := hAc
    divergence := ?_
    growth := ?_
    drift_continuous := O.symm.continuous.comp_continuousOn
      (D.drift_continuous.comp O.continuous.continuousOn hmapC)
    drift_bound := by intro x hx; simpa only [O.symm.norm_map] using D.drift_bound (O x) (hmap hx)
    drift_growth := by
      intro x hx
      simpa only [map_zero,← map_sub,O.symm.norm_map,O.norm_map] using D.drift_growth (O x) (hmap hx)
    source_continuous := D.source_continuous.comp O.continuous.continuousOn hmapC
    source_growth := by intro x hx; simpa only [Function.comp_apply,map_zero,O.norm_map] using D.source_growth (O x) (hmap hx)
    solution_regular := D.solution_regular.comp O.toContinuousLinearEquiv.contDiff.contDiffOn hmap
    solution_continuous := D.solution_continuous.comp O.continuous.continuousOn hmapC
    solution_zero := by
      intro x hx hzero
      apply D.solution_zero (O x)
      · simpa only [mem_closedBall,dist_zero_right,O.norm_map] using hx
      · rw [hinner,hzero]
    solution_bound := fun x hx => D.solution_bound _ (hmapC hx)
    equation := ?_
  }
  · intro x hx
    have ha (i j : Fin (2+2)) : DifferentiableAt ℝ (fun y => D.coeff.a y i j) (G x) :=
      ((D.regular i j).contDiffAt (hU.mem_nhds (hmap hx))).differentiableAt (by norm_num)
    have he : A.a=(fun x => actualLinearCongruenceMatrixTwo G (D.coeff.a (G x))) := by
      funext x
      exact hA x
    rw [he,actual_linear_congruence_column_vector_four G ha]
    change O.symm (actualCoefficientColumnDivergenceFour D.coeff.a (O x))=O.symm (D.drift (O x))
    rw [D.divergence (O x) (hmap hx)]
  · intro x hx
    rw [hA,← actual_linear_isometry_congruence_identity_four O]
    have hh := actual_linear_congruence_operator_norm_four G (D.coeff.a (O x)) (1 : Mat)
    rw [hInv,one_pow,one_mul] at hh
    exact hh.trans (by simpa only [O.norm_map] using D.growth (O x) (hmap hx))
  · intro x hx
    simp only [hA]
    exact actual_linear_drift_equation_transport_four G
      (D.solution_regular.contDiffAt (hU.mem_nhds (hmap hx))) (D.equation _ (hmap hx))

end PowerConvexity
