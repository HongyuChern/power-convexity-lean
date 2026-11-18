import PowerConvexity.Calculus.WeakClassicalRepresentative
import PowerConvexity.Calculus.NormalizedCofactorLinearizedTwo

/-! # The density-weighted weak solution gives the intended classical inverse
once an actual classical representative and closure jet have been proved.
The regularity premise remains explicit and is not an existence theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem cofactor_weak_classical_representative_solves_linearized_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u rho g : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hpsh : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (rho x : ℂ))
    (hrho : ContinuousOn rho U) (hg : ContinuousOn g U)
    {c : ℝ} (hc : 0 < c) (B : EllipticCoeff (2+2) U)
    (hB : ∀ x ∈ U, B.a x = c⁻¹ • complexCofactorCoeff u x)
    {h : E → ℝ}
    (hh : IsWeakSolution ⟨U,hU,hK.isBounded.subset subset_closure,B,
      (fun phi => ∫ x in U, -(c⁻¹*rho x*g x)*phi x)⟩ h)
    {H : E → ℝ} (hH : ContDiffOn ℝ 2 H U) (J : ClosureC2Jet H U)
    (he : H =ᵐ[volume.restrict U] h) :
    ∀ x ∈ U, linearizedCMAOperatorTwo realDirections imagDirections u H x = g x := by
  let F : E → E := fun y => c⁻¹ • matMulE (complexCofactorCoeff u y) (smoothGradField H y)
  have hF (i : Fin (2+2)) : ContDiffOn ℝ 1 (fun y => F y i) U := by
    intro x hx
    have hu4 := hu.contDiffAt (hU.mem_nhds hx)
    have hH2 := hH.contDiffAt (hU.mem_nhds hx)
    change ContDiffWithinAt ℝ 1
      (fun y => c⁻¹ * ∑ j, complexCofactorCoeff u y i j *
        fderiv ℝ H y (EuclideanSpace.single j 1)) U x
    apply ContDiffAt.contDiffWithinAt
    apply contDiffAt_const.mul
    apply ContDiffAt.sum
    intro j _
    exact ((complexCofactorCoeff_contDiffAt hu4 i j).of_le (by norm_num)).mul
      ((hH2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  have hpoint := actual_classical_representative_satisfies_scalar_equation hU hK B
    (((continuousOn_const.mul hrho).mul hg).neg) hh (hH.of_le (by norm_num)) J he hF
    (fun x hx => by
      change matMulE (B.a x) (smoothGradField H x) = _
      rw [hB x hx,matMulE_smul_matrix])
  intro x hx
  have heq := hpoint x hx
  change -classicalDivergence
    (fun y => c⁻¹ • matMulE (complexCofactorCoeff u y) (smoothGradField H y)) x =
      -(c⁻¹*rho x*g x) at heq
  rw [classicalDivergence_const_smul,
    classical_cofactor_flux_eq_density_linearized_two
      (hu.contDiffAt (hU.mem_nhds hx)) (hH.contDiffAt (hU.mem_nhds hx)) (hpsh x hx),
    hdet x hx,Complex.ofReal_re,neg_inj,← mul_assoc] at heq
  have hrhop : 0 < rho x := by
    have hp := (Complex.pos_iff.mp (hpsh x hx).det_pos).1
    simpa only [hdet x hx,Complex.ofReal_re] using hp
  exact mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hc.ne') hrhop.ne') heq

end PowerConvexity
