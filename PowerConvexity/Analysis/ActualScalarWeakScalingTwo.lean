import PowerConvexity.Analysis.ActualZeroTraceBallTransportTwo
import PowerConvexity.Analysis.ActualScalarWeakLinearOperationsTwo

/-! # Exact affine scaling of the actual nonhomogeneous scalar equation.
The bilinear-form proof follows the locked BallScaling computation, using
project change-of-variables and H01 transport results. The source is the
actual function R^2*f(c+R*z), with every H01 test and witness retained.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_integral_comp_affine_unitBall_two {x₀ : E} {R : ℝ} (hR : 0 < R)
    (f : E → ℝ) :
    (∫ z in ball (0 : E) 1, f (x₀+R • z)) =
      (R^Module.finrank ℝ E)⁻¹*(∫ x in ball x₀ R, f x) := by
  simpa only [mul_one] using crossover_integral_comp_affine_ball (x₀ := x₀) (ρ := (1 : ℝ)) hR f

theorem actual_bilinForm_rescale_to_unitBall_two
    {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : EllipticCoeff (2+2) (Metric.ball x₀ R))
    {u φ : E → ℝ}
    (hu : MemW1pWitness 2 u (Metric.ball x₀ R))
    (hφ : MemW1pWitness 2 φ (Metric.ball (0 : E) 1)) :
    bilinFormOfCoeff (rescaleCoeffToUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR A)
      (hu.rescaleToUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR) hφ =
      ((R ^ Module.finrank ℝ E)⁻¹ * R ^ (2 : ℕ)) *
        bilinFormOfCoeff A hu
          (hφ.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR) := by
  let huR := hu.rescaleToUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR
  let hφB := hφ.transportFromUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR
  have hpoint :
      ∀ z : E,
        bilinFormIntegrandOfCoeff
            (rescaleCoeffToUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR A) huR hφ z =
          R ^ (2 : ℕ) *
            bilinFormIntegrandOfCoeff A hu hφB (x₀ + R • z) := by
    intro z
    have hmat :
        matMulE (A.a (x₀ + R • z)) (R • hu.weakGrad (x₀ + R • z)) =
          R • matMulE (A.a (x₀ + R • z)) (hu.weakGrad (x₀ + R • z)) := by
      ext i
      simp [matMulE_apply, Matrix.mulVec_smul, Pi.smul_apply]
    have hgrad :
        hφ.weakGrad z = R • hφB.weakGrad (x₀ + R • z) := by
      have hcancel : R⁻¹ • (x₀ + R • z - x₀) = z := by
        rw [add_sub_cancel_left, inv_smul_smul₀ hR.ne']
      have hB : hφB.weakGrad (x₀ + R • z) =
          R⁻¹ • hφ.weakGrad (R⁻¹ • (x₀ + R • z - x₀)) := rfl
      rw [hB, hcancel, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    calc
      bilinFormIntegrandOfCoeff
          (rescaleCoeffToUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR A) huR hφ z
          = ⟪matMulE (A.a (x₀ + R • z)) (R • hu.weakGrad (x₀ + R • z)),
              hφ.weakGrad z⟫_ℝ := by
                simp [bilinFormIntegrandOfCoeff, huR, rescaleCoeffToUnitBall,
                  MemW1pWitness.rescaleToUnitBall]
      _ = ⟪R • matMulE (A.a (x₀ + R • z)) (hu.weakGrad (x₀ + R • z)),
            R • hφB.weakGrad (x₀ + R • z)⟫_ℝ := by rw [hmat, hgrad]
      _ = R ^ (2 : ℕ) *
            bilinFormIntegrandOfCoeff A hu hφB (x₀ + R • z) := by
            simp [bilinFormIntegrandOfCoeff, hφB, inner_smul_left, inner_smul_right,
              pow_two, mul_assoc]
  unfold bilinFormOfCoeff
  calc
    ∫ z in Metric.ball (0 : E) 1,
        bilinFormIntegrandOfCoeff
          (rescaleCoeffToUnitBall (d := 2+2) (x₀ := x₀) (R := R) hR A) huR hφ z
        = ∫ z in Metric.ball (0 : E) 1,
            R ^ (2 : ℕ) * bilinFormIntegrandOfCoeff A hu hφB (x₀ + R • z) := by
              apply integral_congr_ae
              filter_upwards with z
              exact hpoint z
    _ = R ^ (2 : ℕ) * ∫ z in Metric.ball (0 : E) 1,
          bilinFormIntegrandOfCoeff A hu hφB (x₀ + R • z) := by
            rw [integral_const_mul]
    _ = R ^ (2 : ℕ) *
          ((R ^ Module.finrank ℝ E)⁻¹ *
            ∫ x in Metric.ball x₀ R, bilinFormIntegrandOfCoeff A hu hφB x) := by
              rw [actual_integral_comp_affine_unitBall_two (x₀ := x₀) (R := R) hR
                (fun x => bilinFormIntegrandOfCoeff A hu hφB x)]
    _ = ((R ^ Module.finrank ℝ E)⁻¹ * R ^ (2 : ℕ)) *
          ∫ x in Metric.ball x₀ R, bilinFormIntegrandOfCoeff A hu hφB x := by
            ring
    _ = ((R ^ Module.finrank ℝ E)⁻¹ * R ^ (2 : ℕ)) *
          bilinFormOfCoeff A hu hφB := by
            rfl

theorem actual_scalar_weak_rescale_to_unitBall_two {x₀ : E} {R : ℝ} (hR : 0 < R)
    (A : EllipticCoeff (2+2) (ball x₀ R)) {f u : E → ℝ}
    (hu : ActualScalarWeakEquationTwo A f u) :
    ActualScalarWeakEquationTwo (rescaleCoeffToUnitBall hR A)
      (fun z => R^2*f (x₀+R • z)) (rescaleToUnitBall (x₀ := x₀) (R := R) u) := by
  let uw := MemW1p.someWitness hu.1
  let ur := uw.rescaleToUnitBall hR
  refine ⟨ur.memW1p,?_⟩
  intro sw phi hp pw
  let pb := pw.transportFromUnitBall (x₀ := x₀) (R := R) hR
  have hpb : MemH01 (transportFromUnitBall (x₀ := x₀) (R := R) phi) (ball x₀ R) :=
    actual_memH01_transport_from_unitBall_two hR hp
  have hload : (∫ z in ball (0 : E) 1, (R^2*f (x₀+R • z))*phi z) =
      ((R^Module.finrank ℝ E)⁻¹*R^2)*
        (∫ x in ball x₀ R, f x*transportFromUnitBall (x₀ := x₀) (R := R) phi x) := by
    calc
      (∫ z in ball (0 : E) 1, (R^2*f (x₀+R • z))*phi z) =
          ∫ z in ball (0 : E) 1, R^2*(f (x₀+R • z)*
            transportFromUnitBall (x₀ := x₀) (R := R) phi (x₀+R • z)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by
          simp only [transportFromUnitBall,add_sub_cancel_left,inv_smul_smul₀ hR.ne']
          ring)
      _ = R^2*(∫ z in ball (0 : E) 1, f (x₀+R • z)*
            transportFromUnitBall (x₀ := x₀) (R := R) phi (x₀+R • z)) := integral_const_mul _ _
      _ = R^2*((R^Module.finrank ℝ E)⁻¹*
          (∫ x in ball x₀ R, f x*transportFromUnitBall (x₀ := x₀) (R := R) phi x)) := by
        rw [actual_integral_comp_affine_unitBall_two hR
          (fun x => f x*transportFromUnitBall (x₀ := x₀) (R := R) phi x)]
      _ = _ := by ring
  calc
    bilinFormOfCoeff (rescaleCoeffToUnitBall hR A) sw pw =
        bilinFormOfCoeff (rescaleCoeffToUnitBall hR A) ur pw :=
      bilinFormOfCoeff_eq_left isOpen_ball _ sw ur pw
    _ = ((R^Module.finrank ℝ E)⁻¹*R^2)*bilinFormOfCoeff A uw pb :=
      actual_bilinForm_rescale_to_unitBall_two hR A uw pw
    _ = ((R^Module.finrank ℝ E)⁻¹*R^2)*
        (∫ x in ball x₀ R, f x*transportFromUnitBall (x₀ := x₀) (R := R) phi x) := by
      rw [hu.2 uw _ hpb pb]
    _ = ∫ z in ball (0 : E) 1, (R^2*f (x₀+R • z))*phi z := hload.symm

end PowerConvexity
