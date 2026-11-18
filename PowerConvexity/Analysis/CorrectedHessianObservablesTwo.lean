import PowerConvexity.Calculus.DensityCorrectedHessianTwo
import CHS.Analysis.HessianOscillationStep

/-! # The same actual corrected observables for all balls and directions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "J" => Fin 2 ⊕ Fin 2

def hessianCorrectionCoefficientTwo (C : ℝ) (z : J → ℝ) : ℝ :=
  C*‖∑ i, z i • Sum.elim realDirections imagDirections i‖^2/2

theorem hessianCorrectionCoefficientTwo_nonneg {C : ℝ} (hC : 0 ≤ C) (z : J → ℝ) :
    0 ≤ hessianCorrectionCoefficientTwo C z := by
  unfold hessianCorrectionCoefficientTwo
  positivity

def correctedHessianObservableTwo (C : ℝ) (u : E → ℝ) (z : J → ℝ) (x : E) : ℝ :=
  hessianObservable u z x+hessianCorrectionCoefficientTwo C z*u x

def correctedHessianOscillationTwo (t : Finset (J → ℝ)) (C : ℝ)
    (u : E → ℝ) (x₀ : E) (R : ℝ) : ℝ :=
  ∑ z : t, compactOsc (correctedHessianObservableTwo C u z.1) (closedBall x₀ R)

theorem correctedHessianObservableTwo_continuous
    (C : ℝ) {u : E → ℝ} (hu : ContDiff ℝ 4 u) (z : J → ℝ) :
    Continuous (correctedHessianObservableTwo C u z) :=
  (hessianObservable_continuous hu z).add (continuous_const.mul hu.continuous)

theorem correctedHessianObservableTwo_deficit_supersolution
    {U : Set E} (hU : IsOpen U) {u f : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hf : ContDiffOn ℝ 2 f U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (f x : ℂ))
    (hfp : ∀ x ∈ U, 0 < f x)
    (hA : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    {c : ℝ} (hc : 0 < c) (B : NormalizedEllipticCoeff (2+2) U)
    (hB : ∀ x ∈ U, B.1.a x = c⁻¹ • complexCofactorCoeff u x)
    {C : ℝ}
    (hsource : ∀ x ∈ U, ∀ v : E,
      -(C*‖v‖^2) ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2)
    (z : J → ℝ) (M : ℝ) {x₀ : E} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hclosed : closedBall x₀ R ⊆ U) :
    IsSupersolution (B.restrict
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hclosed)).1
      (fun y => M-correctedHessianObservableTwo C u z y) := by
  let v : E := ∑ i, z i • Sum.elim realDirections imagDirections i
  have h := density_corrected_directional_deficit_cofactor_supersolution_two
    hU hu hf hdet hfp hA hc B hB v (fun x hx => hsource x hx v) M hr hrR hclosed
  have he : (fun y => M-correctedHessianObservableTwo C u z y) =ᵐ[
      MeasureTheory.volume.restrict (ball x₀ r)]
      (fun y => M-(realHessian u y v v+(C*‖v‖^2/2)*u y)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with y hy
    have hyU := hclosed ((closedBall_subset_closedBall hrR.le) (ball_subset_closedBall hy))
    rw [correctedHessianObservableTwo,hessianObservable_eq_directional
      ((hu.contDiffAt (hU.mem_nhds hyU)).of_le (by norm_num))]
    rfl
  exact h.congr_ae he.symm

end PowerConvexity
