import PowerConvexity.Calculus.LinearizationCovariance
import PowerConvexity.Calculus.NormComplement

/-! # Covariance of the actual lowest-root field and its linearization -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedSigmaTwo_eventuallyEq_complexFrame {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0) {x : E} (hx : x ∈ U)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : IsUnit Q.det) :
    modifiedSigmaTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u =ᶠ[𝓝 x]
      modifiedSigmaTwo a b u := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact modifiedSigmaTwo_complexFrame (hu.contDiffAt (hU.mem_nhds hy)) (hneg y hy) Q hQ a b

theorem modifiedSigmaTwo_fderiv_complexFrame {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0) {x : E} (hx : x ∈ U)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : IsUnit Q.det) :
    fderiv ℝ (modifiedSigmaTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u) x =
      fderiv ℝ (modifiedSigmaTwo a b u) x :=
  (modifiedSigmaTwo_eventuallyEq_complexFrame hU hu a b hneg hx Q hQ).fderiv_eq

theorem modifiedSigmaTwo_contraction_complexFrame {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x))
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : IsUnit Q.det) :
    (∑ p,∑ q,(complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x)⁻¹ q p*
      dz (complexFrameReal Q a b q) (-complexFrameImag Q a b q)
        (dz (complexFrameReal Q a b p) (complexFrameImag Q a b p)
          (fun y => (modifiedSigmaTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u y:ℂ))) x) =
    (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigmaTwo a b u y:ℂ))) x) := by
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hs := modifiedSigmaTwo_contDiffAt_two hu4 (hneg x hx) a b (hA x hx) hgap
  have he := modifiedSigmaTwo_eventuallyEq_complexFrame hU (hu.of_le (by norm_num)) a b hneg hx Q hQ
  have hec : (fun y => (modifiedSigmaTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u y:ℂ))
      =ᶠ[𝓝 x] (fun y => (modifiedSigmaTwo a b u y:ℂ)) := he.mono (fun y hy => congrArg Complex.ofReal hy)
  calc
    _ = (∑ p,∑ q,(complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x)⁻¹ q p*
      dz (complexFrameReal Q a b q) (-complexFrameImag Q a b q)
        (dz (complexFrameReal Q a b p) (complexFrameImag Q a b p)
          (fun y => (modifiedSigmaTwo a b u y:ℂ))) x) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      rw [dz_dz_congr_nhds hec]
    _ = _ := complex_contraction_complexFrame (hu4.of_le (by norm_num)) hs Q hQ a b

end PowerConvexity
