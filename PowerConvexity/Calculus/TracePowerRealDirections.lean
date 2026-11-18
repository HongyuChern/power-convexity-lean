import PowerConvexity.Calculus.ModifiedTracePowerReal
import PowerConvexity.Calculus.ExtremalEigenvalueRealDerivatives

/-! # Appendix B trace limits in literal real Frechet directional derivatives -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem paper_B3_1_tracePowerRoot_real_first_limit {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (k : ι → ℝ) (i : ι)
    (hdiag : K x = Matrix.diagonal (fun j => (k j:ℂ)))
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i)
    (hreal : ∀ n : ℕ, ∀ y ∈ U, (K y ^ (n+1)).trace.im = 0) (v : E) :
    Filter.Tendsto (fun n : ℕ => fderiv ℝ (fun y => (tracePowerRoot K (n+1) y:ℂ)) x v)
      Filter.atTop (𝓝 (fderiv ℝ (fun y => K y i i) x v)) := by
  simpa only [dz_add_self_zero] using
    paper_B3_1_tracePowerRoot_first_limit hU hK hx k i hdiag hi h0 hgap hreal (v+v) 0

theorem paper_B3_2_tracePowerRoot_real_second_limit {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (k : ι → ℝ) (i : ι)
    (hdiag : K x = Matrix.diagonal (fun j => (k j:ℂ)))
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i)
    (hreal : ∀ n : ℕ, ∀ y ∈ U, (K y ^ (n+2)).trace.im = 0) (v w : E) :
    Filter.Tendsto (fun n : ℕ => fderiv ℝ
      (fun y => fderiv ℝ (fun z => (tracePowerRoot K (n+2) z:ℂ)) y v) x w)
      Filter.atTop (𝓝 (fderiv ℝ (fun y => fderiv ℝ (fun z => K z i i) y v) x w +
        ∑ j ∈ Finset.univ.erase i,
          (fderiv ℝ (fun y => K y i j) x w * fderiv ℝ (fun y => K y j i) x v +
            fderiv ℝ (fun y => K y i j) x v * fderiv ℝ (fun y => K y j i) x w) /
            ((k i-k j:ℝ):ℂ))) := by
  simpa only [matrixDZ,dz_add_self_zero] using
    paper_B3_2_tracePowerRoot_second_limit hU hK hx k i hdiag hi h0 hgap hreal (v+v) 0 (w+w) 0

/-- Actual C4 modifiedK downstream application, with real directions and no
assumed differentiable eigenvalue branch or assumed real trace powers. -/
theorem modifiedK_tracePowerRoot_real_second_limit_actual_largest [CompleteSpace E]
    {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hneg : ∀ y ∈ U, u y < 0) (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (k : ι → ℝ) (i : ι)
    (hdiag : modifiedK a b u x = Matrix.diagonal (fun j => (k j:ℂ)))
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i)
    (v w : E) :
    Filter.Tendsto (fun n : ℕ => fderiv ℝ
      (fun y => fderiv ℝ (fun z => (tracePowerRoot (modifiedK a b u) (n+2) z:ℂ)) y v) x w)
      Filter.atTop (𝓝 (fderiv ℝ (fun y => fderiv ℝ
        (fun z => (largestRealEigenvalue (modifiedK a b u z):ℂ)) y v) x w)) := by
  simpa only [dz_add_self_zero] using
    modifiedK_tracePowerRoot_second_limit_actual_largest hU hu a b hneg hA hx k i hdiag
      hi h0 hgap (v+v) 0 (w+w) 0

end PowerConvexity
