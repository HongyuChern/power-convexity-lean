import PowerConvexity.Analysis.ActualHolderJetCofactorCoefficientTwo
import PowerConvexity.Analysis.ActualCofactorBoundedHolderInverseTwo

/-! # The actual classical Holder jet has a bounded determinant inverse

Both the elliptic coefficient and its closure Holder bound are constructed
from this very jet. No inverse, boundary-expansion or coefficient Holder
hypothesis is supplied. The background is the genuine strict subsolution
used in the weak Dirichlet construction.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] holderResponseJetSeminormedGroup

theorem actual_holder_jet_determinant_bounded_inverse_two
    {U : Set E} [CompactSpace (closure U)]
    (hU : IsOpen U) (hK : IsCompact (closure U)) (hproper : U≠univ) (hconv : Convex ℝ U)
    {o : E} {r₀ diameter alpha : ℝ} (hr₀ : 0 < r₀) (hdia : 0 ≤ diameter)
    (hball : closedBall o r₀ ⊆ U) (hdiam : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter)
    {phi : E → ℝ} (hphi : ContDiff ℝ 3 phi)
    (hphi0 : ∀ c ∈ frontier U, phi c=0) (hDphi : ∀ c ∈ frontier U, fderiv ℝ phi c≠0)
    (hdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z∈U ↔ phi z<0)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian realDirections imagDirections w x).PosDef)
    (hwb : ∀ x ∈ frontier U, w x=0)
    (p : actualHolderC2JetSpaceTwo U alpha)
    (hu : ContDiffOn ℝ 4 (actualClosureExtensionTwo U p.1.1) U)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections
      (actualClosureExtensionTwo U p.1.1) x).PosDef)
    {rho : E → ℝ}
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections
      (actualClosureExtensionTwo U p.1.1) x).det=(rho x : ℂ))
    (hrho : ContDiff ℝ 1 rho) (hrho1 : ∀ x ∈ U, 1 ≤ rho x) :
    ∃ S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha,
      (actualHolderDeterminantDerivativeTwo U alpha realDirections imagDirections p).comp S=
        ContinuousLinearMap.id ℝ (actualHolderLoadSpaceTwo (closure U) ℝ alpha) ∧
      S.comp (actualHolderDeterminantDerivativeTwo U alpha realDirections imagDirections p)=
        ContinuousLinearMap.id ℝ (actualHolderC2JetSpaceTwo U alpha) := by
  have hdet1 : ∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections
      (actualClosureExtensionTwo U p.1.1) x).det.re := by
    intro x hx
    rw [hdet x hx,Complex.ofReal_re]
    exact hrho1 x hx
  obtain ⟨c,hc,Ka,hKa,A,hAl,hA,hAH⟩ :=
    actual_holder_jet_cofactor_coefficient_two hU alpha p hu hpos hdet1
  have huM : ∀ x ∈ closure U, -actualClosureExtensionTwo U p.1.1 x ≤ ‖p.1.1‖ := by
    intro x hx
    rw [actualClosureExtensionTwo_apply U p.1.1 hx]
    apply (neg_le_abs _).trans
    exact p.1.1.norm_coe_le_norm ⟨x,hx⟩
  exact actual_holder_determinant_derivative_bounded_inverse_two hU hK hproper hconv hr₀ hdia
    hball hdiam hphi hphi0 hDphi hdef halpha halpha1 hKa hw hwp hwb p hu hpos hdet
    hrho hrho1 hc (norm_nonneg p.1.1) huM A hA hAH

end PowerConvexity
