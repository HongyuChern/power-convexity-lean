import PowerConvexity.Calculus.ActualJetSpectrumContinuityTwo

/-! # Local spectral continuity at the unperturbed branch

The neighborhood may contain parameters outside the negative/positive branch.
Only actual jets are continuous there; invertibility and negativity are used
at the evaluation point. This avoids a circular small-radius assumption.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace P]

theorem actualFamily_modifiedSigmaTwo_continuousWithinAt_of_jets
    (a b : Fin 2 → E) (u : P → E → ℝ) (x : P → E) {S : Set P}
    (hu : ∀ p ∈ S, ContDiffAt ℝ 2 (u p) (x p))
    (hv : ContinuousOn (fun p => u p (x p)) S)
    (hD : ContinuousOn (fun p => fderiv ℝ (u p) (x p)) S)
    (hH : ContinuousOn (fun p => realHessian (u p) (x p)) S)
    {p : P} (hp : p ∈ S) (hneg : u p (x p) < 0)
    (hpos : (complexHessian a b (u p) (x p)).PosDef) :
    ContinuousWithinAt (fun p => modifiedSigmaTwo a b (u p) (x p)) S p := by
  have hg := actualFamily_complexGradient_continuousOn a b u x
    (fun p hp => (hu p hp).differentiableAt (by norm_num)) hD
  have hm := actualFamily_complexHessian_continuousOn a b u x hu hH
  have hpure := actualFamily_pureHessian_continuousOn a b u x hu hH
  have hd : ContinuousWithinAt (fun p => ((2*(-u p (x p)):ℝ):ℂ)) S p :=
    Complex.ofRealCLM.continuous.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_const.mul (hv p hp).neg)
  have hden : ((2*(-u p (x p)):ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos (by norm_num) (neg_pos.mpr hneg)))
  have hAc : ContinuousWithinAt (fun p => modifiedA a b (u p) (x p)) S p := by
    apply continuousWithinAt_pi.mpr
    intro i
    apply continuousWithinAt_pi.mpr
    intro j
    simp only [modifiedA,div_eq_mul_inv]
    exact ((continuous_apply j).continuousAt.comp_continuousWithinAt ((continuous_apply i).continuousAt.comp_continuousWithinAt (hm p hp))).add
      ((((continuous_apply i).continuousAt.comp_continuousWithinAt (hg p hp)).mul
        (Complex.conjCLE.continuous.continuousAt.comp_continuousWithinAt ((continuous_apply j).continuousAt.comp_continuousWithinAt (hg p hp)))).mul
        (hd.inv₀ hden))
  have hBc : ContinuousWithinAt (fun p => modifiedB a b (u p) (x p)) S p := by
    apply continuousWithinAt_pi.mpr
    intro i
    apply continuousWithinAt_pi.mpr
    intro j
    simp only [modifiedB,div_eq_mul_inv]
    exact ((continuous_apply j).continuousAt.comp_continuousWithinAt ((continuous_apply i).continuousAt.comp_continuousWithinAt (hpure p hp))).add
      ((((continuous_apply i).continuousAt.comp_continuousWithinAt (hg p hp)).mul
        ((continuous_apply j).continuousAt.comp_continuousWithinAt (hg p hp))).mul (hd.inv₀ hden))
  exact lowerEigenvalueTwo_continuous.continuousAt.comp_continuousWithinAt
    (schurQuotient_continuousWithinAt hAc hBc
      (modifiedA_posDef a b hneg hpos))


end PowerConvexity
