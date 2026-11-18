import PowerConvexity.Calculus.QuadraticJointHessians
import PowerConvexity.Calculus.EigenvalueFieldTwo
import PowerConvexity.Calculus.QuadraticModifiedParameter
import CHS.Calculus.ClosureJets

/-! # Spectral continuity from actual pulled-back spatial jets

The parameter space is arbitrary. The derivatives in the hypotheses remain
actual derivatives of the physical potential, evaluated at the physical point.
Only their continuity after parameterization is required.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E P ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace P]

theorem actualFamily_complexGradient_continuousOn
    (a b : ι → E) (u : P → E → ℝ) (x : P → E) {S : Set P}
    (hu : ∀ p ∈ S, DifferentiableAt ℝ (u p) (x p))
    (hD : ContinuousOn (fun p => fderiv ℝ (u p) (x p)) S) :
    ContinuousOn (fun p => complexGradient a b (u p) (x p)) S := by
  apply ((continuous_jetWirtinger a b).comp_continuousOn hD).congr
  intro p hp
  funext i
  exact complexGradient_real_entry (hu p hp) a b i

theorem actualFamily_complexHessian_continuousOn
    (a b : ι → E) (u : P → E → ℝ) (x : P → E) {S : Set P}
    (hu : ∀ p ∈ S, ContDiffAt ℝ 2 (u p) (x p))
    (hH : ContinuousOn (fun p => realHessian (u p) (x p)) S) :
    ContinuousOn (fun p => complexHessian a b (u p) (x p)) S := by
  apply ((continuous_jetComplexHessian a b).comp_continuousOn hH).congr
  intro p hp
  funext i j
  exact complexHessian_real_entry (hu p hp) a b i j

theorem actualFamily_pureHessian_continuousOn
    (a b : ι → E) (u : P → E → ℝ) (x : P → E) {S : Set P}
    (hu : ∀ p ∈ S, ContDiffAt ℝ 2 (u p) (x p))
    (hH : ContinuousOn (fun p => realHessian (u p) (x p)) S) :
    ContinuousOn (fun p => pureHessian a b (u p) (x p)) S := by
  apply ((continuous_jetPureHessian a b).comp_continuousOn hH).congr
  intro p hp
  funext i j
  exact pureHessian_real_entry (hu p hp) a b i j

variable [Fintype ι] [DecidableEq ι]

theorem schurQuotient_continuousWithinAt
    {A B : P → Matrix ι ι ℂ} {S : Set P} {p : P}
    (hAc : ContinuousWithinAt A S p) (hBc : ContinuousWithinAt B S p)
    (hA : (A p).PosDef) :
    ContinuousWithinAt (fun z => matrixSchur (A z) (B z)*(A z)⁻¹) S p := by
  have hAb : (A p).map star = (A p).transpose := by
    ext i j
    exact hA.isHermitian.apply j i
  have hn : ((A p).map star).det ≠ 0 := by
    rw [hAb,Matrix.det_transpose]
    exact ne_of_gt hA.det_pos
  have hAbc : ContinuousWithinAt (fun z => (A z).map star) S p := by
    have hs : Continuous (fun M : Matrix ι ι ℂ => M.map star) := by fun_prop
    exact hs.continuousAt.comp_continuousWithinAt hAc
  have hBbc : ContinuousWithinAt (fun z => (B z).map star) S p := by
    have hs : Continuous (fun M : Matrix ι ι ℂ => M.map star) := by fun_prop
    exact hs.continuousAt.comp_continuousWithinAt hBc
  have hRI : (Ring.inverse : ℂ → ℂ) = Inv.inv := by
    funext z
    exact Ring.inverse_eq_inv z
  have hI : ContinuousWithinAt (fun z => ((A z).map star)⁻¹) S p := by
    apply ContinuousAt.comp_continuousWithinAt ?_ hAbc
    apply continuousAt_matrix_inv
    rw [hRI]
    exact continuousAt_id.inv₀ hn
  have hJ : ContinuousWithinAt (fun z => (A z)⁻¹) S p := by
    apply ContinuousAt.comp_continuousWithinAt ?_ hAc
    apply continuousAt_matrix_inv
    rw [hRI]
    exact continuousAt_id.inv₀ (ne_of_gt hA.det_pos)
  exact (hAc.sub ((hBc.mul hI).mul hBbc)).mul hJ

theorem actualFamily_modifiedSigmaTwo_continuousOn_of_jets
    (a b : Fin 2 → E) (u : P → E → ℝ) (x : P → E) {S : Set P}
    (hu : ∀ p ∈ S, ContDiffAt ℝ 2 (u p) (x p))
    (hv : ContinuousOn (fun p => u p (x p)) S)
    (hD : ContinuousOn (fun p => fderiv ℝ (u p) (x p)) S)
    (hH : ContinuousOn (fun p => realHessian (u p) (x p)) S)
    (hneg : ∀ p ∈ S, u p (x p) < 0)
    (hpos : ∀ p ∈ S, (complexHessian a b (u p) (x p)).PosDef) :
    ContinuousOn (fun p => modifiedSigmaTwo a b (u p) (x p)) S := by
  have hg := actualFamily_complexGradient_continuousOn a b u x
    (fun p hp => (hu p hp).differentiableAt (by norm_num)) hD
  have hm := actualFamily_complexHessian_continuousOn a b u x hu hH
  have hpure := actualFamily_pureHessian_continuousOn a b u x hu hH
  have hd : ContinuousOn (fun p => ((2*(-u p (x p)):ℝ):ℂ)) S :=
    Complex.ofRealCLM.continuous.comp_continuousOn (continuousOn_const.mul hv.neg)
  have hden (p : P) (hp : p ∈ S) : ((2*(-u p (x p)):ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos (by norm_num) (neg_pos.mpr (hneg p hp))))
  have hAc : ContinuousOn (fun p => modifiedA a b (u p) (x p)) S := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simp only [modifiedA,div_eq_mul_inv]
    exact ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hm)).add
      ((((continuous_apply i).comp_continuousOn hg).mul
        (Complex.conjCLE.continuous.comp_continuousOn ((continuous_apply j).comp_continuousOn hg))).mul
        (hd.inv₀ hden))
  have hBc : ContinuousOn (fun p => modifiedB a b (u p) (x p)) S := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simp only [modifiedB,div_eq_mul_inv]
    exact ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hpure)).add
      ((((continuous_apply i).comp_continuousOn hg).mul
        ((continuous_apply j).comp_continuousOn hg)).mul (hd.inv₀ hden))
  intro p hp
  exact lowerEigenvalueTwo_continuous.continuousAt.comp_continuousWithinAt
    (schurQuotient_continuousWithinAt (hAc p hp) (hBc p hp)
      (modifiedA_posDef a b (hneg p hp) (hpos p hp)))

end PowerConvexity
