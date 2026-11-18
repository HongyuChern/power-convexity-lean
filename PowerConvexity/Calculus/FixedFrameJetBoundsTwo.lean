import PowerConvexity.Calculus.HessianFrameFieldsTwo

/-! # A finite list of fixed-frame actual jets needed for uniform normalization -/
set_option autoImplicit false
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def fixedFrameJetBoundTwo (a b : Fin 2 → E) (u : E → ℝ) (x : E) (K : ℝ) : Prop :=
  matrixEntryBoundTwo (modifiedA a b u x) K ∧
  matrixEntryBoundTwo (modifiedA a b u x)⁻¹ K ∧
  matrixEntryBoundTwo (complexHessian a b u x)⁻¹ K ∧
  ‖(powerWeight (u x):ℂ)‖ ≤ K ∧
  (∀ i, ‖complexGradient a b u x i‖ ≤ K) ∧
  (∀ k p, matrixEntryBoundTwo (matrixDZ (a p) (b p) (powerHessianFieldsTwo a b u k) x) K) ∧
  (∀ k q, matrixEntryBoundTwo (matrixDZ (a q) (-b q) (powerHessianFieldsTwo a b u k) x) K) ∧
  (∀ p q, matrixEntryBoundTwo (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (modifiedA a b u)) x) K) ∧
  (∀ i, ‖a i‖ ≤ K) ∧ (∀ i, ‖b i‖ ≤ K)

theorem fixedFrameJetBoundTwo_mono (a b : Fin 2 → E) (u : E → ℝ) (x : E)
    {K L : ℝ} (h : fixedFrameJetBoundTwo a b u x K) (hKL : K ≤ L) :
    fixedFrameJetBoundTwo a b u x L := by
  obtain ⟨hA,hiA,hG,hh,hg,hp,hm,hpp,ha,hb⟩ := h
  exact ⟨matrixEntryBoundTwo_mono hA hKL,matrixEntryBoundTwo_mono hiA hKL,
    matrixEntryBoundTwo_mono hG hKL,hh.trans hKL,(fun i => (hg i).trans hKL),
    (fun k p => matrixEntryBoundTwo_mono (hp k p) hKL),
    (fun k q => matrixEntryBoundTwo_mono (hm k q) hKL),
    (fun p q => matrixEntryBoundTwo_mono (hpp p q) hKL),
    (fun i => (ha i).trans hKL),(fun i => (hb i).trans hKL)⟩

end PowerConvexity
