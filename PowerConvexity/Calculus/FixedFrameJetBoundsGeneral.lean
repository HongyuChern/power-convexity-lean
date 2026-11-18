import PowerConvexity.Calculus.HessianFrameFieldsGeneral

/-! # A finite list of fixed-frame actual jets needed for uniform normalization -/
set_option autoImplicit false
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def fixedFrameJetBoundGeneral (a b : ι → E) (u : E → ℝ) (x : E) (K : ℝ) : Prop :=
  matrixEntryBoundGeneral (modifiedA a b u x) K ∧
  matrixEntryBoundGeneral (modifiedA a b u x)⁻¹ K ∧
  matrixEntryBoundGeneral (complexHessian a b u x)⁻¹ K ∧
  ‖(powerWeight (u x):ℂ)‖ ≤ K ∧
  (∀ i, ‖complexGradient a b u x i‖ ≤ K) ∧
  (∀ k p, matrixEntryBoundGeneral (matrixDZ (a p) (b p) (powerHessianFieldsGeneral a b u k) x) K) ∧
  (∀ k q, matrixEntryBoundGeneral (matrixDZ (a q) (-b q) (powerHessianFieldsGeneral a b u k) x) K) ∧
  (∀ p q, matrixEntryBoundGeneral (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (modifiedA a b u)) x) K) ∧
  (∀ i, ‖a i‖ ≤ K) ∧ (∀ i, ‖b i‖ ≤ K)

theorem fixedFrameJetBoundGeneral_mono (a b : ι → E) (u : E → ℝ) (x : E)
    {K L : ℝ} (h : fixedFrameJetBoundGeneral a b u x K) (hKL : K ≤ L) :
    fixedFrameJetBoundGeneral a b u x L := by
  obtain ⟨hA,hiA,hG,hh,hg,hp,hm,hpp,ha,hb⟩ := h
  exact ⟨matrixEntryBoundGeneral_mono hA hKL,matrixEntryBoundGeneral_mono hiA hKL,
    matrixEntryBoundGeneral_mono hG hKL,hh.trans hKL,(fun i => (hg i).trans hKL),
    (fun k p => matrixEntryBoundGeneral_mono (hp k p) hKL),
    (fun k q => matrixEntryBoundGeneral_mono (hm k q) hKL),
    (fun p q => matrixEntryBoundGeneral_mono (hpp p q) hKL),
    (fun i => (ha i).trans hKL),(fun i => (hb i).trans hKL)⟩

end PowerConvexity
