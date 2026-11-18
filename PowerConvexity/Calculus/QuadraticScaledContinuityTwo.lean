import PowerConvexity.Calculus.QuadraticJointSpectrumTwo

/-! # Joint continuity for the actual scaled perturbation homotopy -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB CHS.Calculus.complexHessian CHS.Calculus.pureHessian complexGradient
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem quadraticFamily_scaled_spectrum_continuousOn
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : Fin 2 → E)
    {u : E → ℝ} {X : Set E} {S : Set P} {T : Set ℝ}
    (hu : ∀ x ∈ X, ContDiffAt ℝ 2 u x)
    (hneg : ∀ t ∈ T, ∀ x ∈ X, ∀ p ∈ S, u x+t*(F p).val x < 0)
    (hA : ∀ t ∈ T, ∀ x ∈ X, ∀ p ∈ S,
      (modifiedA a b (fun y => u y+t*(F p).val y) x).PosDef) :
    ContinuousOn (fun z : ℝ × (E × P) => modifiedSigmaTwo a b
      (fun y => u y+z.1*(F z.2.2).val y) z.2.1) (T ×ˢ (X ×ˢ S)) := by
  intro z hz
  have he (t : ℝ) (p : P) : (F (t • p)).val = fun y => t*(F p).val y := by
    rw [map_smul]
    rfl
  have hc := quadraticFamily_joint_modifiedSigmaTwo_continuousAt F a b
    (hu z.2.1 hz.2.1)
    (show u z.2.1+(F (z.1 • z.2.2)).val z.2.1 < 0 by rw [he]; exact hneg _ hz.1 _ hz.2.1 _ hz.2.2)
    (show (modifiedA a b (fun y => u y+(F (z.1 • z.2.2)).val y) z.2.1).PosDef by
      rw [he]; exact hA _ hz.1 _ hz.2.1 _ hz.2.2)
  have hm : ContinuousAt (fun w : ℝ × (E × P) => (w.2.1,w.1 • w.2.2)) z := by fun_prop
  have hh := (hc.comp (f := fun w : ℝ × (E × P) => (w.2.1,w.1 • w.2.2))
    (x := z) hm).continuousWithinAt (s := T ×ˢ (X ×ˢ S))
  simpa only [Function.comp_def,he] using hh

end PowerConvexity
