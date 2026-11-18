import PowerConvexity.Analysis.ContractionZero
import PowerConvexity.Calculus.ComplexGradientMinimum

/-! # Full real Hessian vanishes at a zero elliptic contraction of a local minimum -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem complexHessianContraction_eq_zero_iff
    (a b : ι → E) (e : Module.Basis (ι ⊕ ι) ℝ E)
    (he : (e : (ι ⊕ ι) → E) = Sum.elim a b)
    {W : Matrix ι ι ℂ} (hW : W.PosDef)
    (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hs : ∀ v w, H v w = H w v) (hn : ∀ v, 0 ≤ H v v) :
    complexHessianContraction a b W H = 0 ↔ H = 0 := by
  simpa only [complexHessianContraction,he] using
    matrixHessianContraction_eq_zero_iff e (realLinearizationMatrix_posDef hW) H hs hn

theorem realHessian_eq_zero_of_localMin_linearized_zero
    (a b : ι → E) (e : Module.Basis (ι ⊕ ι) ℝ E)
    (he : (e : (ι ⊕ ι) → E) = Sum.elim a b)
    {u f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hmin : IsLocalMin f x) (hpsh : (complexHessian a b u x).PosDef)
    (hzero : complexLinearized a b u f x = 0) : realHessian f x = 0 := by
  rw [complexLinearized_eq_real a b u hf] at hzero
  exact (complexHessianContraction_eq_zero_iff a b e he hpsh.inv
    (realHessian f x) (realHessian_symm hf) (realHessian_nonneg_of_isLocalMin hf hmin)).mp hzero

end PowerConvexity
