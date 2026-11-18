import CHS.Calculus.BasisHessian
import CHS.Calculus.ClosureRegularity

/-! Initial dependency check for the real/complex Hessian interface in §2.1. -/

set_option autoImplicit false

namespace PowerConvexity

open CHS.Calculus
open scoped ComplexOrder ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem probe_realHessian_posDef_iff_schur {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : Fin 2 → E)
    (hA : (complexHessian a b u x).PosDef) :
    (realBlockHessian a b u x).PosDef ↔ (schurHessian a b u x).PosDef := by
  obtain ⟨hReal, hSchur⟩ := realBlockHessian_posDef_equivalences hu a b hA
  exact hReal.trans hSchur

#check @complexHessian
#check @pureHessian
#check @matrix_differential_identities
#check @schurHessian_LM
#check @schurHessian_LM_nonpos
#check @ClosureC2Jet
#print axioms probe_realHessian_posDef_iff_schur

end PowerConvexity
