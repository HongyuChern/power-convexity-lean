import PowerConvexity.Analysis.StrictSubharmonicMaximum
import PowerConvexity.Calculus.ComplexGradientMinimum

/-!
# Negativity of a classical Dirichlet solution on the strict psh branch

Only interior C2 regularity, continuity on the compact closure and zero
boundary values are required here.  Strict plurisubharmonicity is retained
as an actual positive complex Hessian, not inferred from its determinant.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem complex_trace_eq_real_contraction {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    (complexHessian a b u x).trace.re =
      complexHessianContraction a b 1 (realHessian u x) := by
  rw [← complexHessianContraction_pairing a b 1 hu]
  have huc : ContDiffAt ℝ 2 (fun y => (u y:ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  simp_rw [dz_comm_at huc (a _) (-b _) (a _) (b _)]
  simp [Matrix.one_apply,Matrix.trace,Matrix.diag,complexHessian]

theorem strictPshDirichlet_negative {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (a b : ι → E) (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef) :
    ∀ x ∈ U, u x < 0 := by
  apply negative_of_positive_hessian_contraction hU hK huc hu hboundary
    (fun _ => complexHessianContraction a b 1)
    (fun _ _ => complexHessianContraction_positive a b Matrix.PosDef.one)
  intro x hx
  rw [← complex_trace_eq_real_contraction (hu.contDiffAt (hU.mem_nhds hx))]
  exact (Complex.pos_iff.mp (hpsh x hx).trace_pos).1

end PowerConvexity
