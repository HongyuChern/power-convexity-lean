import PowerConvexityComparator.AppendixAProblem
import PowerConvexity.Calculus.HessianDeterminant
import PowerConvexity.Algebra.ArrowMatrixThree

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace PowerConvexityComparator.AppendixASolution
open AppendixAProblem CHS.Calculus

theorem mixed_eq {n : ℕ} {u : CN n → ℝ} {x : CN n} (hu : ContDiffAt ℝ 2 u x) :
    complexHessian xAxis yAxis u x = mixed u x := by
  ext i j
  exact complexHessian_real_entry hu xAxis yAxis i j

theorem pure_eq {n : ℕ} {u : CN n → ℝ} {x : CN n} (hu : ContDiffAt ℝ 2 u x) :
    pureHessian xAxis yAxis u x = pure u x := by
  ext i j
  exact pureHessian_real_entry hu xAxis yAxis i j

theorem a1Answer : A1Statement := by
  intro n u x hu hA
  have hA' : IsUnit (complexHessian xAxis yAxis u x).det := by
    rw [mixed_eq hu]
    exact isUnit_iff_ne_zero.mpr hA
  have h := PowerConvexity.actual_hessian_determinant_identity_interleaved hu xAxis yAxis hA'
  have hD : (Matrix.of (fun i j : Fin n × Fin 2 => realHessian u x
      (if i.2 = 0 then xAxis i.1 else yAxis i.1)
      (if j.2 = 0 then xAxis j.1 else yAxis j.1))) = realMatrix u x := rfl
  rw [hD, mixed_eq hu, pure_eq hu, Fintype.card_fin] at h
  exact h

theorem a2Answer : A2Statement := by
  intro A B C β γ hB hC
  exact PowerConvexity.arrowMatrixThree_posSemidef_iff A B C β γ hB hC

end PowerConvexityComparator.AppendixASolution
