import PowerConvexity.Calculus.MatrixIdentities
import PowerConvexity.Algebra.DimensionTwo

/-!
# The actual third-derivative matrix in the local dimension-two argument

`W` is built from derivatives of the same potential.  Its skew-Hermitian
symmetry and its contracted trace constraint are proved, not assumed.  The
rank-one inverse representation remains an explicit normalization input to
the final local sign theorem.
-/

set_option autoImplicit false
open scoped BigOperators ContDiff Topology

namespace PowerConvexity

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The paper's `u_{k s q̄} - u_{k̄ s q̄}`. -/
noncomputable def skewThirdHessian (a b : ι → E) (u : E → ℝ) (k : ι) (x : E) :
    Matrix ι ι ℂ :=
  matrixDZ (a k) (b k) (complexHessian a b u) x -
    matrixDZ (a k) (-b k) (complexHessian a b u) x

theorem skewThirdHessian_conjTranspose {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (k : ι) :
    (skewThirdHessian a b u k x).conjTranspose = -skewThirdHessian a b u k x := by
  have hnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u y :=
    (hu.of_le (m := 2) (by norm_num)).eventually (by simp)
  have heq : (fun y => (complexHessian a b u y).conjTranspose) =ᶠ[𝓝 x]
      complexHessian a b u :=
    hnear.mono fun y hy => complexHessian_isHermitian hy a b
  have hadj (v w : E) :
      (matrixDZ v w (complexHessian a b u) x).conjTranspose =
        matrixDZ v (-w) (complexHessian a b u) x := by
    rw [← matrixDZ_conjTranspose]
    exact matrixDZ_congr_nhds v (-w) heq
  unfold skewThirdHessian
  rw [Matrix.conjTranspose_sub, hadj, hadj, neg_neg]
  abel

/-- The first differentiated CMA equation supplies the weighted trace zero. -/
theorem skewThirdHessian_trace_zero {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ)
    (k : ι) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      skewThirdHessian a b u k x p q) = 0 := by
  have hp := complexHessian_det_const_first hu a b hdet (a k) (b k)
  have hm := complexHessian_det_const_first hu a b hdet (a k) (-b k)
  simp only [skewThirdHessian, Matrix.sub_apply, matrixDZ, mul_sub,
    Finset.sum_sub_distrib, hp, hm, sub_self]

/-- The dimension-two algebraic sign for the actual third derivatives.
This is not yet the eigenvalue PDE `sigma_super_harmonic`. -/
theorem local_dimensionTwo_sign {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (a b : Fin 2 → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ)
    (k : Fin 2) (r : Fin 2 → ℂ)
    (hweight : (complexHessian a b u x)⁻¹ = rankOneWeightTwo r) :
    Complex.normSq (Matrix.trace (skewThirdHessian a b u k x)) ≤
      ∑ p, ∑ q, Complex.normSq (skewThirdHessian a b u k x p q) := by
  apply dimensionTwo_skew_sign _ (skewThirdHessian_conjTranspose hu a b k) r
  rw [← hweight]
  exact skewThirdHessian_trace_zero hu a b hdet k

end PowerConvexity
