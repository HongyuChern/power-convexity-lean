import PowerConvexity.Calculus.CoordinateCovariance

/-! # Real linear dependence of constant complex frames on their matrix -/
set_option autoImplicit false
open scoped BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem complexFrameReal_add (A B : Matrix ι ι ℂ) (a b : ι → E) :
    complexFrameReal (A+B) a b = fun i => complexFrameReal A a b i+complexFrameReal B a b i := by
  funext i
  simp only [complexFrameReal,Matrix.add_apply,Complex.add_re,Complex.add_im,add_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  abel

theorem complexFrameImag_add (A B : Matrix ι ι ℂ) (a b : ι → E) :
    complexFrameImag (A+B) a b = fun i => complexFrameImag A a b i+complexFrameImag B a b i := by
  funext i
  simp only [complexFrameImag,Matrix.add_apply,Complex.add_re,Complex.add_im,add_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  abel

theorem complexFrameReal_real_smul (c : ℝ) (A : Matrix ι ι ℂ) (a b : ι → E) :
    complexFrameReal ((c:ℂ) • A) a b = fun i => c • complexFrameReal A a b i := by
  funext i
  simp only [complexFrameReal,Matrix.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero,Finset.smul_sum,smul_add,smul_smul]

theorem complexFrameImag_real_smul (c : ℝ) (A : Matrix ι ι ℂ) (a b : ι → E) :
    complexFrameImag ((c:ℂ) • A) a b = fun i => c • complexFrameImag A a b i := by
  funext i
  simp only [complexFrameImag,Matrix.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero,Finset.smul_sum,smul_sub,smul_smul]

end PowerConvexity
