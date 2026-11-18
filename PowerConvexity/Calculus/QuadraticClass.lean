import PowerConvexity.Calculus.PerturbationJets

/-! # The actual class of real quadratic pluriharmonic perturbations -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Constant, linear and symmetric bilinear coefficients; degree at most two. -/
def IsQuadraticPolynomial (q : E → ℝ) : Prop :=
  ∃ (c : ℝ) (l : E →L[ℝ] ℝ) (H : E →L[ℝ] E →L[ℝ] ℝ),
    (∀ v w, H v w = H w v) ∧ ∀ y, q y = c + l y + H y y

def IsPluriharmonicQuadratic {ι : Type*} (a b : ι → E) (q : E → ℝ) : Prop :=
  IsQuadraticPolynomial q ∧ ∀ x, complexHessian a b q x = 0

theorem IsQuadraticPolynomial_contDiff {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) (k : ℕ∞ω) : ContDiff ℝ k q := by
  obtain ⟨c, l, H, _, hq⟩ := hq
  have he : q = fun y => c + l y + H y y := funext hq
  rw [he]
  exact (contDiff_const.add l.contDiff).add (H.contDiff.clm_apply contDiff_id)

theorem IsQuadraticPolynomial_const_mul {q : E → ℝ}
    (hq : IsQuadraticPolynomial q) (r : ℝ) : IsQuadraticPolynomial (fun y => r*q y) := by
  obtain ⟨c, l, H, hs, he⟩ := hq
  refine ⟨r*c, r • l, r • H, ?_, ?_⟩
  · intro v w
    simp only [smul_apply, smul_eq_mul, hs v w]
  · intro y
    simp only [he y, smul_apply, smul_eq_mul]
    ring

theorem realPartSquare_isQuadraticPolynomial (ell : E →L[ℝ] ℂ) (c : E) :
    IsQuadraticPolynomial (realPartSquare ell c) := by
  let R := Complex.reCLM.comp ell
  let J := Complex.imCLM.comp ell
  let H := R.smulRight R - J.smulRight J
  let l := (-2*R c) • R + (2*J c) • J
  refine ⟨(R c)^2 - (J c)^2, l, H, ?_, ?_⟩
  · intro v w
    simp only [H, sub_apply, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
    ring
  · intro y
    simp only [realPartSquare, pow_two, map_sub, Complex.mul_re,
      Complex.sub_re, Complex.sub_im, l, H, R, J, add_apply, sub_apply,
      ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    ring

theorem realPartSquare_isPluriharmonicQuadratic {ι : Type*}
    (ell : E →L[ℝ] ℂ) (c : E) (a b : ι → E)
    (hJ : ∀ i, ell (b i) = Complex.I * ell (a i)) :
    IsPluriharmonicQuadratic a b (realPartSquare ell c) :=
  ⟨realPartSquare_isQuadraticPolynomial ell c,
    realPartSquare_mixedHessian_zero ell c a b hJ⟩

theorem IsPluriharmonicQuadratic_const_mul {ι : Type*} {a b : ι → E} {q : E → ℝ}
    (hq : IsPluriharmonicQuadratic a b q) (r : ℝ) :
    IsPluriharmonicQuadratic a b (fun y => r*q y) := by
  refine ⟨IsQuadraticPolynomial_const_mul hq.1 r, ?_⟩
  intro x
  rw [complexHessian_const_mul_at (IsQuadraticPolynomial_contDiff hq.1 2).contDiffAt,
    hq.2 x, smul_zero]

end PowerConvexity
