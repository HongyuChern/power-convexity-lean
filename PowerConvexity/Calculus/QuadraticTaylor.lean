import PowerConvexity.Calculus.QuadraticClass

/-! # Exact quadratic Taylor reconstruction and determination by an open set -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem quadratic_coeff_hasFDerivAt (c : ℝ) (l : E →L[ℝ] ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (hs : ∀ v w, H v w = H w v) (x : E) :
    HasFDerivAt (fun y => c+l y+H y y) (l+(2:ℝ) • H x) x := by
  have hh := H.hasFDerivAt.clm_apply (hasFDerivAt_id x)
  convert ((hasFDerivAt_const c x).add l.hasFDerivAt).add hh using 1 <;> try rfl
  ext v
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply,smul_apply,smul_eq_mul,id_eq]
  rw [hs v x]
  ring

theorem quadratic_coeff_realHessian (c : ℝ) (l : E →L[ℝ] ℝ)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (hs : ∀ v w, H v w = H w v) (x : E) :
    realHessian (fun y => c+l y+H y y) x = (2:ℝ) • H := by
  have hD : fderiv ℝ (fun y => c+l y+H y y) = fun y => l+(2:ℝ) • H y :=
    funext fun y => (quadratic_coeff_hasFDerivAt c l H hs y).fderiv
  unfold realHessian
  rw [hD]
  exact (((H.hasFDerivAt (x := x)).const_smul (2:ℝ)).const_add l).fderiv

theorem quadratic_exact_Taylor {q : E → ℝ} (hq : IsQuadraticPolynomial q) (x y : E) :
    q y = q x + fderiv ℝ q x (y-x) + (1/2:ℝ)*realHessian q x (y-x) (y-x) := by
  obtain ⟨c,l,H,hs,he⟩ := hq
  have hfun : q = fun y => c+l y+H y y := funext he
  rw [hfun,(quadratic_coeff_hasFDerivAt c l H hs x).fderiv,
    quadratic_coeff_realHessian c l H hs]
  simp only [add_apply,smul_apply,smul_eq_mul,map_sub,sub_apply]
  rw [hs y x]
  ring

theorem quadratic_zero_of_two_jet_zero {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (x : E) (h0 : q x = 0) (h1 : fderiv ℝ q x = 0) (h2 : realHessian q x = 0) :
    q = 0 := by
  funext y
  rw [quadratic_exact_Taylor hq x y,h0,h1,h2]
  simp

theorem quadratic_zero_of_eventually_zero {q : E → ℝ} (hq : IsQuadraticPolynomial q)
    {x : E} (hz : q =ᶠ[𝓝 x] fun _ => 0) : q = 0 := by
  apply quadratic_zero_of_two_jet_zero hq x hz.self_of_nhds
  · simpa using hz.fderiv_eq (𝕜 := ℝ)
  · have hh := (hz.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    simpa [realHessian] using hh

theorem IsQuadraticPolynomial_add {q h : E → ℝ}
    (hq : IsQuadraticPolynomial q) (hh : IsQuadraticPolynomial h) :
    IsQuadraticPolynomial (q+h) := by
  obtain ⟨c,l,H,hs,he⟩ := hq
  obtain ⟨d,m,J,js,je⟩ := hh
  refine ⟨c+d,l+m,H+J,?_,?_⟩
  · intro v w
    simp only [add_apply,hs v w,js v w]
  · intro y
    simp only [Pi.add_apply,he y,je y,add_apply]
    ring

end PowerConvexity
