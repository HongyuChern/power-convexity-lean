import PowerConvexity.Analysis.ActualCenteredResidualFour

/-! # Translated scalar rescaling with the original actual ellipticity constants -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualCenteredScalarCoeffFour {U V : Set E} (c : E) {r : ℝ} (hr : 0 < r)
    (A : EllipticCoeff (2+2) U) (hmap : MapsTo (fun z : E => c+r • z) V U) :
    EllipticCoeff (2+2) V :=
  (actualComposedLinearCoeffFour (actualScalarDilationEquivFour r hr.ne')
    (actualTranslatedCoeffFour c A)).restrict hmap

@[simp] theorem actualCenteredScalarCoeffFour_a {U V : Set E} (c : E) {r : ℝ} (hr : 0 < r)
    (A : EllipticCoeff (2+2) U) (hmap : MapsTo (fun z : E => c+r • z) V U) (z : E) :
    (actualCenteredScalarCoeffFour c hr A hmap).a z=A.a (c+r • z) := rfl

@[simp] theorem actualCenteredScalarCoeffFour_lam {U V : Set E} (c : E) {r : ℝ} (hr : 0 < r)
    (A : EllipticCoeff (2+2) U) (hmap : MapsTo (fun z : E => c+r • z) V U) :
    (actualCenteredScalarCoeffFour c hr A hmap).lam=A.lam := rfl

@[simp] theorem actualCenteredScalarCoeffFour_Lambda {U V : Set E} (c : E) {r : ℝ} (hr : 0 < r)
    (A : EllipticCoeff (2+2) U) (hmap : MapsTo (fun z : E => c+r • z) V U) :
    (actualCenteredScalarCoeffFour c hr A hmap).Λ=A.Λ := rfl

theorem actual_centered_scalar_coeff_regular_four {U V : Set E} (c : E) {r : ℝ} (hr : 0 < r)
    (A : EllipticCoeff (2+2) U) (hmap : MapsTo (fun z : E => c+r • z) V U) {n : ℕ∞ω}
    (hA : ∀ i j, ContDiffOn ℝ n (fun x => A.a x i j) U) :
    ∀ i j, ContDiffOn ℝ n (fun z => (actualCenteredScalarCoeffFour c hr A hmap).a z i j) V := by
  intro i j
  exact (actual_affine_coefficient_contDiffOn_two hA c r i j).mono hmap

theorem actual_centered_scalar_coeff_divergence_four {U V : Set E} (hU : IsOpen U)
    (c : E) {r : ℝ} (hr : 0 < r) (A : EllipticCoeff (2+2) U)
    (hmap : MapsTo (fun z : E => c+r • z) V U)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) U)
    (hdiv : ∀ x ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1))=0) :
    ∀ z ∈ V, ∀ j,
      (∑ i, fderiv ℝ (fun y => (actualCenteredScalarCoeffFour c hr A hmap).a y i j) z
        (EuclideanSpace.single i 1))=0 := by
  intro z hz j
  exact actual_affine_coefficient_divergence_free_two hU hA hdiv c r z (hmap hz) j

theorem actual_affine_holder_comp_four {Z : Type*} [NormedAddCommGroup Z]
    {g : E → Z} {U V : Set E} (c : E) {r K alpha : ℝ} (hr : 0 < r)
    (hmap : MapsTo (fun z : E => c+r • z) V U)
    (hg : ∀ x ∈ U, ∀ y ∈ U, ‖g x-g y‖ ≤ K*‖x-y‖^alpha) :
    ∀ x ∈ V, ∀ y ∈ V, ‖g (c+r • x)-g (c+r • y)‖ ≤ (K*r^alpha)*‖x-y‖^alpha := by
  intro x hx y hy
  have hn : (c+r • x)-(c+r • y)=r • (x-y) := by rw [smul_sub]; abel
  apply (hg _ (hmap hx) _ (hmap hy)).trans_eq
  rw [hn,norm_smul,Real.norm_eq_abs,abs_of_pos hr,Real.mul_rpow hr.le (norm_nonneg _)]
  ring

theorem actual_centered_scaled_source_holder_four {U V : Set E} {g : E → ℝ}
    (c : E) {r b K alpha : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hmap : MapsTo (fun z : E => c+r • z) V U)
    (hg : ∀ x ∈ U, ∀ y ∈ U, |g x-g y| ≤ K*‖x-y‖^alpha) :
    ∀ x ∈ V, ∀ y ∈ V,
      |b⁻¹*g (c+r • x)-b⁻¹*g (c+r • y)| ≤ (b⁻¹*K*r^alpha)*‖x-y‖^alpha := by
  intro x hx y hy
  have hh := actual_affine_holder_comp_four c hr hmap
    (fun x hx y hy => show ‖g x-g y‖ ≤ K*‖x-y‖^alpha from hg x hx y hy) x hx y hy
  rw [← mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hb)]
  exact (mul_le_mul_of_nonneg_left hh (inv_pos.mpr hb).le).trans_eq (by ring)

end PowerConvexity
