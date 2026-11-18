import PowerConvexity.Calculus.BoundaryNormalSubsolutionEstimateTwo
import PowerConvexity.Calculus.ComplexRealBasis

/-! # A full real Hessian quadratic upper bound at a fixed actual boundary point

Finitely many normal/tangent estimates bound the whole tangent linear functional.
The coefficient is chosen before the unknown solution and before the direction.
This does not yet make the bound uniform over boundary points or parameters.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem abs_linear_apply_le_sum_orthonormal_basis_bounds
    {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] ℝ)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i) (hbound : ∀ i, |L (B i)| ≤ C i) (v : E) :
    |L v| ≤ (∑ i, C i)*‖v‖ := by
  classical
  have hc (i : ι) : |B.repr v i| ≤ ‖v‖ := by
    rw [B.repr_apply_apply]
    simpa only [Real.norm_eq_abs,B.orthonormal.1 i,one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (B i) v
  conv_lhs => rw [← B.sum_repr v,map_sum]
  simp only [map_smul,smul_eq_mul]
  calc
    |∑ i, B.repr v i*L (B i)| ≤ ∑ i, |B.repr v i*L (B i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C i*‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,mul_comm (C i)]
      exact mul_le_mul (hc i) (hbound i) (abs_nonneg _) (norm_nonneg _)
    _ = (∑ i, C i)*‖v‖ := (Finset.sum_mul _ _ _).symm

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem strict_subsolution_boundary_quadratic_upper_at_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w) (hwb : ∀ y ∈ frontier U, w y = 0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ U, (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) w y).det)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ} (hf : ContDiffAt ℝ 3 f x)
    (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (hLevi : ∀ v : E, v ≠ 0 → fderiv ℝ f x v = 0 → fderiv ℝ f x (Complex.I • v) = 0 →
      0 < realHessian f x v v+realHessian f x (Complex.I • v) (Complex.I • v)) :
    ∃ M ≥ 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 3 u U →
      (∀ y ∈ frontier U, u y = 0) →
      (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef) →
      (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = 1) →
      ∀ v : E, J.hessian x v v ≤ M*‖v‖^2 := by
  classical
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  have hn : ‖N‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hN)
  have hNN : fderiv ℝ f x N = ‖N‖^2 := by rw [← hNf,real_inner_self_eq_norm_sq]
  let alpha : E →L[ℝ] ℝ := (‖N‖^2)⁻¹ • fderiv ℝ f x
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E-alpha.smulRight N
  have hPv (v : E) : P v = v-(alpha v) • N := rfl
  have hPt (v : E) : fderiv ℝ f x (P v) = 0 := by
    rw [hPv,map_sub,map_smul,smul_eq_mul,hNN]
    change fderiv ℝ f x v-((‖N‖^2)⁻¹*fderiv ℝ f x v)*‖N‖^2 = 0
    field_simp [hn]
    <;> ring
  let B := (complexRealBasis e).toOrthonormalBasis
    (by simpa only [complexRealBasis_eq_sum] using hab)
  obtain ⟨C,hC,hfirst⟩ := strict_subsolution_uniform_boundary_first_tangent_bounds_two
    hU hconv hK hboundary e (fun j => Complex.I • e j) hab hw hwb
    (fun y hy => hwp y (subset_closure hy)) hwd
  obtain ⟨A,hA,hNormal⟩ := strict_subsolution_boundary_normal_upper_two
    hU hconv hK hboundary e hab hw hwb hwp hwd hx hf hfx hDf hdef hLevi
  have hex (i : Fin 2 ⊕ Fin 2) := strict_subsolution_boundary_normal_tangent_bound_two
    hU hconv hK hboundary e hab hw hwb hwp hwd hx hf hfx hDf hdef (P (B i)) (hPt (B i))
  choose Ci hCi hMixed using hex
  let S : ℝ := ∑ i, Ci i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hCi i)
  let M : ℝ := C*‖P‖^2+2*‖alpha‖*S+‖alpha‖^2*A
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro u J hu hub hup hud v
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  obtain ⟨mu,hmu,hJ⟩ := classicalDirichlet_derivative_eq_positive_defining_multiple_two
    hU hconv hK hu2 J hub e (fun j => Complex.I • e j) hab hup hud hx
    (hf.of_le (by norm_num)) hfx hDf hdef
  have hJt : J.derivative x (P v) = 0 := by
    rw [hJ,ContinuousLinearMap.smul_apply,smul_eq_mul,hPt,mul_zero]
  have ht := (hfirst u J hu2 hub hup hud x hx).2 (P v) hJt
  have hm : |J.hessian x N (P v)| ≤ S*‖v‖ :=
    abs_linear_apply_le_sum_orthonormal_basis_bounds B ((J.hessian x N).comp P) Ci hCi
      (fun i => hMixed i u J hu hub hup hud) v
  have hNbound := hNormal u J hu hub hup hud
  have hPnorm := P.le_opNorm v
  have hcoef : |alpha v| ≤ ‖alpha‖*‖v‖ := by simpa only [Real.norm_eq_abs] using alpha.le_opNorm v
  have hP2 : ‖P v‖^2 ≤ ‖P‖^2*‖v‖^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg (P v)) (mul_nonneg (norm_nonneg P) (norm_nonneg v))).mpr hPnorm
    nlinarith only [hh]
  have hc2 : (alpha v)^2 ≤ ‖alpha‖^2*‖v‖^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (alpha v))
      (mul_nonneg (norm_nonneg alpha) (norm_nonneg v))).mpr hcoef
    rw [sq_abs] at hh
    nlinarith only [hh]
  have htBound : J.hessian x (P v) (P v) ≤ C*‖P‖^2*‖v‖^2 := by
    have hh := mul_le_mul_of_nonneg_left hP2 hC
    nlinarith only [ht,hh]
  have hmBound : 2*(alpha v)*J.hessian x N (P v) ≤ 2*‖alpha‖*S*‖v‖^2 := by
    have hprod := mul_le_mul hcoef hm (abs_nonneg _) (mul_nonneg (norm_nonneg alpha) (norm_nonneg v))
    have hh := le_abs_self ((alpha v)*J.hessian x N (P v))
    rw [abs_mul] at hh
    nlinarith only [hprod,hh]
  have hnBound : (alpha v)^2*J.hessian x N N ≤ ‖alpha‖^2*A*‖v‖^2 := by
    have hh1 := mul_le_mul_of_nonneg_left hNbound (sq_nonneg (alpha v))
    have hh2 := mul_le_mul_of_nonneg_right hc2 hA
    nlinarith only [hh1,hh2]
  have hsplit : v = P v+(alpha v) • N := by rw [hPv]; module
  have he : J.hessian x v v = J.hessian x (P v) (P v)+
      2*(alpha v)*J.hessian x N (P v)+(alpha v)^2*J.hessian x N N := by
    conv_lhs => rw [hsplit]
    simp only [map_add,map_smul,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    rw [closureJet_hessian_symmetric hU hu2 J (frontier_subset_closure hx) (P v) N]
    ring
  rw [he]
  dsimp only [M]
  nlinarith only [htBound,hmBound,hnBound]

end PowerConvexity
