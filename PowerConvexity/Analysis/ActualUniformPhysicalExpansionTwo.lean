import PowerConvexity.Analysis.ActualUniformScalarExpansionTwo
import PowerConvexity.Analysis.ActualPhysicalBallIntegralTwo

/-! # Uniform actual quadratic approximation on physical Euclidean balls -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_physical_ball_subset_of_inverse_norm_two
    {U : Set E} (G : E ≃L[ℝ] E) (c : E) {r B : ℝ} (hr : 0 < r) (hB : 0 < B)
    (hG : ‖G.symm.toContinuousLinearMap‖ ≤ B)
    (hclosed : closedBall c (2*r) ⊆ G ⁻¹' U) : ball (G c) (r/B) ⊆ U := by
  intro y hy
  have hn : ‖G.symm y-c‖ < r := by
    have he : G.symm y-c = G.symm (y-G c) := by simp only [map_sub,G.symm_apply_apply]
    rw [he]
    calc
      ‖G.symm (y-G c)‖ ≤ ‖G.symm.toContinuousLinearMap‖*‖y-G c‖ :=
        G.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ B*‖y-G c‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)
      _ < B*(r/B) := mul_lt_mul_of_pos_left (by simpa only [mem_ball,dist_eq_norm] using hy) hB
      _ = r := by field_simp
  have hm : G.symm y ∈ closedBall c (2*r) := by
    rw [mem_closedBall,dist_eq_norm]
    linarith
  simpa only [mem_preimage,G.apply_symm_apply] using hclosed hm

theorem actual_uniform_physical_quadratic_expansion_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U)
    (hpos : ∀ x ∈ U, (A.a x).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ y ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hfC : ContDiffOn ℝ 1 f U)
    {K F : ℝ} (hK : 0 ≤ K) (hF : 0 ≤ F)
    (hLip : ∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ K*‖x-y‖)
    (hbound : ∀ x ∈ U, |f x| ≤ F)
    (hu : ActualScalarWeakEquationTwo A f u) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ delta > 0, closedBall x₀ delta ⊆ U ∧ ∃ R > 0,
      ∃ C ≥ 0, ∃ theta > 0, theta ≤ (1/32 : ℝ) ∧
      ∀ x ∈ ball x₀ delta, ball x R ⊆ U ∧
        ∃ P : E → ℝ, IsQuadraticPolynomial P ∧
          (∑ i, ∑ j, A.a x i j*euclideanHessian P x i j) = -f x ∧
          ∀ n : ℕ,
            (∫ y in ball x (R*theta^n), (u y-P y)^2) ≤
              C*((1/2 : ℝ)^n)^2*(R*theta^n)^8 := by
  obtain ⟨delta,hd,hdelta,r,hr,hr1,C,hC,theta,htheta,hthetab,happrox⟩ :=
    actual_uniform_local_scalar_quadratic_expansion_two hU hUb A hpos hreg hdiv
      hf hfC hK hF hLip hbound hu hx₀
  let B := max (1 : ℝ) (Real.sqrt A.lam)⁻¹
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let R := r/B
  have hR : 0 < R := div_pos hr hB
  obtain ⟨J,hJ,hJac⟩ := actual_linear_forward_jacobians_uniform_two (Real.sqrt A.Λ)
  let D := J*r^4*C/R^8
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨delta,hd,hdelta,R,hR,D,hD,theta,htheta,hthetab,?_⟩
  intro x hx
  obtain ⟨G,hfreeze,hclosed,hGn,hHn,p,hp,htrace,herror⟩ := happrox x hx
  have hGB : ‖G.symm.toContinuousLinearMap‖ ≤ B := hHn.trans (le_max_right _ _)
  have hsub : ball x R ⊆ U := by
    simpa only [G.apply_symm_apply] using
      actual_physical_ball_subset_of_inverse_norm_two G (G.symm x) hr hB hGB hclosed
  let P := actualPhysicalQuadraticTwo G (G.symm x) r p
  have hP := actual_physical_quadratic_isQuadratic_two G (G.symm x) r hp
  have hpm : MemLp P 2 (volume.restrict U) :=
    continuous_memLp_two_of_subset_compact hUb.isCompact_closure subset_closure
      (IsQuadraticPolynomial_contDiff hP 0).continuous
  have hum := (MemW1p.someWitness hu.1).memLp
  have hI : IntegrableOn (fun y => (u y-P y)^2) U := by
    change Integrable (fun y => (u y-P y)^2) (volume.restrict U)
    exact (hum.sub hpm).integrable_sq
  refine ⟨hsub,P,hP,?_,?_⟩
  · simpa only [G.apply_symm_apply] using
      actual_physical_quadratic_frozen_equation_two G (G.symm x) hr hfreeze hp (htrace 0)
  · intro n
    have hs1 : theta^n ≤ 1 := pow_le_one₀ htheta.le (by linarith : theta ≤ 1)
    have hphys := actual_physical_ball_integral_bound_two hI (fun y => sq_nonneg (u y-P y))
      G (G.symm x) hr (pow_pos htheta n) hs1 hB hGB (hJac G hGn) hclosed
    have hn : (∫ y in ball x (R*theta^n), (u y-P y)^2) ≤
        J*r^4*(∫ z in ball (0 : E) (theta^n), (u (G (G.symm x+r • z))-p z)^2) := by
      simpa only [G.apply_symm_apply,P,actual_physical_quadratic_pullback_two G (G.symm x) hr p] using hphys
    calc
      _ ≤ J*r^4*(C*((1/2 : ℝ)^n)^2*(theta^n)^8) :=
        hn.trans (mul_le_mul_of_nonneg_left (herror n) (mul_nonneg hJ.le (pow_nonneg hr.le 4)))
      _ = D*((1/2 : ℝ)^n)^2*(R*theta^n)^8 := by
        dsimp [D]
        field_simp
        <;> ring

end PowerConvexity
