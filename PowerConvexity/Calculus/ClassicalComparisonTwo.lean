import PowerConvexity.Algebra.DeterminantOrderTwo
import PowerConvexity.Calculus.PerturbationJets
import CHS.Calculus.HessianExtrema

/-! # Classical comparison on the actual strict psh branch in dimension two -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem classical_strict_comparison_two {U : Set E} (hU : IsOpen U)
    (hK : IsCompact (closure U)) (a b : Fin 2 → E) {u v : E → ℝ}
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hAu : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b v x).det.re < (complexHessian a b u x).det.re)
    (hb : ∀ x ∈ frontier U, u x ≤ v x) : ∀ x ∈ closure U, u x ≤ v x := by
  intro x hx
  by_contra hn
  have hxp : 0 < u x-v x := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨y,hyK,hymax⟩ := hK.exists_isMaxOn ⟨x,hx⟩ (huc.sub hvc)
  have hyp : 0 < u y-v y := hxp.trans_le (hymax hx)
  have hy : y ∈ U := by
    by_contra hout
    have hyf : y ∈ frontier U := by rw [frontier,hU.interior_eq]; exact ⟨hyK,hout⟩
    have hh := hb y hyf
    linarith
  have hm : IsLocalMax (fun z => u z-v z) y :=
    hymax.isLocalMax (Filter.mem_of_superset (hU.mem_nhds hy) subset_closure)
  have hBA := complexHessian_sub_posSemidef_of_isLocalMax
    (hu.contDiffAt (hU.mem_nhds hy)) (hv.contDiffAt (hU.mem_nhds hy)) hm a b
  have hmono := det_re_mono_of_posSemidef_sub_two (hAu y hy) hBA
  exact (not_lt_of_ge hmono) (hdet y hy)

/-- The quadratic function is supplied with its actual Hessian and boundary
sign.  The following ball-barrier module constructs it from an orthonormal
coordinate frame; it is not an unproved comparison oracle. -/
theorem classical_comparison_two_with_quadratic {U : Set E} (hU : IsOpen U)
    (hK : IsCompact (closure U)) (a b : Fin 2 → E) {u v ψ : E → ℝ}
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hAu : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b v x).det.re ≤ (complexHessian a b u x).det.re)
    (hb : ∀ x ∈ frontier U, u x ≤ v x)
    (hψc : ContinuousOn ψ (closure U)) (hψ : ContDiffOn ℝ 2 ψ U)
    (hψb : ∀ x ∈ frontier U, ψ x ≤ 0)
    (hψH : ∀ x ∈ U, complexHessian a b ψ x = 1) :
    ∀ x ∈ closure U, u x ≤ v x := by
  have hpert (ε : ℝ) (hε : 0 < ε) : ∀ x ∈ closure U, u x+ε*ψ x ≤ v x := by
    have hH (x : E) (hx : x ∈ U) :
        complexHessian a b (fun y => u y+ε*ψ y) x =
          complexHessian a b u x+(ε:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [complexHessian_add_at (hu.contDiffAt (hU.mem_nhds hx))
        (contDiffAt_const.mul (hψ.contDiffAt (hU.mem_nhds hx))),
        complexHessian_const_mul_at (hψ.contDiffAt (hU.mem_nhds hx)),hψH x hx]
    apply classical_strict_comparison_two (u := fun y => u y+ε*ψ y)
      hU hK a b (huc.add (continuousOn_const.mul hψc)) hvc
      (hu.add (contDiffOn_const.mul hψ)) hv
    · intro x hx
      rw [hH x hx]
      exact (hAu x hx).add_posSemidef (posDef_real_smul Matrix.PosDef.one hε).posSemidef
    · intro x hx
      rw [hH x hx]
      exact (hdet x hx).trans_lt (det_re_strict_add_scalar_two (hAu x hx) hε)
    · intro x hx
      have hh := hψb x hx
      have hp := mul_nonpos_of_nonneg_of_nonpos hε.le hh
      linarith [hb x hx]
  intro x hx
  by_contra hn
  have hg : 0 < u x-v x := sub_pos.mpr (lt_of_not_ge hn)
  let ε := (u x-v x)/(2*(|ψ x|+1))
  have hε : 0 < ε := div_pos hg (by positivity)
  have heq : ε*(2*(|ψ x|+1)) = u x-v x := div_mul_cancel₀ _ (by positivity)
  have hp := hpert ε hε x hx
  have hprod := mul_le_mul_of_nonneg_left (neg_abs_le (ψ x)) hε.le
  have hpabs := mul_nonneg hε.le (abs_nonneg (ψ x))
  nlinarith

end PowerConvexity
