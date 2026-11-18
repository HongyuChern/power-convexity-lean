import PowerConvexity.Analysis.ActualContinuousHolderClassicalTwo
import PowerConvexity.Calculus.ActualClosureFunctionExtensionTwo

/-! # Every complete Holder load has the same actual classical interior response

The input is the actual weak representation of one bounded C0 operator.
The source is the actual weighted load, and its Holder bounds are proved from
the complete load norm. No C1 extension of the load is requested.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_holder_load_weighted_bounds_two
    {U : Set E} [CompactSpace (closure U)] {alpha Kd Bd : ℝ}
    (hKd : 0 ≤ Kd) (hBd : 0 ≤ Bd) {d : E → ℝ}
    (hdC : ContinuousOn d (closure U))
    (hdB : ∀ x ∈ closure U, |d x| ≤ Bd)
    (hdH : ∀ x ∈ closure U, ∀ y ∈ closure U, |d x-d y| ≤ Kd*‖x-y‖^alpha)
    (g : actualHolderLoadSpaceTwo (closure U) ℝ alpha) :
    let v := actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha g)
    let f := fun x => -(d x*v x)
    ContinuousOn f (closure U) ∧
      (∀ x ∈ closure U, |f x| ≤ Bd*‖g‖) ∧
      ∀ x ∈ closure U, ∀ y ∈ closure U, |f x-f y| ≤ ((Kd+Bd)*‖g‖)*‖x-y‖^alpha := by
  let v := actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha g)
  have hvB : ∀ x ∈ closure U, |v x| ≤ ‖g‖ := by
    intro x hx
    rw [show v x=actualHolderLoadSpaceTwo_value _ _ alpha g ⟨x,hx⟩ from
      actualClosureExtensionTwo_apply U _ hx]
    exact ((actualHolderLoadSpaceTwo_value _ _ alpha g).norm_coe_le_norm ⟨x,hx⟩).trans
      (actualHolderLoadSpaceTwo_value_norm_le _ _ alpha g)
  have hvH : ∀ x ∈ closure U, ∀ y ∈ closure U, |v x-v y| ≤ ‖g‖*‖x-y‖^alpha := by
    intro x hx y hy
    have hh := actualHolderLoadSpaceTwo_holder_bound (closure U) ℝ alpha g ⟨x,hx⟩ ⟨y,hy⟩
    simpa only [v,actualClosureExtensionTwo_apply U _ hx,actualClosureExtensionTwo_apply U _ hy,
      Subtype.dist_eq,dist_eq_norm,Real.norm_eq_abs] using hh
  refine ⟨(hdC.mul (actualClosureExtensionTwo_continuousOn U _)).neg,?_,?_⟩
  · intro x hx
    rw [abs_neg,abs_mul]
    exact mul_le_mul (hdB x hx) (hvB x hx) (abs_nonneg _) hBd
  · intro x hx y hy
    change |-(d x*v x)-(-(d y*v y))| ≤ ((Kd+Bd)*‖g‖)*‖x-y‖^alpha
    rw [show -(d x*v x)-(-(d y*v y))=-(d x*(v x-v y)+(d x-d y)*v y) by ring,abs_neg]
    calc
      _ ≤ |d x*(v x-v y)| + |(d x-d y)*v y| := abs_add_le _ _
      _ = |d x| * |v x-v y| + |d x-d y| * |v y| := by rw [abs_mul,abs_mul]
      _ ≤ Bd*(‖g‖*‖x-y‖^alpha)+(Kd*‖x-y‖^alpha)*‖g‖ :=
        add_le_add (mul_le_mul (hdB x hx) (hvH x hx y hy) (abs_nonneg _) hBd)
          (mul_le_mul (hdH x hx y hy) (hvB y hy) (abs_nonneg _) (by positivity))
      _ = _ := by ring

theorem actual_holder_weak_response_classical_two
    {U : Set E} [CompactSpace (closure U)] (hU : IsOpen U) (hK : IsCompact (closure U))
    (A : EllipticCoeff (2+2) U)
    (hpos : ∀ x ∈ U, (A.a x).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ y ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1))=0)
    {alpha Ka Kd Bd : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKd : 0 ≤ Kd) (hBd : 0 ≤ Bd)
    (hAH : ∀ x ∈ closure U, ∀ y ∈ closure U,
      ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a y)‖ ≤ Ka*‖x-y‖^alpha)
    {d : E → ℝ} (hdC : ContinuousOn d (closure U))
    (hdB : ∀ x ∈ closure U, |d x| ≤ Bd)
    (hdH : ∀ x ∈ closure U, ∀ y ∈ closure U, |d x-d y| ≤ Kd*‖x-y‖^alpha)
    (T : C(closure U,ℝ) →L[ℝ] C(closure U,ℝ))
    (hweak : ∀ g : C(closure U,ℝ), ∃ H : E → ℝ,
      ActualScalarWeakEquationTwo A (fun x => -(d x*actualClosureExtensionTwo U g x)) H ∧
      ∀ x : closure U, T g x=H x)
    (g : actualHolderLoadSpaceTwo (closure U) ℝ alpha) :
    let v := actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha g)
    let u := actualClosureExtensionTwo U (T (actualHolderLoadSpaceTwo_value _ _ alpha g))
    ActualScalarWeakEquationTwo A (fun x => -(d x*v x)) u ∧
      ContDiffOn ℝ 2 u U ∧
      ∀ x ∈ U, (∑ i, ∑ j, A.a x i j*euclideanHessian u x i j)=d x*v x := by
  let G := actualHolderLoadSpaceTwo_value (closure U) ℝ alpha g
  let v := actualClosureExtensionTwo U G
  let u := actualClosureExtensionTwo U (T G)
  let f := fun x => -(d x*v x)
  obtain ⟨hfC,hfB,hfH⟩ := actual_holder_load_weighted_bounds_two hKd hBd hdC hdB hdH g
  obtain ⟨H,hHw,hHT⟩ := hweak G
  have he : H =ᵐ[volume.restrict U] u := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [show u x=T G ⟨x,subset_closure hx⟩ from actualClosureExtensionTwo_apply U _ (subset_closure hx)]
    exact (hHT ⟨x,subset_closure hx⟩).symm
  have huw : ActualScalarWeakEquationTwo A f u := actual_scalar_weak_congr_ae_two he hHw
  have hfm : MemLp f 2 (volume.restrict U) :=
    continuousOn_memLp_two_of_subset_compact hU.measurableSet hK subset_closure hfC
  have huC : ContinuousOn u U := (actualClosureExtensionTwo_continuousOn U (T G)).mono subset_closure
  obtain ⟨hu2,hpde⟩ := actual_continuous_holder_classical_two hU (hK.isBounded.subset subset_closure)
    A hpos hreg hdiv hKa (by positivity : 0 ≤ (Kd+Bd)*‖g‖)
    (by positivity : 0 ≤ Bd*‖g‖) halpha halpha1
    (fun x hx y hy => hAH x (subset_closure hx) y (subset_closure hy))
    hfm (hfC.mono subset_closure)
    (fun x hx y hy => hfH x (subset_closure hx) y (subset_closure hy))
    (fun x hx => hfB x (subset_closure hx)) huC huw
  refine ⟨huw,hu2,?_⟩
  intro x hx
  simpa only [f,neg_neg] using hpde x hx

end PowerConvexity
