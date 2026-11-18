import PowerConvexity.Calculus.ActualClassicalResponseCompletionTwo

/-! # The actual unit-load response and the sharp C0 inverse norm

The response to the constant load one is exactly one half of the same
nonlinear potential.  Thus the C0 inverse norm already detects the full
depth of that potential.  This still supplies no boundary Hessian estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def classicalC1UnitLoadTwo (V : Set E) : classicalC1LoadClosureTwo V :=
  ⟨1,⟨fun _ => 1,contDiff_const,fun _ => rfl⟩⟩

theorem actual_classical_C0_response_unit_load_two
    {V : Set E} [CompactSpace (closure V)]
    {a b : Fin 2 → E} {v : E → ℝ}
    (hV : IsOpen V) (hK : IsCompact (closure V))
    (hvC : ContinuousOn v (closure V)) (hv2 : ContDiffOn ℝ 2 v V)
    (hvb : ∀ x ∈ frontier V, v x=0)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    {R : classicalC1LoadClosureTwo V →L[ℝ] C(closure V, ℝ)}
    (hR : IsClassicalC0ResponseTwo a b v R) :
    ∀ x : closure V, R (classicalC1UnitLoadTwo V) x=(1/2 : ℝ)*v x := by
  have hh : ClassicalLinearizedZeroDataTwo a b v V (fun _ => 1)
      (fun x => (1/2 : ℝ)*v x) := by
    refine ⟨continuousOn_const.mul hvC,contDiffOn_const.mul hv2,?_,?_⟩
    · intro x hx
      change (1/2 : ℝ)*v x=0
      rw [hvb x hx,mul_zero]
    · intro x hx
      rw [linearizedCMAOperatorTwo_smul_actual_two,
        linearizedCMAOperatorTwo_self a b (hv2.contDiffAt (hV.mem_nhds hx)) (hvp x hx)]
      norm_num
  exact hR.eq_classical hV hK hvC hv2 hvb hvp (classicalC1UnitLoadTwo V)
    (fun _ => rfl) hh

theorem actual_classical_complete_C0_response_norm_lower_two
    {V : Set E} [CompactSpace (closure V)]
    {a b : Fin 2 → E} {v : E → ℝ}
    (hV : IsOpen V) (hK : IsCompact (closure V))
    (hvC : ContinuousOn v (closure V)) (hv2 : ContDiffOn ℝ 2 v V)
    (hvb : ∀ x ∈ frontier V, v x=0)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    {R : classicalC1LoadClosureTwo V →L[ℝ] C(closure V, ℝ)}
    (hR : IsClassicalC0ResponseTwo a b v R)
    {T : C(closure V, ℝ) →L[ℝ] C(closure V, ℝ)}
    (hT : ∀ f : classicalC1LoadClosureTwo V, T f.1=R f) :
    ‖(⟨fun x => v x,hvC.domRestrict⟩ : C(closure V, ℝ))‖/2 ≤ ‖T‖ := by
  let vC : C(closure V, ℝ) := ⟨fun x => v x,hvC.domRestrict⟩
  have hunit : T 1=(1/2 : ℝ) • vC := by
    apply ContinuousMap.ext
    intro x
    have ht := congrArg (fun f : C(closure V, ℝ) => f x) (hT (classicalC1UnitLoadTwo V))
    exact ht.trans (actual_classical_C0_response_unit_load_two hV hK hvC hv2 hvb hvp hR x)
  have hunitnorm : ‖(1 : C(closure V, ℝ))‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).mpr
    intro x
    norm_num
  have hbound := (T.le_opNorm (1 : C(closure V, ℝ))).trans
    (mul_le_mul_of_nonneg_left hunitnorm (norm_nonneg T))
  rw [hunit,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 1/2),mul_one] at hbound
  change ‖vC‖/2 ≤ ‖T‖
  linarith

/-- The C0 norm is exactly half the depth norm of the same potential, not an
unspecified constant coming from a differently normalized elliptic operator. -/
theorem actual_classical_complete_C0_response_norm_exact_two
    {V : Set E} [CompactSpace (closure V)]
    {a b : Fin 2 → E} {v : E → ℝ}
    (hV : IsOpen V) (hK : IsCompact (closure V))
    (hvC : ContinuousOn v (closure V)) (hv2 : ContDiffOn ℝ 2 v V)
    (hvb : ∀ x ∈ frontier V, v x=0)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    {R : classicalC1LoadClosureTwo V →L[ℝ] C(closure V, ℝ)}
    (hR : IsClassicalC0ResponseTwo a b v R)
    {T : C(closure V, ℝ) →L[ℝ] C(closure V, ℝ)}
    (hT : ∀ f : classicalC1LoadClosureTwo V, T f.1=R f) :
    ‖T‖ = ‖(⟨fun x => v x,hvC.domRestrict⟩ : C(closure V, ℝ))‖/2 := by
  let vC : C(closure V, ℝ) := ⟨fun x => v x,hvC.domRestrict⟩
  have hvB : ∀ x ∈ closure V, -v x ≤ ‖vC‖ := by
    intro x hx
    have hn := vC.norm_coe_le_norm ⟨x,hx⟩
    change ‖v x‖ ≤ ‖vC‖ at hn
    rw [Real.norm_eq_abs] at hn
    exact (neg_le_abs (v x)).trans hn
  have hsolve : ∀ g : E → ℝ, ContDiff ℝ 1 g →
      ∃ h : E → ℝ, ClassicalLinearizedZeroDataTwo a b v V g h := by
    intro g hg
    let f : classicalC1LoadClosureTwo V :=
      ⟨⟨fun y => g y,hg.continuous.comp continuous_subtype_val⟩,⟨g,hg,fun _ => rfl⟩⟩
    obtain ⟨g',h,hg',hfg,hh,_⟩ := hR f
    refine ⟨h,hh.1,hh.2.1,hh.2.2.1,?_⟩
    intro x hx
    exact (hh.2.2.2 x hx).trans (hfg ⟨x,subset_closure hx⟩).symm
  obtain ⟨R',hR'n,hR'⟩ := actual_classical_bounded_C0_response_two a b v hV hK hvC hv2
    hvb hvp (norm_nonneg vC) hvB hsolve
  have hRR' : R=R' := hR.unique hV hK hvC hv2 hvb hvp hR'
  obtain ⟨T',hT'n,_,hT'unique⟩ := actual_classical_C0_response_extension_two R
  have hTT' : T=T' := hT'unique T hT
  apply le_antisymm
  · rw [hTT']
    exact hT'n.trans (by simpa only [hRR'] using hR'n)
  · exact actual_classical_complete_C0_response_norm_lower_two hV hK hvC hv2 hvb hvp hR hT

end PowerConvexity
