import PowerConvexity.Calculus.ActualIsometricCofactorZeroBoundaryTwo

/-! # Actual classical linearized Dirichlet solves on the physical domain

This constructs C2 interior, continuous zero-boundary solutions on the same
physical domain, with uniqueness among all classical zero-boundary solutions.
A closure C2 jet and a Schauder inverse bound are not asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "F" => AmbientSpace (2+2)

theorem linearizedCMAOperatorTwo_comp_linearIsometry_two
    (L : F ≃ₗᵢ[ℝ] E) {v h : E → ℝ} {x : F}
    (hv : ContDiffAt ℝ 2 v (L x)) (hh : ContDiffAt ℝ 2 h (L x)) :
    linearizedCMAOperatorTwo realDirections imagDirections (fun y => v (L y))
      (fun y => h (L y)) x =
      linearizedCMAOperatorTwo (fun i => L (realDirections i))
        (fun i => L (imagDirections i)) v h (L x) := by
  have hhL : ContDiffAt ℝ 2 (fun y => h (L y)) x :=
    hh.comp x L.toContinuousLinearEquiv.contDiff.contDiffAt
  unfold linearizedCMAOperatorTwo
  rw [← complexHessianContraction_pairing _ _ _ hhL,
    ← complexHessianContraction_pairing _ _ _ hh,
    complex_contraction_eq_trace hhL,complex_contraction_eq_trace hh,
    complexHessian_comp_linearIsometry L hv,complexHessian_comp_linearIsometry L hh]

theorem actual_physical_linearized_zero_boundary_dirichlet_two
    {V : Set E} (hV : IsOpen V) (hK : IsCompact (closure V))
    (L : F ≃ₗᵢ[ℝ] E) (a b : Fin 2 → E)
    (hLa : ∀ i, L (realDirections i) = a i) (hLb : ∀ i, L (imagDirections i) = b i)
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure V, (complexHessian a b w x).PosDef)
    (hwb : ∀ x ∈ frontier V, w x = 0)
    {v ρ : E → ℝ} (hv : ContDiffOn ℝ 4 v V)
    (hvC : ContinuousOn v (closure V)) (hvb : ∀ x ∈ frontier V, v x = 0)
    (hvp : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    (hvd : ∀ x ∈ V, (complexHessian a b v x).det = (ρ x : ℂ))
    (hρ : ContDiff ℝ 1 ρ) (hρlo : ∀ x ∈ V, 1 ≤ ρ x)
    {c : ℝ} (hc : 0 < c) (A : EllipticCoeff (2+2) (L ⁻¹' V))
    (hA : ∀ x ∈ L ⁻¹' V, A.a x = c⁻¹ • complexCofactorCoeff (fun y => v (L y)) x)
    (g : E → ℝ) (hg : ContDiff ℝ 1 g) :
    ∃ h : E → ℝ, Continuous h ∧ ContDiffOn ℝ 2 h V ∧
      (∀ x ∈ frontier V, h x = 0) ∧
      (∀ x ∈ V, linearizedCMAOperatorTwo a b v h x = g x) ∧
      MemH01 (fun y => h (L y)) (L ⁻¹' V) ∧
      ActualScalarWeakEquationTwo A (fun y => -(c⁻¹*ρ (L y)*g (L y))) (fun y => h (L y)) ∧
      ∀ k : E → ℝ, ContinuousOn k (closure V) → ContDiffOn ℝ 2 k V →
        (∀ x ∈ frontier V, k x = 0) →
        (∀ x ∈ V, linearizedCMAOperatorTwo a b v k x = g x) → EqOn h k (closure V) := by
  obtain ⟨H,hHC,hH2,hH0,hHb,hHL,hHw⟩ :=
    actual_isometric_cofactor_classical_zero_boundary_two hV hK L a b hLa hLb
      hw hwp hwb hv hvp hvd hρ hρlo hc A hA g hg
  let h : E → ℝ := fun x => H (L.symm x)
  have hhL : (fun y => h (L y)) = H := by funext y; simp only [h,L.symm_apply_apply]
  have hhC : Continuous h := hHC.comp L.symm.continuous
  have hh2 : ContDiffOn ℝ 2 h V := hH2.comp
    L.symm.toContinuousLinearEquiv.contDiff.contDiffOn
    (fun x hx => by simpa only [mem_preimage,L.apply_symm_apply] using hx)
  have hhb : ∀ x ∈ frontier V, h x = 0 := by
    intro x hx
    apply hHb
    have hfr : L ⁻¹' frontier V = frontier (L ⁻¹' V) := L.toHomeomorph.preimage_frontier V
    rw [← hfr]
    simpa only [mem_preimage,L.apply_symm_apply] using hx
  have hhPDE : ∀ x ∈ V, linearizedCMAOperatorTwo a b v h x = g x := by
    intro x hx
    have hxL : L.symm x ∈ L ⁻¹' V := by simpa only [mem_preimage,L.apply_symm_apply] using hx
    have hvx : ContDiffAt ℝ 2 v (L (L.symm x)) := by
      simpa only [L.apply_symm_apply] using (hv.contDiffAt (hV.mem_nhds hx)).of_le (by norm_num)
    have hhx : ContDiffAt ℝ 2 h (L (L.symm x)) := by
      simpa only [L.apply_symm_apply] using hh2.contDiffAt (hV.mem_nhds hx)
    have he := linearizedCMAOperatorTwo_comp_linearIsometry_two L hvx hhx
    rw [hhL] at he
    simpa only [hLa,hLb,L.apply_symm_apply] using he.symm.trans (hHL _ hxL)
  refine ⟨h,hhC,hh2,hhb,hhPDE,?_,?_,?_⟩
  · rw [hhL]; exact hH0
  · rw [hhL]; exact hHw
  · intro k hkC hk2 hkb hkPDE
    have hz : EqOn (fun x => h x-k x) (fun _ => 0) (closure V) :=
      linearizedCMAOperatorTwo_zero_kernel a b hV hK hvC (hv.of_le (by norm_num)) hvb hvp
        (hhC.continuousOn.sub hkC) (hh2.sub hk2)
        (fun x hx => by rw [hhb x hx,hkb x hx,sub_self]) (by
          intro x hx
          unfold linearizedCMAOperatorTwo
          simp_rw [sub_eq_add_neg]
          rw [realHessian_add (hh2.contDiffAt (hV.mem_nhds hx))
            ((hk2.contDiffAt (hV.mem_nhds hx)).neg),realHessian_neg,map_add,
            map_neg (complexHessianContraction a b (complexHessian a b v x)⁻¹) (realHessian k x)]
          rw [← sub_eq_add_neg]
          exact sub_eq_zero.mpr ((hhPDE x hx).trans (hkPDE x hx).symm))
    intro x hx
    exact sub_eq_zero.mp (hz hx)

end PowerConvexity
