import PowerConvexity.Analysis.ActualClassicalDirichletExistenceTwo
import PowerConvexity.Calculus.MinkowskiFixedDomainClosureC2Two
import PowerConvexity.Calculus.ClassicalMinkowskiEndpointsTwo

/-! # The actual intermediate-domain existence port, frozen lines 1156--1167

The original endpoint supplies actual regular defining functions and strict
subsolutions on every intermediate Minkowski domain. The proved nonlinear
continuation theorem now constructs classical solutions on those very domains.
The final assembly retains the prescribed endpoint as the same function.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance acmeRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance acmeRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem actual_classical_dirichlet_minkowski_exists_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x=0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det=1)
    {t R : ℝ} (ht : 0<t) (ht1 : t<1) (hR : 0<R) :
    ∃ v : E → ℝ, ClassicalDirichletDataTwo e (fun j => Complex.I • e j)
      (minkowskiDomain t U (ball (0 : E) R)) v := by
  let b := fun j => Complex.I • e j
  let V := minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨w,f,hw,hf,hwp,hwb,hfb,_hstart,_hreg,_hbound⟩ :=
    classicalDirichlet_minkowski_fixed_uniform_closure_C2_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR
  have hVo : IsOpen V := by
    dsimp only [V]
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hVK : IsCompact (closure V) := by
    have hBK : IsCompact (closure (ball (0 : E) R)) := by
      rw [closure_ball 0 hR.ne']
      exact isCompact_closedBall 0 R
    dsimp only [V]
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul t).add (hBK.smul (1-t))
  have hgeometry : HasC2LocalDefiningFunction V := smoothLocalDefiningFunction_implies_C2
    (minkowskiDomain_hasSmoothLocalDefiningFunction hU hconv hK hboundary ht ht1 hR)
  exact actual_classical_dirichlet_exists_two hVo
    (minkowskiDomain_convex hconv (convex_ball (0 : E) R) t) hVK hgeometry e hab
    hw hwb (fun x hx => (hwp x hx).1)
    (fun x hx => le_of_lt (Complex.lt_def.mp (hwp x hx).2).1)
    (hf.of_le (by norm_num)) (fun x hx => ⟨(hfb x hx).1,(hfb x hx).2.1⟩)
    (fun x hx => (hfb x hx).2.2)

theorem actual_classical_minkowski_intermediate_family_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x=0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det=1)
    {R : ℝ} (hR : 0<R) :
    ∀ t : Icc (0 : ℝ) 1, 0<(t : ℝ) → (t : ℝ)<1 →
      ∃ v : E → ℝ, ClassicalDirichletDataTwo e (fun j => Complex.I • e j)
        (minkowskiDomain t U (ball (0 : E) R)) v := by
  intro t ht ht1
  exact actual_classical_dirichlet_minkowski_exists_two hU hconv hK hboundary hu J hb e hab
    hpsh hdet ht ht1 hR

theorem actual_classical_minkowski_family_exists_two
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {u : E → ℝ} (hu : ClassicalDirichletDataTwo e (fun j => Complex.I • e j) U u)
    {R : ℝ} (hR : 0<R) :
    ∃ v : Icc (0 : ℝ) 1 → E → ℝ,
      ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) U (ball (0 : E) R) v ∧
        v ⟨1,by norm_num⟩=u := by
  obtain ⟨J⟩ := hu.2.1
  exact classicalMinkowskiFamily_of_exists_open_parameter e (fun j => Complex.I • e j) hab
    hne hR hu (actual_classical_minkowski_intermediate_family_two hU hconv hK hboundary
      (hu.1.of_le (by norm_num)) J hu.2.2.2.2 e hab hu.2.2.1 hu.2.2.2.1 hR)

end PowerConvexity
