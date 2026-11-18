import PowerConvexity.Analysis.ActualUniformContinuationGlobalHolderTwo
import PowerConvexity.Analysis.ActualUniformHolderLiftIdentificationTwo
import PowerConvexity.Calculus.ActualSmoothHolderDensityPathTwo

/-! # One complete Holder realization for the same actual continuation family

The exponent and norm bound precede all auxiliary parameters and solutions.
The path in the complete load space has the exact original density. Every
actual classical solution lifts uniquely, with the same true closure values,
to the positive branch solving this exact Holder-space determinant equation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance auchlRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance auchlRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
  actualDensityJetSeminormed
variable {U : Set E} [CompactSpace (closure U)]

theorem actual_continuation_uniform_holder_realization_two
    (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hgeometry : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 6 w) (hwb : ∀ y ∈ frontier U, w y=0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ B ≥ 0,
      ∃ rho : ℝ → actualHolderLoadSpaceTwo (closure U) ℝ alpha,
      Continuous rho ∧
      (∀ s : ℝ, ∀ x : closure U,
        actualHolderLoadSpaceTwo_value (closure U) ℝ alpha (rho s) x=
          dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s x) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u →
      ∀ J : ClosureC2Jet u U, ∃! p : actualHolderC2JetSpaceTwo U alpha,
        actualHolderC2JetSpaceTwo_value U alpha p=⟨fun x => u x,J.continuous_value.domRestrict⟩ ∧
        ‖p‖ ≤ B ∧
        (∀ x : closure U, (actualHolderComplexFieldTwo U alpha e (fun j => Complex.I • e j) p x).PosDef) ∧
        actualHolderDeterminantTwo U alpha e (fun j => Complex.I • e j) p=rho s := by
  obtain ⟨alpha,ha,ha1,K,hK0,hholder⟩ := actual_continuation_uniform_global_hessian_holder_two
    hU hconv hK hgeometry e hab hw hwb hwp hwd hf hfb hdef
  obtain ⟨M,hM,hbound⟩ := continuation_density_uniform_closure_C2_bound_two
    hU hconv hK hgeometry e hab (hw.of_le (by norm_num)) hwb hwp hwd hf hfb hdef
  obtain ⟨rho,hrho,hrhoeq⟩ := actual_continuation_density_holder_path_two hconv hK ha.le ha1.le
    e (fun j => Complex.I • e j) (hw.of_le (by norm_num))
  let B := max M K
  have hB : 0 ≤ B := hM.trans (le_max_left _ _)
  refine ⟨alpha,ha,ha1,B,hB,rho,hrho,hrhoeq,?_⟩
  intro s hs u hu J
  have hu2 : ContDiffOn ℝ 2 u U := hu.1.of_le (by norm_num)
  have hb (x : E) (hx : x∈closure U) : |u x| ≤ B ∧ ‖J.derivative x‖ ≤ B ∧ ‖J.hessian x‖ ≤ B := by
    obtain ⟨h0,h1,h2⟩ := hbound s hs u hu J x hx
    exact ⟨h0.trans (le_max_left _ _),h1.trans (le_max_left _ _),h2.trans (le_max_left _ _)⟩
  have hh (x : E) (hx : x∈closure U) (y : E) (hy : y∈closure U) :
      ‖J.hessian x-J.hessian y‖ ≤ B*‖x-y‖^alpha :=
    (hholder s hs u hu J x hx y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  obtain ⟨p,hp,_⟩ := actualHolderC2JetSpaceTwo_lift U hU alpha hu2 J hu.2.2.2.2 hB hb hh
  have hregular := dirichletContinuationDensityTwo_contDiff e (fun j => Complex.I • e j)
    (hw.of_le (by norm_num)) s
  have hnonzero (x : E) (hx : x∈closure U) :
      dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s x≠0 := by
    have hh := (dirichletContinuationDensityTwo_bounds e (fun j => Complex.I • e j) hs (hwd x hx)).1
    linarith
  obtain ⟨hpositive,hequation⟩ := actual_holder_lift_variable_density_equation_two U hU alpha
    e (fun j => Complex.I • e j) hu2 J hregular.continuous.continuousOn hnonzero
    hu.2.2.1 hu.2.2.2.1 (rho s) (hrhoeq s) p hp.1
  refine ⟨p,⟨hp.1,hp.2,hpositive,hequation⟩,?_⟩
  intro q hq
  exact actualHolderC2JetSpaceTwo_value_injective U hU alpha (hq.1.trans hp.1.symm)

end PowerConvexity
