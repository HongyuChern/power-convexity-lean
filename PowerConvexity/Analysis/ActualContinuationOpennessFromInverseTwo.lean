import PowerConvexity.Analysis.ActualUniformContinuationHolderLiftTwo
import PowerConvexity.Analysis.ActualUniformHolderClassicalUpgradeTwo

/-! # Classical nonlinear openness from the actual bounded determinant inverse

The Holder realization and the C4 upgrade have already been proved for the
same functions. This assembly uses the actual inverse identities explicitly;
the next geometric inverse theorem is responsible for supplying them.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance acoiRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance acoiRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
  actualDensityJetSeminormed

theorem actual_continuation_classical_solvable_isOpen_of_bounded_inverse_two
    {U : Set E} [CompactSpace (closure U)]
    (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hgeometry : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 6 w) (hwb : ∀ y ∈ frontier U, w y=0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    (hinverse : ∀ alpha : ℝ, 0<alpha → alpha<1 → ∀ s : Icc (0 : ℝ) 1,
      ∀ p : actualHolderC2JetSpaceTwo U alpha,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s)
        (actualClosureExtensionTwo U p.1.1) →
      ∃ S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha,
        (actualHolderDeterminantDerivativeTwo U alpha e (fun j => Complex.I • e j) p).comp S=
          ContinuousLinearMap.id ℝ (actualHolderLoadSpaceTwo (closure U) ℝ alpha) ∧
        S.comp (actualHolderDeterminantDerivativeTwo U alpha e (fun j => Complex.I • e j) p)=
          ContinuousLinearMap.id ℝ (actualHolderC2JetSpaceTwo U alpha)) :
    IsOpen {s : Icc (0 : ℝ) 1 | ∃ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u} := by
  obtain ⟨alpha,ha,ha1,B,hB,rho,hrho,hrhoeq,hlift⟩ :=
    actual_continuation_uniform_holder_realization_two hU hconv hK hgeometry e hab
      hw hwb hwp hwd hf hfb hdef
  let b := fun j => Complex.I • e j
  have hclassical (s : Icc (0 : ℝ) 1) (p : actualHolderC2JetSpaceTwo U alpha)
      (hp : ∀ x : closure U, (actualHolderComplexFieldTwo U alpha e b p x).PosDef)
      (heq : actualHolderDeterminantTwo U alpha e b p=rho s) :
      ClassicalDirichletDensityDataTwo e b U (dirichletContinuationDensityTwo e b w s)
        (actualClosureExtensionTwo U p.1.1) :=
    actual_holder_positive_solution_classical_two hU ha ha1 e hab p (rho s)
      ((dirichletContinuationDensityTwo_contDiff_C4 e b hw s).of_le (by norm_num)).contDiffOn
      (hrhoeq s) hp heq
  have hopen := actualHolderDeterminantTwo_parameter_open U hU alpha e b
    (fun s : Icc (0 : ℝ) 1 => rho s) (hrho.comp continuous_subtype_val)
    (fun s p hp heq => by
      obtain ⟨S,hSright,hSleft⟩ := hinverse alpha ha ha1 s p (hclassical s p hp heq)
      refine ⟨S,?_,?_⟩
      · intro q
        exact congrArg (fun A : actualHolderC2JetSpaceTwo U alpha →L[ℝ]
          actualHolderC2JetSpaceTwo U alpha => A q) hSleft
      · intro q
        exact congrArg (fun A : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ]
          actualHolderLoadSpaceTwo (closure U) ℝ alpha => A q) hSright)
  have hset : {s : Icc (0 : ℝ) 1 | ∃ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e b U (dirichletContinuationDensityTwo e b w s) u}=
      {s : Icc (0 : ℝ) 1 | ∃ p : actualHolderC2JetSpaceTwo U alpha,
        (∀ x : closure U, (actualHolderComplexFieldTwo U alpha e b p x).PosDef) ∧
        actualHolderDeterminantTwo U alpha e b p=rho s} := by
    ext s
    constructor
    · rintro ⟨u,hu⟩
      obtain ⟨J⟩ := hu.2.1
      obtain ⟨p,hp,_⟩ := hlift s s.property u hu J
      exact ⟨p,hp.2.2.1,hp.2.2.2⟩
    · rintro ⟨p,hp,heq⟩
      exact ⟨actualClosureExtensionTwo U p.1.1,hclassical s p hp heq⟩
  change IsOpen {s : Icc (0 : ℝ) 1 | ∃ u : E → ℝ,
    ClassicalDirichletDensityDataTwo e b U (dirichletContinuationDensityTwo e b w s) u}
  rw [hset]
  exact hopen

end PowerConvexity
