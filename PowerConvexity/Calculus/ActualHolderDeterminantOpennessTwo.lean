import PowerConvexity.Calculus.ActualHolderComplexFieldTwo
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! # Actual local nonlinear solvability in the same complete Holder spaces

The derivative is the actual determinant derivative proved in the preceding
module.  A supplied bounded classical inverse therefore yields an actual
local inverse of the nonlinear density map.  Positivity of the complex
Hessian is preserved uniformly on the compact closure.  The output consists
of C2 Holder solutions with genuine zero trace and closure jets; upgrading
their interior regularity to C4 remains a separate task.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 100000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
  actualDensityJetSeminormed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (U : Set E) [CompactSpace (closure U)]
local notation "Hess" => E →L[ℝ] E →L[ℝ] ℝ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

theorem actualHolderDeterminantTwo_local_inverse_of_bounded_inverse
    (hU : IsOpen U) (alpha : ℝ) (a b : Fin 2 → E)
    (p : actualHolderC2JetSpaceTwo U alpha)
    (S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha)
    (hleft : Function.LeftInverse S (actualHolderDeterminantDerivativeTwo U alpha a b p))
    (hright : Function.RightInverse S (actualHolderDeterminantDerivativeTwo U alpha a b p))
    (hpositive : ∀ x : closure U, (actualHolderComplexFieldTwo U alpha a b p x).PosDef) :
    ∃ Psi : actualHolderLoadSpaceTwo (closure U) ℝ alpha → actualHolderC2JetSpaceTwo U alpha,
      Psi (actualHolderDeterminantTwo U alpha a b p)=p ∧
      HasStrictFDerivAt Psi S (actualHolderDeterminantTwo U alpha a b p) ∧
      ∀ᶠ f in 𝓝 (actualHolderDeterminantTwo U alpha a b p),
        actualHolderDeterminantTwo U alpha a b (Psi f)=f ∧
        ∀ x : closure U, (actualHolderComplexFieldTwo U alpha a b (Psi f) x).PosDef := by
  letI : Fact (IsOpen U) := ⟨hU⟩
  let D := actualHolderDeterminantTwo U alpha a b
  let L := actualHolderDeterminantDerivativeTwo U alpha a b p
  let e : actualHolderC2JetSpaceTwo U alpha ≃L[ℝ]
      actualHolderLoadSpaceTwo (closure U) ℝ alpha :=
    ContinuousLinearEquiv.equivOfInverse L S hleft hright
  have hD : HasStrictFDerivAt D (e : actualHolderC2JetSpaceTwo U alpha →L[ℝ]
      actualHolderLoadSpaceTwo (closure U) ℝ alpha) p :=
    actualHolderDeterminantTwo_hasStrictFDerivAt U alpha a b p
  let Psi := hD.localInverse D e p
  refine ⟨Psi,hD.localInverse_apply_image,hD.to_localInverse,?_⟩
  filter_upwards [hD.eventually_right_inverse,
    hD.localInverse_tendsto.eventually
      (actualHolderComplexFieldTwo_posDef_nhds U hU alpha a b p hpositive)] with f hf hfp
  exact ⟨hf,hfp⟩

theorem actualHolderDeterminantTwo_actual_C2_solution
    (hU : IsOpen U) (alpha : ℝ) (a b : Fin 2 → E)
    (p : actualHolderC2JetSpaceTwo U alpha)
    (f : actualHolderLoadSpaceTwo (closure U) ℝ alpha)
    (hD : actualHolderDeterminantTwo U alpha a b p=f)
    (hpositive : ∀ x : closure U, (actualHolderComplexFieldTwo U alpha a b p x).PosDef) :
    ContDiffOn ℝ 2 (actualClosureExtensionTwo U p.1.1) U ∧
      Nonempty (ClosureC2Jet (actualClosureExtensionTwo U p.1.1) U) ∧
      (∀ x ∈ U, (complexHessian a b (actualClosureExtensionTwo U p.1.1) x).PosDef) ∧
      (∀ (x : E) (hx : x ∈ U),
        (complexHessian a b (actualClosureExtensionTwo U p.1.1) x).det=
          (actualHolderLoadSpaceTwo_value (closure U) ℝ alpha f ⟨x,subset_closure hx⟩ : ℂ)) ∧
      ∀ x ∈ frontier U, actualClosureExtensionTwo U p.1.1 x=0 := by
  obtain ⟨hp,J,_,_⟩ := actualHolderC2JetSpaceTwo_regular U hU alpha p
  have hpos (x : E) (hx : x ∈ U) :
      (complexHessian a b (actualClosureExtensionTwo U p.1.1) x).PosDef := by
    rw [← actualHolderComplexFieldTwo_eq_actual U hU alpha a b p hx]
    exact hpositive ⟨x,subset_closure hx⟩
  refine ⟨hp,⟨J⟩,hpos,?_,p.2.2.2⟩
  intro x hx
  have hr := congrArg (fun g : actualHolderLoadSpaceTwo (closure U) ℝ alpha =>
    actualHolderLoadSpaceTwo_value (closure U) ℝ alpha g ⟨x,subset_closure hx⟩) hD
  rw [actualHolderDeterminantTwo_eq_actual U hU alpha a b p hx] at hr
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using hr
  · simpa only [Complex.ofReal_im] using (Complex.pos_iff.mp (hpos x hx).det_pos).2.symm

theorem actualHolderDeterminantTwo_parameter_open
    {T : Type*} [TopologicalSpace T]
    (hU : IsOpen U) (alpha : ℝ) (a b : Fin 2 → E)
    (rho : T → actualHolderLoadSpaceTwo (closure U) ℝ alpha) (hrho : Continuous rho)
    (hinverse : ∀ t : T, ∀ p : actualHolderC2JetSpaceTwo U alpha,
      (∀ x : closure U, (actualHolderComplexFieldTwo U alpha a b p x).PosDef) →
      actualHolderDeterminantTwo U alpha a b p=rho t →
      ∃ S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha,
        Function.LeftInverse S (actualHolderDeterminantDerivativeTwo U alpha a b p) ∧
        Function.RightInverse S (actualHolderDeterminantDerivativeTwo U alpha a b p)) :
    IsOpen {t : T | ∃ p : actualHolderC2JetSpaceTwo U alpha,
      (∀ x : closure U, (actualHolderComplexFieldTwo U alpha a b p x).PosDef) ∧
      actualHolderDeterminantTwo U alpha a b p=rho t} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro t ⟨p,hpos,hp⟩
  obtain ⟨S,hleft,hright⟩ := hinverse t p hpos hp
  obtain ⟨Psi,_,_,hPsi⟩ := actualHolderDeterminantTwo_local_inverse_of_bounded_inverse
    U hU alpha a b p S hleft hright hpos
  rw [hp] at hPsi
  filter_upwards [hrho.continuousAt.tendsto.eventually hPsi] with s hs
  exact ⟨Psi (rho s),hs.2,hs.1⟩

end PowerConvexity
