import PowerConvexity.Calculus.ContinuousLinearConjugacyDerivative

/-! # Bounded two-sided inverses under an actual Banach-space conjugacy -/
set_option autoImplicit false
noncomputable section
namespace PowerConvexity
variable {X Y V W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem actual_bounded_inverse_of_linear_conjugacy
    (P : X ≃L[ℝ] Y) (Q : V ≃L[ℝ] W) (L : X →L[ℝ] V) (K : Y →L[ℝ] W)
    (S : W →L[ℝ] Y)
    (hconj : K.comp P.toContinuousLinearMap=Q.toContinuousLinearMap.comp L)
    (hSright : K.comp S=ContinuousLinearMap.id ℝ W)
    (hSleft : S.comp K=ContinuousLinearMap.id ℝ Y) :
    ∃ R : V →L[ℝ] X,
      L.comp R=ContinuousLinearMap.id ℝ V ∧ R.comp L=ContinuousLinearMap.id ℝ X := by
  have hc (x : X) : K (P x)=Q (L x) :=
    congrArg (fun A : X →L[ℝ] W => A x) hconj
  let R := P.symm.toContinuousLinearMap.comp (S.comp Q.toContinuousLinearMap)
  refine ⟨R,?_,?_⟩
  · apply ContinuousLinearMap.ext
    intro v
    change L (P.symm (S (Q v)))=v
    apply Q.injective
    rw [←hc,P.apply_symm_apply]
    exact congrArg (fun A : W →L[ℝ] W => A (Q v)) hSright
  · apply ContinuousLinearMap.ext
    intro x
    change P.symm (S (Q (L x)))=x
    apply P.injective
    rw [P.apply_symm_apply,←hc]
    exact congrArg (fun A : Y →L[ℝ] Y => A (P x)) hSleft

end PowerConvexity
