import PowerConvexity.Calculus.QuadraticJointJets
import Mathlib.RingTheory.AlgebraTower

/-! # The actual real basis associated with a complex basis -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace PowerConvexity
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

def complexRealIndexEquiv (ι : Type*) : Fin 2 × ι ≃ ι ⊕ ι where
  toFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  invFun := Sum.elim (fun i => (0,i)) (fun i => (1,i))
  left_inv p := by
    rcases p with ⟨i,j⟩
    fin_cases i <;> rfl
  right_inv p := by
    cases p <;> rfl

noncomputable def complexRealBasis (e : Module.Basis ι ℂ E) : Module.Basis (ι ⊕ ι) ℝ E :=
  (Complex.basisOneI.smulTower e).reindex (complexRealIndexEquiv ι)

@[simp]
theorem complexRealBasis_inl (e : Module.Basis ι ℂ E) (i : ι) :
    complexRealBasis e (.inl i) = e i := by
  simp [complexRealBasis,Module.Basis.reindex_apply,complexRealIndexEquiv,Complex.coe_basisOneI]

@[simp]
theorem complexRealBasis_inr (e : Module.Basis ι ℂ E) (i : ι) :
    complexRealBasis e (.inr i) = Complex.I • e i := by
  simp [complexRealBasis,Module.Basis.reindex_apply,complexRealIndexEquiv,Complex.coe_basisOneI]

theorem complexRealBasis_eq_sum (e : Module.Basis ι ℂ E) :
    (complexRealBasis e : (ι ⊕ ι) → E) = Sum.elim e (fun i => Complex.I • e i) := by
  funext i
  cases i <;> simp

end PowerConvexity
