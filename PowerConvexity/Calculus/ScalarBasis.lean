import PowerConvexity.Calculus.PowerSemidefinite

/-! # The canonical real basis of the complex line and positive Hessians -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators

namespace PowerConvexity
open CHS.Calculus

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem realBlockHessian_posDef_of_basis_quadratic {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (e : Module.Basis (ι ⊕ ι) ℝ E)
    (hQ : ∀ v : E, v ≠ 0 → 0 < realHessian u x v v) :
    (realBlockHessian (fun i => e (.inl i)) (fun i => e (.inr i)) u x).PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (realBlockHessian_isHermitian hu _ _)
  intro z hz
  rw [star_trivial, ← realHessian_sum_directions_quadratic hu]
  have he : (∑ i, z i • Sum.elim (fun i => e (.inl i)) (fun i => e (.inr i)) i) =
      ∑ i, z i • e i := by
    apply Finset.sum_congr rfl
    intro i _
    cases i <;> rfl
  rw [he]
  apply hQ
  intro hv
  apply hz
  have hr := e.repr_sum_self z
  rw [hv, map_zero] at hr
  exact hr.symm

noncomputable def scalarRealBasis : Module.Basis (Fin 1 ⊕ Fin 1) ℝ ℂ :=
  Complex.basisOneI.reindex (finSumFinEquiv (m := 1) (n := 1)).symm

@[simp]
theorem scalarRealBasis_inl (i : Fin 1) : scalarRealBasis (.inl i) = (1 : ℂ) := by
  fin_cases i
  simp [scalarRealBasis, Module.Basis.reindex_apply, Complex.coe_basisOneI, finSumFinEquiv]

@[simp]
theorem scalarRealBasis_inr (i : Fin 1) : scalarRealBasis (.inr i) = Complex.I := by
  fin_cases i
  simp [scalarRealBasis, Module.Basis.reindex_apply, Complex.coe_basisOneI, finSumFinEquiv]

theorem realHessian_power_scalar_quadratic_pos_iff {u : ℂ → ℝ} {x : ℂ} {ρ : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (hρpos : 0 < ρ)
    (hρ : complexHessian (fun _ : Fin 1 => (1 : ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ : ℂ)) :
    (∀ v : ℂ, v ≠ 0 → 0 < realHessian (powerTransform u) x v v) ↔
      0 < scalarSigma 1 Complex.I u x := by
  rw [← realHessian_power_scalar_posDef_iff hu hx 1 Complex.I hρpos hρ]
  constructor
  · intro h
    simpa only [scalarRealBasis_inl, scalarRealBasis_inr] using
      realBlockHessian_posDef_of_basis_quadratic (powerTransform_contDiffAt hu hx) scalarRealBasis h
  · intro h
    apply realHessian_pos_of_basis_block (powerTransform_contDiffAt hu hx) scalarRealBasis
    simpa only [scalarRealBasis_inl, scalarRealBasis_inr] using h

end PowerConvexity
