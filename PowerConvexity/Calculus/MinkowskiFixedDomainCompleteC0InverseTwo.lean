import PowerConvexity.Calculus.MinkowskiFixedDomainPhysicalLinearizedTwo
import PowerConvexity.Calculus.ActualPhysicalCompleteC0InverseTwo

/-! # One complete C0 weak inverse along the actual fixed-domain path

The initial subsolution, physical isometry, cofactor normalization, ellipticity
bound and C0 operator bound are all chosen before the density parameter and
its candidate solution.  The completed operator is identified with the actual
zero-trace weak solution on every continuous load, and with the classical
interior-C2 solution on C1 loads.  Existence of the nonlinear candidate and
boundary Schauder control are not assumed to follow from this C0 statement.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance mfccRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mfccRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local notation "F" => AmbientSpace (2+2)

theorem classicalDirichlet_minkowski_fixed_complete_weak_C0_inverse_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x=0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det=1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) :
    let b := fun j => Complex.I • e j
    let V := minkowskiDomain t U (ball (0 : E) R)
    ∃ w : E → ℝ, ContDiff ℝ 6 w ∧
      (∀ x ∈ closure V, (complexHessian e b w x).PosDef ∧
        (1 : ℂ) < (complexHessian e b w x).det) ∧
      (∀ x ∈ frontier V, w x=0) ∧
      ClassicalDirichletDensityDataTwo e b V (dirichletContinuationDensityTwo e b w 0) w ∧
      ∃ L : F ≃ₗᵢ[ℝ] E,
        (∀ i, L (realDirections i)=e i) ∧
        (∀ i, L (imagDirections i)=Complex.I • e i) ∧
        ∃ c > 0, ∃ Λ ≥ 1, ∃ hVK : IsCompact (closure V),
          letI : CompactSpace (closure V) := isCompact_iff_compactSpace.mp hVK
          ∃ M ≥ 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
            ClassicalDirichletDensityDataTwo e b V (dirichletContinuationDensityTwo e b w s) v →
            ∃ B : NormalizedEllipticCoeff (2+2) (L ⁻¹' V), B.1.Λ=Λ ∧
              (∀ y ∈ L ⁻¹' V, B.1.a y=c⁻¹ • complexCofactorCoeff (fun z => v (L z)) y) ∧
              ∃ T : C(closure V, ℝ) →L[ℝ] C(closure V, ℝ), ‖T‖ ≤ M/2 ∧
                (∀ g : E → ℝ, ContinuousOn g (closure V) → ∃ H : E → ℝ,
                  Continuous H ∧ MemH01 (fun y => H (L y)) (L ⁻¹' V) ∧
                  ActualScalarWeakEquationTwo B.1
                    (fun y => -(c⁻¹*dirichletContinuationDensityTwo e b w s (L y)*g (L y)))
                    (fun y => H (L y)) ∧
                  (∀ x ∈ frontier V, H x=0) ∧
                  ∀ hg : ContinuousOn g (closure V), ∀ x : closure V,
                    T ⟨fun y => g y,hg.domRestrict⟩ x=H x) ∧
                ∀ g : E → ℝ, ∀ hg : ContDiff ℝ 1 g, ∃ h : E → ℝ,
                  Continuous h ∧ ContDiffOn ℝ 2 h V ∧
                  (∀ x ∈ frontier V, h x=0) ∧
                  (∀ x ∈ V, linearizedCMAOperatorTwo e b v h x=g x) ∧
                  MemH01 (fun y => h (L y)) (L ⁻¹' V) ∧
                  ActualScalarWeakEquationTwo B.1
                    (fun y => -(c⁻¹*dirichletContinuationDensityTwo e b w s (L y)*g (L y)))
                    (fun y => h (L y)) ∧
                  ∀ x : closure V,
                    T ⟨fun y => g y,hg.continuous.comp continuous_subtype_val⟩ x=h x := by
  let b := fun j => Complex.I • e j
  let V := minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨w,hw,hwp,hwb,hstart,L,hLa,hLb,c,hc,Λ,hΛ,hsolve⟩ :=
    classicalDirichlet_minkowski_fixed_physical_linearized_dirichlet_two
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
  refine ⟨w,hw,hwp,hwb,hstart,L,hLa,hLb,c,hc,Λ,hΛ,hVK,?_⟩
  letI : CompactSpace (closure V) := isCompact_iff_compactSpace.mp hVK
  obtain ⟨B₀,hB₀⟩ := (hVK.image hw.continuous).isBounded.exists_norm_le
  let M := max B₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M,hM,?_⟩
  intro s hs v hv
  have hwv := dirichletContinuationDensityTwo_subsolution_le e b hab hVo hVK
    (hw.of_le (by norm_num)) (fun x hx => (hwp x (subset_closure hx)).1)
    (fun x hx => le_of_lt (Complex.lt_def.mp (hwp x (subset_closure hx)).2).1) hwb hs hv
  have hvM : ∀ x ∈ closure V, -v x ≤ M := by
    intro x hx
    have hwM : -w x ≤ M := by
      have hb := hB₀ (w x) ⟨x,hx,rfl⟩
      have ha : |w x| ≤ B₀ := by simpa only [Real.norm_eq_abs] using hb
      exact (neg_le_abs (w x)).trans (ha.trans (le_max_left _ _))
    exact (neg_le_neg (hwv x hx)).trans hwM
  obtain ⟨B,hBΛ,hB,_⟩ := hsolve s hs v hv
  refine ⟨B,hBΛ,hB,?_⟩
  apply actual_physical_complete_C0_inverse_two hVo hVK L e b hLa hLb
    (hw.of_le (by norm_num)) (fun x hx => (hwp x hx).1) hwb hv.1
    hv.continuous_closure hv.2.2.2.2 hv.2.2.1 hv.2.2.2.1
    ((dirichletContinuationDensityTwo_contDiff e b (hw.of_le (by norm_num)) s).of_le (by norm_num))
    ?_ hc hM hvM B.1 hB
  intro x hx
  exact (dirichletContinuationDensityTwo_bounds e b hs
    (le_of_lt (Complex.lt_def.mp (hwp x (subset_closure hx)).2).1)).1

end PowerConvexity
