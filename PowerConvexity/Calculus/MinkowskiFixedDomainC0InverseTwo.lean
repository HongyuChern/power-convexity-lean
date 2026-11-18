import PowerConvexity.Calculus.MinkowskiFixedDomainPhysicalLinearizedTwo
import PowerConvexity.Calculus.ActualPhysicalC0InverseTwo

/-! # A uniform complete-C0 response on the actual fixed-domain family

The subsolution, compact physical domain, zero boundary, cofactor operator and
classical response all come from the original endpoint hypotheses.  One norm
constant is chosen before the auxiliary density parameter and before its
candidate classical solution.  The nonlinear existence and the boundary
Hessian modulus are not consequences of this C0 inverse and remain separate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance mfciRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mfciRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem classicalDirichlet_minkowski_fixed_uniform_C0_inverse_two
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
      ∃ hVK : IsCompact (closure V),
        letI : CompactSpace (closure V) := isCompact_iff_compactSpace.mp hVK
        ∃ M ≥ 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
          ClassicalDirichletDensityDataTwo e b V (dirichletContinuationDensityTwo e b w s) v →
          ∃ T : C(closure V, ℝ) →L[ℝ] C(closure V, ℝ), ‖T‖ ≤ M/2 ∧
            (∀ f : C(closure V, ℝ), ∀ x, ∀ hx : x ∈ frontier V,
              T f ⟨x,frontier_subset_closure hx⟩=0) ∧
            ∀ g : E → ℝ, ∀ hg : ContDiff ℝ 1 g, ∃ h : E → ℝ,
              ClassicalLinearizedZeroDataTwo e b v V g h ∧
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
  refine ⟨w,hw,hwp,hwb,hstart,hVK,?_⟩
  letI : CompactSpace (closure V) := isCompact_iff_compactSpace.mp hVK
  obtain ⟨B,hB⟩ := (hVK.image hw.continuous).isBounded.exists_norm_le
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M,hM,?_⟩
  intro s hs v hv
  have hwv := dirichletContinuationDensityTwo_subsolution_le e b hab hVo hVK
    (hw.of_le (by norm_num)) (fun x hx => (hwp x (subset_closure hx)).1)
    (fun x hx => le_of_lt (Complex.lt_def.mp (hwp x (subset_closure hx)).2).1) hwb hs hv
  have hvM : ∀ x ∈ closure V, -v x ≤ M := by
    intro x hx
    have hwM : -w x ≤ M := by
      have hb := hB (w x) ⟨x,hx,rfl⟩
      have ha : |w x| ≤ B := by simpa only [Real.norm_eq_abs] using hb
      exact (neg_le_abs (w x)).trans (ha.trans (le_max_left _ _))
    exact (neg_le_neg (hwv x hx)).trans hwM
  obtain ⟨A,hAΛ,hA,haSolve⟩ := hsolve s hs v hv
  have hsurj : ∀ g : E → ℝ, ContDiff ℝ 1 g →
      ∃ h : E → ℝ, ClassicalLinearizedZeroDataTwo e b v V g h := by
    intro g hg
    obtain ⟨h,hhC,hh2,hhb,hhPDE,_⟩ := haSolve g hg
    exact ⟨h,hhC.continuousOn,hh2,hhb,hhPDE⟩
  obtain ⟨R₀,hR₀n,hR₀⟩ := actual_classical_bounded_C0_response_two e b v hVo hVK
    hv.continuous_closure (hv.1.of_le (by norm_num)) hv.2.2.2.2 hv.2.2.1 hM hvM hsurj
  obtain ⟨T,hTn,hT,_⟩ := actual_classical_C0_response_extension_two R₀
  refine ⟨T,hTn.trans hR₀n,?_,?_⟩
  · intro f x hx
    exact actual_classical_C0_extension_zero_boundary_two hR₀ hT f hx
  · intro g hg
    obtain ⟨h,hh⟩ := hsurj g hg
    refine ⟨h,hh,?_⟩
    let f : classicalC1LoadClosureTwo V :=
      ⟨⟨fun y => g y,hg.continuous.comp continuous_subtype_val⟩,
        ⟨g,hg,fun _ => rfl⟩⟩
    have he := hR₀.eq_classical hVo hVK hv.continuous_closure
      (hv.1.of_le (by norm_num)) hv.2.2.2.2 hv.2.2.1 f (fun _ => rfl) hh
    intro x
    exact congrArg (fun k : C(closure V, ℝ) => k x) (hT f) |>.trans (he x)

end PowerConvexity
