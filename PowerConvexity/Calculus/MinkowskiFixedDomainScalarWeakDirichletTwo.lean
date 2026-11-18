import PowerConvexity.Calculus.MinkowskiFixedDomainCofactorTwo
import PowerConvexity.Analysis.CofactorScalarWeakDirichlet

/-! # The actual linearized continuation load on the fixed Minkowski domain.
For L_v h = g, the normalized cofactor weak equation has the scalar load
-(1/c) rho_s g. This load is proved L2 from the actual smooth density and
compact domain; no extra integrability premise is imposed. The conclusion
is still a Sobolev zero-trace weak solution, not a classical inverse.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance mfdswdRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mfdswdRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem classicalDirichlet_minkowski_fixed_scalar_weak_dirichlet_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) :
    let b := fun j => Complex.I • e j
    let V := minkowskiDomain t U (ball (0 : E) R)
    ∃ w f : E → ℝ, ContDiff ℝ 6 w ∧ ContDiff ℝ 6 f ∧
      (∀ x ∈ closure V, (complexHessian e b w x).PosDef ∧
        (1 : ℂ) < (complexHessian e b w x).det) ∧
      (∀ x ∈ frontier V, w x = 0) ∧
      (∀ x ∈ frontier V, f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
        (∀ᶠ z in 𝓝 x, z ∈ V ↔ f z < 0)) ∧
      ClassicalDirichletDensityDataTwo e b V (dirichletContinuationDensityTwo e b w 0) w ∧
      (∀ s : ℝ, ContDiff ℝ 4 (dirichletContinuationDensityTwo e b w s)) ∧
      ∃ L : DeGiorgi.AmbientSpace (2+2) ≃ₗᵢ[ℝ] E,
        (∀ i, L (realDirections i) = e i) ∧
        (∀ i, L (imagDirections i) = Complex.I • e i) ∧
        ∃ c : ℝ, 0 < c ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
          ClassicalDirichletDensityDataTwo e b V (dirichletContinuationDensityTwo e b w s) v →
          ∃ B : DeGiorgi.NormalizedEllipticCoeff (2+2) (L ⁻¹' V), B.1.Λ = Λ ∧
            (∀ x ∈ L ⁻¹' V, B.1.a x = c⁻¹ • complexCofactorCoeff (fun y => v (L y)) x) ∧
            ∀ g : E → ℝ, Continuous g →
              ∃ h : AmbientSpace (2+2) → ℝ, MemH01 h (L ⁻¹' V) ∧
                (∀ hw : MemW1pWitness 2 h (L ⁻¹' V),
                  ∀ phi : AmbientSpace (2+2) → ℝ, MemH01 phi (L ⁻¹' V) →
                  ∀ hphi : MemW1pWitness 2 phi (L ⁻¹' V),
                    bilinFormOfCoeff B.1 hw hphi =
                      ∫ x in L ⁻¹' V,
                        -(c⁻¹ * dirichletContinuationDensityTwo e b w s (L x) * g (L x))*phi x) ∧
                ∀ k : AmbientSpace (2+2) → ℝ, MemH01 k (L ⁻¹' V) →
                  (∀ kw : MemW1pWitness 2 k (L ⁻¹' V),
                    ∀ phi : AmbientSpace (2+2) → ℝ, MemH01 phi (L ⁻¹' V) →
                    ∀ hphi : MemW1pWitness 2 phi (L ⁻¹' V),
                      bilinFormOfCoeff B.1 kw hphi =
                        ∫ x in L ⁻¹' V,
                          -(c⁻¹ * dirichletContinuationDensityTwo e b w s (L x) * g (L x))*phi x) →
                  h =ᵐ[volume.restrict (L ⁻¹' V)] k := by
  let b := fun j => Complex.I • e j
  let V := minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨w,f,hw,hf,hwp,hwb,hfb,hstart,hreg,L,hLa,hLb,c,hc,Λ,hΛ,hcoeff⟩ :=
    classicalDirichlet_minkowski_fixed_uniform_cofactor_ellipticity_two
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
  have hWo : IsOpen (L ⁻¹' V) := hVo.preimage L.continuous
  have hWK : IsCompact (L ⁻¹' closure V) := L.toHomeomorph.isCompact_preimage.mpr hVK
  have hWb : Bornology.IsBounded (L ⁻¹' V) :=
    hWK.isBounded.subset (preimage_mono subset_closure)
  refine ⟨w,f,hw,hf,hwp,hwb,hfb,hstart,hreg,L,hLa,hLb,c,hc,Λ,hΛ,?_⟩
  intro s hs v hv
  obtain ⟨B,hBΛ,hB⟩ := hcoeff s hs v hv
  refine ⟨B,hBΛ,hB,?_⟩
  intro g hg
  let load : AmbientSpace (2+2) → ℝ :=
    fun x => -(c⁻¹ * dirichletContinuationDensityTwo e b w s (L x) * g (L x))
  have hload : Continuous load :=
    ((continuous_const.mul ((hreg s).continuous.comp L.continuous)).mul
      (hg.comp L.continuous)).neg
  have hloadL2 : MemLp load 2 (volume.restrict (L ⁻¹' V)) :=
    continuous_memLp_two_of_subset_compact hWK (preimage_mono subset_closure) hload
  obtain ⟨h,hh,huniq⟩ := scalar_weak_dirichlet_exists
    (by norm_num : 2 ≤ 2+2) hWo hWb B.1 hloadL2
  refine ⟨h,hh.1,hh.2,?_⟩
  intro k hk0 hk
  exact huniq k ⟨hk0,hk⟩

end PowerConvexity
