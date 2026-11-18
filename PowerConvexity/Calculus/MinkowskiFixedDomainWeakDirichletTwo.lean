import PowerConvexity.Calculus.MinkowskiFixedDomainCofactorTwo
import PowerConvexity.Analysis.CofactorWeakDirichlet

/-! # Actual weak cofactor Dirichlet solvability on the constructed fixed domain.
Zero boundary means H01 trace; no classical C2 jet or pointwise boundary regularity is asserted. -/
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
local instance mfdwdRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mfdwdRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem classicalDirichlet_minkowski_fixed_cofactor_weak_dirichlet_two
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
            ∀ F : AmbientSpace (2+2) → AmbientSpace (2+2),
              MemLp F 2 (volume.restrict (L ⁻¹' V)) →
              ∃ h : AmbientSpace (2+2) → ℝ, MemH01 h (L ⁻¹' V) ∧
                (∀ hw : MemW1pWitness 2 h (L ⁻¹' V),
                  ∀ phi : AmbientSpace (2+2) → ℝ, MemH01 phi (L ⁻¹' V) →
                  ∀ hphi : MemW1pWitness 2 phi (L ⁻¹' V),
                    bilinFormOfCoeff B.1 hw hphi = divergenceRHSOfField F hphi) ∧
                ∀ k : AmbientSpace (2+2) → ℝ, MemH01 k (L ⁻¹' V) →
                  (∀ kw : MemW1pWitness 2 k (L ⁻¹' V),
                    ∀ phi : AmbientSpace (2+2) → ℝ, MemH01 phi (L ⁻¹' V) →
                    ∀ hphi : MemW1pWitness 2 phi (L ⁻¹' V),
                      bilinFormOfCoeff B.1 kw hphi = divergenceRHSOfField F hphi) →
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
  have hWb : Bornology.IsBounded (L ⁻¹' V) :=
    (L.toHomeomorph.isCompact_preimage.mpr hVK).isBounded.subset
      (preimage_mono subset_closure)
  refine ⟨w,f,hw,hf,hwp,hwb,hfb,hstart,hreg,L,hLa,hLb,c,hc,Λ,hΛ,?_⟩
  intro s hs v hv
  obtain ⟨B,hBΛ,hB⟩ := hcoeff s hs v hv
  refine ⟨B,hBΛ,hB,?_⟩
  intro F hF
  obtain ⟨h,hh⟩ := weakProblem_exists_of_divergenceData (by norm_num : 2 ≤ 2+2) hWo hWb B.1 hF
  have hidentity := actual_weak_dirichlet_all_test_identity rfl hh
  refine ⟨h,hidentity.1,hidentity.2,?_⟩
  intro k hk0 hk
  apply weakProblem_unique (by norm_num : 2 ≤ 2+2) hh
  refine ⟨hk0,?_⟩
  intro kw phi hphi0 hphi
  rw [hk kw phi hphi0 hphi]
  exact (weakProblemRHSOfField_eq_of_memH01 hWo hphi0 hphi).symm

end PowerConvexity
