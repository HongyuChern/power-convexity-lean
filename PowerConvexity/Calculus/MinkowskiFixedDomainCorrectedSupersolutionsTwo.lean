import PowerConvexity.Calculus.MinkowskiFixedDomainCofactorTwo
import PowerConvexity.Calculus.ContinuationSourceAllDirectionsTwo
import PowerConvexity.Calculus.DensityCorrectedHessianTwo

/-! # Actual corrected Hessian supersolutions on the fixed Minkowski domain.
The C6 strict subsolution, isometry, ellipticity ratio and source constant
are all chosen before an auxiliary solution. The conclusion uses the
actual full H01 weak supersolution predicate on every interior ball.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance mfdcsRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mfdcsRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem classicalDirichlet_minkowski_fixed_corrected_hessian_supersolutions_two
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
      ∃ L : AmbientSpace (2+2) ≃ₗᵢ[ℝ] E,
        (∀ i, L (realDirections i) = e i) ∧
        (∀ i, L (imagDirections i) = Complex.I • e i) ∧
        ∃ c : ℝ, 0 < c ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C : ℝ, 0 ≤ C ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
          ClassicalDirichletDensityDataTwo e b V (dirichletContinuationDensityTwo e b w s) v →
          ∃ B : NormalizedEllipticCoeff (2+2) (L ⁻¹' V), B.1.Λ = Λ ∧
            (∀ x ∈ L ⁻¹' V, B.1.a x = c⁻¹ • complexCofactorCoeff (fun y => v (L y)) x) ∧
            ∀ (z : AmbientSpace (2+2)) (M : ℝ) (x₀ : AmbientSpace (2+2)) (r S : ℝ),
              (hr : 0 < r) → (hrS : r < S) → (hclosed : closedBall x₀ S ⊆ L ⁻¹' V) →
              IsSupersolution (B.restrict
                ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrS.le)).trans hclosed)).1
                (fun y => M-(realHessian (fun q => v (L q)) y z z+(C*‖z‖^2/2)*v (L y))) := by
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
  let W := L ⁻¹' V
  have hWo : IsOpen W := hVo.preimage L.continuous
  have hclW : closure W = L ⁻¹' closure V := (L.toHomeomorph.preimage_closure V).symm
  have hWK : IsCompact (closure W) := by
    rw [hclW]
    exact L.toHomeomorph.isCompact_preimage.mpr hVK
  let wL := fun y => w (L y)
  have hwL : ContDiff ℝ 4 wL := (hw.of_le (by norm_num)).comp L.contDiff
  have hweq (x : AmbientSpace (2+2)) :
      complexHessian realDirections imagDirections wL x = complexHessian e b w (L x) := by
    rw [complexHessian_comp_linearIsometry L (hw.contDiffAt.of_le (by norm_num))]
    rw [show (fun i => L (realDirections i)) = e from funext hLa,
      show (fun i => L (imagDirections i)) = b from funext hLb]
  have hwdL (x : AmbientSpace (2+2)) (hx : x ∈ closure W) :
      (1 : ℝ) ≤ (complexHessian realDirections imagDirections wL x).det.re := by
    rw [hweq]
    have hxV : L x ∈ closure V := by rwa [hclW] at hx
    exact le_of_lt (Complex.lt_def.mp (hwp (L x) hxV).2).1
  have hrhoeq (s : ℝ) (x : AmbientSpace (2+2)) :
      dirichletContinuationDensityTwo realDirections imagDirections wL s x =
        dirichletContinuationDensityTwo e b w s (L x) := by
    simp only [dirichletContinuationDensityTwo,hweq]
  obtain ⟨C,hC,hsource⟩ := dirichletContinuationDensityTwo_uniform_second_source_all_directions
    realDirections imagDirections hWK hwL hwdL
  refine ⟨w,f,hw,hf,hwp,hwb,hfb,hstart,hreg,L,hLa,hLb,c,hc,Λ,hΛ,C,hC,?_⟩
  intro s hs v hv
  obtain ⟨B,hBΛ,hB⟩ := hcoeff s hs v hv
  refine ⟨B,hBΛ,hB,?_⟩
  intro z M x₀ r S hr hrS hclosed
  let vL := fun q => v (L q)
  have hvL : ContDiffOn ℝ 4 vL W := hv.1.comp L.contDiff.contDiffOn (fun _ hx => hx)
  have hveq (x : AmbientSpace (2+2)) (hx : x ∈ W) :
      complexHessian realDirections imagDirections vL x = complexHessian e b v (L x) := by
    rw [complexHessian_comp_linearIsometry L
      ((hv.1.contDiffAt (hVo.mem_nhds hx)).of_le (by norm_num))]
    rw [show (fun i => L (realDirections i)) = e from funext hLa,
      show (fun i => L (imagDirections i)) = b from funext hLb]
  have hvdet (x : AmbientSpace (2+2)) (hx : x ∈ W) :
      (complexHessian realDirections imagDirections vL x).det =
        (dirichletContinuationDensityTwo realDirections imagDirections wL s x : ℂ) := by
    rw [hveq x hx,hrhoeq]
    exact hv.2.2.2.1 (L x) hx
  have hvA (x : AmbientSpace (2+2)) (hx : x ∈ W) :
      (complexHessian realDirections imagDirections vL x).PosDef := by
    rw [hveq x hx]
    exact hv.2.2.1 (L x) hx
  exact density_corrected_directional_deficit_cofactor_supersolution_two hWo hvL
    (dirichletContinuationDensityTwo_contDiff realDirections imagDirections hwL s).contDiffOn
    hvdet (fun x hx => zero_lt_one.trans_le
      (dirichletContinuationDensityTwo_bounds realDirections imagDirections hs
        (hwdL x (subset_closure hx))).1)
    hvA hc B hB z (fun x hx => hsource s hs x (subset_closure hx) z) M hr hrS hclosed

end PowerConvexity
