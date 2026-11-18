import PowerConvexity.Analysis.ActualHolderJetDeterminantInverseTwo
import PowerConvexity.Analysis.ActualHolderDeterminantInverseTransportTwo

/-! # The genuine bounded determinant inverse in the original complex frame

Every geometric and analytic datum is pulled through the same ambient real
linear isometry.  The canonical inverse is then conjugated by the actual
complete Holder load and zero-boundary jet equivalences.  Neither an inverse
nor an independent boundary coefficient modulus is an input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
  actualDensityJetSeminormed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "F" => AmbientSpace (2+2)

theorem actual_isometric_holder_jet_determinant_bounded_inverse_two
    {U : Set E} [CompactSpace (closure U)]
    (hU : IsOpen U) (hK : IsCompact (closure U)) (hproper : U≠univ) (hconv : Convex ℝ U)
    {o : E} {r₀ diameter alpha : ℝ} (hr₀ : 0 < r₀) (hdia : 0 ≤ diameter)
    (hball : closedBall o r₀ ⊆ U) (hdiam : ∀ c ∈ frontier U, ‖o-c‖ ≤ diameter)
    {phi : E → ℝ} (hphi : ContDiff ℝ 3 phi)
    (hphi0 : ∀ c ∈ frontier U, phi c=0) (hDphi : ∀ c ∈ frontier U, fderiv ℝ phi c≠0)
    (hdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z∈U ↔ phi z<0)
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (T : F ≃ₗᵢ[ℝ] E) (a b : Fin 2 → E)
    (ha : ∀ i, T (realDirections i)=a i) (hb : ∀ i, T (imagDirections i)=b i)
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian a b w x).PosDef)
    (hwb : ∀ x ∈ frontier U, w x=0)
    (p : actualHolderC2JetSpaceTwo U alpha)
    (hu : ContDiffOn ℝ 4 (actualClosureExtensionTwo U p.1.1) U)
    (hpos : ∀ x ∈ U, (complexHessian a b (actualClosureExtensionTwo U p.1.1) x).PosDef)
    {rho : E → ℝ}
    (hdet : ∀ x ∈ U, (complexHessian a b (actualClosureExtensionTwo U p.1.1) x).det=(rho x : ℂ))
    (hrho : ContDiff ℝ 1 rho) (hrho1 : ∀ x ∈ U, 1 ≤ rho x) :
    ∃ S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha,
      (actualHolderDeterminantDerivativeTwo U alpha a b p).comp S=
        ContinuousLinearMap.id ℝ (actualHolderLoadSpaceTwo (closure U) ℝ alpha) ∧
      S.comp (actualHolderDeterminantDerivativeTwo U alpha a b p)=
        ContinuousLinearMap.id ℝ (actualHolderC2JetSpaceTwo U alpha) := by
  let V := T ⁻¹' U
  have hV : IsOpen V := hU.preimage T.continuous
  have hVc : Convex ℝ V := hconv.linear_preimage T.toLinearEquiv.toLinearMap
  have hcl : closure V=T ⁻¹' closure U := (T.toHomeomorph.preimage_closure U).symm
  have hfront : frontier V=T ⁻¹' frontier U := (T.toHomeomorph.preimage_frontier U).symm
  have hVK : IsCompact (closure V) := by
    rw [hcl]
    exact T.toHomeomorph.isCompact_preimage.mpr hK
  letI : CompactSpace (closure V) := isCompact_iff_compactSpace.mp hVK
  have hVp : V≠univ := by
    intro h
    apply hproper
    apply Set.eq_univ_of_forall
    intro x
    have hx : T.symm x∈V := by rw [h]; trivial
    change T (T.symm x)∈U at hx
    simpa only [T.apply_symm_apply] using hx
  have hballT : closedBall (T.symm o) r₀ ⊆ V := by
    intro z hz
    apply hball
    have he : dist (T z) o=dist z (T.symm o) := by
      simpa only [T.apply_symm_apply] using T.dist_map z (T.symm o)
    simpa only [mem_closedBall,he] using hz
  have hdiamT : ∀ c ∈ frontier V, ‖T.symm o-c‖ ≤ diameter := by
    intro c hc
    have hcU : T c∈frontier U := by rwa [hfront] at hc
    have he : ‖T.symm o-c‖=‖o-T c‖ := by
      rw [← T.norm_map (T.symm o-c),map_sub,T.apply_symm_apply]
    rw [he]
    exact hdiam (T c) hcU
  let phiT : F → ℝ := fun z => phi (T z)
  have hphiT : ContDiff ℝ 3 phiT := hphi.comp T.contDiff
  have hphi0T : ∀ c ∈ frontier V, phiT c=0 := by
    intro c hc
    exact hphi0 (T c) (by rwa [hfront] at hc)
  have hDphiT : ∀ c ∈ frontier V, fderiv ℝ phiT c≠0 := by
    intro c hc hz
    apply hDphi (T c) (by rwa [hfront] at hc)
    have hD : fderiv ℝ phiT c=(fderiv ℝ phi (T c)).comp
        T.toContinuousLinearEquiv.toContinuousLinearMap :=
      ((hphi.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.comp c
        T.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun D : F →L[ℝ] ℝ => D (T.symm v)) hz
    rw [hD] at hv
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,T.apply_symm_apply,_root_.zero_apply] using hv
  have hdefT : ∀ c ∈ frontier V, ∀ᶠ z in 𝓝 c, z∈V ↔ phiT z<0 := by
    intro c hc
    exact T.continuous.continuousAt.tendsto.eventually (hdef (T c) (by rwa [hfront] at hc))
  let wT : F → ℝ := fun z => w (T z)
  have hwT : ContDiff ℝ 2 wT := hw.comp T.contDiff
  have hwpT : ∀ x ∈ closure V, (complexHessian realDirections imagDirections wT x).PosDef := by
    intro x hx
    change (complexHessian realDirections imagDirections (fun y => w (T y)) x).PosDef
    rw [complexHessian_comp_linearIsometry T hw.contDiffAt,
      show (fun i => T (realDirections i))=a from funext ha,
      show (fun i => T (imagDirections i))=b from funext hb]
    exact hwp (T x) (by rwa [hcl] at hx)
  have hwbT : ∀ x ∈ frontier V, wT x=0 := by
    intro x hx
    exact hwb (T x) (by rwa [hfront] at hx)
  let q := actualHolderJetIsometricEquivTwo U V hU hV T rfl alpha p
  have hq4 : ContDiffOn ℝ 4 (actualClosureExtensionTwo V q.1.1) V := by
    apply (hu.comp T.toContinuousLinearEquiv.contDiff.contDiffOn (fun x hx => hx)).congr
    intro x hx
    exact actualHolderJetIsometricEquivTwo_apply_value U V hU hV T rfl alpha p (subset_closure hx)
  have hqp : ∀ x ∈ V, (complexHessian realDirections imagDirections
      (actualClosureExtensionTwo V q.1.1) x).PosDef := by
    intro x hx
    rw [actual_holder_jet_isometric_complex_hessian_two U V hU hV T rfl alpha a b ha hb p hx]
    exact hpos (T x) hx
  let rhoT : F → ℝ := fun z => rho (T z)
  have hqd : ∀ x ∈ V, (complexHessian realDirections imagDirections
      (actualClosureExtensionTwo V q.1.1) x).det=(rhoT x : ℂ) := by
    intro x hx
    rw [actual_holder_jet_isometric_complex_hessian_two U V hU hV T rfl alpha a b ha hb p hx]
    exact hdet (T x) hx
  have hS := actual_holder_jet_determinant_bounded_inverse_two hV hVK hVp hVc hr₀ hdia
    hballT hdiamT hphiT hphi0T hDphiT hdefT halpha halpha1 hwT hwpT hwbT q hq4 hqp hqd
    (hrho.comp T.contDiff) (fun x hx => hrho1 (T x) hx)
  let S := Classical.choose hS
  have hSi := Classical.choose_spec hS
  exact actual_holder_determinant_inverse_isometric_two U V hU hV T rfl alpha a b ha hb p S hSi.1 hSi.2

end PowerConvexity
