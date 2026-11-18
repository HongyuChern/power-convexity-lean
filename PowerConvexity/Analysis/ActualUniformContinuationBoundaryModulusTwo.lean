import PowerConvexity.Analysis.ActualUniformNonlinearClosureBoundaryModulusTwo
import PowerConvexity.Analysis.ActualUniformIsometricClosureJetTwo
import PowerConvexity.Calculus.ContinuationUniformClosureC2Two
import PowerConvexity.Calculus.ActualContinuationDensityHigherBoundsTwo
import PowerConvexity.Calculus.ContinuationSourceAllDirectionsTwo
import PowerConvexity.Calculus.ComplexFrameCMAJets

/-! # The actual continuation family's common boundary Hessian modulus

The original fixed-domain C2 estimate and the derivatives of the actual
fixed subsolution supply every constant in the nonlinear rough boundary
estimate. A single real isometry transports the true closure jets, with
exact operator norms. No boundary modulus is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance aucbRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance aucbRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local notation "V" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_continuation_uniform_boundary_hessian_modulus_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hgeometry : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 6 w) (hwb : ∀ y ∈ frontier U, w y=0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0) :
    ∃ R > 0, R ≤ 1 ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C ≥ 0,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u →
      ∀ J : ClosureC2Jet u U, ∀ c ∈ frontier U, ∀ x ∈ closure U, ‖x-c‖ < R →
        ‖J.hessian x-J.hessian c‖ ≤ C*‖x-c‖^alpha := by
  by_cases hne : U.Nonempty
  swap
  · have hUe : U=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨1,by norm_num,le_rfl,1/2,by norm_num,by norm_num,0,le_rfl,?_⟩
    intro s hs u hu J c hc
    simpa only [hUe,frontier_empty,mem_empty_iff_false] using hc
  obtain ⟨M,hM,hbound⟩ := continuation_density_uniform_closure_C2_bound_two
    hU hconv hK hgeometry e hab (hw.of_le (by norm_num)) hwb hwp hwd hf hfb hdef
  obtain ⟨T,hTa,hTb⟩ := exists_euclideanIsometry_complexFrame_two e hab
  let W := T ⁻¹' U
  have hWo : IsOpen W := hU.preimage T.continuous
  have hWc : Convex ℝ W := hconv.linear_preimage T.toLinearEquiv.toLinearMap
  have hclW : closure W=T ⁻¹' closure U := (T.toHomeomorph.preimage_closure U).symm
  have hfrW : frontier W=T ⁻¹' frontier U := (T.toHomeomorph.preimage_frontier U).symm
  have hWK : IsCompact (closure W) := by
    rw [hclW]
    exact T.toHomeomorph.isCompact_preimage.mpr hK
  have hWne : W.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨T.symm x,by change T (T.symm x)∈U; simpa only [T.apply_symm_apply]⟩
  have hWp : W≠univ := by
    intro h
    apply hWK.ne_univ
    rw [h,closure_univ]
  let fT := fun z => f (T z)
  have hfT : ContDiff ℝ 3 fT := hf.comp T.contDiff
  have hfbT : ∀ c ∈ frontier W, fT c=0 ∧ fderiv ℝ fT c≠0 := by
    intro c hc
    have hcU : T c∈frontier U := by rwa [hfrW] at hc
    refine ⟨(hfb _ hcU).1,?_⟩
    intro hz
    apply (hfb _ hcU).2
    have hD : fderiv ℝ fT c=(fderiv ℝ f (T c)).comp
        T.toContinuousLinearEquiv.toContinuousLinearMap :=
      ((hf.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.comp c
        T.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun D : V →L[ℝ] ℝ => D (T.symm v)) hz
    rw [hD] at hv
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,T.apply_symm_apply,
      ContinuousLinearMap.zero_apply] using hv
  have hdefT : ∀ c ∈ frontier W, ∀ᶠ z in 𝓝 c, z∈W ↔ fT z<0 := by
    intro c hc
    have hcU : T c∈frontier U := by rwa [hfrW] at hc
    exact T.continuous.continuousAt.tendsto.eventually (hdef _ hcU)
  have hf1 : ContDiff ℝ 2 (fderiv ℝ fT) := hfT.fderiv_right (m := 2) (by norm_num)
  have hf2 : ContDiff ℝ 1 (realHessian fT) := hf1.fderiv_right (m := 1) (by norm_num)
  have hf3 : Continuous (fderiv ℝ (realHessian fT)) :=
    (hf2.fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨F1,hF1⟩ := hWK.exists_bound_of_continuousOn
    (f := fderiv ℝ fT) hf1.continuous.continuousOn
  obtain ⟨F2,hF2⟩ := hWK.exists_bound_of_continuousOn
    (f := realHessian fT) hf2.continuous.continuousOn
  obtain ⟨F3,hF3⟩ := hWK.exists_bound_of_continuousOn
    (f := fderiv ℝ (realHessian fT)) hf3.continuousOn
  let F := max 0 (max F1 (max F2 F3))
  have hF : 0 ≤ F := le_max_left _ _
  have h1 : F1 ≤ F := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : F2 ≤ F := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h3 : F3 ≤ F := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  let wT := fun z => w (T z)
  have hwT : ContDiff ℝ 6 wT := hw.comp T.contDiff
  have hweq (x : V) : complexHessian realDirections imagDirections wT x=
      complexHessian e (fun j => Complex.I • e j) w (T x) := by
    rw [complexHessian_comp_linearIsometry T (hw.contDiffAt.of_le (by norm_num))]
    rw [show (fun i => T (realDirections i))=e from funext hTa,
      show (fun i => T (imagDirections i))=(fun j => Complex.I • e j) from funext hTb]
  have hwdT (x : V) (hx : x∈closure W) :
      (1 : ℝ) ≤ (complexHessian realDirections imagDirections wT x).det.re := by
    rw [hweq]
    exact hwd (T x) (by rwa [hclW] at hx)
  have hrhoeq (s : ℝ) (x : V) :
      dirichletContinuationDensityTwo realDirections imagDirections wT s x=
        dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s (T x) := by
    simp only [dirichletContinuationDensityTwo,hweq]
  obtain ⟨D,hD,hden⟩ := dirichletContinuationDensityTwo_uniform_bounds
    realDirections imagDirections hWK (hwT.of_le (by norm_num)) hwdT
  obtain ⟨P,hP,hder⟩ := actual_continuation_density_uniform_third_jets_two
    realDirections imagDirections hWK hwT
  obtain ⟨Csrc,hCsrc,hsource⟩ := dirichletContinuationDensityTwo_uniform_second_source_all_directions
    realDirections imagDirections hWK (hwT.of_le (by norm_num)) hwdT
  obtain ⟨R,hR,hR1,alpha,ha,ha1,C,hC,hmod⟩ :=
    actual_uniform_nonlinear_closure_boundary_hessian_modulus_two hWo hWc hWK hWne hWp
      hfT hfbT hdefT hM hM hP hF hD hCsrc
      (fun z hz => (hF1 z hz).trans h1) (fun z hz => (hF2 z hz).trans h2)
      (fun z hz => (hF3 z hz).trans h3)
  refine ⟨R,hR,hR1,alpha,ha,ha1,C,hC,?_⟩
  intro s hs u hu J c hc x hx hxc
  let uT := fun z => u (T z)
  have huT : ContDiffOn ℝ 4 uT W := hu.1.comp T.contDiff.contDiffOn (fun _ hz => hz)
  have hu2 : ContDiffOn ℝ 2 u U := hu.1.of_le (by norm_num)
  let JT := actualClosureC2JetIsometricPullbackTwo T hU hu2 J
  have hueq (z : V) (hz : z∈W) :
      complexHessian realDirections imagDirections uT z=
        complexHessian e (fun j => Complex.I • e j) u (T z) := by
    rw [complexHessian_comp_linearIsometry T (hu2.contDiffAt (hU.mem_nhds hz))]
    rw [show (fun i => T (realDirections i))=e from funext hTa,
      show (fun i => T (imagDirections i))=(fun j => Complex.I • e j) from funext hTb]
  have hJT1 (z : V) (hz : z∈closure W) : ‖JT.derivative z‖ ≤ M := by
    rw [actual_isometric_closure_jet_derivative_norm_two]
    exact (hbound s hs u hu J (T z) (by rwa [hclW] at hz)).2.1
  have hJT2 (z : V) (hz : z∈closure W) : ‖JT.hessian z‖ ≤ M := by
    rw [actual_isometric_closure_jet_hessian_norm_two]
    exact (hbound s hs u hu J (T z) (by rwa [hclW] at hz)).2.2
  have hcT : T.symm c∈frontier W := by rw [hfrW]; simpa only [mem_preimage,T.apply_symm_apply]
  have hxT : T.symm x∈closure W := by rw [hclW]; simpa only [mem_preimage,T.apply_symm_apply]
  have hdist : ‖T.symm x-T.symm c‖=‖x-c‖ := by rw [←T.symm.map_sub,T.symm.norm_map]
  have hresult := hmod uT (dirichletContinuationDensityTwo realDirections imagDirections wT s) huT
    (dirichletContinuationDensityTwo_contDiff realDirections imagDirections (hwT.of_le (by norm_num)) s).contDiffOn
    (dirichletContinuationDensityTwo_contDiff realDirections imagDirections (hwT.of_le (by norm_num)) s).continuous.continuousOn
    JT (fun z hz => hu.2.2.2.2 (T z) (by rwa [hfrW] at hz))
    (fun z hz => by rw [hueq z hz]; exact hu.2.2.1 (T z) hz)
    (fun z hz => by rw [hueq z hz,hrhoeq]; exact hu.2.2.2.1 (T z) hz)
    (fun z hz => hden s hs z (subset_closure hz)) hJT1 hJT2
    (fun z hz => (hder s hs z (subset_closure hz)).1)
    (fun z hz => hsource s hs z (subset_closure hz))
    (T.symm c) hcT (T.symm x) hxT (by rwa [hdist])
  rw [actual_isometric_closure_jet_hessian_difference_two,T.apply_symm_apply,
    T.apply_symm_apply,hdist] at hresult
  exact hresult

end PowerConvexity
