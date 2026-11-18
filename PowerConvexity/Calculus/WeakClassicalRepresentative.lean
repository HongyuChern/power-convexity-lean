import PowerConvexity.Calculus.ClosureJetSobolev
import PowerConvexity.Analysis.ScalarWeakDirichlet
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # An actual classical representative satisfies the actual scalar equation.
This proves consistency from the full H01 weak equation and AE equality.
It does not construct the classical representative or boundary regularity.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators RealInnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem actual_classical_representative_satisfies_scalar_equation
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (A : EllipticCoeff d U) {load : E → ℝ} (hload : ContinuousOn load U)
    {h : E → ℝ}
    (hh : IsWeakSolution ⟨U,hU,hK.isBounded.subset subset_closure,A,
      (fun phi => ∫ x in U, load x*phi x)⟩ h)
    {H : E → ℝ} (hH : ContDiffOn ℝ 1 H U) (J : ClosureC2Jet H U)
    (he : H =ᵐ[volume.restrict U] h)
    {F : E → E} (hF : ∀ i : Fin d, ContDiffOn ℝ 1 (fun x => F x i) U)
    (hflux : ∀ x ∈ U, matMulE (A.a x) (smoothGradField H x) = F x) :
    ∀ x ∈ U, -classicalDivergence F x = load x := by
  let hw : MemW1pWitness 2 h U := hh.1.1.someWitness
  have hgrad := closureJet_weakGradient_eq_classical_ae hU hK hH J he hw
  have hdiv := hasWeakDiv_classical_of_contDiffOn hU hF
  have hdc : ContinuousOn (classicalDivergence F) U := by
    apply continuousOn_finsetSum
    intro i _
    exact (((hF i).fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn).clm_apply
      continuousOn_const
  have hz : ∀ᵐ x ∂volume, x ∈ U → classicalDivergence F x+load x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hdc.add hload).locallyIntegrableOn hU.measurableSet)
    intro phi hp hpc hps
    let ht : IsSmoothTestOn U phi := ⟨hp,hpc,hps⟩
    let hpw := smoothTestWitness hU ht
    have heq := hh.2 hw phi (smoothTest_memH01 hU ht) hpw
    have hpair : bilinFormOfCoeff A hw hpw =
        ∫ x in U, ∑ i, F x i*fderiv ℝ phi x (EuclideanSpace.single i 1) := by
      unfold bilinFormOfCoeff bilinFormIntegrandOfCoeff
      apply integral_congr_ae
      filter_upwards [hgrad,ae_restrict_mem hU.measurableSet] with x hx hxU
      rw [hx,hflux x hxU]
      simp only [hpw,smoothTestWitness,smoothGradField,PiLp.inner_apply,
        PiLp.toLp_apply,Real.inner_apply]
    rw [hpair,hdiv phi hp hpc hps] at heq
    have h1 := local_continuous_mul_test_integrable hU hdc hp.continuous hpc hps
    have h2 := local_continuous_mul_test_integrable hU hload hp.continuous hpc hps
    have hzero : (∫ x in U, (classicalDivergence F x+load x)*phi x) = 0 := by
      simp only [add_mul]
      rw [integral_add h1.integrableOn h2.integrableOn]
      linarith
    have hout : ∀ x ∉ U, phi x • (classicalDivergence F x+load x) = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (f := phi) (fun hs => hx (hps hs)),zero_smul]
    change (∫ x, phi x • (classicalDivergence F x+load x)) = 0
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    simpa only [smul_eq_mul,mul_comm] using hzero
  have hzU : (fun x => classicalDivergence F x+load x) =ᵐ[volume.restrict U] (fun _ => 0) :=
    (ae_restrict_iff' hU.measurableSet).mpr hz
  have hpoint := Measure.eqOn_open_of_ae_eq hzU hU (hdc.add hload) continuousOn_const
  intro x hx
  have hhx := hpoint hx
  linarith

end PowerConvexity
