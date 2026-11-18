import PowerConvexity.Analysis.ActualUniformFlatZeroQuotientFour
import PowerConvexity.Analysis.ActualUniformQuotientNormalizationFour

/-! # Uniform physical boundary quotient for bounded rough coefficients

The common radius and constants precede all normals and actual responses.
Small drift, unit load and unit response are obtained by genuine spatial and
amplitude normalization. No coefficient modulus or initial slope is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_physical_zero_boundary_quotient_four
    {Lambda B F M : ℝ} (hLambda : 1 ≤ Lambda) (hB : 0 ≤ B)
    (hF : 0 ≤ F) (hM : 0 ≤ M) :
    ∃ R > 0, R ≤ (1/2 : ℝ) ∧ ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C > 0,
      ∀ N : E, ‖N‖=1 → ∀ D : ActualFlatQuotientEquationFour N Lambda B F,
      (∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → D.solution x=0) →
      (∀ x ∈ actualFlatClosedUpperBallFour N 1, |D.solution x| ≤ M) →
      ∃ a : ℝ, |a| ≤ C ∧ ∀ x ∈ actualFlatClosedUpperBallFour N R,
        |D.solution x-a*inner ℝ N x| ≤ C*‖x‖^alpha*inner ℝ N x := by
  obtain ⟨kappa,hk,hk2,alpha,ha,ha1,C0,hC0,hquot⟩ :=
    actual_uniform_flat_zero_boundary_quotient_four hLambda
  let r := kappa/(B+1)
  have hden : 0 < B+1 := by linarith
  have hr : 0 < r := div_pos hk hden
  have hrk : r ≤ kappa := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hr1 : r ≤ 1 := hrk.trans (hk2.trans (by norm_num))
  have hrB : r*B ≤ kappa := by
    have hcancel : r*(B+1)=kappa := by dsimp only [r]; field_simp
    nlinarith
  let A := M+F+1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAM : M ≤ A := by dsimp only [A]; linarith
  have hAF : F ≤ A := by dsimp only [A]; linarith
  have hsource : (r/A)*(r*F) ≤ 1 := by
    have hrr : r*r ≤ 1 := by nlinarith
    calc
      (r/A)*(r*F) = (r*r*F)/A := by ring
      _ ≤ 1 := (div_le_one hA).2 (by nlinarith [mul_le_mul_of_nonneg_right hrr hF])
  let K := A*C0*r⁻¹*(r⁻¹)^alpha
  let C := A*C0*r⁻¹+K+1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hsC : A*C0*r⁻¹ ≤ C := by dsimp only [C]; linarith
  have hKC : K ≤ C := by
    have hp : 0 ≤ A*C0*r⁻¹ := by positivity
    dsimp only [C]
    linarith
  refine ⟨r*(1/2),by positivity,by nlinarith,alpha,ha,ha1,C,hC,?_⟩
  intro N hN D hzero hbound
  let Dr := actualFlatQuotientDilateFour hr hr1 D
  let Dc := actualFlatQuotientAmplitudeFour (c := r/A) (by positivity) Dr
  let Ds := actualFlatQuotientIncreaseBoundsFour hrB hsource Dc
  have hsol (x : E) : Ds.solution x=A⁻¹*D.solution (r • x) := by
    change (r/A)*(r⁻¹*D.solution (r • x))=A⁻¹*D.solution (r • x)
    field_simp
  have hz : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → Ds.solution x=0 := by
    intro x hx ht
    rw [hsol,hzero (r • x) ?_ ?_,mul_zero]
    · have hxU : x ∈ actualFlatClosedUpperBallFour N 1 :=
        ⟨hx,show 0 ≤ inner ℝ N x from ht.ge⟩
      have hh := actual_flat_closed_unit_dilation_maps_four N hr hr1 hxU
      exact hh.1
    · simp only [inner_smul_right,ht,mul_zero]
  have hb : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |Ds.solution x| ≤ 1 := by
    intro x hx
    rw [hsol,abs_mul,abs_of_pos (inv_pos.mpr hA)]
    have hh := (hbound _ (actual_flat_closed_unit_dilation_maps_four N hr hr1 hx)).trans hAM
    have hm := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hA.le)
    simpa only [inv_mul_cancel₀ hA.ne'] using hm
  obtain ⟨a0,ha0,herr⟩ := hquot N hN Ds hz hb
  let a := A*a0*r⁻¹
  have hac : |a| ≤ C := by
    dsimp only [a]
    rw [abs_mul,abs_mul,abs_of_pos hA,abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha0 hA.le)
      (inv_nonneg.mpr hr.le)).trans hsC
  refine ⟨a,hac,?_⟩
  intro x hx
  have hy : r⁻¹ • x ∈ actualFlatClosedUpperBallFour N (1/2) := by
    have hh := actual_flat_smul_closedUpperBall_four (inv_pos.mpr hr) hx
    simpa only [← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul] using hh
  have hh := herr (r⁻¹ • x) hy
  rw [hsol,smul_smul,mul_inv_cancel₀ hr.ne',one_smul,inner_smul_right,
    norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),
    Real.mul_rpow (inv_nonneg.mpr hr.le) (norm_nonneg x)] at hh
  have he : A*(A⁻¹*D.solution x-a0*(r⁻¹*inner ℝ N x))=
      D.solution x-a*inner ℝ N x := by
    dsimp only [a]
    field_simp
    <;> ring
  have hm := mul_le_mul_of_nonneg_left hh hA.le
  have hmleft : A*|A⁻¹*D.solution x-a0*(r⁻¹*inner ℝ N x)|=
      |A*(A⁻¹*D.solution x-a0*(r⁻¹*inner ℝ N x))| := by rw [abs_mul,abs_of_pos hA]
  rw [hmleft,he] at hm
  have he' : |D.solution x-a*inner ℝ N x| ≤ K*‖x‖^alpha*inner ℝ N x := by
    apply hm.trans_eq
    dsimp only [K]
    ring
  exact he'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg (norm_nonneg x) alpha)) hx.2)

end PowerConvexity
