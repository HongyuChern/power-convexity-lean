import PowerConvexity.Analysis.ActualGraphShearFour
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! # A genuine C3 graph height obtained from the inverse function theorem
The normalized defining differential is the actual real unit-normal covector.
The constructed height is constant along every normal line, globally.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_regular_level_graph {N : E} (hN : ‖N‖=1) {f : E → ℝ}
    (hf : ContDiffAt ℝ 3 f 0) (hf0 : f 0=0)
    (hDf : ∀ v : E, fderiv ℝ f 0 v=inner ℝ N v) :
    ∃ rho : E → ℝ, ContDiffAt ℝ 3 rho 0 ∧ rho 0=0 ∧ fderiv ℝ rho 0=0 ∧
      (∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) ∧
      ∀ᶠ y : E in 𝓝 0, f (y-inner ℝ N y • N+rho y • N)=0 := by
  let l : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E N
  have hl (v : E) : l v=inner ℝ N v := rfl
  have hlN : l N=1 := by rw [hl,real_inner_self_eq_norm_sq,hN]; norm_num
  have hDfL : fderiv ℝ f 0=l := by ext v; exact hDf v
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E-l.smulRight N
  have hP (v : E) : P v=v-l v • N := rfl
  have hlP (v : E) : l (P v)=0 := by
    rw [hP,map_sub,map_smul,hlN,smul_eq_mul,mul_one,sub_self]
  have hPN : P N=0 := by rw [hP,hlN,one_smul,sub_self]
  let F : E → E := fun y => y+(f y-l y) • N
  have hF : ContDiffAt ℝ 3 F 0 := contDiffAt_id.add ((hf.sub l.contDiff.contDiffAt).smul contDiffAt_const)
  have hFd : HasFDerivAt F (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 := by
    have hid : (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E)=ContinuousLinearMap.id ℝ E := by ext y; rfl
    rw [hid]
    have hh := (hasFDerivAt_id (𝕜 := ℝ) (0 : E)).add
      (((hf.differentiableAt (by norm_num)).hasFDerivAt.sub l.hasFDerivAt).smul_const N)
    simpa only [F,hDfL,Pi.add_def,Pi.sub_def,Function.comp_def,id_eq,sub_self,
      ContinuousLinearMap.zero_smulRight,add_zero] using hh
  have hF0 : F 0=0 := by simp [F,hf0]
  have hlF (y : E) : l (F y)=f y := by
    simp only [F,map_add,map_smul,hlN,smul_eq_mul,mul_one]
    ring
  let G := hF.localInverse hFd (by norm_num)
  have hG0 : G 0=0 := by simpa only [G,hF0] using hF.localInverse_apply_image hFd (by norm_num)
  have hGc : ContDiffAt ℝ 3 G 0 := by simpa only [G,hF0] using hF.to_localInverse hFd (by norm_num)
  have hGd : HasFDerivAt G (ContinuousLinearMap.id ℝ E) 0 := by
    have hh := (hF.hasStrictFDerivAt' hFd (by norm_num)).to_localInverse.hasFDerivAt
    have hid : ((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E)=ContinuousLinearMap.id ℝ E := by ext y; rfl
    rw [hid] at hh
    simpa only [G,ContDiffAt.localInverse,hF0] using hh
  have hFG : ∀ᶠ y : E in 𝓝 0, F (G y)=y := by
    simpa only [G,ContDiffAt.localInverse,hF0] using
      (hF.hasStrictFDerivAt' hFd (by norm_num)).eventually_right_inverse
  let rho : E → ℝ := fun y => l (G (P y))
  have hPc : ContDiffAt ℝ 3 P 0 := P.contDiff.contDiffAt
  have hGP : ContDiffAt ℝ 3 (fun y => G (P y)) 0 := by
    have hGcP : ContDiffAt ℝ 3 G (P 0) := by simpa only [map_zero] using hGc
    exact hGcP.comp 0 hPc
  have hrho : ContDiffAt ℝ 3 rho 0 := l.contDiff.contDiffAt.comp 0 hGP
  have hGD : HasFDerivAt (fun y => G (P y)) P 0 := by
    have hh := (show HasFDerivAt G (ContinuousLinearMap.id ℝ E) (P 0) from by simpa only [map_zero] using hGd).comp 0 P.hasFDerivAt
    simpa only [Function.comp_def,ContinuousLinearMap.id_comp] using hh
  have hrhoD : fderiv ℝ rho 0=0 := by
    have hh := l.hasFDerivAt.comp 0 hGD
    change HasFDerivAt rho (l.comp P) 0 at hh
    rw [hh.fderiv]
    ext v
    exact hlP v
  refine ⟨rho,hrho,by simp only [rho,map_zero,hG0],hrhoD,?_,?_⟩
  · intro x t
    simp only [rho,map_add,map_smul,hPN,smul_zero,add_zero]
  · have ht : Tendsto P (𝓝 (0 : E)) (𝓝 (0 : E)) := by simpa only [map_zero] using P.continuous.tendsto 0
    filter_upwards [ht.eventually hFG] with y hy
    have hfzero : f (G (P y))=0 := by rw [← hlF,hy,hlP]
    have he : G (P y)=P y+rho y • N := by
      have hh := hy
      change G (P y)+(f (G (P y))-l (G (P y))) • N=P y at hh
      rw [hfzero,zero_sub,neg_smul] at hh
      have hh' : G (P y)-rho y • N=P y := by simpa only [rho,sub_eq_add_neg] using hh
      exact sub_eq_iff_eq_add.mp hh'
    rw [← hl y,← hP y,← he]
    exact hfzero

local notation "F4" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_regular_level_graph_four {N : F4} (hN : ‖N‖=1) {f : F4 → ℝ}
    (hf : ContDiffAt ℝ 3 f 0) (hf0 : f 0=0)
    (hDf : ∀ v : F4, fderiv ℝ f 0 v=inner ℝ N v) :
    ∃ rho : F4 → ℝ, ContDiffAt ℝ 3 rho 0 ∧ rho 0=0 ∧ fderiv ℝ rho 0=0 ∧
      (∀ x : F4, ∀ t : ℝ, rho (x+t • N)=rho x) ∧
      ∀ᶠ y : F4 in 𝓝 0, f (y-inner ℝ N y • N+rho y • N)=0 :=
  actual_regular_level_graph hN hf hf0 hDf

end PowerConvexity
