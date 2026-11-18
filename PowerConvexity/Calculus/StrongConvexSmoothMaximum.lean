import PowerConvexity.Calculus.ExactSmoothMaximum

/-! # Quantitative smooth maxima with a common real Hessian lower bound

The error is controlled by the number of actual finite support functions.
A common strictly positive real quadratic part is preserved by every step.
These are geometric smoothing statements, not assertions of classical CMA
solvability on the resulting sublevel domains.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

theorem smoothPositivePrimitive_nonneg (x : ℝ) : 0 ≤ smoothPositivePrimitive x := by
  by_cases hx : x ≤ 0
  · rw [smoothPositivePrimitive_zero_of_nonpos hx]
  · exact intervalIntegral.integral_nonneg_of_forall (le_of_not_ge hx)
      Real.smoothTransition.nonneg

theorem smoothPositivePrimitive_le_max (x : ℝ) :
    smoothPositivePrimitive x ≤ max x 0 := by
  by_cases hx : x ≤ 0
  · rw [smoothPositivePrimitive_zero_of_nonpos hx,max_eq_right hx]
  · have hx0 : 0 ≤ x := le_of_not_ge hx
    have hi := intervalIntegral.integral_mono_on (μ := volume) hx0
      (Real.smoothTransition.continuous.intervalIntegrable (0 : ℝ) x)
      (continuous_const.intervalIntegrable (0 : ℝ) x)
      (fun s _ => Real.smoothTransition.le_one s)
    simpa only [smoothPositivePrimitive,intervalIntegral.integral_const,sub_zero,
      smul_eq_mul,mul_one,max_eq_left hx0] using hi

theorem smoothPositivePrimitive_affine_lower (x : ℝ) :
    x-(1-smoothPositivePrimitive 1) ≤ smoothPositivePrimitive x := by
  by_cases hx : 1 ≤ x
  · rw [smoothPositivePrimitive_affine_of_one_le hx]
    linarith
  · have hx1 : x ≤ 1 := le_of_not_ge hx
    have hi := intervalIntegral.integral_mono_on (μ := volume) hx1
      (Real.smoothTransition.continuous.intervalIntegrable x 1)
      (continuous_const.intervalIntegrable x 1)
      (fun s _ => Real.smoothTransition.le_one s)
    have hib : (∫ s in x..(1 : ℝ), Real.smoothTransition s) ≤ 1-x := by
      simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_one] using hi
    have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.smoothTransition.continuous.intervalIntegrable (0 : ℝ) x)
      (Real.smoothTransition.continuous.intervalIntegrable x 1)
    change smoothPositivePrimitive x+(∫ s in x..(1 : ℝ), Real.smoothTransition s) =
      smoothPositivePrimitive 1 at ha
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exactSmoothMaximum_bounds {eps : ℝ} (heps : 0 < eps)
    (f g : E → ℝ) (x : E) :
    max (f x) (g x) ≤ exactSmoothMaximum eps f g x ∧
      exactSmoothMaximum eps f g x ≤ max (f x) (g x)+eps := by
  let k := 1-smoothPositivePrimitive 1
  let s := eps⁻¹*(f x-g x)+k
  have heq : eps*s=f x-g x+eps*k := by
    dsimp only [s]
    rw [mul_add,←mul_assoc,mul_inv_cancel₀ heps.ne',one_mul]
  have hk : k ≤ 1 := by dsimp only [k]; linarith [smoothPositivePrimitive_one_mem_Icc.1]
  have hp0 := mul_nonneg heps.le (smoothPositivePrimitive_nonneg s)
  have hpl := mul_le_mul_of_nonneg_left (smoothPositivePrimitive_affine_lower s) heps.le
  change max (f x) (g x) ≤ g x+eps*smoothPositivePrimitive s ∧
    g x+eps*smoothPositivePrimitive s ≤ max (f x) (g x)+eps
  constructor
  · apply max_le
    · change eps*(s-k) ≤ eps*smoothPositivePrimitive s at hpl
      nlinarith
    · linarith
  · by_cases hs : s ≤ 0
    · rw [smoothPositivePrimitive_zero_of_nonpos hs,mul_zero,add_zero]
      linarith [le_max_right (f x) (g x)]
    · have hp := smoothPositivePrimitive_le_max s
      rw [max_eq_left (le_of_not_ge hs)] at hp
      have hm := mul_le_mul_of_nonneg_left hp heps.le
      have hmk := mul_le_mul_of_nonneg_left hk heps.le
      nlinarith [le_max_left (f x) (g x)]

theorem exactSmoothMaximum_contDiff_infty {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (eps : ℝ) :
    ContDiff ℝ ∞ (exactSmoothMaximum eps f g) := by
  exact hg.add (contDiff_const.mul (smoothPositivePrimitive_contDiff.comp
    ((contDiff_const.mul (hf.sub hg)).add contDiff_const)))

theorem exactSmoothMaximum_real_hessian_lower {eps m : ℝ} (heps : 0 < eps)
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hfH : ∀ v : E, m*‖v‖^2 ≤ realHessian f x v v)
    (hgH : ∀ v : E, m*‖v‖^2 ≤ realHessian g x v v) :
    ∀ v : E, m*‖v‖^2 ≤ realHessian (exactSmoothMaximum eps f g) x v v := by
  intro v
  let s := eps⁻¹*(f x-g x)+(1-smoothPositivePrimitive 1)
  have ha0 := Real.smoothTransition.nonneg s
  have ha1 := Real.smoothTransition.le_one s
  have hb0 : 0 ≤ eps⁻¹*deriv Real.smoothTransition s :=
    mul_nonneg (inv_nonneg.mpr heps.le) Real.smoothTransition.monotone.deriv_nonneg
  have hfirst := mul_le_mul_of_nonneg_left (hfH v) ha0
  have hsecond := mul_le_mul_of_nonneg_left (hgH v) (sub_nonneg.mpr ha1)
  have hthird := mul_nonneg hb0 (sq_nonneg (fderiv ℝ f x v-fderiv ℝ g x v))
  rw [realHessian_exactSmoothMaximum heps hf hg]
  change m*‖v‖^2 ≤ Real.smoothTransition s*realHessian f x v v+
    (1-Real.smoothTransition s)*realHessian g x v v+
    (eps⁻¹*deriv Real.smoothTransition s)*
      (fderiv ℝ f x v-fderiv ℝ g x v)*(fderiv ℝ f x v-fderiv ℝ g x v)
  nlinarith

def actualFiniteSmoothMaximum (eps : ℝ) (f0 : E → ℝ) : List (E → ℝ) → E → ℝ
  | [] => f0
  | g::gs => exactSmoothMaximum eps g (actualFiniteSmoothMaximum eps f0 gs)

theorem actualFiniteSmoothMaximum_lower {eps : ℝ} (heps : 0 < eps)
    (f0 : E → ℝ) (fs : List (E → ℝ)) (x : E) :
    f0 x ≤ actualFiniteSmoothMaximum eps f0 fs x ∧
      ∀ f ∈ fs, f x ≤ actualFiniteSmoothMaximum eps f0 fs x := by
  induction fs with
  | nil => simp only [actualFiniteSmoothMaximum,List.not_mem_nil,le_refl,false_implies,
      forall_const,and_self]
  | cons g gs ih =>
    have hb := (exactSmoothMaximum_bounds heps g (actualFiniteSmoothMaximum eps f0 gs) x).1
    have htail := (le_max_right (g x) (actualFiniteSmoothMaximum eps f0 gs x)).trans hb
    refine ⟨ih.1.trans htail,?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hfs
    · exact (le_max_left _ _).trans hb
    · exact (ih.2 f hfs).trans htail

theorem actualFiniteSmoothMaximum_upper {eps B : ℝ} (heps : 0 < eps)
    (f0 : E → ℝ) (fs : List (E → ℝ)) (x : E)
    (hf0 : f0 x ≤ B) (hfs : ∀ f ∈ fs, f x ≤ B) :
    actualFiniteSmoothMaximum eps f0 fs x ≤ B+(fs.length : ℝ)*eps := by
  induction fs with
  | nil => simpa only [actualFiniteSmoothMaximum,List.length_nil,Nat.cast_zero,zero_mul,add_zero]
      using hf0
  | cons g gs ih =>
    have ht := ih (fun f hf => hfs f (List.mem_cons_of_mem g hf))
    have hn : 0 ≤ (gs.length : ℝ)*eps := mul_nonneg (Nat.cast_nonneg _) heps.le
    have hg : g x ≤ B+(gs.length : ℝ)*eps := (hfs g (List.mem_cons_self)).trans (by linarith)
    have hm := (exactSmoothMaximum_bounds heps g (actualFiniteSmoothMaximum eps f0 gs) x).2
    have hb := max_le hg ht
    simp only [actualFiniteSmoothMaximum,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

theorem actualFiniteSmoothMaximum_contDiff_infty (eps : ℝ)
    (f0 : E → ℝ) (fs : List (E → ℝ)) (hf0 : ContDiff ℝ ∞ f0)
    (hfs : ∀ f ∈ fs, ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (actualFiniteSmoothMaximum eps f0 fs) := by
  induction fs with
  | nil => exact hf0
  | cons g gs ih =>
    exact exactSmoothMaximum_contDiff_infty (hfs g List.mem_cons_self)
      (ih (fun f hf => hfs f (List.mem_cons_of_mem g hf))) eps

theorem actualFiniteSmoothMaximum_real_hessian_lower {eps m : ℝ} (heps : 0 < eps)
    (f0 : E → ℝ) (fs : List (E → ℝ)) (hf0 : ContDiff ℝ ∞ f0)
    (hfs : ∀ f ∈ fs, ContDiff ℝ ∞ f)
    (hfH : ∀ x v : E, m*‖v‖^2 ≤ realHessian f0 x v v)
    (hfsH : ∀ f ∈ fs, ∀ x v : E, m*‖v‖^2 ≤ realHessian f x v v) :
    ∀ x v : E, m*‖v‖^2 ≤ realHessian (actualFiniteSmoothMaximum eps f0 fs) x v v := by
  induction fs with
  | nil => exact hfH
  | cons g gs ih =>
    have htail : ContDiff ℝ ∞ (actualFiniteSmoothMaximum eps f0 gs) :=
      actualFiniteSmoothMaximum_contDiff_infty eps f0 gs hf0
        (fun f hf => hfs f (List.mem_cons_of_mem g hf))
    have htH := ih (fun f hf => hfs f (List.mem_cons_of_mem g hf))
      (fun f hf => hfsH f (List.mem_cons_of_mem g hf))
    intro x v
    exact exactSmoothMaximum_real_hessian_lower heps
      (((contDiff_infty.mp (hfs g List.mem_cons_self)) 2).contDiffAt)
      (((contDiff_infty.mp htail) 2).contDiffAt)
      (hfsH g List.mem_cons_self x) (htH x) v

end PowerConvexity
