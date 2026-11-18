import PowerConvexity.Calculus.StrongConvexSmoothMaximum
import PowerConvexity.Calculus.QuadraticBallPotential
import Mathlib.Analysis.LocallyConvex.Separation

/-! # A genuine smooth strongly convex separator from finitely many supports

A compact convex set and a disjoint compact set are separated by an actual
globally smooth function with a positive real Hessian bound and a quadratic
lower bound. The construction uses finitely many Hahn--Banach supports and
the quantified smooth maximum. It introduces neither a solution of CMA nor
an unproved domain-approximation oracle.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_affine_support_with_margin
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    {x : E} (hx : x ∉ K) :
    ∃ (ell : E →L[ℝ] ℝ) (c : ℝ),
      (∀ y ∈ K, ell y-c ≤ -2) ∧ 0 < ell x-c := by
  obtain ⟨f,u,v,hfu,huv,hvf⟩ := geometric_hahn_banach_compact_closed
    hconv hK (convex_singleton x) isClosed_singleton (disjoint_singleton_right.mpr hx)
  let a := 2/(v-u)
  have ha : 0 < a := div_pos (by norm_num) (sub_pos.mpr huv)
  have heq : a*(v-u)=2 := by
    dsimp only [a]
    rw [div_mul_cancel₀ _ (sub_pos.mpr huv).ne']
  refine ⟨a • f,a*u+2,?_,?_⟩
  · intro y hy
    change a*f y-(a*u+2) ≤ -2
    have hm := mul_le_mul_of_nonneg_left (hfu y hy).le ha.le
    linarith
  · change 0 < a*f x-(a*u+2)
    have hh := mul_lt_mul_of_pos_left (hvf x (mem_singleton x)) ha
    nlinarith

def actualAffineSupportQuadratic (delta : ℝ) (ell : E →L[ℝ] ℝ) (c : ℝ) : E → ℝ :=
  fun x => delta*‖x‖^2+ell x-c

theorem actualAffineSupportQuadratic_contDiff (delta : ℝ)
    (ell : E →L[ℝ] ℝ) (c : ℝ) :
    ContDiff ℝ ∞ (actualAffineSupportQuadratic delta ell c) :=
  ((contDiff_const.mul (contDiff_norm_sq ℝ)).add ell.contDiff).sub contDiff_const

theorem actualAffineSupportQuadratic_realHessian (delta : ℝ)
    (ell : E →L[ℝ] ℝ) (c : ℝ) (x v w : E) :
    realHessian (actualAffineSupportQuadratic delta ell c) x v w =
      2*delta*inner ℝ v w := by
  have hl : realHessian (fun y : E => ell y) x = 0 := by
    have hd : fderiv ℝ (fun y : E => ell y) = fun _ => ell :=
      funext fun y => ell.fderiv
    unfold realHessian
    rw [hd]
    exact fderiv_const_apply ell
  unfold actualAffineSupportQuadratic
  simp only [sub_eq_add_neg]
  rw [realHessian_add_const,
    realHessian_add (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt) ell.contDiff.contDiffAt,
    realHessian_const_mul,hl]
  change delta*realHessian (fun y : E => ‖y‖^2) x v w+0 = 2*delta*inner ℝ v w
  rw [realHessian_norm_square]
  ring

theorem exists_smooth_strongly_convex_separator_of_quadratic_bound
    {K S : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hS : IsCompact S) (hKS : Disjoint K S) {delta : ℝ} (hdelta : 0 < delta)
    (hquad : ∀ x ∈ K, delta*‖x‖^2 ≤ 1) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧
      (∀ x v : E, 2*delta*‖v‖^2 ≤ realHessian F x v v) ∧
      (∀ x ∈ K, F x < 0) ∧ (∀ x ∈ S, 0 < F x) ∧
      ∀ x : E, delta*‖x‖^2-2 ≤ F x := by
  classical
  have hsep (x : S) : ∃ (ell : E →L[ℝ] ℝ) (c : ℝ),
      (∀ y ∈ K, ell y-c ≤ -2) ∧ 0 < ell x-c := by
    apply exists_affine_support_with_margin hK hconv
    exact fun hx => (Set.disjoint_left.mp hKS) hx x.property
  choose ell c hell hc using hsep
  let O : S → Set E := fun x => {y | 0 < ell x y-c x}
  have hO (x : S) : IsOpen (O x) :=
    isOpen_lt continuous_const ((ell x).continuous.sub continuous_const)
  have hcover : S ⊆ ⋃ x : S, O x := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hc ⟨y,hy⟩⟩
  obtain ⟨support,hsupport⟩ := hS.elim_finite_subcover O hO hcover
  let q : S → E → ℝ := fun x => actualAffineSupportQuadratic delta (ell x) (c x)
  let f0 : E → ℝ := actualAffineSupportQuadratic delta 0 2
  let fs : List (E → ℝ) := support.toList.map q
  let eps := 1/((fs.length : ℝ)+1)
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hlen : (fs.length : ℝ)*eps < 1 := by
    have hh : ((fs.length : ℝ)+1)*eps=1 := by
      dsimp only [eps]
      exact mul_one_div_cancel (by positivity : (fs.length : ℝ)+1 ≠ 0)
    nlinarith
  have hf0 : ContDiff ℝ ∞ f0 := actualAffineSupportQuadratic_contDiff delta 0 2
  have hfs : ∀ f ∈ fs, ContDiff ℝ ∞ f := by
    intro f hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    exact actualAffineSupportQuadratic_contDiff delta (ell i) (c i)
  have hfH (x v : E) : 2*delta*‖v‖^2 ≤ realHessian f0 x v v := by
    rw [actualAffineSupportQuadratic_realHessian,real_inner_self_eq_norm_sq]
  have hfsH : ∀ f ∈ fs, ∀ x v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v := by
    intro f hf x v
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    rw [actualAffineSupportQuadratic_realHessian,real_inner_self_eq_norm_sq]
  let F := actualFiniteSmoothMaximum eps f0 fs
  refine ⟨F,actualFiniteSmoothMaximum_contDiff_infty eps f0 fs hf0 hfs,
    actualFiniteSmoothMaximum_real_hessian_lower heps f0 fs hf0 hfs hfH hfsH,?_,?_,?_⟩
  · intro x hx
    have h0 : f0 x ≤ -1 := by
      change delta*‖x‖^2+0-2 ≤ -1
      linarith [hquad x hx]
    have hq : ∀ f ∈ fs, f x ≤ -1 := by
      intro f hf
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
      change delta*‖x‖^2+ell i x-c i ≤ -1
      linarith [hquad x hx,hell i x hx]
    have hh := actualFiniteSmoothMaximum_upper heps f0 fs x h0 hq
    change actualFiniteSmoothMaximum eps f0 fs x < 0
    linarith
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hsupport hx)
    obtain ⟨hi,hiO⟩ := mem_iUnion.mp hi
    have himem : q i ∈ fs := List.mem_map.mpr ⟨i,Finset.mem_toList.mpr hi,rfl⟩
    have hqp : 0 < q i x := by
      have hiPos : 0 < ell i x-c i := hiO
      change 0 < delta*‖x‖^2+ell i x-c i
      nlinarith [mul_nonneg hdelta.le (sq_nonneg ‖x‖)]
    exact hqp.trans_le ((actualFiniteSmoothMaximum_lower heps f0 fs x).2 (q i) himem)
  · intro x
    simpa only [f0,actualAffineSupportQuadratic,zero_apply,add_zero] using
      (actualFiniteSmoothMaximum_lower heps f0 fs x).1


theorem exists_smooth_strongly_convex_separator
    {K S : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hS : IsCompact S) (hKS : Disjoint K S) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ F : E → ℝ,
      ContDiff ℝ ∞ F ∧
      (∀ x v : E, 2*delta*‖v‖^2 ≤ realHessian F x v v) ∧
      (∀ x ∈ K, F x < 0) ∧ (∀ x ∈ S, 0 < F x) ∧
      ∀ x : E, delta*‖x‖^2-2 ≤ F x := by
  obtain ⟨L,hL⟩ := hK.isBounded.exists_norm_le
  let A := max L 0
  have hA : 0 ≤ A := le_max_right _ _
  let delta := (A^2+1)⁻¹
  have hdelta : 0 < delta := inv_pos.mpr (by positivity)
  have hdeltaeq : delta*(A^2+1)=1 := inv_mul_cancel₀ (by positivity : A^2+1 ≠ 0)
  have hquad : ∀ x ∈ K, delta*‖x‖^2 ≤ 1 := by
    intro x hx
    have hxA : ‖x‖ ≤ A := (hL x hx).trans (le_max_left _ _)
    have hsq := (sq_le_sq₀ (norm_nonneg x) hA).mpr hxA
    have hh := mul_le_mul_of_nonneg_left hsq hdelta.le
    nlinarith
  obtain ⟨F,hF⟩ := exists_smooth_strongly_convex_separator_of_quadratic_bound
    hK hconv hS hKS hdelta hquad
  exact ⟨delta,hdelta,F,hF⟩

end PowerConvexity
