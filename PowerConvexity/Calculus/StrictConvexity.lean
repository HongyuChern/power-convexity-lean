import PowerConvexity.Calculus.ModifiedSchur
import CHS.Calculus.HessianQuadraticForm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap

/-!
# From positive real Hessians to the public strict-convexity predicate

`StrictConvexOn ℝ U f` has its usual strict chord-inequality meaning.  We prove
the implication from positive real Hessians, without asserting the false
converse for general C² functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology BigOperators ComplexOrder

namespace PowerConvexity

open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem deriv2_comp_lineMap {u : E → ℝ} (x y : E) (t : ℝ)
    (hu : ContDiffAt ℝ 2 u (AffineMap.lineMap x y t)) :
    deriv (deriv (fun s : ℝ => u (AffineMap.lineMap x y s))) t =
      realHessian u (AffineMap.lineMap x y t) (y - x) (y - x) := by
  let γ : ℝ → E := AffineMap.lineMap x y
  have hγ (s : ℝ) : HasDerivAt γ (y - x) s := AffineMap.hasDerivAt_lineMap
  have hnear : ∀ᶠ z in 𝓝 (γ t), ContDiffAt ℝ 1 u z :=
    (hu.of_le (m := 1) (by norm_num)).eventually (by simp)
  have heq : deriv (fun s : ℝ => u (γ s)) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ u (γ s) (y - x)) := by
    filter_upwards [(hγ t).continuousAt.eventually hnear] with s hs
    exact (((hs.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt s (hγ s)).deriv
  have hdf : DifferentiableAt ℝ (fderiv ℝ u) (γ t) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD := hdf.hasFDerivAt.comp_hasDerivAt t (hγ t)
  have hEval := hD.clm_apply (hasDerivAt_const t (y - x))
  change deriv (deriv (fun s : ℝ => u (γ s))) t = _
  rw [heq.deriv_eq]
  simpa only [realHessian, map_zero, add_zero, Function.comp_apply, γ] using hEval.deriv

theorem strictConvexOn_of_realHessian_pos {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hu : ContDiffOn ℝ 2 u U)
    (hH : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < realHessian u x v v) :
    StrictConvexOn ℝ U u := by
  refine ⟨hconv, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let γ : ℝ → E := AffineMap.lineMap x y
  let g : ℝ → ℝ := fun t => u (γ t)
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ U :=
    hconv.segment_subset hx hy (lineMap_mem_segment ℝ x y ht)
  have hγ : Continuous γ := AffineMap.lineMap_continuous
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) :=
    hu.continuousOn.comp hγ.continuousOn hmem
  have hstrict : StrictConvexOn ℝ (Icc (0 : ℝ) 1) g := by
    apply strictConvexOn_of_deriv2_pos' (convex_Icc _ _) hg
    intro t ht
    change 0 < deriv (deriv (fun s : ℝ => u (AffineMap.lineMap x y s))) t
    rw [deriv2_comp_lineMap x y t (hu.contDiffAt (hU.mem_nhds (hmem t ht)))]
    exact hH (γ t) (hmem t ht) (y - x) (sub_ne_zero.mpr hxy.symm)
  have h := hstrict.2 (x := 0) (by constructor <;> norm_num)
    (y := 1) (by constructor <;> norm_num) (by norm_num) ha hb hab
  have hab' : 1 - b = a := by linarith
  simpa [g, γ, AffineMap.lineMap_apply_module, smul_eq_mul, hab'] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem realHessian_pos_of_basis_block {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (e : Module.Basis (ι ⊕ ι) ℝ E)
    (hH : (realBlockHessian (fun i => e (.inl i)) (fun i => e (.inr i)) u x).PosDef)
    (v : E) (hv : v ≠ 0) : 0 < realHessian u x v v := by
  let z : ι ⊕ ι → ℝ := fun i => e.repr v i
  have hz : z ≠ 0 := by
    intro h
    apply hv
    apply e.repr.injective
    rw [map_zero]
    ext i
    exact congrFun h i
  have hp := hH.dotProduct_mulVec_pos hz
  rw [star_trivial, ← realHessian_sum_directions_quadratic hu] at hp
  have he : (∑ i, z i • Sum.elim (fun i => e (.inl i)) (fun i => e (.inr i)) i) = v := by
    convert e.sum_repr v using 1
    apply Finset.sum_congr rfl
    intro i _
    cases i <;> rfl
  simpa only [he] using hp

/-- The global bridge to the main theorem's public conclusion.  The missing
PDE input is explicitly the positive modified Schur matrix at every point. -/
theorem strictConvexOn_power_of_modifiedSchur {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hu : ContDiffOn ℝ 2 u U)
    (e : Module.Basis (ι ⊕ ι) ℝ E) (hneg : ∀ x ∈ U, u x < 0)
    (hA : ∀ x ∈ U,
      (complexHessian (fun i => e (.inl i)) (fun i => e (.inr i)) u x).PosDef)
    (hM : ∀ x ∈ U,
      (modifiedSchur (fun i => e (.inl i)) (fun i => e (.inr i)) u x).PosDef) :
    StrictConvexOn ℝ U (powerTransform u) := by
  apply strictConvexOn_of_realHessian_pos hU hconv (powerTransform_contDiffOn hu hneg)
  intro x hx v hv
  have hu2 := hu.contDiffAt (hU.mem_nhds hx)
  have hblock := (realHessian_power_posDef_iff_modifiedSchur hu2 (hneg x hx)
    (fun i => e (.inl i)) (fun i => e (.inr i)) (hA x hx)).mpr (hM x hx)
  exact realHessian_pos_of_basis_block (powerTransform_contDiffAt hu2 (hneg x hx)) e hblock v hv

end PowerConvexity
