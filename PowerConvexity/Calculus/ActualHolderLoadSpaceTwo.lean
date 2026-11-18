import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Prod

/-! # A complete space of actual Holder loads

The norm records the continuous function and its bounded actual difference
quotient.  The compatibility equations define a closed linear subspace of a
product of Banach spaces.  In particular, this is not the incomplete space of
C1 extensions equipped only with the uniform norm.  No PDE inverse estimate is
part of this construction.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Metric
open scoped Topology ENNReal
namespace PowerConvexity
variable (K F : Type*) [MetricSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def actualHolderLoadSpaceTwo (alpha : ℝ) :
    Submodule ℝ (C(K,F) × lp (fun _ : K × K => F) ∞) where
  carrier := {z | (∀ x y : K, (dist x y)^alpha • z.2 (x,y)=z.1 x-z.1 y) ∧
    ∀ x : K, z.2 (x,x)=0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro x y
      change (dist x y)^alpha • (f.2 (x,y)+g.2 (x,y))=
        (f.1 x+g.1 x)-(f.1 y+g.1 y)
      rw [smul_add,hf.1 x y,hg.1 x y]
      abel
    · intro x
      change f.2 (x,x)+g.2 (x,x)=0
      rw [hf.2 x,hg.2 x,add_zero]
  smul_mem' := by
    intro c f hf
    constructor
    · intro x y
      change (dist x y)^alpha • (c • f.2 (x,y))=c • f.1 x-c • f.1 y
      rw [smul_comm,hf.1 x y,smul_sub]
    · intro x
      change c • f.2 (x,x)=0
      rw [hf.2 x,smul_zero]

theorem actualHolderLoadSpaceTwo_isClosed (alpha : ℝ) :
    IsClosed (actualHolderLoadSpaceTwo K F alpha :
      Set (C(K,F) × lp (fun _ : K × K => F) ∞)) := by
  apply isClosed_of_closure_subset
  intro z hz
  constructor
  · intro x y
    have he : Continuous (fun z : C(K,F) × lp (fun _ : K × K => F) ∞ => z.2 (x,y)) :=
      (lp.evalCLM ℝ (fun _ : K × K => F) ∞ (x,y)).continuous.comp continuous_snd
    have hclosed := isClosed_eq (he.const_smul ((dist x y)^alpha))
      (((continuous_eval_const x).comp continuous_fst).sub
        ((continuous_eval_const y).comp continuous_fst))
    exact closure_minimal (fun p hp => hp.1 x y) hclosed hz
  · intro x
    have he : Continuous (fun z : C(K,F) × lp (fun _ : K × K => F) ∞ => z.2 (x,x)) :=
      (lp.evalCLM ℝ (fun _ : K × K => F) ∞ (x,x)).continuous.comp continuous_snd
    have hclosed := isClosed_eq he
      (continuous_const : Continuous (fun _ : C(K,F) × lp (fun _ : K × K => F) ∞ => (0 : F)))
    exact closure_minimal (fun p hp => hp.2 x) hclosed hz

instance actualHolderLoadSpaceTwo_completeSpace [CompleteSpace F] (alpha : ℝ) :
    CompleteSpace (actualHolderLoadSpaceTwo K F alpha) :=
  (actualHolderLoadSpaceTwo_isClosed K F alpha).completeSpace_coe

def actualHolderLoadSpaceTwo_value (alpha : ℝ) :
    actualHolderLoadSpaceTwo K F alpha →L[ℝ] C(K,F) :=
  (ContinuousLinearMap.fst ℝ C(K,F) (lp (fun _ : K × K => F) ∞)).comp
    (actualHolderLoadSpaceTwo K F alpha).subtypeL

theorem actualHolderLoadSpaceTwo_value_norm_le (alpha : ℝ)
    (f : actualHolderLoadSpaceTwo K F alpha) :
    ‖actualHolderLoadSpaceTwo_value K F alpha f‖ ≤ ‖f‖ :=
  norm_fst_le f.1

theorem actualHolderLoadSpaceTwo_holder_bound (alpha : ℝ)
    (f : actualHolderLoadSpaceTwo K F alpha) (x y : K) :
    ‖actualHolderLoadSpaceTwo_value K F alpha f x-
      actualHolderLoadSpaceTwo_value K F alpha f y‖ ≤ ‖f‖*(dist x y)^alpha := by
  have hd : 0 ≤ (dist x y)^alpha := Real.rpow_nonneg dist_nonneg _
  change ‖f.1.1 x-f.1.1 y‖ ≤ ‖f‖*(dist x y)^alpha
  rw [← f.2.1 x y,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
  calc
    (dist x y)^alpha*‖f.1.2 (x,y)‖ ≤ (dist x y)^alpha*‖f.1.2‖ :=
      mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _) hd
    _ ≤ (dist x y)^alpha*‖f‖ :=
      mul_le_mul_of_nonneg_left (norm_snd_le f.1) hd
    _ = _ := mul_comm _ _

theorem actualHolderLoadSpaceTwo_value_injective (alpha : ℝ) :
    Function.Injective (actualHolderLoadSpaceTwo_value K F alpha) := by
  intro f g hfg
  have hv : f.1.1=g.1.1 := hfg
  apply Subtype.ext
  apply Prod.ext hv
  apply lp.ext
  funext p
  rcases p with ⟨x,y⟩
  by_cases hxy : x=y
  · subst y
    exact (f.2.2 x).trans (g.2.2 x).symm
  · apply smul_right_injective F (Real.rpow_pos_of_pos (dist_pos.mpr hxy) alpha).ne'
    exact (f.2.1 x y).trans ((congrArg (fun k : C(K,F) => k x-k y) hv).trans
      (g.2.1 x y).symm)

theorem actualHolderLoadSpaceTwo_lift (alpha : ℝ) (f : C(K,F)) {M : ℝ}
    (hM : 0 ≤ M) (hholder : ∀ x y : K, ‖f x-f y‖ ≤ M*(dist x y)^alpha) :
    ∃! H : actualHolderLoadSpaceTwo K F alpha,
      actualHolderLoadSpaceTwo_value K F alpha H=f ∧ ‖H‖ ≤ max ‖f‖ M := by
  let q : K × K → F := fun p => ((dist p.1 p.2)^alpha)⁻¹ • (f p.1-f p.2)
  have hq (p : K × K) : ‖q p‖ ≤ M := by
    rcases p with ⟨x,y⟩
    by_cases hxy : x=y
    · subst y
      simpa only [q,sub_self,smul_zero,norm_zero] using hM
    · have hd : 0 < (dist x y)^alpha := Real.rpow_pos_of_pos (dist_pos.mpr hxy) alpha
      rw [show q (x,y)=((dist x y)^alpha)⁻¹ • (f x-f y) from rfl,
        norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)]
      calc
        ((dist x y)^alpha)⁻¹*‖f x-f y‖ ≤ ((dist x y)^alpha)⁻¹*(M*(dist x y)^alpha) :=
          mul_le_mul_of_nonneg_left (hholder x y) (inv_nonneg.mpr hd.le)
        _ = M := by field_simp
  let Q : lp (fun _ : K × K => F) ∞ :=
    ⟨q,memℓp_infty ⟨M,by rintro _ ⟨p,rfl⟩; exact hq p⟩⟩
  have hQ : ‖Q‖ ≤ M := lp.norm_le_of_forall_le hM hq
  have hmem : (f,Q) ∈ actualHolderLoadSpaceTwo K F alpha := by
    constructor
    · intro x y
      change (dist x y)^alpha • (((dist x y)^alpha)⁻¹ • (f x-f y))=f x-f y
      by_cases hxy : x=y
      · subst y
        simp only [sub_self,smul_zero]
      · exact smul_inv_smul₀ (Real.rpow_pos_of_pos (dist_pos.mpr hxy) alpha).ne' _
    · intro x
      change ((dist x x)^alpha)⁻¹ • (f x-f x)=0
      simp only [sub_self,smul_zero]
  let H : actualHolderLoadSpaceTwo K F alpha := ⟨(f,Q),hmem⟩
  refine ⟨H,⟨rfl,?_⟩,?_⟩
  · change max ‖f‖ ‖Q‖ ≤ max ‖f‖ M
    exact max_le_max le_rfl hQ
  · intro H' hH'
    exact actualHolderLoadSpaceTwo_value_injective K F alpha hH'.1

end PowerConvexity
