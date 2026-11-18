import PowerConvexity.Calculus.ActualHolderLoadSpaceTwo
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Actual bounded bilinear operations on the complete Holder load spaces

The output is identified pointwise with the supplied continuous bilinear
operation.  The actual difference quotient gives the norm bound, including
the factor two in the Holder seminorm.  This is the Banach-space operation
needed for the two-dimensional determinant, without any PDE solvability
assumption.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Metric
open scoped ENNReal
namespace PowerConvexity
variable {K F G H : Type*} [MetricSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

local instance actualHolderBilinearLoadSeminormed (alpha : ℝ) :
    SeminormedAddCommGroup (actualHolderLoadSpaceTwo K F alpha) :=
  (inferInstance : NormedAddCommGroup (actualHolderLoadSpaceTwo K F alpha)).toSeminormedAddCommGroup

theorem actualHolderLoadSpaceTwo_bilinear_lift (alpha : ℝ)
    (B : F →L[ℝ] G →L[ℝ] H)
    (f : actualHolderLoadSpaceTwo K F alpha)
    (g : actualHolderLoadSpaceTwo K G alpha) :
    ∃! h : actualHolderLoadSpaceTwo K H alpha,
      (∀ x : K, actualHolderLoadSpaceTwo_value K H alpha h x =
        B (actualHolderLoadSpaceTwo_value K F alpha f x)
          (actualHolderLoadSpaceTwo_value K G alpha g x)) ∧
      ‖h‖ ≤ (2*‖B‖)*‖f‖*‖g‖ := by
  let fv := actualHolderLoadSpaceTwo_value K F alpha f
  let gv := actualHolderLoadSpaceTwo_value K G alpha g
  let hv : C(K,H) := ⟨fun x => B (fv x) (gv x),
    B.isBoundedBilinearMap.continuous.comp (fv.continuous.prodMk gv.continuous)⟩
  have hf (x : K) : ‖fv x‖ ≤ ‖f‖ :=
    (fv.norm_coe_le_norm x).trans (actualHolderLoadSpaceTwo_value_norm_le K F alpha f)
  have hg (x : K) : ‖gv x‖ ≤ ‖g‖ :=
    (gv.norm_coe_le_norm x).trans (actualHolderLoadSpaceTwo_value_norm_le K G alpha g)
  let M := (2*‖B‖)*‖f‖*‖g‖
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hhv : ‖hv‖ ≤ M := by
    apply (ContinuousMap.norm_le hv hM).mpr
    intro x
    have hb := B.le_of_opNorm₂_le_of_le (le_refl ‖B‖) (hf x) (hg x)
    change ‖B (fv x) (gv x)‖ ≤ M
    change ‖B (fv x) (gv x)‖ ≤ (2*‖B‖)*‖f‖*‖g‖
    have hn : 0 ≤ ‖B‖*‖f‖*‖g‖ := by positivity
    nlinarith
  have hholder (x y : K) : ‖hv x-hv y‖ ≤ M*(dist x y)^alpha := by
    have he : hv x-hv y = B (fv x-fv y) (gv x)+B (fv y) (gv x-gv y) := by
      change B (fv x) (gv x)-B (fv y) (gv y) = _
      simp only [map_sub,ContinuousLinearMap.sub_apply]
      abel
    have hfd := actualHolderLoadSpaceTwo_holder_bound K F alpha f x y
    have hgd := actualHolderLoadSpaceTwo_holder_bound K G alpha g x y
    have hb1 := B.le_of_opNorm₂_le_of_le (le_refl ‖B‖) hfd (hg x)
    have hb2 := B.le_of_opNorm₂_le_of_le (le_refl ‖B‖) (hf y) hgd
    rw [he]
    calc
      ‖B (fv x-fv y) (gv x)+B (fv y) (gv x-gv y)‖ ≤
          ‖B (fv x-fv y) (gv x)‖+‖B (fv y) (gv x-gv y)‖ := norm_add_le _ _
      _ ≤ ‖B‖*(‖f‖*(dist x y)^alpha)*‖g‖+
          ‖B‖*‖f‖*(‖g‖*(dist x y)^alpha) := add_le_add hb1 hb2
      _ = M*(dist x y)^alpha := by dsimp [M]; ring
  obtain ⟨h,hh,_⟩ := actualHolderLoadSpaceTwo_lift K H alpha hv hM hholder
  refine ⟨h,⟨?_,hh.2.trans (max_le hhv le_rfl)⟩,?_⟩
  · intro x
    exact congrArg (fun z : C(K,H) => z x) hh.1
  · intro h' hh'
    apply actualHolderLoadSpaceTwo_value_injective K H alpha
    apply ContinuousMap.ext
    intro x
    exact (hh'.1 x).trans (congrArg (fun z : C(K,H) => z x) hh.1).symm

def actualHolderLoadBilinearValueTwo (alpha : ℝ)
    (B : F →L[ℝ] G →L[ℝ] H)
    (f : actualHolderLoadSpaceTwo K F alpha)
    (g : actualHolderLoadSpaceTwo K G alpha) : actualHolderLoadSpaceTwo K H alpha :=
  (actualHolderLoadSpaceTwo_bilinear_lift alpha B f g).exists.choose

theorem actualHolderLoadBilinearValueTwo_apply (alpha : ℝ)
    (B : F →L[ℝ] G →L[ℝ] H)
    (f : actualHolderLoadSpaceTwo K F alpha)
    (g : actualHolderLoadSpaceTwo K G alpha) (x : K) :
    actualHolderLoadSpaceTwo_value K H alpha (actualHolderLoadBilinearValueTwo alpha B f g) x =
      B (actualHolderLoadSpaceTwo_value K F alpha f x)
        (actualHolderLoadSpaceTwo_value K G alpha g x) :=
  (actualHolderLoadSpaceTwo_bilinear_lift alpha B f g).exists.choose_spec.1 x

theorem actualHolderLoadBilinearValueTwo_norm_le (alpha : ℝ)
    (B : F →L[ℝ] G →L[ℝ] H)
    (f : actualHolderLoadSpaceTwo K F alpha)
    (g : actualHolderLoadSpaceTwo K G alpha) :
    ‖actualHolderLoadBilinearValueTwo alpha B f g‖ ≤ (2*‖B‖)*‖f‖*‖g‖ :=
  (actualHolderLoadSpaceTwo_bilinear_lift alpha B f g).exists.choose_spec.2

def actualHolderLoadBilinearTwo (alpha : ℝ) (B : F →L[ℝ] G →L[ℝ] H) :
    actualHolderLoadSpaceTwo K F alpha →L[ℝ]
      actualHolderLoadSpaceTwo K G alpha →L[ℝ] actualHolderLoadSpaceTwo K H alpha := by
  let b : actualHolderLoadSpaceTwo K F alpha →ₗ[ℝ]
      actualHolderLoadSpaceTwo K G alpha →ₗ[ℝ] actualHolderLoadSpaceTwo K H alpha :=
    LinearMap.mk₂ ℝ (actualHolderLoadBilinearValueTwo alpha B)
      (by
        intro f g h
        apply actualHolderLoadSpaceTwo_value_injective K H alpha
        apply ContinuousMap.ext
        intro x
        simp only [map_add,ContinuousMap.add_apply,actualHolderLoadBilinearValueTwo_apply,
          ContinuousLinearMap.add_apply])
      (by
        intro c f g
        apply actualHolderLoadSpaceTwo_value_injective K H alpha
        apply ContinuousMap.ext
        intro x
        simp only [map_smul,ContinuousMap.smul_apply,actualHolderLoadBilinearValueTwo_apply,
          ContinuousLinearMap.smul_apply])
      (by
        intro f g h
        apply actualHolderLoadSpaceTwo_value_injective K H alpha
        apply ContinuousMap.ext
        intro x
        simp only [map_add,ContinuousMap.add_apply,actualHolderLoadBilinearValueTwo_apply])
      (by
        intro c f g
        apply actualHolderLoadSpaceTwo_value_injective K H alpha
        apply ContinuousMap.ext
        intro x
        simp only [map_smul,ContinuousMap.smul_apply,actualHolderLoadBilinearValueTwo_apply])
  exact b.mkContinuous₂ (2*‖B‖) (actualHolderLoadBilinearValueTwo_norm_le alpha B)

theorem actualHolderLoadBilinearTwo_apply (alpha : ℝ)
    (B : F →L[ℝ] G →L[ℝ] H)
    (f : actualHolderLoadSpaceTwo K F alpha)
    (g : actualHolderLoadSpaceTwo K G alpha) (x : K) :
    actualHolderLoadSpaceTwo_value K H alpha (actualHolderLoadBilinearTwo alpha B f g) x =
      B (actualHolderLoadSpaceTwo_value K F alpha f x)
        (actualHolderLoadSpaceTwo_value K G alpha g x) :=
  actualHolderLoadBilinearValueTwo_apply alpha B f g x

end PowerConvexity
