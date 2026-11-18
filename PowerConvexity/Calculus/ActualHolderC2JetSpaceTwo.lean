import PowerConvexity.Calculus.ActualClosureFunctionExtensionTwo
import Mathlib.Topology.Sequences
import PowerConvexity.Calculus.ActualThirdJetNormTwo

/-! # The complete space of actual zero-boundary C2 Holder jets

The first and second derivatives are genuine interior Fréchet derivatives.
Their continuous closure values, and the actual Holder difference quotient of
the Hessian, are part of the norm. Closedness is proved by the uniform limit
theorem for derivatives; no ambient differentiability at the boundary is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : Set E) [CompactSpace (closure U)]

abbrev ActualHolderC2RawTwo (alpha : ℝ) :=
  C(closure U,ℝ) × (C(closure U,E →L[ℝ] ℝ) ×
    actualHolderLoadSpaceTwo (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha)

def actualHolderC2JetSpaceTwo (alpha : ℝ) : Submodule ℝ (ActualHolderC2RawTwo U alpha) where
  carrier := {p |
    (∀ x ∈ U, HasFDerivAt (actualClosureExtensionTwo U p.1)
      (actualClosureExtensionTwo U p.2.1 x) x) ∧
    (∀ x ∈ U, HasFDerivAt (actualClosureExtensionTwo U p.2.1)
      (actualClosureExtensionTwo U
        (actualHolderLoadSpaceTwo_value _ _ alpha p.2.2) x) x) ∧
    ∀ x ∈ frontier U, actualClosureExtensionTwo U p.1 x=0}
  zero_mem' := by
    constructor
    · intro x hx
      simpa only [Prod.fst_zero,Prod.snd_zero,actualClosureExtensionTwo_zero,Pi.zero_apply]
        using hasFDerivAt_zero (𝕜 := ℝ) (F := ℝ) x
    constructor
    · intro x hx
      simpa only [Prod.fst_zero,Prod.snd_zero,map_zero,actualClosureExtensionTwo_zero,Pi.zero_apply]
        using hasFDerivAt_zero (𝕜 := ℝ) (F := E →L[ℝ] ℝ) x
    · intro x hx
      simp only [Prod.fst_zero,actualClosureExtensionTwo_zero,Pi.zero_apply]
  add_mem' := by
    intro p q hp hq
    constructor
    · intro x hx
      simpa only [Prod.fst_add,Prod.snd_add,actualClosureExtensionTwo_add,Pi.add_apply]
        using (hp.1 x hx).add (hq.1 x hx)
    constructor
    · intro x hx
      simpa only [Prod.fst_add,Prod.snd_add,map_add,actualClosureExtensionTwo_add,Pi.add_apply]
        using (hp.2.1 x hx).add (hq.2.1 x hx)
    · intro x hx
      simpa only [Prod.fst_add,actualClosureExtensionTwo_add,Pi.add_apply,hp.2.2 x hx,hq.2.2 x hx,add_zero]
  smul_mem' := by
    intro c p hp
    constructor
    · intro x hx
      change HasFDerivAt (actualClosureExtensionTwo U (c • p.1))
        (actualClosureExtensionTwo U (c • p.2.1) x) x
      simpa only [actualClosureExtensionTwo_smul,Pi.smul_apply]
        using (hp.1 x hx).const_smul c
    constructor
    · intro x hx
      change HasFDerivAt (actualClosureExtensionTwo U (c • p.2.1))
        (actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha (c • p.2.2)) x) x
      have he : actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha (c • p.2.2))=
          c • actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha p.2.2) := by
        rw [map_smul]
        exact actualClosureExtensionTwo_smul (F := E →L[ℝ] E →L[ℝ] ℝ) U c
          (actualHolderLoadSpaceTwo_value (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha p.2.2)
      rw [actualClosureExtensionTwo_smul,he]
      exact (hp.2.1 x hx).const_smul c
    · intro x hx
      change actualClosureExtensionTwo U (c • p.1) x=0
      simp only [actualClosureExtensionTwo_smul,Pi.smul_apply,hp.2.2 x hx,smul_zero]

theorem actualHolderC2JetSpaceTwo_isClosed (hU : IsOpen U) (alpha : ℝ) :
    IsClosed (actualHolderC2JetSpaceTwo U alpha : Set (ActualHolderC2RawTwo U alpha)) := by
  letI : FirstCountableTopology C(closure U,ℝ) := inferInstance
  letI : FirstCountableTopology C(closure U,E →L[ℝ] ℝ) := inferInstance
  letI : FirstCountableTopology (actualHolderLoadSpaceTwo (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha) := inferInstance
  letI : FirstCountableTopology (C(closure U,E →L[ℝ] ℝ) ×
    actualHolderLoadSpaceTwo (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha) := inferInstance
  apply IsSeqClosed.isClosed
  intro p q hp hpq
  have hv := actualClosureExtensionTwo_tendstoUniformly U hpq.fst_nhds
  have hD := actualClosureExtensionTwo_tendstoUniformly U hpq.snd_nhds.fst_nhds
  have hH := actualClosureExtensionTwo_tendstoUniformly U
    (((actualHolderLoadSpaceTwo_value (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha).continuous.tendsto _).comp
      hpq.snd_nhds.snd_nhds)
  constructor
  · intro x hx
    exact hasFDerivAt_of_tendstoUniformlyOn hU hD.tendstoUniformlyOn
      (fun n y hy => (hp n).1 y hy) (fun y hy => hv.tendsto_at y) hx
  constructor
  · intro x hx
    exact hasFDerivAt_of_tendstoUniformlyOn hU hH.tendstoUniformlyOn
      (fun n y hy => (hp n).2.1 y hy) (fun y hy => hD.tendsto_at y) hx
  · intro x hx
    exact tendsto_nhds_unique (hv.tendsto_at x)
      (by simpa only [funext (fun n => (hp n).2.2 x hx)] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

instance actualHolderC2JetSpaceTwo_completeSpace [hU : Fact (IsOpen U)] (alpha : ℝ) :
    CompleteSpace (actualHolderC2JetSpaceTwo U alpha) :=
  (actualHolderC2JetSpaceTwo_isClosed U hU.out alpha).completeSpace_coe

def actualHolderC2JetSpaceTwo_value (alpha : ℝ) :
    actualHolderC2JetSpaceTwo U alpha →L[ℝ] C(closure U,ℝ) :=
  (ContinuousLinearMap.fst ℝ C(closure U,ℝ)
    (C(closure U,E →L[ℝ] ℝ) × actualHolderLoadSpaceTwo (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha)).comp
    (actualHolderC2JetSpaceTwo U alpha).subtypeL

def actualHolderC2JetSpaceTwo_gradient (alpha : ℝ) :
    actualHolderC2JetSpaceTwo U alpha →L[ℝ] C(closure U,E →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.fst ℝ C(closure U,E →L[ℝ] ℝ)
    (actualHolderLoadSpaceTwo (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha)).comp
    (ContinuousLinearMap.snd ℝ C(closure U,ℝ)
      (C(closure U,E →L[ℝ] ℝ) × actualHolderLoadSpaceTwo (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha))).comp
    (actualHolderC2JetSpaceTwo U alpha).subtypeL

def actualHolderC2JetSpaceTwo_hessian (alpha : ℝ) :
    actualHolderC2JetSpaceTwo U alpha →L[ℝ]
      actualHolderLoadSpaceTwo (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha :=
  ((ContinuousLinearMap.snd ℝ C(closure U,E →L[ℝ] ℝ)
    (actualHolderLoadSpaceTwo (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha)).comp
    (ContinuousLinearMap.snd ℝ C(closure U,ℝ)
      (C(closure U,E →L[ℝ] ℝ) × actualHolderLoadSpaceTwo (closure U) (E →L[ℝ] E →L[ℝ] ℝ) alpha))).comp
    (actualHolderC2JetSpaceTwo U alpha).subtypeL

end PowerConvexity
