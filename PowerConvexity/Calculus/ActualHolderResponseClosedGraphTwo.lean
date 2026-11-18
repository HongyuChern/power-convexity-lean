import PowerConvexity.Calculus.ActualHolderResponseLiftTwo
import Mathlib.Analysis.Normed.Operator.Banach

/-! # The same actual response is bounded once every Holder load has an actual Holder jet

The closed graph is proved through the injective value map and the already
continuous C0 response. Completeness of both actual graph spaces is used.
No density in the full Holder norm, and no assumed Schauder norm bound, is
used in this functional-analytic step.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
attribute [local instance] holderResponseJetSeminormedGroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : Set E) [CompactSpace (closure U)]

theorem actual_holder_response_closed_graph_lift_two (hU : IsOpen U) (alpha : ℝ)
    (T : C(closure U,ℝ) →L[ℝ] C(closure U,ℝ))
    (hsolve : ∀ f : actualHolderLoadSpaceTwo (closure U) ℝ alpha,
      ∃ p : actualHolderC2JetSpaceTwo U alpha,
        actualHolderC2JetSpaceTwo_value U alpha p=T (actualHolderLoadSpaceTwo_value _ _ alpha f)) :
    ∃! S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha,
      (actualHolderC2JetSpaceTwo_value U alpha).comp S=
        T.comp (actualHolderLoadSpaceTwo_value (closure U) ℝ alpha) := by
  classical
  letI : Fact (IsOpen U) := ⟨hU⟩
  let V := actualHolderLoadSpaceTwo_value (closure U) ℝ alpha
  let W := actualHolderC2JetSpaceTwo_value U alpha
  choose p hp using hsolve
  change ∀ f, W (p f)=T (V f) at hp
  have hinj := actualHolderC2JetSpaceTwo_value_injective U hU alpha
  let L : actualHolderLoadSpaceTwo (closure U) ℝ alpha →ₗ[ℝ] actualHolderC2JetSpaceTwo U alpha :=
    { toFun := p
      map_add' := by
        intro f g
        apply hinj
        change W (p (f+g))=W (p f+p g)
        rw [hp (f+g)]
        simp only [map_add,hp f,hp g]
      map_smul' := by
        intro c f
        apply hinj
        change W (p (c • f))=W (c • p f)
        rw [hp (c • f)]
        simp only [map_smul,hp f] }
  have hc : Continuous L := by
    apply LinearMap.continuous_of_seq_closed_graph (𝕜 := ℝ)
      (E := actualHolderLoadSpaceTwo (closure U) ℝ alpha)
      (F := actualHolderC2JetSpaceTwo U alpha) L
    intro f x y hfx hLy
    have hy := (W.continuous.tendsto y).comp hLy
    have hx := ((T.comp V).continuous.tendsto x).comp hfx
    have he : W ∘ (L ∘ f)=(T.comp V) ∘ f := by
      funext n
      exact hp (f n)
    rw [he] at hy
    apply hinj
    exact (tendsto_nhds_unique hy hx).trans (hp x).symm
  let S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha :=
    ⟨L,hc⟩
  have hSv : W.comp S=T.comp V := by
    apply ContinuousLinearMap.ext
    intro f
    exact hp f
  refine ⟨S,hSv,?_⟩
  intro S' hS'
  apply ContinuousLinearMap.ext
  intro f
  apply hinj
  have hl := congrArg (fun Q : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] C(closure U,ℝ) => Q f) hS'
  have hr := congrArg (fun Q : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] C(closure U,ℝ) => Q f) hSv
  exact hl.trans hr.symm

end PowerConvexity
