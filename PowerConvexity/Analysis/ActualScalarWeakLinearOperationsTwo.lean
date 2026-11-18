import PowerConvexity.Analysis.ActualScalarWeakLocalizationTwo

/-! # Linear operations on the actual scalar weak equation.
Every conclusion retains the full test class and all gradient witnesses.
In particular, subtraction of a weak homogeneous solution preserves the
actual scalar source, which is needed for polynomial improvement steps.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

theorem actual_scalar_weak_source_congr_ae_two {U : Set F}
    {A : EllipticCoeff (2+2) U} {f g u : F → ℝ}
    (hfg : f =ᵐ[volume.restrict U] g) (hu : ActualScalarWeakEquationTwo A f u) :
    ActualScalarWeakEquationTwo A g u := by
  refine ⟨hu.1,?_⟩
  intro uw phi hp pw
  rw [hu.2 uw phi hp pw]
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

theorem actual_scalar_weak_smul_two {U : Set F} (hU : IsOpen U)
    {A : EllipticCoeff (2+2) U} {f u : F → ℝ}
    (hu : ActualScalarWeakEquationTwo A f u) (c : ℝ) :
    ActualScalarWeakEquationTwo A (fun x => c*f x) (fun x => c*u x) := by
  let uw := MemW1p.someWitness hu.1
  refine ⟨(uw.smul c).memW1p,?_⟩
  intro cw phi hp pw
  rw [bilinFormOfCoeff_eq_left hU A cw (uw.smul c) pw,
    bilinFormOfCoeff_smul_left,hu.2 uw phi hp pw,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

theorem actual_scalar_weak_add_two {U : Set F} (hU : IsOpen U)
    {A : EllipticCoeff (2+2) U} {f g u v : F → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) (hv : ActualScalarWeakEquationTwo A g v) :
    ActualScalarWeakEquationTwo A (fun x => f x+g x) (fun x => u x+v x) := by
  let uw := MemW1p.someWitness hu.1
  let vw := MemW1p.someWitness hv.1
  refine ⟨(uw.add vw).memW1p,?_⟩
  intro sw phi hp pw
  rw [bilinFormOfCoeff_eq_left hU A sw (uw.add vw) pw,
    bilinFormOfCoeff_add_left,hu.2 uw phi hp pw,hv.2 vw phi hp pw]
  have he : (fun x => (f x+g x)*phi x) = (fun x => f x*phi x+g x*phi x) := by
    funext x; ring
  have hfi : Integrable (fun x => f x*phi x) (volume.restrict U) := hf.integrable_mul pw.memLp
  have hgi : Integrable (fun x => g x*phi x) (volume.restrict U) := hg.integrable_mul pw.memLp
  rw [he,integral_add hfi hgi]

theorem actual_scalar_weak_sub_homogeneous_two {U : Set F} (hU : IsOpen U)
    {A : EllipticCoeff (2+2) U} {f u v : F → ℝ}
    (hu : ActualScalarWeakEquationTwo A f u) (hv : IsHomogeneousWeakSolution A v) :
    ActualScalarWeakEquationTwo A f (fun x => u x-v x) := by
  let uw := MemW1p.someWitness hu.1
  let vw := MemW1p.someWitness hv.1
  have hs : ActualScalarWeakEquationTwo A f (fun x => u x+(-1)*v x) := by
    refine ⟨(uw.add (vw.smul (-1))).memW1p,?_⟩
    intro sw phi hp pw
    rw [bilinFormOfCoeff_eq_left hU A sw (uw.add (vw.smul (-1))) pw,
      bilinFormOfCoeff_add_left,bilinFormOfCoeff_smul_left,
      hu.2 uw phi hp pw,hv.2 vw phi hp pw,mul_zero,add_zero]
  exact actual_scalar_weak_congr_ae_two
    (Filter.Eventually.of_forall (fun x => by ring)) hs

end PowerConvexity
