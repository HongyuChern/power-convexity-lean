import DifferentialGeometry.External.DeGiorgi.Holder.PublicEstimate
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory

/-! # Actual continuous representatives for the linear regularity step.
The input is the actual local weak equation, with its W1,2 integrability.
No continuity or representative is postulated. The representative retains
the same weak equation and, for harmonic replacement, the same zero trace
of its difference from the prescribed Sobolev datum.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "F" => AmbientSpace d

theorem actual_homogeneousWeakSolution_congr_ae
    {U : Set F} {A : EllipticCoeff d U} {u v : F → ℝ}
    (huv : u =ᵐ[volume.restrict U] v)
    (hu : IsHomogeneousWeakSolution A u) :
    IsHomogeneousWeakSolution A v := by
  refine ⟨(MemW1pWitness.ofAeEq huv (MemW1p.someWitness hu.1)).memW1p, ?_⟩
  intro hv phi hphi hphiw
  let huw : MemW1pWitness 2 u U := MemW1pWitness.ofAeEq huv.symm hv
  exact hu.2 huw phi hphi hphiw

theorem actual_zeroTrace_congr_ae
    {U : Set F} {u v : F → ℝ}
    (huv : u =ᵐ[volume.restrict U] v) (hu : MemH01 u U) :
    MemH01 v U := by
  obtain ⟨_,hw,phi,hreg,hcomp,hsupp,hlim,hgrad⟩ := hu
  let hvw := MemW1pWitness.ofAeEq huv hw
  refine ⟨hvw.memW1p,hvw,phi,hreg,hcomp,hsupp,?_,hgrad⟩
  convert hlim using 1
  funext n
  apply eLpNorm_congr_ae
  filter_upwards [huv] with x hx
  simp only [hx]

theorem actual_homogeneous_weak_continuous_representative
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (ball (0 : F) 1))
    {u : F → ℝ} (hu : IsHomogeneousWeakSolution A.1 u) :
    ∃ v : F → ℝ, v =ᵐ[volume.restrict (ball (0 : F) 1)] u ∧
      IsHomogeneousWeakSolution A.1 v ∧
      ContinuousOn v (ball (0 : F) (1/2 : ℝ)) ∧
      ∃ alpha C : ℝ, 0 < alpha ∧ 0 ≤ C ∧
        ∀ x ∈ ball (0 : F) (1/2 : ℝ),
        ∀ y ∈ ball (0 : F) (1/2 : ℝ),
          |v x-v y| ≤ C * ‖x-y‖ ^ alpha := by
  have hint : IntegrableOn (fun z => |u z| ^ (2 : ℝ)) (ball (0 : F) 1) volume := by
    simpa only [IntegrableOn, Real.rpow_two, sq_abs] using hu.1.1.integrable_sq
  obtain ⟨v,hvu,alpha,ha,_,hh⟩ :=
    holder_Moser_of_homogeneousWeakSolution hd A (by norm_num : 1 < (2 : ℝ)) hu hint
  have hvu' : v =ᵐ[volume.restrict (ball (0 : F) 1)] u := hvu
  let K : ℝ := CHolderMoser d * A.1.Λ ^ ((d : ℝ)/(2*2)) *
    ((2 : ℝ)/(2-1)) ^ ((d : ℝ)/2) *
    (∫ z in ball (0 : F) 1, |u z| ^ (2 : ℝ)) ^ (1/(2 : ℝ))
  have hbound : ∀ x ∈ ball (0 : F) (1/2 : ℝ),
      ∀ y ∈ ball (0 : F) (1/2 : ℝ), |v x-v y| ≤ |K| * ‖x-y‖ ^ alpha := by
    intro x hx y hy
    exact (hh x hx y hy).trans
      (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg (norm_nonneg _) _))
  have hholder := holderOnWith_of_realBound (abs_nonneg K) ha.le hbound
  refine ⟨v,hvu',actual_homogeneousWeakSolution_congr_ae hvu'.symm hu,
    hholder.continuousOn ha,alpha,|K|,ha,abs_nonneg K,hbound⟩

theorem actual_continuous_harmonic_replacement
    (hd : 2 < (d : ℝ))
    (A : NormalizedEllipticCoeff d (ball (0 : F) 1))
    {u : F → ℝ} (hu : MemW1p 2 u (ball (0 : F) 1)) :
    ∃ v : F → ℝ, IsHomogeneousWeakSolution A.1 v ∧
      MemH01 (fun x => v x-u x) (ball (0 : F) 1) ∧
      ContinuousOn v (ball (0 : F) (1/2 : ℝ)) ∧
      ∀ w : F → ℝ, IsHomogeneousWeakSolution A.1 w →
        MemH01 (fun x => w x-u x) (ball (0 : F) 1) →
        ContinuousOn w (ball (0 : F) (1/2 : ℝ)) →
        EqOn v w (ball (0 : F) (1/2 : ℝ)) := by
  have hd' : 2 ≤ d := by exact_mod_cast hd.le
  obtain ⟨h,hh,hzero⟩ := aHarmonic_replacement_exists hd' isOpen_ball isBounded_ball A.1 hu
  obtain ⟨v,hvh,hv,hvc,_⟩ := actual_homogeneous_weak_continuous_representative hd A hh
  have hz : MemH01 (fun x => v x-u x) (ball (0 : F) 1) := by
    apply actual_zeroTrace_congr_ae (u := fun x => h x-u x) _ hzero
    filter_upwards [hvh] with x hx
    rw [hx]
  refine ⟨v,hv,hz,hvc,?_⟩
  intro w hw hwz hwc
  have hae := aHarmonic_replacement_unique hd' isOpen_ball isBounded_ball A.1 hu hv hz hw hwz
  have haeh : v =ᵐ[volume.restrict (ball (0 : F) (1/2 : ℝ))] w :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by norm_num)) hae
  exact Measure.eqOn_open_of_ae_eq haeh isOpen_ball hvc hwc

end PowerConvexity
