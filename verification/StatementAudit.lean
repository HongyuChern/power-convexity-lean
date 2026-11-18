import PowerConvexity.C114Complete
import PowerConvexity.Targets.MainTheorem
import Lean

open Lean Meta

#eval show MetaM Unit from do
  let previous ← getConstInfo `PowerConvexity.mainTheorem
  let current ← getConstInfo `PowerConvexity.actual_original_route_mainTheorem
  unless ← isDefEq previous.type current.type do
    throwError "The new theorem and frozen project endpoint have different types."
  logInfo "PASS: new proof has the same Lean type as PowerConvexity.mainTheorem."

#check @PowerConvexity.actual_classical_minkowski_intermediate_family_two
#check @PowerConvexity.actual_classical_minkowski_family_exists_two
#check @PowerConvexity.actual_paper_family_common_collar_exhaustion_two
#check @PowerConvexity.actual_original_dirichlet_hessian_sigma_strictConvex_uncentered_two
#check @PowerConvexity.actual_original_route_mainTheorem
#print PowerConvexity.ClassicalDirichletDataTwo
#print PowerConvexity.ClassicalMinkowskiFamilyTwo
#print PowerConvexity.distanceInteriorDomain
#print PowerConvexity.modifiedSigmaTwo
#check @CHS.Calculus.ClosureC2Jet
