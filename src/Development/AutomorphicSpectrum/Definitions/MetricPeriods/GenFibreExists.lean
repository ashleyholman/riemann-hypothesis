module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MultiIsProjVarFOfRatDiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.PB.Known

open ReciprocityTheory.ChartRestriction.G

alias divSuppArith := _root_.ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith

theorem fieldNumbers (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    AI.I1.ExistsUniqueStatement F ι ∧ AI.I1.SymmStatement F ι ∧ AI.I1.MultilinStatement F ι :=
  ⟨GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full F ι, AI.I1.symm_thm F ι, AI.I1.multilin_thm F ι⟩

end GlobalTheory.CompanionTheory.Ar.PB.Known
