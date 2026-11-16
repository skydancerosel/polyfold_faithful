import Polyfold.Chapter1.ScBanach

/-!
# Product of sc-operators

The product `ScOperator.prodMap` of two sc-operators. The composition results of the basic class are
in `Chapter3/BasicClassComposition.lean`.
-/

open Set Filter Topology Function
noncomputable section
namespace Polyfold
variable {E F E' F' E'' F'' : ScBanach}

/-- The direct sum `S ⊕ T : E ⊕ F → E' ⊕ F'` of two sc-operators. -/
def ScOperator.prodMap (S : ScOperator E E') (T : ScOperator F F') :
    ScOperator (E.prod F) (E'.prod F') where
  lvl m := (S m).prodMap (T m)
  incl_comm m x := Prod.ext (S.incl_comm m x.1) (T.incl_comm m x.2)

end Polyfold
end
