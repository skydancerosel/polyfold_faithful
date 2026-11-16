import Polyfold.Chapter2.StrongBundle

/-!
# Sums and differences of sc-smooth maps

The sc-operators of addition and negation (`ScBanach.addOp`, `ScBanach.negOp`) and the sc-smoothness
of sums, negatives, differences and the second projection. The sections of Chapter 3 are in
`Chapter3/StrongBundleSections.lean`.
-/

open Set Filter Topology Function
noncomputable section
namespace Polyfold
variable {E F : ScBanach}

/-- The addition `F ⊕ F → F` as an sc-operator. -/
def ScBanach.addOp (F : ScBanach) : ScOperator (F.prod F) F where
  lvl m := ContinuousLinearMap.fst ℝ (F m) (F m) + ContinuousLinearMap.snd ℝ (F m) (F m)
  incl_comm m x := by
    change F.incl m (x.1 + x.2) = F.incl m x.1 + F.incl m x.2
    exact map_add _ _ _

/-- The negation `F → F` as an sc-operator. -/
def ScBanach.negOp (F : ScBanach) : ScOperator F F where
  lvl m := -ContinuousLinearMap.id ℝ (F m)
  incl_comm m x := by
    change F.incl m (-x) = -(F.incl m x)
    exact map_neg _ _

section SumRule
variable {U : Set (E 0)} {f g : E 0 → F 0}

/-- **The sum rule**: the sum of sc-smooth maps is sc-smooth (pairing followed by the
sc-operator `F ⊕ F → F`). -/
theorem IsScSmooth.add (hU : IsScDomain E U) (hf : IsScSmooth U f) (hg : IsScSmooth U g) :
    IsScSmooth U fun x => f x + g x := by
  have := IsScSmooth.comp hU (isScDomain_univ _) (F.addOp.isScSmooth (isScDomain_univ _))
    (hf.scPair hU hg) (mapsTo_univ _ _)
  exact this.congr hU fun x _ => rfl

theorem IsScSmooth.neg (hU : IsScDomain E U) (hf : IsScSmooth U f) :
    IsScSmooth U fun x => -f x := by
  have := IsScSmooth.comp hU (isScDomain_univ _) (F.negOp.isScSmooth (isScDomain_univ _)) hf
    (mapsTo_univ _ _)
  exact this.congr hU fun x _ => rfl

theorem IsScSmooth.sub (hU : IsScDomain E U) (hf : IsScSmooth U f) (hg : IsScSmooth U g) :
    IsScSmooth U fun x => f x - g x :=
  (hf.add hU (hg.neg hU)).congr hU fun _ _ => (sub_eq_add_neg _ _).symm

/-- The second component of a map sc-smooth into `E' ⊕ F'`. -/
theorem IsScSmooth.snd {E' F' : ScBanach} {h : E 0 → (E'.prod F') 0} (hU : IsScDomain E U)
    (hh : IsScSmooth U h) : IsScSmooth (F := F') U fun x => (h x).2 := by
  have := IsScSmooth.comp hU (isScDomain_univ _) ((E'.prodSndOp F').isScSmooth (isScDomain_univ _))
    hh (mapsTo_univ _ _)
  exact this.congr hU fun x _ => rfl

end SumRule
end Polyfold
end
