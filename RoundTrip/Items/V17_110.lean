import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_110

set_option maxSynthPendingDepth 3

namespace RoundTrip.V17_110
open Polyfold
open Polyfold.GCT.PolyfoldConstruction
open Polyfold.EpGroupoid Polyfold.EPLocalization Polyfold.EPLocalization.EPLoc

/-- The project's statement, universes at `0` (`EP.{0}` is the universe of the models of a
`GCT.{0}`). -/
def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.pull_toOriented.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_of_family.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_iff.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOriented_iff_forall.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.integral_eq_integralVia.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4_book.{0}) ∧
  (type_of% @Polyfold.EPLocalization.OrientedBranched.exists_tame_pull.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.pull_toOriented.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_of_family.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_iff.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOriented_iff_forall.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.integral_eq_integralVia.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4_book.{0},
    @Polyfold.EPLocalization.OrientedBranched.exists_tame_pull.{0}⟩

/-! Re-proofs (the project's proofs, copied; they use no item theorem) of the conjuncts of `A`
that `B` does not give: the ep-groupoid transfer of tame structures along a generalized
isomorphism, `f^*Θ̂_{Ψ'} = Θ̂_Ψ`, and "tame oriented on one model ⇒ on every model" for all `n`
and without compactness (`B`'s part (a) assumes `n ≥ 1` and `|supp Θ|` compact). -/

theorem exists_tame_pull' {X Y : EP.{0}} {n : ℕ} {f : EPLoc.of X ⟶ EPLoc.of Y}
    (hf : IsGeneralizedIso f) (B : OrientedBranched Y)
    (hB : ∀ y ∈ supp B.Θ, ∃ D : Y.X.OrientedTameStructure n B.Θ y, D.Represents B.T) :
    ∀ x ∈ supp (OrientedBranched.pull hf B).Θ,
      ∃ C : X.X.OrientedTameStructure n (OrientedBranched.pull hf B).Θ x,
        C.Represents (OrientedBranched.pull hf B).T := fun x hx => by
  obtain ⟨C, -, hC⟩ := (rep f).hcov_pullTheta (isEquivalence_rep_Φ hf)
    (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
    (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) B.isBranchedEpSubgroupoid
    B.hasIndependentTangentSums B.isOrientation
    (FormEval.hcov_of_tameOpen (FormEval.tameOpen Y.X) hB) x hx
  exact ⟨C, hC⟩

theorem pull_toOriented' {C : GCT.{0}} {S : C.PolyfoldConstruction} (A : S.OrientedSubcategory)
    (c c' : S.CoveringFamily) :
    OrientedBranched.pull (S.isGeneralizedIso_comparison c c') (A.toOriented c') =
      A.toOriented c :=
  OrientedBranched.ext' (pullTheta_comparison_modelPull (c := c) (c' := c')
    A.isBranched.isFunctorial) (A.pullSection_comparison c c')

theorem of_family' {C : GCT.{0}} {S : C.PolyfoldConstruction} {n : ℕ}
    (A : S.OrientedSubcategory) (c c' : S.CoveringFamily) (h : A.IsTameOrientedVia c' n) :
    A.IsTameOrientedVia c n := by
  have key := exists_tame_pull' (S.isGeneralizedIso_comparison c c') (A.toOriented c') h
  rw [pull_toOriented' A c c'] at key
  exact key

/-- **Harness.**  The statement of `theorem_17_6_4_book` contains the proof term
`A.isTameOrientedVia_of_family c' c hloc` (an item theorem, whose proof uses `pull_toOriented` and
`exists_tame_pull`).  Any term whose type mentions `A` therefore reaches these three banned
theorems.  `Main'` is that statement with the copy `of_family'` in its place, and `A'` is `A`
with `Main'`; `A = A'` by `rfl` (proof irrelevance).  The directions are proved for `A'` and
transported point-free, so `#rt_check` sees only the proofs. -/
def Main' : Prop :=
  ∀ {C : GCT.{0}} {S : C.PolyfoldConstruction} {n : ℕ} (A : S.OrientedSubcategory)
    (c c' : S.CoveringFamily) (hn : 0 < n) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c n) (ω : S.catFormsInfty n),
    A.integralVia c hn hcpt hloc ω = A.integralVia c' hn hcpt (of_family' A c' c hloc) ω

def A' : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.pull_toOriented.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_of_family.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_iff.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOriented_iff_forall.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.integral_eq_integralVia.{0}) ∧
  Main' ∧
  (type_of% @Polyfold.EPLocalization.OrientedBranched.exists_tame_pull.{0})

theorem A_eq_A' : A = A' := rfl

/-- Main conjunct: `theorem_17_6_4_book`. -/
def Main : Prop :=
  type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4_book.{0}

theorem Main_eq_Main' : Main = Main' := rfl

theorem A'_to_B : A' → B := by
  rintro ⟨-, h4, hfam, -, -, -, -, -⟩ C S A n hn hc
  exact ⟨fun ⟨c₀, h₀⟩ c => hfam A c c₀ h₀,
    fun c c' ht ht' ω => h4 A c c' hn hc ht ht' ω⟩

theorem B_to_A' : B → A' := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun A c c' => pull_toOriented' A c c'
  · intro C S n A c c' hn hc ht ht' ω
    exact (hB C S A n hn hc).2 c c' ht ht' ω
  · exact fun A c c' h => of_family' A c c' h
  · exact fun A c c' => ⟨of_family' A c' c, of_family' A c c'⟩
  · intro C S n A _
    exact ⟨fun ⟨c', h⟩ c => of_family' A c c' h, fun h => ⟨Classical.arbitrary _, h _⟩⟩
  · intro C S n A hn hc h c ht ω
    exact (hB C S A n hn hc).2 _ c _ ht ω
  · intro C S n A c c' hn hc ht ω
    exact (hB C S A n hn hc).2 c c' ht _ ω
  · exact fun hf B hB => exists_tame_pull' hf B hB

theorem A_to_B : A → B := A'_to_B
theorem B_to_A : B → A := B_to_A'

/-- `B ⇒ main`. -/
theorem B_to_main' : B → Main' := fun hB => (B_to_A' hB).2.2.2.2.2.2.1
theorem B_to_main : B → Main := B_to_main'

/-- `main ⇒ B`: part (b) of `B` from the main conjunct (proof irrelevance for the tameness proof
on the second family); part (a) is not a consequence of the main conjunct, and is supplied by the
re-proved transfer `of_family'` (no hypothesis used for it). -/
theorem main'_to_B : Main' → B := by
  intro h C S A n hn hc
  exact ⟨fun ⟨c₀, h₀⟩ c => of_family' A c c₀ h₀,
    fun c c' ht ht' ω => h A c c' hn hc ht ω⟩
theorem main_to_B : Main → B := main'_to_B

#rt_check RoundTrip.V17_110.A_to_B [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.pull_toOriented, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_of_family, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_iff, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOriented_iff_forall, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.integral_eq_integralVia, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4_book, Polyfold.EPLocalization.OrientedBranched.exists_tame_pull]
#rt_check RoundTrip.V17_110.B_to_A [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.pull_toOriented, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_of_family, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_iff, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOriented_iff_forall, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.integral_eq_integralVia, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4_book, Polyfold.EPLocalization.OrientedBranched.exists_tame_pull]
#rt_check RoundTrip.V17_110.main_to_B [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.pull_toOriented, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_of_family, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_iff, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOriented_iff_forall, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.integral_eq_integralVia, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4_book, Polyfold.EPLocalization.OrientedBranched.exists_tame_pull]
#rt_check RoundTrip.V17_110.B_to_main [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.pull_toOriented, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_of_family, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_iff, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOriented_iff_forall, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.integral_eq_integralVia, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4_book, Polyfold.EPLocalization.OrientedBranched.exists_tame_pull]
#rt_overlap RoundTrip.V17_110.B_to_A [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.pull_toOriented, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_of_family, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOrientedVia_iff, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isTameOriented_iff_forall, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.integral_eq_integralVia, Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_4_book, Polyfold.EPLocalization.OrientedBranched.exists_tame_pull]

end RoundTrip.V17_110
