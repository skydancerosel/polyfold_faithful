import Polyfold.Chapter9.GapP2_E1_BranchedIntegral

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 9, §9.5: the local measures (9.21) (p. 441) and **Lemmas 9.5.7, 9.5.9, 9.5.10,
9.5.11** (pp. 439–445) for an arbitrary oriented family of sheets, as they are used again for the
boundary measures of **Theorems 9.5.15, 9.5.16** (p. 449: "using the same techniques").  Numbers
and pages are the 2021 text's.

# Oriented sheet families and their local measures

E1's `GapP2_E1_LocalMeasure.lean` proves (9.20), (9.21) and Lemmas 9.5.7–9.5.11 for the sheets
`Mᵢ` of an oriented tame structure.  The boundary measures integrate instead over the boundary
sheets `∂Mᵢ` with the orientations `o_{∂Mᵢ}`, which are not the sheets of a branching structure.
Here the same statements are proved for an abstract family:

* `OrientedSheetFamily X D m x`: a natural representation of `G_x` on `U(x)`, finitely many
  `m`-dimensional oriented smooth submanifolds `Nᵢ` with rational weights `σᵢ`, whose union is
  `D ∩ U(x)` for a fixed set `D ⊆ X` closed under morphisms (`IsMorSaturated D`).
  For a structure of the interior, `D = supp Θ`, `Nᵢ = Mᵢ`; for the boundary, `D` is the set of
  points where `T̂Θ` has a term of reduced codimension one and `Nᵢ = ∂₁Mᵢ`
  (`GapP2_E7_BoundaryFamily.lean`).
* `Represents T'`: `T'(y) = ∑_{y ∈ Nᵢ} σᵢ T_y(Nᵢ, oᵢ)` on `D ∩ U(x)`; `IsNaturalOn T' D`: `T'` is
  carried along by the sc-diffeomorphisms whose tangent maps are those of morphisms.
* `sheetSum`, `localMeasure`, `localMeasureEff` ((9.21)), `sheetSum_eq_of_orientedSum_eq`
  ((9.20)), **`lemma_9_5_7`**, `sheetSum_image`, **`lemma_9_5_9`**, **`lemma_9_5_10`**,
  **`lemma_9_5_11`** for families.
* `OrientedTameStructure.toFamily`: every oriented tame structure is a family for `D = supp Θ`,
  with the same sums (`sheetSum_toFamily`, `represents_toFamily`), and an orientation of `Θ` is
  natural (`isNaturalOn_of_isOrientation`): E1's statements are the instance `D = supp Θ`.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology MeasureTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

variable (X : EpGroupoid Obj Mor) in
/-- A set of objects closed under morphisms: `s(φ) ∈ D ↔ t(φ) ∈ D`. -/
def IsMorSaturated (D : Set Obj) : Prop := ∀ φ : Mor, X.src φ ∈ D ↔ X.tgt φ ∈ D

variable (X : EpGroupoid Obj Mor) in
/-- **`T'` is natural on `D`**: for every sc-diffeomorphism `f : U → U'` whose tangent maps are
those of morphisms (`IsMorTangentOn`), `T'(f(a)) = Tf_* T'(a)` for `a ∈ D ∩ U`. -/
def IsNaturalOn (T' : Obj → X.PObj.OrTangent →₀ ℚ) (D : Set Obj) : Prop :=
  ∀ {f f' : Obj → Obj} {U U' : Set Obj} (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U'),
    X.IsMorTangentOn hf U → ∀ a ∈ D, a ∈ U →
      T' (f a) = (T' a).mapDomain (MPolyfold.OrTangent.map
        (MPolyfold.tangentMapOn hf.isScSmoothOn))

variable (X : EpGroupoid Obj Mor) in
/-- **An oriented sheet family at `x` for `D`**: a natural representation of `G_x` on `U(x)`
(Definition 7.1.11), finitely many `m`-dimensional oriented smooth submanifolds `Nᵢ` with weights
`σᵢ`, and `⋃ Nᵢ = D ∩ U(x)`. -/
structure OrientedSheetFamily (D : Set Obj) (m : ℕ) (x : Obj) where
  rep : X.NaturalRep x
  ι : Type u
  [fintype : Fintype ι]
  N : ι → Set Obj
  σ : ι → ℚ
  orient : ∀ i, X.PObj.SubmanifoldOrientation (N i) m
  isSmoothSubmanifold : ∀ i, X.PObj.IsSmoothSubmanifold (N i)
  iUnion_eq : ⋃ i, N i = D ∩ rep.U

attribute [instance] OrientedSheetFamily.fintype

variable {X : EpGroupoid Obj Mor} {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*}
  [AddCommGroup Ω] [Module ℝ Ω] (𝓘 : X.SheetIntegration G Ω) {D : Set Obj} {m : ℕ}

namespace OrientedSheetFamily

open scoped Classical

section Basic

variable {x : Obj} (F : X.OrientedSheetFamily D m x)

/-- `M_U = ⋃ Nᵢ`. -/
def MU : Set Obj := ⋃ i, F.N i

theorem MU_eq : F.MU = D ∩ F.rep.U := F.iUnion_eq

theorem subset_MU (i : F.ι) : F.N i ⊆ F.MU := subset_iUnion F.N i

theorem MU_subset_U : F.MU ⊆ F.rep.U := fun z hz => by rw [F.MU_eq] at hz; exact hz.2

theorem MU_subset_D : F.MU ⊆ D := fun z hz => by rw [F.MU_eq] at hz; exact hz.1

theorem N_subset_U (i : F.ι) : F.N i ⊆ F.rep.U := (F.subset_MU i).trans F.MU_subset_U

/-- `∑_{y ∈ Nᵢ} σᵢ · T_y(Nᵢ, oᵢ)`. -/
def orientedSum (y : Obj) : X.PObj.OrTangent →₀ ℚ :=
  ∑ i, if y ∈ F.N i then Finsupp.single ((F.orient i).tangent y) (F.σ i) else 0

/-- The family describes `T'` on `D ∩ U(x)`. -/
def Represents (T' : Obj → X.PObj.OrTangent →₀ ℚ) : Prop :=
  ∀ y ∈ D ∩ F.rep.U, T' y = F.orientedSum y

variable (G) in
/-- `A` has measurable traces on all sheets. -/
def IsMeas (A : Set Obj) : Prop := ∀ i, G.IsMeasIn (F.N i) A

/-- **`∑ σᵢ ∫_{A ∩ Nᵢ} ω|(Nᵢ, oᵢ)`.** -/
def sheetSum (ω : Ω) (A : Set Obj) : ℝ :=
  ∑ i, (F.σ i : ℝ) * 𝓘.integ ω (F.N i) (F.orient i).tangent (A ∩ F.N i)

/-- **(9.21): `(1/♯G_x) ∑ σᵢ ∫_{Kᵢ} ω|(Nᵢ, oᵢ)`.** -/
def localMeasure (ω : Ω) (K : Set X.OrbitSpace) : ℝ :=
  (Nat.card (X.Isotropy x) : ℝ)⁻¹ * F.sheetSum 𝓘 ω (X.π ⁻¹' K)

/-- **(9.21) effective: `(1/♯G_x^eff) ∑ σᵢ ∫_{Kᵢ} ω|(Nᵢ, oᵢ)`.** -/
def localMeasureEff (ω : Ω) (K : Set X.OrbitSpace) : ℝ :=
  (Nat.card (X.EffIsotropy x) : ℝ)⁻¹ * F.sheetSum 𝓘 ω (X.π ⁻¹' K)

theorem sheetSum_congr (ω : Ω) {A A' : Set Obj} (h : ∀ i, A ∩ F.N i = A' ∩ F.N i) :
    F.sheetSum 𝓘 ω A = F.sheetSum 𝓘 ω A' :=
  Finset.sum_congr rfl fun i _ => by rw [h i]

theorem MU_inter_inter (A : Set Obj) (i : F.ι) : F.MU ∩ A ∩ F.N i = A ∩ F.N i := by
  ext y
  simp only [mem_inter_iff]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨F.subset_MU i h.2, h.1⟩, h.2⟩⟩

theorem sheetSum_MU_inter (ω : Ω) (A : Set Obj) :
    F.sheetSum 𝓘 ω (F.MU ∩ A) = F.sheetSum 𝓘 ω A :=
  F.sheetSum_congr 𝓘 ω fun i => F.MU_inter_inter A i

theorem sheetSum_add (ω τ : Ω) (A : Set Obj) :
    F.sheetSum 𝓘 (ω + τ) A = F.sheetSum 𝓘 ω A + F.sheetSum 𝓘 τ A := by
  simp only [sheetSum, 𝓘.integ_add, mul_add, Finset.sum_add_distrib]

theorem sheetSum_smul (c : ℝ) (ω : Ω) (A : Set Obj) :
    F.sheetSum 𝓘 (c • ω) A = c * F.sheetSum 𝓘 ω A := by
  simp only [sheetSum, 𝓘.integ_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sheetSum_empty (hS : ∀ i, F.N i ∈ S) (ω : Ω) : F.sheetSum 𝓘 ω ∅ = 0 :=
  Finset.sum_eq_zero fun i _ => by
    rw [empty_inter, 𝓘.integ_empty ω (hS i) (F.orient i), mul_zero]

theorem sheetSum_hasSum (hS : ∀ i, F.N i ∈ S) (ω : Ω) (A : ℕ → Set Obj)
    (hA : ∀ k, F.IsMeas G (A k)) (hd : Pairwise (Function.onFun Disjoint A)) :
    HasSum (fun k => F.sheetSum 𝓘 ω (A k)) (F.sheetSum 𝓘 ω (⋃ k, A k)) := by
  unfold sheetSum
  refine hasSum_sum fun i _ => HasSum.mul_left _ ?_
  rw [iUnion_inter]
  exact 𝓘.integ_hasSum ω _ (hS i) (F.orient i) (fun k => A k ∩ F.N i)
    (fun k => inter_subset_right)
    (fun k => (hA k i).inter (SheetNullSets.isMeasIn_self _))
    fun k l hkl => (hd hkl).mono inter_subset_left inter_subset_left

theorem sheetSum_iUnion_fintype (hS : ∀ i, F.N i ∈ S) (ω : Ω) {T : Type*} [Fintype T]
    (P : T → Set Obj) (hP : ∀ t, F.IsMeas G (P t)) (hd : Pairwise (Function.onFun Disjoint P)) :
    F.sheetSum 𝓘 ω (⋃ t, P t) = ∑ t, F.sheetSum 𝓘 ω (P t) := by
  unfold sheetSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, iUnion_inter]
  congr 1
  have h := 𝓘.integ_biUnion_finset ω (hS i) (F.orient i) Finset.univ (fun t => P t ∩ F.N i)
    (fun t => inter_subset_right)
    (fun t => (hP t i).inter (SheetNullSets.isMeasIn_self _))
    fun s t hst => (hd hst).mono inter_subset_left inter_subset_left
  simpa using h

end Basic

/-! ### Lemma 9.5.7 for families -/

section Independence

variable {x x' : Obj} (F : X.OrientedSheetFamily D m x) (F' : X.OrientedSheetFamily D m x')

include 𝓘 in
/-- Measurability passes from the sheets of `F` to those of `F'`, for subsets of `M_U`. -/
theorem IsMeas.of_subset_MU (hS : ∀ i, F.N i ∈ S) (hS' : ∀ i, F'.N i ∈ S) {A : Set Obj}
    (hA : F.IsMeas G A) (hAM : A ⊆ F.MU) : F'.IsMeas G A := fun j =>
  𝓘.isMeasIn_of_cover hS (hS' j) (inter_subset_left.trans hAM) hA

/-- **(9.20) for families**: equal weighted sums of oriented tangent spaces on `A ⊆ M_U` give
equal sums of integrals. -/
theorem sheetSum_eq_of_orientedSum_eq (hS : ∀ i, F.N i ∈ S) (hS' : ∀ i, F'.N i ∈ S) (ω : Ω)
    {A : Set Obj} (hAM : A ⊆ F.MU) (hA : F.IsMeas G A)
    (hsum : ∀ y ∈ A, F.orientedSum y = F'.orientedSum y) :
    F.sheetSum 𝓘 ω A = F'.sheetSum 𝓘 ω A := by
  have hA' : F'.IsMeas G A := hA.of_subset_MU 𝓘 F F' hS hS' hAM
  exact 𝓘.sum_integ_eq_sum_integ ω F.orient F'.orient hS hS' F.σ F'.σ
    (fun i => (hA i).inter (SheetNullSets.isMeasIn_self _))
    (fun j => (hA' j).inter (SheetNullSets.isMeasIn_self _)) fun y hy => hsum y hy

theorem sheetSum_eq_of_represents {T' : Obj → X.PObj.OrTangent →₀ ℚ} (hS : ∀ i, F.N i ∈ S)
    (hS' : ∀ i, F'.N i ∈ S) (hFT : F.Represents T') (hF'T : F'.Represents T') (ω : Ω)
    {A : Set Obj} (hAM : A ⊆ F.MU ∩ F'.MU) (hA : F.IsMeas G A) :
    F.sheetSum 𝓘 ω A = F'.sheetSum 𝓘 ω A := by
  refine F.sheetSum_eq_of_orientedSum_eq 𝓘 F' hS hS' ω (hAM.trans inter_subset_left) hA
    fun y hy => ?_
  have h1 := (hAM hy).1
  have h2 := (hAM hy).2
  rw [MU_eq] at h1 h2
  rw [← hFT y h1, ← hF'T y h2]

end Independence

/-- **Lemma 9.5.7 for families (2021 p. 439)**: two families on the same `U(x)` with the same
weighted sums of oriented tangent spaces give the same local measures. -/
theorem lemma_9_5_7 {x : Obj} (F F' : X.OrientedSheetFamily D m x) (hS : ∀ i, F.N i ∈ S)
    (hS' : ∀ i, F'.N i ∈ S) (hU : F.rep.U = F'.rep.U)
    (hb : ∀ y ∈ F.rep.U, F.orientedSum y = F'.orientedSum y) (ω : Ω)
    {K : Set X.OrbitSpace} (hK : F.IsMeas G (X.π ⁻¹' K)) :
    F.localMeasure 𝓘 ω K = F'.localMeasure 𝓘 ω K ∧
      F.localMeasureEff 𝓘 ω K = F'.localMeasureEff 𝓘 ω K := by
  have hMU : F.MU = F'.MU := by rw [MU_eq, MU_eq, hU]
  have hmeas : F.IsMeas G (F.MU ∩ X.π ⁻¹' K) := fun i =>
    (hK i).congr_inter (F.MU_inter_inter _ i).symm
  have h : F.sheetSum 𝓘 ω (X.π ⁻¹' K) = F'.sheetSum 𝓘 ω (X.π ⁻¹' K) := by
    rw [← F.sheetSum_MU_inter, ← F'.sheetSum_MU_inter, ← hMU]
    exact F.sheetSum_eq_of_orientedSum_eq 𝓘 F' hS hS' ω inter_subset_left hmeas fun y hy =>
      hb y (F.MU_subset_U hy.1)
  exact ⟨by rw [localMeasure, localMeasure, h], by rw [localMeasureEff, localMeasureEff, h]⟩

/-! ### Sc-diffeomorphisms given by morphisms -/

section Image

variable {x x' : Obj} (F : X.OrientedSheetFamily D m x) (F' : X.OrientedSheetFamily D m x')
  {f f' : Obj → Obj} {U U' : Set Obj}

include 𝓘 in
/-- The image of a measurable subset of `M_U` under an sc-diffeomorphism given by morphisms is
measurable in the sheets of any family. -/
theorem IsMeas.image (hS : ∀ i, F.N i ∈ S) (hS' : ∀ i, F'.N i ∈ S)
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (hmor : X.IsMorTangentOn hf U) {A : Set Obj}
    (hAU : A ⊆ F.MU ∩ U) (hA : F.IsMeas G A) : F'.IsMeas G (f '' A) := by
  have hUo : IsOpen U := hf.isScSmoothOn.isOpen
  have hNS : ∀ i, F.N i ∩ U ∈ S := fun i => 𝓘.inter_mem _ (hS i) U hUo
  have hmor' : ∀ i, X.IsMorTangentOn hf (F.N i ∩ U) := fun i w hw => hmor w hw.2
  have hN'S : ∀ i, f '' (F.N i ∩ U) ∈ S := fun i =>
    𝓘.image_mem _ (hNS i) hf inter_subset_right (hmor' i)
  have hAi : ∀ i, G.IsMeasIn (F.N i ∩ U) (A ∩ F.N i) := fun i =>
    SheetNullSets.IsMeasIn.transfer (hS i) (hNS i)
      (by rw [inter_comm (F.N i) (F.N i ∩ U)]; exact 𝓘.isMeasIn_inter _ (hNS i) _ (hS i))
      (fun y hy => ⟨hy.2, hy.2, (hAU hy.1).2⟩)
      ((hA i).inter (SheetNullSets.isMeasIn_self _))
  have himg : ∀ i, G.IsMeasIn (f '' (F.N i ∩ U)) (f '' A) := fun i => by
    have h := 𝓘.isMeasIn_image _ (hNS i) hf inter_subset_right (hmor' i) (A ∩ F.N i)
      (fun y hy => ⟨hy.2, (hAU hy.1).2⟩) (hAi i)
    refine h.congr_inter ?_
    ext z
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hz⟩
      exact ⟨⟨a, ha.1, rfl⟩, hz⟩
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      have : b = a := by
        rw [← hf.left_inv b hb.2, hab, hf.left_inv a (hAU ha).2]
      exact ⟨⟨a, ⟨ha, this ▸ hb.1⟩, rfl⟩, ⟨b, hb, hab⟩⟩
  intro j
  refine 𝓘.isMeasIn_of_cover hN'S (hS' j) ?_ himg
  rintro _ ⟨⟨a, ha, rfl⟩, -⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hAU ha).1
  exact mem_iUnion.2 ⟨i, a, ⟨hi, (hAU ha).2⟩, rfl⟩

/-- **The change of variables behind Lemmas 9.5.9 and 9.5.11, for families**: for `f` an
sc-diffeomorphism given by morphisms, two families describing a natural `T'`, and a measurable
`A ⊆ M_U ∩ U` with `f(A) ⊆ M_{U'}`, the sum of `F'` over `f(A)` is the sum of `F` over `A`. -/
theorem sheetSum_image {T' : Obj → X.PObj.OrTangent →₀ ℚ} (hnat : X.IsNaturalOn T' D)
    (hS : ∀ i, F.N i ∈ S) (hS' : ∀ i, F'.N i ∈ S)
    (hFT : F.Represents T') (hF'T : F'.Represents T')
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') (hmor : X.IsMorTangentOn hf U) (ω : Ω)
    {A : Set Obj} (hAU : A ⊆ F.MU ∩ U) (hA : F.IsMeas G A) (hfA : f '' A ⊆ F'.MU) :
    F'.sheetSum 𝓘 ω (f '' A) = F.sheetSum 𝓘 ω A := by
  have hUo : IsOpen U := hf.isScSmoothOn.isOpen
  have hNS : ∀ i, F.N i ∩ U ∈ S := fun i => 𝓘.inter_mem _ (hS i) U hUo
  have hmor' : ∀ i, X.IsMorTangentOn hf (F.N i ∩ U) := fun i w hw => hmor w hw.2
  have hN'S : ∀ i, f '' (F.N i ∩ U) ∈ S := fun i =>
    𝓘.image_mem _ (hNS i) hf inter_subset_right (hmor' i)
  have hMN : ∀ i, X.PObj.IsSmoothSubmanifold (F.N i ∩ U) := fun i =>
    (F.isSmoothSubmanifold i).inter_isOpen hUo
  let o' : ∀ i, X.PObj.SubmanifoldOrientation (f '' (F.N i ∩ U)) m := fun i =>
    ((F.orient i).restrict hUo).mapDiffeo (hMN i) hf inter_subset_right
  have himgset : ∀ i, f '' (A ∩ F.N i) = f '' A ∩ f '' (F.N i ∩ U) := by
    intro i
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha.1, rfl⟩, ⟨a, ⟨ha.2, (hAU ha.1).2⟩, rfl⟩⟩
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
      have : b = a := by
        rw [← hf.left_inv b hb.2, hab, hf.left_inv a (hAU ha).2]
      exact ⟨a, ⟨ha, this ▸ hb.1⟩, rfl⟩
  have hAi : ∀ i, G.IsMeasIn (F.N i ∩ U) (A ∩ F.N i) := fun i =>
    SheetNullSets.IsMeasIn.transfer (hS i) (hNS i)
      (by rw [inter_comm (F.N i) (F.N i ∩ U)]; exact 𝓘.isMeasIn_inter _ (hNS i) _ (hS i))
      (fun y hy => ⟨hy.2, hy.2, (hAU hy.1).2⟩)
      ((hA i).inter (SheetNullSets.isMeasIn_self _))
  have step1 : ∀ i, 𝓘.integ ω (F.N i) (F.orient i).tangent (A ∩ F.N i) =
      𝓘.integ ω (f '' (F.N i ∩ U)) (o' i).tangent (f '' A ∩ f '' (F.N i ∩ U)) := by
    intro i
    rw [← himgset i]
    have h1 := 𝓘.integ_congr ω _ (hS i) _ (hNS i) (F.orient i) ((F.orient i).restrict hUo)
      (A ∩ F.N i) (fun y hy => ⟨hy.2, hy.2, (hAU hy.1).2⟩)
      ((hA i).inter (SheetNullSets.isMeasIn_self _))
      (fun y hy => ((F.orient i).restrict_tangent hUo (hAU hy.1).2).symm)
    have h2 := 𝓘.integ_image ω _ (hNS i) ((F.orient i).restrict hUo) (hMN i) hf
      inter_subset_right (hmor' i) (A ∩ F.N i) (fun y hy => ⟨hy.2, (hAU hy.1).2⟩) (hAi i)
    rw [h1, ← h2]
  have hA' : F'.IsMeas G (f '' A) := hA.image 𝓘 F F' hS hS' hf hmor hAU
  have hAimg : ∀ i, G.IsMeasIn (f '' (F.N i ∩ U)) (f '' A ∩ f '' (F.N i ∩ U)) := fun i => by
    rw [← himgset i]
    exact 𝓘.isMeasIn_image _ (hNS i) hf inter_subset_right (hmor' i) (A ∩ F.N i)
      (fun y hy => ⟨hy.2, (hAU hy.1).2⟩) (hAi i)
  have hC : F.sheetSum 𝓘 ω A = ∑ i, (F.σ i : ℝ) *
      𝓘.integ ω (f '' (F.N i ∩ U)) (o' i).tangent (f '' A ∩ f '' (F.N i ∩ U)) :=
    Finset.sum_congr rfl fun i _ => by rw [step1 i]
  rw [hC]
  symm
  refine 𝓘.sum_integ_eq_sum_integ ω o' F'.orient hN'S hS' F.σ F'.σ hAimg
    (fun j => (hA' j).inter (SheetNullSets.isMeasIn_self _)) ?_
  rintro _ ⟨a, ha, rfl⟩
  have haM : a ∈ F.MU := (hAU ha).1
  have haU : a ∈ U := (hAU ha).2
  have hfaM : f a ∈ F'.MU := hfA ⟨a, ha, rfl⟩
  rw [MU_eq] at haM hfaM
  have hR : (∑ l, if f a ∈ F'.N l then
      Finsupp.single ((F'.orient l).tangent (f a)) (F'.σ l) else 0) = T' (f a) :=
    (hF'T (f a) hfaM).symm
  have hL : (∑ i, if f a ∈ f '' (F.N i ∩ U) then
      Finsupp.single ((o' i).tangent (f a)) (F.σ i) else 0) =
      (T' a).mapDomain (MPolyfold.OrTangent.map (MPolyfold.tangentMapOn hf.isScSmoothOn)) := by
    rw [hFT a haM, orientedSum, Finsupp.mapDomain_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hai : a ∈ F.N i
    · have hmem : f a ∈ f '' (F.N i ∩ U) := ⟨a, ⟨hai, haU⟩, rfl⟩
      rw [if_pos hmem, if_pos hai, Finsupp.mapDomain_single]
      congr 1
      have h := MPolyfold.SubmanifoldOrientation.mapDiffeo_tangent ((F.orient i).restrict hUo)
        (hMN i) hf inter_subset_right (y := a) ⟨hai, haU⟩
      rw [(F.orient i).restrict_tangent hUo haU] at h
      exact h
    · have hnm : f a ∉ f '' (F.N i ∩ U) := by
        rintro ⟨b, hb, hab⟩
        have : b = a := by rw [← hf.left_inv b hb.2, hab, hf.left_inv a haU]
        exact hai (this ▸ hb.1)
      rw [if_neg hnm, if_neg hai, Finsupp.mapDomain_zero]
  rw [hL, hR, hnat hf hmor a haM.1 haU]

end Image

/-! ### The isotropy action on `M_U` -/

section Action

variable {x : Obj} (F : X.OrientedSheetFamily D m x)

/-- **`M_U = D ∩ U(x)` is `G_x`-invariant** for saturated `D`. -/
theorem mapsTo_Φ_MU (hD : X.IsMorSaturated D) (g : X.Isotropy x) :
    MapsTo (F.rep.Φ g) F.MU F.MU := fun z hz => by
  have hzU := F.MU_subset_U hz
  rw [MU_eq] at hz ⊢
  refine ⟨?_, F.rep.mapsTo_Φ g hzU⟩
  have h := hD (F.rep.Γ g z)
  rw [F.rep.src_Γ g z hzU, F.rep.tgt_Γ g z hzU] at h
  exact h.1 hz.1

/-- The preimage of `K ⊆ |M_U ∩ V|` in `M_U` is the union of the translates of its part in `V`. -/
theorem MU_inter_preimage_eq_iUnion (hD : X.IsMorSaturated D) {V : Set Obj} {K : Set X.OrbitSpace}
    (hK : K ⊆ X.π '' (F.MU ∩ V)) :
    F.MU ∩ X.π ⁻¹' K = ⋃ g : X.Isotropy x, F.rep.Φ g '' (F.MU ∩ V ∩ X.π ⁻¹' K) := by
  refine Subset.antisymm (fun z hz => ?_) (iUnion_subset fun g => ?_)
  · obtain ⟨w, ⟨hwM, hwV⟩, hwz⟩ := hK hz.2
    obtain ⟨g, hg⟩ := (F.rep.π_eq_π_iff_exists_smul (y := ⟨w, F.MU_subset_U hwM⟩)
      (z := ⟨z, F.MU_subset_U hz.1⟩)).1 hwz
    refine mem_iUnion.2 ⟨g, w, ⟨⟨hwM, hwV⟩, ?_⟩, congrArg Subtype.val hg⟩
    rw [mem_preimage, hwz]
    exact hz.2
  · rintro _ ⟨w, ⟨⟨hwM, -⟩, hwK⟩, rfl⟩
    exact ⟨F.mapsTo_Φ_MU hD g hwM, by rwa [mem_preimage, F.rep.π_Φ g (F.MU_subset_U hwM)]⟩

/-- **The decomposition of the proof of Lemma 9.5.9 (2021 p. 443), for families.** -/
theorem MU_inter_preimage_eq_iUnion_quotient (hD : X.IsMorSaturated D) (a : F.rep.U)
    {V : Set Obj} (hVH : ∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, F.rep.Φ g '' V = V)
    {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' (F.MU ∩ V)) :
    F.MU ∩ X.π ⁻¹' K = ⋃ q : X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a,
      F.rep.Φ (Quotient.out q) '' (F.MU ∩ V ∩ X.π ⁻¹' K) := by
  rw [F.MU_inter_preimage_eq_iUnion hD hK]
  refine Subset.antisymm (iUnion_subset fun g => ?_)
    (iUnion_subset fun q => subset_iUnion (fun g => F.rep.Φ g '' _) _)
  rintro _ ⟨w, ⟨⟨hwM, hwV⟩, hwK⟩, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (MulAction.stabilizer (X.Isotropy x) a) g
  have hg : g = Quotient.out (g : X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) *
      (h : X.Isotropy x)⁻¹ := by
    rw [hh, mul_inv_cancel_right]
  have hw' : F.rep.Φ (h : X.Isotropy x)⁻¹ w ∈ V := by
    rw [← hVH _ (inv_mem h.2)]
    exact mem_image_of_mem _ hwV
  refine mem_iUnion.2 ⟨(g : X.Isotropy x ⧸ _), F.rep.Φ (h : X.Isotropy x)⁻¹ w,
    ⟨⟨F.mapsTo_Φ_MU hD _ hwM, hw'⟩, ?_⟩, ?_⟩
  · rwa [mem_preimage, F.rep.π_Φ _ (F.MU_subset_U hwM)]
  · conv_rhs => rw [hg]
    rw [F.rep.Φ_mul _ _ w (F.MU_subset_U hwM)]

end Action

/-! ### Lemmas 9.5.9 and 9.5.10 for families -/

section Restriction

variable {x : Obj} (F : X.OrientedSheetFamily D m x)

/-- **The computation in the proof of Lemma 9.5.9 (2021 p. 443), for families.** -/
theorem sheetSum_preimage_eq_card_mul_slice (hD : X.IsMorSaturated D)
    {T' : Obj → X.PObj.OrTangent →₀ ℚ} (hnat : X.IsNaturalOn T' D) (hS : ∀ i, F.N i ∈ S)
    (hFT : F.Represents T') (a : F.rep.U) {V : Set Obj} (hVU : V ⊆ F.rep.U)
    (hVH : ∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, F.rep.Φ g '' V = V)
    (hVd : ∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (F.rep.Φ g '' V) V)
    (ω : Ω) {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' (F.MU ∩ V))
    (hKtm : F.IsMeas G (F.MU ∩ V ∩ X.π ⁻¹' K)) :
    F.sheetSum 𝓘 ω (X.π ⁻¹' K) =
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) *
        F.sheetSum 𝓘 ω (F.MU ∩ V ∩ X.π ⁻¹' K) := by
  have hfin : Finite (X.Isotropy x) := NatRepConstruction.finite_isotropy X x
  have : Fintype (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) := Fintype.ofFinite _
  set Kt : Set Obj := F.MU ∩ V ∩ X.π ⁻¹' K with hKt
  have hdec := F.MU_inter_preimage_eq_iUnion_quotient hD a hVH (K := K) hK
  have hdisj := F.rep.pairwise_disjoint_image_Φ_out a hVU hVd (A := Kt)
    (fun z hz => hz.1.2)
  have hKtU : Kt ⊆ F.MU ∩ F.rep.U := fun z hz => ⟨hz.1.1, F.MU_subset_U hz.1.1⟩
  have himgM : ∀ q : X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a,
      F.rep.Φ (Quotient.out q) '' Kt ⊆ F.MU := fun q => by
    refine Subset.trans ?_ (inter_subset_left (t := X.π ⁻¹' K))
    rw [hdec]
    exact subset_iUnion (fun q => F.rep.Φ (Quotient.out q) '' Kt) q
  have hinv : ∀ q : X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a,
      F.sheetSum 𝓘 ω (F.rep.Φ (Quotient.out q) '' Kt) = F.sheetSum 𝓘 ω Kt := fun q =>
    F.sheetSum_image 𝓘 F hnat hS hS hFT hFT (F.rep.isScDiffeoOn_Φ _)
      (F.rep.isMorTangentOn_Φ _) ω hKtU hKtm (himgM q)
  rw [← F.sheetSum_MU_inter, hdec, F.sheetSum_iUnion_fintype 𝓘 hS ω _
    (fun q => hKtm.image 𝓘 F F hS hS (F.rep.isScDiffeoOn_Φ _) (F.rep.isMorTangentOn_Φ _) hKtU)
    hdisj, Finset.sum_congr rfl fun q _ => hinv q, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, nsmul_eq_mul]

/-- The same with a family `F'` at `y` on `V`. -/
theorem sheetSum_preimage_eq_card_mul (hD : X.IsMorSaturated D)
    {T' : Obj → X.PObj.OrTangent →₀ ℚ} (hnat : X.IsNaturalOn T' D) (hS : ∀ i, F.N i ∈ S)
    (hFT : F.Represents T') (a : F.rep.U) {V : Set Obj} (hVo : IsOpen V) (hVU : V ⊆ F.rep.U)
    (hVH : ∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, F.rep.Φ g '' V = V)
    (hVd : ∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (F.rep.Φ g '' V) V)
    (F' : X.OrientedSheetFamily D m (a : Obj)) (hF'U : F'.rep.U = V) (hS' : ∀ i, F'.N i ∈ S)
    (hF'T : F'.Represents T') (ω : Ω) {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' F'.MU)
    (hKm : F.IsMeas G (X.π ⁻¹' K)) :
    F.sheetSum 𝓘 ω (X.π ⁻¹' K) =
      (Nat.card (X.Isotropy x ⧸ MulAction.stabilizer (X.Isotropy x) a) : ℝ) *
        F'.sheetSum 𝓘 ω (X.π ⁻¹' K) := by
  have hMU' : F'.MU = F.MU ∩ V := by
    rw [MU_eq, MU_eq, hF'U, inter_assoc, inter_eq_right.2 hVU]
  have hKtm : F.IsMeas G (F.MU ∩ V ∩ X.π ⁻¹' K) := fun i => by
    have h1 : G.IsMeasIn (F.N i) (V ∩ X.π ⁻¹' K) :=
      (SheetNullSets.isMeasIn_of_borel (MeasurableSpace.measurableSet_generateFrom hVo)).inter
        (hKm i)
    refine h1.congr_inter ?_
    rw [inter_assoc F.MU V, F.MU_inter_inter]
  have h2 : F'.sheetSum 𝓘 ω (X.π ⁻¹' K) = F.sheetSum 𝓘 ω (F.MU ∩ V ∩ X.π ⁻¹' K) := by
    rw [← F'.sheetSum_MU_inter, hMU']
    exact (F.sheetSum_eq_of_represents 𝓘 F' hS hS' hFT hF'T ω
      (fun z hz => ⟨hz.1.1, by rw [hMU']; exact hz.1⟩) hKtm).symm
  rw [F.sheetSum_preimage_eq_card_mul_slice 𝓘 hD hnat hS hFT a hVU hVH hVd ω
    (by rw [← hMU']; exact hK) hKtm, h2]

/-- **Lemma 9.5.9 for families (2021 p. 442)**: `μ_ω^U(K) = μ_ω^V(K)` for `K ⊆ |M_V|`. -/
theorem lemma_9_5_9 (hD : X.IsMorSaturated D) {T' : Obj → X.PObj.OrTangent →₀ ℚ}
    (hnat : X.IsNaturalOn T' D) (hS : ∀ i, F.N i ∈ S) (hFT : F.Represents T') (a : F.rep.U)
    {V : Set Obj} (hVo : IsOpen V) (hVU : V ⊆ F.rep.U)
    (hVH : ∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, F.rep.Φ g '' V = V)
    (hVd : ∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (F.rep.Φ g '' V) V)
    (F' : X.OrientedSheetFamily D m (a : Obj)) (hF'U : F'.rep.U = V) (hS' : ∀ i, F'.N i ∈ S)
    (hF'T : F'.Represents T') (ω : Ω) {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' F'.MU)
    (hKm : F.IsMeas G (X.π ⁻¹' K)) :
    F.localMeasure 𝓘 ω K = F'.localMeasure 𝓘 ω K := by
  have hfin : Finite (X.Isotropy x) := NatRepConstruction.finite_isotropy X x
  have hfin' : Finite (X.Isotropy (a : Obj)) := NatRepConstruction.finite_isotropy X _
  rw [localMeasure, localMeasure, F.sheetSum_preimage_eq_card_mul 𝓘 hD hnat hS hFT a hVo hVU hVH
    hVd F' hF'U hS' hF'T ω hK hKm]
  exact OrientedTameStructure.inv_mul_mul_eq
    (F.rep.card_quotient_stabilizer_mul_card_isotropy a) Nat.card_pos Nat.card_pos _

/-- **Lemma 9.5.10 for families (2021 p. 444)**: the same for the effective measures under the
property of Definition 7.2.18 of `U(x)`. -/
theorem lemma_9_5_10 (hD : X.IsMorSaturated D) {T' : Obj → X.PObj.OrTangent →₀ ℚ}
    (hnat : X.IsNaturalOn T' D) (hS : ∀ i, F.N i ∈ S) (hFT : F.Represents T')
    (hL : F.rep.HasLUC) (a : F.rep.U)
    {V : Set Obj} (hVo : IsOpen V) (hVU : V ⊆ F.rep.U)
    (hVH : ∀ g ∈ MulAction.stabilizer (X.Isotropy x) a, F.rep.Φ g '' V = V)
    (hVd : ∀ g ∉ MulAction.stabilizer (X.Isotropy x) a, Disjoint (F.rep.Φ g '' V) V)
    (F' : X.OrientedSheetFamily D m (a : Obj)) (hF'U : F'.rep.U = V) (hS' : ∀ i, F'.N i ∈ S)
    (hF'T : F'.Represents T') (ω : Ω) {K : Set X.OrbitSpace} (hK : K ⊆ X.π '' F'.MU)
    (hKm : F.IsMeas G (X.π ⁻¹' K)) :
    F.localMeasureEff 𝓘 ω K = F'.localMeasureEff 𝓘 ω K := by
  have := finite_effIsotropy (X := X) x
  have := finite_effIsotropy (X := X) (a : Obj)
  rw [localMeasureEff, localMeasureEff, F.sheetSum_preimage_eq_card_mul 𝓘 hD hnat hS hFT a hVo
    hVU hVH hVd F' hF'U hS' hF'T ω hK hKm]
  exact OrientedTameStructure.inv_mul_mul_eq
    (F.rep.card_quotient_stabilizer_mul_card_effIsotropy hL a) Nat.card_pos Nat.card_pos _

end Restriction

/-! ### Lemma 9.5.11 for families -/

section Morphism

variable {x x' : Obj} (F : X.OrientedSheetFamily D m x) (F' : X.OrientedSheetFamily D m x')
  {f f' : Obj → Obj}

theorem sheetSum_preimage_eq_of_morDiffeo (hD : X.IsMorSaturated D)
    {T' : Obj → X.PObj.OrTangent →₀ ℚ} (hnat : X.IsNaturalOn T' D) (hS : ∀ i, F.N i ∈ S)
    (hS' : ∀ i, F'.N i ∈ S) (hFT : F.Represents T') (hF'T : F'.Represents T')
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' F.rep.U F'.rep.U)
    (hmor : X.IsMorTangentOn hf F.rep.U) (ω : Ω)
    {K : Set X.OrbitSpace} (hKm : F.IsMeas G (X.π ⁻¹' K)) :
    F.sheetSum 𝓘 ω (X.π ⁻¹' K) = F'.sheetSum 𝓘 ω (X.π ⁻¹' K) := by
  have hrel : ∀ w ∈ F.rep.U, (f w ∈ D ↔ w ∈ D) ∧ X.π (f w) = X.π w := fun w hw => by
    obtain ⟨ψ, hsrc, htgt, -⟩ := hmor w hw
    have h1 := hD ψ
    rw [hsrc, htgt] at h1
    exact ⟨h1.symm, ((X.π_eq_π_iff).2 ⟨ψ, hsrc, htgt⟩).symm⟩
  set A : Set Obj := F.MU ∩ X.π ⁻¹' K with hA
  have himg : f '' A = F'.MU ∩ X.π ⁻¹' K := by
    ext z
    rw [hA, MU_eq, MU_eq]
    constructor
    · rintro ⟨w, ⟨⟨hws, hwU⟩, hwK⟩, rfl⟩
      obtain ⟨h1, h2⟩ := hrel w hwU
      exact ⟨⟨h1.2 hws, hf.mapsTo hwU⟩, by rw [mem_preimage, h2]; exact hwK⟩
    · rintro ⟨⟨hzs, hzU⟩, hzK⟩
      have hw : f' z ∈ F.rep.U := hf.symm.mapsTo hzU
      have hfz : f (f' z) = z := hf.right_inv z hzU
      obtain ⟨h1, h2⟩ := hrel (f' z) hw
      rw [hfz] at h1 h2
      exact ⟨f' z, ⟨⟨h1.1 hzs, hw⟩, by rw [mem_preimage, ← h2]; exact hzK⟩, hfz⟩
  have hAm : F.IsMeas G A := fun i =>
    (hKm i).congr_inter (F.MU_inter_inter _ i).symm
  have hAU : A ⊆ F.MU ∩ F.rep.U := fun z hz => ⟨hz.1, F.MU_subset_U hz.1⟩
  rw [← F.sheetSum_MU_inter, ← F'.sheetSum_MU_inter, ← himg]
  exact (F.sheetSum_image 𝓘 F' hnat hS hS' hFT hF'T hf hmor ω hAU hAm
    (by rw [himg]; exact inter_subset_left)).symm

/-- **Lemma 9.5.11 for families (2021 p. 445)**: an sc-diffeomorphism `U → U'` given by
morphisms with `f(x) = x'` preserves the local measures and the effective local measures. -/
theorem lemma_9_5_11 (hD : X.IsMorSaturated D) {T' : Obj → X.PObj.OrTangent →₀ ℚ}
    (hnat : X.IsNaturalOn T' D) (hS : ∀ i, F.N i ∈ S)
    (hS' : ∀ i, F'.N i ∈ S) (hFT : F.Represents T') (hF'T : F'.Represents T')
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' F.rep.U F'.rep.U)
    (hmor : X.IsMorTangentOn hf F.rep.U)
    (hfx : f x = x') (ω : Ω) {K : Set X.OrbitSpace} (hKm : F.IsMeas G (X.π ⁻¹' K)) :
    F.localMeasure 𝓘 ω K = F'.localMeasure 𝓘 ω K ∧
      F.localMeasureEff 𝓘 ω K = F'.localMeasureEff 𝓘 ω K := by
  obtain ⟨ψ, hsrc, htgt, -⟩ := hmor x F.rep.mem_U
  rw [hfx] at htgt
  have h := F.sheetSum_preimage_eq_of_morDiffeo 𝓘 F' hD hnat hS hS' hFT hF'T hf hmor ω hKm
  exact ⟨by rw [localMeasure, localMeasure, h, card_isotropy_eq_of_mor ψ hsrc htgt],
    by rw [localMeasureEff, localMeasureEff, h, card_effIsotropy_eq_of_mor ψ hsrc htgt]⟩

end Morphism

end OrientedSheetFamily

/-! ### The interior: oriented tame structures are families for `D = supp Θ` -/

section Interior

variable {Θ : Obj → ℚ}

/-- `supp Θ` is saturated for a functor `Θ`. -/
theorem isMorSaturated_supp (hΘ : X.IsFunctorial Θ) : X.IsMorSaturated (supp Θ) := fun φ => by
  change 0 < Θ _ ↔ 0 < Θ _
  rw [hΘ φ]

/-- **An orientation `T̂Θ` is natural on `supp Θ`** (the naturality step in the proof of
Lemma 9.5.9, `T̂Θ ∘ t = Tφ_* ∘ T̂Θ ∘ s`). -/
theorem isNaturalOn_of_isOrientation (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T) :
    X.IsNaturalOn T (supp Θ) := by
  intro f f' U U' hf hmor a ha haU
  have hsm : a ∈ X.PObj.smoothSet := hΘ.support_subset ha
  obtain ⟨ψ, hsrc, htgt, hψ⟩ := hmor a haU
  have hnat := hT.natural ψ (by rw [hsrc]; exact hsm)
  rw [hsrc, htgt, grHatPush] at hnat
  have hmem := (hT.mem a hsm).2
  rw [← hnat]
  exact Finsupp.mapDomain_congr fun g hg => by
    have hor := hmem g hg
    rw [MPolyfold.OrTangent.map_eq_push]
    exact MPolyfold.OrTangent.push_congr (fun α hα => hψ α (hor.1 α hα))
      fun v hv i => hor.mem_carrier hv i

namespace OrientedTameStructure

variable {n : ℕ} {x : Obj} (C : X.OrientedTameStructure n Θ x)

/-- **An oriented tame structure is an oriented sheet family for `D = supp Θ`.** -/
def toFamily : X.OrientedSheetFamily (supp Θ) n x where
  rep := C.rep
  ι := C.ι
  N := C.M
  σ := C.σ
  orient := C.orient
  isSmoothSubmanifold := C.isSmoothSubmanifold
  iUnion_eq := by
    rw [← C.U_eq]
    exact C.toLocalBranchingStructure.MU_eq

theorem sheetSum_toFamily (ω : Ω) (A : Set Obj) :
    C.toFamily.sheetSum 𝓘 ω A = C.sheetSum 𝓘 ω A := rfl

theorem localMeasure_toFamily (ω : Ω) (K : Set X.OrbitSpace) :
    C.toFamily.localMeasure 𝓘 ω K = C.localMeasure 𝓘 ω K := rfl

theorem localMeasureEff_toFamily (ω : Ω) (K : Set X.OrbitSpace) :
    C.toFamily.localMeasureEff 𝓘 ω K = C.localMeasureEff 𝓘 ω K := rfl

theorem represents_toFamily (hΘ : X.IsBranchedEpSubgroupoid Θ)
    {T : Obj → X.PObj.OrTangent →₀ ℚ} (hCT : C.Represents T) : C.toFamily.Represents T :=
  fun y hy => by
    have h := hCT y (C.U_eq ▸ hy.2) (hΘ.support_subset hy.1)
    rw [h, C.orientedSum_eq_sum_ite]
    rfl

end OrientedTameStructure

end Interior

end EpGroupoid

end Polyfold
