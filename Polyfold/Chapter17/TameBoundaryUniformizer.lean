import Polyfold.Chapter17.TameBoundaryCategory
import Polyfold.Chapter17.PolyfoldFaces

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.4 (pp. 791–797): **the face uniformizers `Ψ_θ : G_θ ⋉ θ → bC`**.

For `Ψ ∈ F(α)`, `Ψ : G ⋉ O → C`, `ō` with `Ψ(ō) = α ∈ ∂C` and a good open neighbourhood `U(ō)`
(Definition 17.4.1), every face `θ ∈ F_{U(ō)}` gives a functor `Ψ_θ` on the translation groupoid
of the stabilizer `G_θ` acting on `θ`.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* The action of `G` on faces: `natRep_Φ_eq` (in `G ⋉ O` the natural action of a natural
  representation at `ō` is `y ↦ g ∗ y`), `GoodNbhd.smul_mem`, `GoodNbhd.smul_mem_faces`,
  `GoodNbhd.faceAction` (`G × F_{U(ō)} → F_{U(ō)}`, p. 792) and **Definition 17.4.5**
  (`faceStabilizer`, `definition_17_4_5`).
* `germLift_hat_iff`: under continuity of `Ψ̂`, `Ψ̂(g, x)` carries face germs as `g ∗ ·` does.
* The objects over points of a uniformizer: `ptTr` (`(x, 1_{Ψ(x)}, ō_ref)`), `ptObj` (a face germ
  at `x` as an object of `bC`), `bLift_ptObj_iff` (a morphism `φ = h.mor` lifts iff `h` carries
  the germs), `ptMor`, `ptObj_injective`, `exists_ptObj_eq`.
* The face germs `GoodNbhd.faceGerm` of `θ` at `x ∈ θ` (Part I's `Φ_{(ō, U(ō), θ)}⁻¹`),
  `exists_faceGerm_eq`, `eq_of_faceGerm_eq`, `isLiftOf_smul_faceGerm` (`g ∗ ·` carries the germ of
  `θ` at `x` to that of `g(θ)` at `g ∗ x`).
* `faceObj` (**(17.64)**; `faceObj_eq_toBObj` and `display_17_64`: the book's formula
  `[Ψ(x), Ψ'', U''(ō''), θ'']` for every choice, with `θ''` unique), `smulMor`, `faceMor`,
  `faceFunctor` (`Ψ_θ`) and **Lemma 17.4.6** (`lemma_17_4_6`: injective on objects and fully
  faithful).
* **(17.65)** `FacePt`, `barObj`, `smulMor` and **Lemma 17.4.9** (`lemma_17_4_9`),
  **Lemma 17.4.8** (`faceImage`, `lemma_17_4_8`), **(17.67)–(17.69)** (`barSetoid`,
  `barOrbitMap`, `barOrbitMap_injective`, `display_17_68`, `display_17_69`,
  `barSetoid_r_iff_of_eq`).
* `FaceTr` (`M(Ψ_θ, Ψ'_{θ'})`), `faceTrToTr`, **Lemma 17.4.10** (`lemma_17_4_10`), `trUU`
  (`M(Ψ, Ψ')_{U,U'}`), **Lemma 17.4.11** (`lemma_17_4_11`), **Definition 17.4.12**
  (`transFaceSet`, `definition_17_4_12`, with existence and uniqueness of `h_*θ` and
  `M(Ψ, Ψ')*_{θ,θ'} = image of M(Ψ_θ, Ψ'_{θ'})`).
* Non-degeneracy of the hypotheses: `quadrant_hatContinuous`, `quadrant_isCentred`,
  `quadrant_tameBoundaryUniformizer_witness` (T6's quadrant polyfold: tame, two objects of `bC`
  over the corner, two faces of a good neighbourhood).

## Readings

* **Centring.** Definition 17.1.3 does not require `G` to fix `ō`; the construction of `Ψ_θ`
  (`G` acting on `F_{U(ō)}`, p. 792) presumes it ("`G` is the isotropy group of `α`"). We assume
  `S.IsCentred` (every `Ψ ∈ F(α)` is centred at `α`).
* **Continuity of `Ψ̂`.** That `Ψ_θ(g, x)` is a morphism of `bC` uses that the local
  sc-diffeomorphism of `Ψ̂(g, x) ∈ M(Ψ, Ψ)` is `g ∗ ·` near `x`, which is the conclusion of
  Lemma 17.1.9 (`Ψ̂` an sc-diffeomorphism). That lemma holds under continuity of `Ψ̂`
  (`lemma_17_1_9_of_continuous`), which we assume as `S.HatContinuous`.
* "`f` maps `θ` near `x` to `θ''` near `ō''`" is read at the level of face germs
  (`GermLift`, Part I's `IsLiftOf`), as in Definition 17.4.2.
* The proof of fullness in Lemma 17.4.6 runs an open–closed argument in `θ°`; with `U(ō)`
  invariant under `G` (`GoodNbhd.smul_mem`) it is replaced by: `g(θ)` and `θ` are faces of
  `U(ō)` with the same germ at `g ∗ x`, hence equal.
* (17.69): the "obvious homeomorphism" `⊔_i |θ_i| → G \ ⊔_θ θ` is used as an identification
  (`barSetoid_r_iff_of_eq`: on one face the orbits are those of `G_θ`), and `display_17_69` is the
  bijection of `G \ ⊔_θ θ` onto `|B_C|⁻¹(|Ψ(U(ō))|)`; the topology of `|bC|` (and so the
  homeomorphism statements) belongs to Definition 17.4.17 and later.
* `G ⋉ ⊔_θ θ` is not built as a groupoid; Lemma 17.4.9 is stated for the object map `barObj`
  and the morphisms `smulMor`.
-/

open Set Function Topology Filter
open scoped Pointwise

universe u

namespace Polyfold

open TameBoundary

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### The action of `G` on `O` and on the faces of `U(ō)` -/

section Action

variable (Ψ : S.Unif)

/-- `g ∗ · : O → O` is an sc-diffeomorphism with inverse `g⁻¹ ∗ ·`. -/
theorem isScDiffeoOn_smul (g : Ψ.1.G) :
    Ψ.1.P.IsScDiffeoOn Ψ.1.P (fun y => g • y) (fun y => g⁻¹ • y) univ univ :=
  ⟨Ψ.1.smooth_smul g, Ψ.1.smooth_smul g⁻¹, mapsTo_univ _ _, mapsTo_univ _ _,
    fun y _ => inv_smul_smul g y, fun y _ => smul_inv_smul g y⟩

theorem isDHomeoOn_smul (g : Ψ.1.G) :
    IsDHomeoOn Ψ.1.P.degIndex Ψ.1.P.degIndex (fun y => g • y) univ :=
  (isScDiffeoOn_smul Ψ g).isDHomeoOn

theorem degIndex_smul (g : Ψ.1.G) (y : Ψ.1.O) : Ψ.1.P.degIndex (g • y) = Ψ.1.P.degIndex y :=
  (isDHomeoOn_smul Ψ g).deg_eq y (mem_univ _)

variable {Ψ}

/-- **In `G ⋉ O` the natural action is the group action**: for a natural representation at `ō`
and an isotropy element `(g, ō)`, `Φ(g)(y) = g ∗ y` on `U(ō)` (`Γ` is continuous into the discrete
`G`-factor on the connected `U(ō)`). -/
theorem natRep_Φ_eq {o : Ψ.1.O} (R : Ψ.1.ep.NaturalRep o) (g : Ψ.1.ep.Isotropy o) {y : Ψ.1.O}
    (hy : y ∈ R.U) : R.Φ g y = g.val.1 • y := by
  have hc : ContinuousOn (fun z => (R.Γ g z).1) R.U :=
    continuous_fst.comp_continuousOn (R.isScSmoothOn_Γ g).continuousOn
  have hk : (R.Γ g y).1 = (R.Γ g o).1 :=
    R.isConnected_U.isPreconnected.constant hc hy R.mem_U
  have hs : (R.Γ g y).2 = y := R.src_Γ g y hy
  have hk' : (R.Γ g y).1 = g.val.1 := by rw [hk, R.Γ_self]
  rw [← R.tgt_Γ g y hy]
  change (R.Γ g y).1 • (R.Γ g y).2 = _
  rw [hk', hs]

/-- The isotropy element `(g, ō)` of a fixed point `ō`. -/
def isoOf {o : Ψ.1.O} (hfix : Ψ.1.FixesPoint o) (g : Ψ.1.G) : Ψ.1.ep.Isotropy o :=
  ⟨(g, o), rfl, hfix g⟩

end Action

variable (S) in
/-- **`G` fixes `ō`** (the reading of p. 792, "`G` the isotropy group of `α`"): every `Ψ ∈ F(α)`
is centred at `α`. Not a condition of Definition 17.1.3. -/
def IsCentred : Prop := ∀ α, ∀ Ψ ∈ S.F α, Ψ.toUniformizer.IsCentredAt α

variable (S) in
/-- **`Ψ̂` is continuous** for every `Ψ` (the hypothesis under which Lemma 17.1.9 holds,
`lemma_17_1_9_of_continuous`). -/
def HatContinuous : Prop := ∀ Ψ : S.Unif, Continuous (S.hat Ψ)

theorem IsCentred.fixesPoint (hC : S.IsCentred) {α : C.Obj} {Ψ : C.LocalUniformizer}
    (hΨ : Ψ ∈ S.F α) {o : Ψ.O} (ho : Ψ.obj o = α) : Ψ.FixesPoint o := by
  obtain ⟨q, hq, hfix⟩ := hC α Ψ hΨ
  have : q = o := Ψ.injective_obj (hq.trans ho.symm)
  rw [← this]
  exact hfix

section Faces

variable {Ψ : S.Unif} {o : Ψ.1.O} (hfix : Ψ.1.FixesPoint o)

namespace GoodNbhd

variable (V : S.GoodNbhd Ψ o)

include hfix in
/-- **`U(ō)` is `G`-invariant** when `G` fixes `ō`. -/
theorem smul_mem (g : Ψ.1.G) {y : Ψ.1.O} (hy : y ∈ V.1.U) : g • y ∈ V.1.U := by
  have h := V.1.mapsTo_Φ (isoOf hfix g) hy
  rwa [natRep_Φ_eq V.1.rep _ (V.1.U_subset hy)] at h

include hfix in
theorem smul_U (g : Ψ.1.G) : g • V.1.U = V.1.U := by
  refine Subset.antisymm ?_ fun y hy => ⟨g⁻¹ • y, V.smul_mem hfix g⁻¹ hy, smul_inv_smul g y⟩
  rintro _ ⟨y, hy, rfl⟩
  exact V.smul_mem hfix g hy

include hfix in
/-- **`G` permutes the faces of `U(ō)`** (2021 p. 792). -/
theorem smul_mem_faces (g : Ψ.1.G) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) : g • θ ∈ V.faces := by
  have h := (isDHomeoOn_smul Ψ g).isFaceIn_image (subset_univ _) hθ
  rw [Set.image_smul, Set.image_smul, V.smul_U hfix] at h
  exact h

/-- **The action `G × F_{U(ō)} → F_{U(ō)} : (g, θ) ↦ g(θ)`** (2021 p. 792). -/
abbrev faceAction : MulAction Ψ.1.G V.faces where
  smul g θ := ⟨g • θ.1, V.smul_mem_faces hfix g θ.2⟩
  one_smul θ := Subtype.ext (one_smul _ θ.1)
  mul_smul g h θ := Subtype.ext (mul_smul g h θ.1)

end GoodNbhd

variable (Ψ) in
/-- **2021 Definition 17.4.5, p. 792**: `G_θ`, the subgroup of `G` fixing the face `θ`. -/
def faceStabilizer (θ : Set Ψ.1.O) : Subgroup Ψ.1.G := MulAction.stabilizer Ψ.1.G θ

theorem mem_faceStabilizer {θ : Set Ψ.1.O} {g : Ψ.1.G} : g ∈ faceStabilizer Ψ θ ↔ g • θ = θ :=
  MulAction.mem_stabilizer_iff

/-- **2021 Definition 17.4.5**: `G_θ` is the stabilizer of `θ` for the action of `G` on
`F_{U(ō)}`. -/
theorem definition_17_4_5 (V : S.GoodNbhd Ψ o) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    (faceStabilizer Ψ θ : Set Ψ.1.G) =
      @MulAction.stabilizer Ψ.1.G V.faces _ (V.faceAction hfix) ⟨θ, hθ⟩ := by
  ext g
  change g • θ = θ ↔ (⟨g • θ, _⟩ : V.faces) = ⟨θ, hθ⟩
  rw [Subtype.ext_iff]

/-- `g ∈ G_θ` maps `θ` to itself. -/
theorem smul_mem_of_mem_faceStabilizer {θ : Set Ψ.1.O} (g : faceStabilizer Ψ θ) {x : Ψ.1.O}
    (hx : x ∈ θ) : (g : Ψ.1.G) • x ∈ θ := by
  have h : (g : Ψ.1.G) • θ = θ := mem_faceStabilizer.1 g.2
  exact h.subset (smul_mem_smul_set hx)

/-- `G_θ` acts on `θ`. -/
instance faceStabilizerAction (θ : Set Ψ.1.O) : MulAction (faceStabilizer Ψ θ) θ where
  smul g x := ⟨(g : Ψ.1.G) • x.1, smul_mem_of_mem_faceStabilizer g x.2⟩
  one_smul x := Subtype.ext (one_smul _ x.1)
  mul_smul g h x := Subtype.ext (mul_smul (g : Ψ.1.G) h x.1)

@[simp] theorem coe_faceStabilizer_smul {θ : Set Ψ.1.O} (g : faceStabilizer Ψ θ) (x : θ) :
    ((g • x : θ) : Ψ.1.O) = (g : Ψ.1.G) • (x : Ψ.1.O) := rfl

end Faces

/-! ### The local sc-diffeomorphism of `Ψ̂(g, x)` -/

section Hat

variable {hT : S.IsTame} {Ψ : S.Unif}

/-- **Under continuity of `Ψ̂`, the local sc-diffeomorphism of `Ψ̂(g, x) = (x, Ψ(g, x), g ∗ x)` is
`g ∗ ·` near `x`** (Lemma 17.1.9: `Ψ̂({g} × O)` is the sheet on which `s` is an
sc-diffeomorphism). -/
theorem germMap_hat_eventuallyEq (hc : Continuous (S.hat Ψ)) (g : Ψ.1.G) (x : Ψ.1.O)
    (T : S.AdmissibleTriple (S.hat Ψ (g, x))) : T.germMap =ᶠ[𝓝 x] fun y => g • y := by
  have h := T.eventuallyEq_srcInv (F := fun y => S.hat Ψ (g, y)) isOpen_univ (mem_univ x)
    (hc.comp (continuous_const.prodMk continuous_id)).continuousOn (fun y _ => rfl) T.mem_carrier
  filter_upwards [h] with y hy
  change (T.srcInv y).tgt = g • y
  rw [← hy]
  rfl

/-- `Ψ̂(g, x)` carries `p` to `q` iff `g ∗ ·` does. -/
theorem germLift_hat_iff (hc : Continuous (S.hat Ψ)) (g : Ψ.1.G) {x : Ψ.1.O} {p q : S.bO hT Ψ}
    (hp : bMap (S.hdU hT Ψ) p = x) :
    S.GermLift hT (S.hat Ψ (g, x)) p q ↔
      IsLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ) (fun y => g • y) p q := by
  constructor
  · rintro ⟨-, T, hl⟩
    obtain ⟨q', hq'⟩ := exists_isLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ) (isDHomeoOn_smul Ψ g)
      (mem_univ (bMap (S.hdU hT Ψ) p))
    rw [hl.unique hq' (by rw [hp]; exact germMap_hat_eventuallyEq hc g x T)]
    exact hq'
  · intro hl
    let T := (S.exists_admissibleTriple (S.hat Ψ (g, x))).some
    have hm : bMap (S.hdU hT Ψ) p ∈ T.srcSet := by rw [hp]; exact T.src_mem
    obtain ⟨q', hq'⟩ := exists_isLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ) T.isDHomeoOn_germMap hm
    refine ⟨hp, T, ?_⟩
    rw [hq'.unique hl (by rw [hp]; exact germMap_hat_eventuallyEq hc g x T)] at hq'
    exact hq'

end Hat

/-! ### Objects of `bC` over the points of a uniformizer -/

section Points

variable {hT : S.IsTame} {hS : S.HasUniformizers}

variable (hS) in
/-- `(x, 1_{Ψ(x)}, ō_ref) ∈ M(Ψ, bdryRefUnif Ψ(x))`. -/
noncomputable def ptTr (Ψ : S.Unif) (x : Ψ.1.O) : S.Tr Ψ (S.bdryRefUnif hS (Ψ.1.obj x)) :=
  ⟨x, C.toGroupoidStr.unit (Ψ.1.obj x), S.refPt hS _, C.toGroupoidStr.src_unit _,
    (C.toGroupoidStr.tgt_unit _).trans (obj_refPt hS _).symm⟩

variable (hT hS) in
/-- **A face germ `p` at `x ∈ ∂O` as an object of `bC`** over `Ψ(x)` (the class
`[Ψ(x), Ψ'', U''(ō''), θ'']` of (17.64), `ptObj_eq_toBObj`). -/
noncomputable def ptObj {Ψ : S.Unif} (p : S.bO hT Ψ) : S.BObj hT hS :=
  ⟨Ψ.1.obj (bMap _ p), germPush (S.ptTr hS Ψ (bMap _ p)) p rfl,
    (germLift_germPush (S.ptTr hS Ψ (bMap _ p)) p rfl).bMap_tgt⟩

variable {Ψ Ψ' : S.Unif}

@[simp] theorem ptObj_α (p : S.bO hT Ψ) : (S.ptObj hT hS p).α = Ψ.1.obj (bMap _ p) := rfl

theorem germLift_ptObj (p : S.bO hT Ψ) :
    S.GermLift hT (S.ptTr hS Ψ (bMap _ p)) p (S.ptObj hT hS p).p :=
  germLift_germPush _ _ rfl

/-- **A morphism `φ = h.mor` lifts to `ptObj p → ptObj p'` iff `h` carries `p` to `p'`.** -/
theorem bLift_ptObj_iff (h : S.Tr Ψ Ψ') {p : S.bO hT Ψ} {p' : S.bO hT Ψ'}
    (hp : bMap _ p = h.src) (hp' : bMap _ p' = h.tgt) :
    S.BLift (S.ptObj hT hS p) h.mor (S.ptObj hT hS p') ↔ S.GermLift hT h p p' := by
  have hs : C.toGroupoidStr.src h.mor = Ψ.1.obj (bMap _ p) := by rw [hp]; exact h.src_mor
  have ht : C.toGroupoidStr.tgt h.mor = Ψ'.1.obj (bMap _ p') := by rw [hp']; exact h.tgt_mor
  have h1 := germLift_ptObj (hS := hS) p
  have h2 := germLift_ptObj (hS := hS) p'
  constructor
  · rintro ⟨hs', ht', hl⟩
    have hab₁ : C.toGroupoidStr.src (S.bdryRefTr hS h.mor hs' ht').mor =
        C.toGroupoidStr.tgt (S.ptTr hS Ψ (bMap _ p)).mor := by
      change C.toGroupoidStr.src h.mor = C.toGroupoidStr.tgt (C.toGroupoidStr.unit _)
      rw [GroupoidStr.tgt_unit]; exact hs
    have k₁ := germLift_comp hab₁ rfl h1 hl
    have hab₂ : C.toGroupoidStr.src (S.toTr (GroupoidStr.TransitionSet.inv
        (S.ptTr hS Ψ' (bMap _ p'))) : S.Tr (S.bdryRefUnif hS (Ψ'.1.obj (bMap _ p'))) Ψ').mor =
        C.toGroupoidStr.tgt (S.toTr (GroupoidStr.TransitionSet.comp (S.bdryRefTr hS h.mor hs' ht')
          (S.ptTr hS Ψ (bMap _ p)) hab₁) :
            S.Tr Ψ (S.bdryRefUnif hS (Ψ'.1.obj (bMap _ p')))).mor := by
      change C.toGroupoidStr.src (C.toGroupoidStr.inv (C.toGroupoidStr.unit _)) =
        C.toGroupoidStr.tgt (C.toGroupoidStr.comp h.mor (C.toGroupoidStr.unit _))
      rw [GroupoidStr.src_inv, GroupoidStr.tgt_unit, C.toGroupoidStr.tgt_comp _ _ (by
        rw [GroupoidStr.tgt_unit]; exact hs), ht]
    have k₂ := germLift_comp hab₂ rfl k₁ (germLift_inv h2)
    have he : (S.toTr (GroupoidStr.TransitionSet.comp
        (S.toTr (GroupoidStr.TransitionSet.inv (S.ptTr hS Ψ' (bMap _ p'))) :
          S.Tr (S.bdryRefUnif hS (Ψ'.1.obj (bMap _ p'))) Ψ')
        (S.toTr (GroupoidStr.TransitionSet.comp (S.bdryRefTr hS h.mor hs' ht')
          (S.ptTr hS Ψ (bMap _ p)) hab₁) :
            S.Tr Ψ (S.bdryRefUnif hS (Ψ'.1.obj (bMap _ p')))) hab₂) : S.Tr Ψ Ψ') = h := by
      refine GroupoidStr.TransitionSet.ext hp ?_ hp'
      change C.toGroupoidStr.comp (C.toGroupoidStr.inv (C.toGroupoidStr.unit _))
        (C.toGroupoidStr.comp h.mor (C.toGroupoidStr.unit _)) = h.mor
      rw [GroupoidStr.inv_unit, GroupoidStr.comp_unit_of_eq hs, GroupoidStr.unit_comp_of_eq ht]
    rw [he] at k₂
    exact k₂
  · intro hl
    refine ⟨hs, ht, ?_⟩
    have hab₁ : C.toGroupoidStr.src h.mor = C.toGroupoidStr.tgt
        (S.toTr (GroupoidStr.TransitionSet.inv (S.ptTr hS Ψ (bMap _ p))) :
          S.Tr (S.bdryRefUnif hS (Ψ.1.obj (bMap _ p))) Ψ).mor := by
      change C.toGroupoidStr.src h.mor = C.toGroupoidStr.tgt (C.toGroupoidStr.inv
        (C.toGroupoidStr.unit _))
      rw [GroupoidStr.tgt_inv, GroupoidStr.src_unit]; exact hs
    have k₁ := germLift_comp hab₁ hp.symm (germLift_inv h1) hl
    have hab₂ : C.toGroupoidStr.src (S.ptTr hS Ψ' (bMap _ p')).mor = C.toGroupoidStr.tgt (S.toTr
        (GroupoidStr.TransitionSet.comp h (S.toTr (GroupoidStr.TransitionSet.inv
          (S.ptTr hS Ψ (bMap _ p))) : S.Tr (S.bdryRefUnif hS (Ψ.1.obj (bMap _ p))) Ψ) hab₁) :
            S.Tr (S.bdryRefUnif hS (Ψ.1.obj (bMap _ p))) Ψ').mor := by
      change C.toGroupoidStr.src (C.toGroupoidStr.unit _) = C.toGroupoidStr.tgt
        (C.toGroupoidStr.comp h.mor (C.toGroupoidStr.inv (C.toGroupoidStr.unit _)))
      rw [GroupoidStr.src_unit, C.toGroupoidStr.tgt_comp _ _ (by
        rw [GroupoidStr.tgt_inv, GroupoidStr.src_unit]; exact hs), ht]
    have k₂ := germLift_comp hab₂ hp' k₁ h2
    have he : (S.toTr (GroupoidStr.TransitionSet.comp (S.ptTr hS Ψ' (bMap _ p')) (S.toTr
        (GroupoidStr.TransitionSet.comp h (S.toTr (GroupoidStr.TransitionSet.inv
          (S.ptTr hS Ψ (bMap _ p))) : S.Tr (S.bdryRefUnif hS (Ψ.1.obj (bMap _ p))) Ψ) hab₁) :
            S.Tr (S.bdryRefUnif hS (Ψ.1.obj (bMap _ p))) Ψ') hab₂) :
              S.Tr (S.bdryRefUnif hS (Ψ.1.obj (bMap _ p))) (S.bdryRefUnif hS (Ψ'.1.obj (bMap _ p')))) =
          S.bdryRefTr hS h.mor hs ht := by
      refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
      change C.toGroupoidStr.comp (C.toGroupoidStr.unit _)
        (C.toGroupoidStr.comp h.mor (C.toGroupoidStr.inv (C.toGroupoidStr.unit _))) = h.mor
      rw [GroupoidStr.inv_unit, GroupoidStr.comp_unit_of_eq hs, GroupoidStr.unit_comp_of_eq ht]
    rw [he] at k₂
    exact k₂

/-- The morphism `(ptObj p, h.mor, ptObj p')` of `bC` for `h` carrying `p` to `p'`. -/
noncomputable def ptMor (h : S.Tr Ψ Ψ') {p : S.bO hT Ψ} {p' : S.bO hT Ψ'} (hl : S.GermLift hT h p p') :
    S.BMor hT hS :=
  ⟨S.ptObj hT hS p, h.mor, S.ptObj hT hS p', (bLift_ptObj_iff h hl.bMap_src hl.bMap_tgt).2 hl⟩

/-- `ptObj` is injective. -/
theorem ptObj_injective : Injective (S.ptObj (Ψ := Ψ) hT hS) := by
  intro p p' he
  have hb : Ψ.1.obj (bMap _ p) = Ψ.1.obj (bMap _ p') := congrArg BObj.α he
  have hx : bMap (S.hdU hT Ψ) p = bMap _ p' := Ψ.1.injective_obj hb
  have hl := (bLift_ptObj_iff (S.toTr (GroupoidStr.TransitionSet.unit (bMap _ p')) : S.Tr Ψ Ψ)
    (hS := hS) hx rfl).1 (by rw [he]; exact BLift.unit _)
  exact germLift_unique (germLift_unit hx) hl

end Points

/-! ### Face germs of the faces of `U(ō)` -/

section FaceGerms

variable (hT : S.IsTame) {Ψ : S.Unif} {o : Ψ.1.O}

namespace GoodNbhd

variable (V : S.GoodNbhd Ψ o)

/-- `Φ_{(ō, U(ō), θ)} : U(ō, U(ō), θ) → θ` is bijective (`U(ō)` is centred at `ō`). -/
theorem phi_bijective {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    Bijective (phi (S.hdU hT Ψ) (V.triple hT hθ)) :=
  phi_bijective_of_isCenteredAt (S.hdU hT Ψ) (t := V.triple hT hθ) V.isCenteredAt

/-- **The face germ of `θ` at `x ∈ θ`**: `Φ_{(ō, U(ō), θ)}⁻¹(x)`, the class of the face of a small
neighbourhood of `x` contained in `θ`. -/
noncomputable def faceGerm {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (x : Ψ.1.O) (hx : x ∈ θ) :
    S.bO hT Ψ :=
  ((Equiv.ofBijective _ (V.phi_bijective hT hθ)).symm ⟨x, hx⟩).1

variable {hT}

theorem faceGerm_mem_uSet {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (x : Ψ.1.O) (hx : x ∈ θ) :
    V.faceGerm hT hθ x hx ∈ uSet (S.hdU hT Ψ) (V.triple hT hθ) :=
  ((Equiv.ofBijective _ (V.phi_bijective hT hθ)).symm ⟨x, hx⟩).2

@[simp] theorem bMap_faceGerm {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (x : Ψ.1.O) (hx : x ∈ θ) :
    bMap (S.hdU hT Ψ) (V.faceGerm hT hθ x hx) = x :=
  congrArg Subtype.val ((Equiv.ofBijective _ (V.phi_bijective hT hθ)).apply_symm_apply ⟨x, hx⟩)

theorem faceGerm_eq_of_mem {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) {x : Ψ.1.O} (hx : x ∈ θ)
    {q : S.bO hT Ψ} (hq : q ∈ uSet (S.hdU hT Ψ) (V.triple hT hθ)) (hb : bMap _ q = x) :
    V.faceGerm hT hθ x hx = q :=
  bMap_injOn_uSet (S.hdU hT Ψ) _ (V.faceGerm_mem_uSet hθ x hx) hq (by rw [hb, bMap_faceGerm])

/-- At `ō` the face germ of `θ` is `[ō, U(ō), θ]`. -/
theorem faceGerm_self {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    V.faceGerm hT hθ o (V.mem_of_mem_faces hθ) = V.germ hT hθ :=
  V.faceGerm_eq_of_mem hθ _ (cls_mem_uSet (S.hdU hT Ψ) _) rfl

theorem faceGerm_congr {θ θ' : Set Ψ.1.O} (h : θ = θ') (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V.faces)
    {x : Ψ.1.O} (hx : x ∈ θ) (hx' : x ∈ θ') : V.faceGerm hT hθ x hx = V.faceGerm hT hθ' x hx' := by
  subst h; rfl

/-- **Distinct faces of `U(ō)` through `x` have distinct germs at `x`.** -/
theorem eq_of_faceGerm_eq {θ θ' : Set Ψ.1.O} {hθ : θ ∈ V.faces} {hθ' : θ' ∈ V.faces}
    {x : Ψ.1.O} {hx : x ∈ θ} {hx' : x ∈ θ'}
    (h : V.faceGerm hT hθ x hx = V.faceGerm hT hθ' x hx') : θ = θ' :=
  eq_of_mem_uSet (S.hdU hT Ψ) (t₁ := V.triple hT hθ) (t₂ := V.triple hT hθ') rfl
    (V.faceGerm_mem_uSet hθ x hx) (h ▸ V.faceGerm_mem_uSet hθ' x hx')

/-- **Every face germ at `x ∈ U(ō) ∩ ∂O` is the germ of a face of `U(ō)` through `x`.** -/
theorem exists_faceGerm_eq (q : S.bO hT Ψ) (hq : bMap _ q ∈ V.1.U) :
    ∃ (θ : Set Ψ.1.O) (hθ : θ ∈ V.faces) (hx : bMap _ q ∈ θ), V.faceGerm hT hθ _ hx = q := by
  obtain ⟨⟨θ, hθ⟩, hm⟩ := exists_mem_uSet_tripleOf (S.hdU hT Ψ) V.mem_faceStructuredNbhdsAt
    V.isCenteredAt hq
  have hθ' : θ ∈ V.faces := hθ.1
  refine ⟨θ, hθ', bMap_mem_of_mem_uSet (S.hdU hT Ψ) hm, ?_⟩
  exact V.faceGerm_eq_of_mem hθ' _ hm rfl

variable (hfix : Ψ.1.FixesPoint o)

include hfix in
/-- **`g ∗ ·` carries the germ of `θ` at `x` to the germ of `g(θ)` at `g ∗ x`.** -/
theorem isLiftOf_smul_faceGerm {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (g : Ψ.1.G) {x : Ψ.1.O}
    (hx : x ∈ θ) :
    IsLiftOf (S.hdU hT Ψ) (S.hdU hT Ψ) (fun y => g • y) (V.faceGerm hT hθ x hx)
      (V.faceGerm hT (V.smul_mem_faces hfix g hθ) (g • x) (smul_mem_smul_set hx)) := by
  obtain ⟨s, hs, hsx, hsm, hse⟩ := V.faceGerm_mem_uSet hθ x hx
  have hf := isDHomeoOn_smul Ψ g
  have hU : (fun y => g • y) '' V.1.U = V.1.U := V.smul_U hfix g
  have hx' : s.x = x := by
    have := V.bMap_faceGerm (hT := hT) hθ x hx
    rw [← hs] at this
    exact this
  refine ⟨univ, hf, s, subset_univ _, hs, ?_⟩
  symm
  refine V.faceGerm_eq_of_mem _ _ ⟨s.map _ hf (subset_univ _), rfl, ?_, ?_, ?_⟩ ?_
  · exact smul_mem_smul_set hsx
  · have h := hf.isMor_image (subset_univ _) s.mem.2.1 hsm
    change IsMor _ (g • s.x) ((fun y => g • y) '' s.V) (g • o) ((fun y => g • y) '' V.1.U) at h
    rw [hU, hfix g] at h
    exact h
  · have h := hf.image_faceExt (S.hdU hT Ψ) (S.hdU hT Ψ) V.isOpen (subset_univ _) hsm.1
      s.mem_faces.1
    change (fun y => g • y) '' faceExt _ V.1.U s.θ =
      faceExt _ ((fun y => g • y) '' V.1.U) ((fun y => g • y) '' s.θ) at h
    have hse' : faceExt Ψ.1.P.degIndex V.1.U s.θ = θ := hse
    rw [hse', hU] at h
    change faceExt _ V.1.U ((fun y => g • y) '' s.θ) = (fun y => g • y) '' θ
    exact h.symm
  · change g • s.x = g • x
    rw [hx']

end GoodNbhd

end FaceGerms

/-! ### (17.64), (17.65): the functors `Ψ_θ` and `Ψ̄` -/

section FaceFunctor

variable {hT : S.IsTame} {hS : S.HasUniformizers} {Ψ : S.Unif} {o : Ψ.1.O}

namespace GoodNbhd

variable (V : S.GoodNbhd Ψ o)

variable (hT hS) in
/-- **2021 (17.64)**: `Ψ_θ(x)`, the object of `bC` over `Ψ(x)` given by the face germ of `θ` at
`x`. -/
noncomputable def faceObj {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (x : Ψ.1.O) (hx : x ∈ θ) :
    S.BObj hT hS :=
  S.ptObj hT hS (V.faceGerm hT hθ x hx)

@[simp] theorem faceObj_α {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (x : Ψ.1.O) (hx : x ∈ θ) :
    (V.faceObj hT hS hθ x hx).α = Ψ.1.obj x := by
  change Ψ.1.obj (bMap _ _) = _
  rw [bMap_faceGerm]

theorem faceObj_congr {θ θ' : Set Ψ.1.O} (h : θ = θ') (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V.faces)
    {x : Ψ.1.O} (hx : x ∈ θ) (hx' : x ∈ θ') :
    V.faceObj hT hS hθ x hx = V.faceObj hT hS hθ' x hx' := by
  subst h; rfl

/-- `Ψ̄` (17.65) is injective on objects: `Ψ_θ(x) = Ψ_{θ'}(x')` forces `x = x'` and `θ = θ'`. -/
theorem faceObj_inj {θ θ' : Set Ψ.1.O} {hθ : θ ∈ V.faces} {hθ' : θ' ∈ V.faces} {x x' : Ψ.1.O}
    {hx : x ∈ θ} {hx' : x' ∈ θ'} (h : V.faceObj hT hS hθ x hx = V.faceObj hT hS hθ' x' hx') :
    x = x' ∧ θ = θ' := by
  have hg := ptObj_injective h
  have hxx : x = x' := by
    have := congrArg (bMap (S.hdU hT Ψ)) hg
    rwa [bMap_faceGerm, bMap_faceGerm] at this
  subst hxx
  exact ⟨rfl, V.eq_of_faceGerm_eq hg⟩

variable (hc : S.HatContinuous) (hfix : Ψ.1.FixesPoint o)

include hc hfix in
theorem germLift_hat_faceGerm {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (g : Ψ.1.G) {x : Ψ.1.O}
    (hx : x ∈ θ) :
    S.GermLift hT (S.hat Ψ (g, x)) (V.faceGerm hT hθ x hx)
      (V.faceGerm hT (V.smul_mem_faces hfix g hθ) (g • x) (smul_mem_smul_set hx)) :=
  (germLift_hat_iff (hc Ψ) g (V.bMap_faceGerm hθ x hx)).2 (V.isLiftOf_smul_faceGerm hfix hθ g hx)

variable (hT hS) in
/-- **The morphism `Ψ̄(g, (x, θ)) = (Ψ_θ(x), Ψ(g, x), Ψ_{g(θ)}(g ∗ x))`** of `bC` (17.65). -/
noncomputable def smulMor {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (g : Ψ.1.G) (x : Ψ.1.O)
    (hx : x ∈ θ) : S.BMor hT hS :=
  ptMor (S.hat Ψ (g, x)) (V.germLift_hat_faceGerm hc hfix hθ g hx)

@[simp] theorem smulMor_src {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (g : Ψ.1.G) (x : Ψ.1.O)
    (hx : x ∈ θ) : (V.smulMor hT hS hc hfix hθ g x hx).src = V.faceObj hT hS hθ x hx := rfl

@[simp] theorem smulMor_tgt {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (g : Ψ.1.G) (x : Ψ.1.O)
    (hx : x ∈ θ) : (V.smulMor hT hS hc hfix hθ g x hx).tgt =
      V.faceObj hT hS (V.smul_mem_faces hfix g hθ) (g • x) (smul_mem_smul_set hx) := rfl

@[simp] theorem smulMor_mor {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (g : Ψ.1.G) (x : Ψ.1.O)
    (hx : x ∈ θ) : (V.smulMor hT hS hc hfix hθ g x hx).mor = Ψ.1.mor (g, x) := rfl

include hc hfix in
/-- **A morphism `Ψ_θ(x) → Ψ_{θ'}(x')` of `bC` is `Ψ̄(g, (x, θ))` with `g ∗ x = x'` and
`g(θ) = θ'`** (the core of the proofs of Lemmas 17.4.6, 17.4.8, 17.4.9). -/
theorem exists_smul_of_bLift {θ θ' : Set Ψ.1.O} {hθ : θ ∈ V.faces} {hθ' : θ' ∈ V.faces}
    {x x' : Ψ.1.O} {hx : x ∈ θ} {hx' : x' ∈ θ'} {φ : C.Mor}
    (h : S.BLift (V.faceObj hT hS hθ x hx) φ (V.faceObj hT hS hθ' x' hx')) :
    ∃ g : Ψ.1.G, g • x = x' ∧ Ψ.1.mor (g, x) = φ ∧ g • θ = θ' := by
  have hs : C.toGroupoidStr.src φ = Ψ.1.obj x := h.src_eq.trans (V.faceObj_α hθ x hx)
  have ht : C.toGroupoidStr.tgt φ = Ψ.1.obj x' := h.tgt_eq.trans (V.faceObj_α hθ' x' hx')
  obtain ⟨g, hgx, hgm⟩ := Ψ.1.toUniformizer.exists_smul_eq_mor hs ht
  refine ⟨g, hgx, hgm, ?_⟩
  subst hgx hgm
  have hl := (bLift_ptObj_iff (S.hat Ψ (g, x)) (V.bMap_faceGerm hθ x hx)
    (V.bMap_faceGerm hθ' _ hx')).1 h
  exact (V.eq_of_faceGerm_eq (germLift_unique (V.germLift_hat_faceGerm hc hfix hθ g hx) hl))

variable (hT hS) in
/-- **`Ψ_θ(g, x) = (Ψ_θ(x), Ψ(g, x), Ψ_θ(g ∗ x))`** for `g ∈ G_θ` (p. 792). -/
noncomputable def faceMor {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) (g : faceStabilizer Ψ θ)
    (x : Ψ.1.O) (hx : x ∈ θ) : S.BMor hT hS :=
  ⟨V.faceObj hT hS hθ x hx, Ψ.1.mor (g, x),
    V.faceObj hT hS hθ ((g : Ψ.1.G) • x) (smul_mem_of_mem_faceStabilizer g hx), by
      have h : S.BLift (V.faceObj hT hS hθ x hx) (Ψ.1.mor (g, x))
          (V.faceObj hT hS (V.smul_mem_faces hfix g hθ) ((g : Ψ.1.G) • x)
            (smul_mem_smul_set hx)) := (V.smulMor hT hS hc hfix hθ g x hx).lifts
      rwa [V.faceObj_congr (mem_faceStabilizer.1 g.2)] at h⟩

variable (hT hS) in
/-- **The functor `Ψ_θ : G_θ ⋉ θ → bC`** (2021 p. 792). -/
noncomputable def faceFunctor {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    GroupoidFunctor (GroupoidStr.translation (faceStabilizer Ψ θ) θ) (S.bdryGroupoid hT hS) where
  obj x := V.faceObj hT hS hθ x.1 x.2
  mor m := V.faceMor hT hS hc hfix hθ m.1 m.2.1 m.2.2
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp a b h := by
    have h' : (V.faceMor hT hS hc hfix hθ a.1 a.2.1 a.2.2).src =
        (V.faceMor hT hS hc hfix hθ b.1 b.2.1 b.2.2).tgt := by
      change V.faceObj hT hS hθ a.2.1 a.2.2 = V.faceObj hT hS hθ ((b.1 : Ψ.1.G) • b.2.1) _
      have h'' : a.2.1 = (b.1 : Ψ.1.G) • b.2.1 := congrArg Subtype.val h
      simp only [h'']
    change _ = BMor.comp _ _
    rw [BMor.comp_of_eq h']
    refine BMor.ext_of_src rfl ?_
    exact Ψ.1.functor.mor_comp ((a.1 : Ψ.1.G), a.2.1) ((b.1 : Ψ.1.G), b.2.1)
      (congrArg Subtype.val h)
  mor_unit x := by
    refine BMor.ext_of_src rfl ?_
    change Ψ.1.mor (1, x.1) = C.toGroupoidStr.unit (V.faceObj hT hS hθ x.1 x.2).α
    rw [V.faceObj_α]
    exact Ψ.1.functor.mor_unit x.1

/-- **2021 Lemma 17.4.6, p. 792**: `Ψ_θ : G_θ ⋉ θ → bC` is injective on objects and fully
faithful. -/
theorem lemma_17_4_6 {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    Injective (V.faceFunctor hT hS hc hfix hθ).obj ∧ (V.faceFunctor hT hS hc hfix hθ).toFunctor.Full ∧
      (V.faceFunctor hT hS hc hfix hθ).toFunctor.Faithful := by
  refine ⟨fun x x' h => Subtype.ext (V.faceObj_inj h).1, ?_, ?_⟩
  · refine (GroupoidFunctor.full_iff _).2 fun x x' Φ hs ht => ?_
    have hl : S.BLift (V.faceObj hT hS hθ x.1 x.2) Φ.mor (V.faceObj hT hS hθ x'.1 x'.2) := by
      have := Φ.lifts
      rw [show Φ.src = _ from hs, show Φ.tgt = _ from ht] at this
      exact this
    obtain ⟨g, hgx, hgm, hgθ⟩ := V.exists_smul_of_bLift hc hfix hl
    refine ⟨(⟨g, mem_faceStabilizer.2 hgθ⟩, x), rfl, Subtype.ext hgx, ?_⟩
    exact BMor.ext_of_src hs.symm hgm
  · refine (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ hm => ?_
    have h := Ψ.1.toUniformizer.mor_injective (congrArg BMor.mor hm)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) hs

variable (hT hS) in
/-- `|Ψ_θ(θ)| ⊆ |bC|`. -/
def faceImage {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) : Set (S.bdryGroupoid hT hS).OrbitSpace :=
  {z | ∃ x, ∃ hx : x ∈ θ, (S.bdryGroupoid hT hS).π (V.faceObj hT hS hθ x hx) = z}

include hc hfix in
theorem faceImage_subset {θ θ' : Set Ψ.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V.faces) {g : Ψ.1.G}
    (hg : g • θ = θ') : V.faceImage hT hS hθ ⊆ V.faceImage hT hS hθ' := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : g • x ∈ θ' := by rw [← hg]; exact smul_mem_smul_set hx
  refine ⟨g • x, hx', (((S.bdryGroupoid hT hS).π_eq_π_iff).2
    ⟨V.smulMor hT hS hc hfix hθ g x hx, rfl, ?_⟩).symm⟩
  exact V.faceObj_congr hg _ _ _ _

include hc hfix in
/-- **2021 Lemma 17.4.8, p. 795**: for faces `θ, θ'` of `U(ō)`, either `|Ψ_θ(θ)| = |Ψ_{θ'}(θ')|`
or the two sets are disjoint; they agree iff `g(θ) = θ'` for some `g ∈ G`. -/
theorem lemma_17_4_8 {θ θ' : Set Ψ.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V.faces) :
    (V.faceImage hT hS hθ = V.faceImage hT hS hθ' ∨
      Disjoint (V.faceImage hT hS hθ) (V.faceImage hT hS hθ')) ∧
    (V.faceImage hT hS hθ = V.faceImage hT hS hθ' ↔ ∃ g : Ψ.1.G, g • θ = θ') := by
  have key : (V.faceImage hT hS hθ ∩ V.faceImage hT hS hθ').Nonempty →
      ∃ g : Ψ.1.G, g • θ = θ' := by
    rintro ⟨_, ⟨x, hx, rfl⟩, ⟨x', hx', he⟩⟩
    obtain ⟨Φ, hs, ht⟩ := ((S.bdryGroupoid hT hS).π_eq_π_iff).1 he.symm
    have hl : S.BLift (V.faceObj hT hS hθ x hx) Φ.mor (V.faceObj hT hS hθ' x' hx') := by
      have := Φ.lifts
      rw [show Φ.src = _ from hs, show Φ.tgt = _ from ht] at this
      exact this
    obtain ⟨g, -, -, hg⟩ := V.exists_smul_of_bLift hc hfix hl
    exact ⟨g, hg⟩
  have hiff : V.faceImage hT hS hθ = V.faceImage hT hS hθ' ↔ ∃ g : Ψ.1.G, g • θ = θ' := by
    constructor
    · intro he
      have hx := V.mem_of_mem_faces hθ
      refine key ⟨_, ⟨o, hx, rfl⟩, ?_⟩
      rw [← he]
      exact ⟨o, hx, rfl⟩
    · rintro ⟨g, hg⟩
      refine Subset.antisymm (V.faceImage_subset hc hfix hθ hθ' hg)
        (V.faceImage_subset hc hfix hθ' hθ (g := g⁻¹) ?_)
      rw [← hg, inv_smul_smul]
  refine ⟨?_, hiff⟩
  by_cases h : (V.faceImage hT hS hθ ∩ V.faceImage hT hS hθ').Nonempty
  · exact Or.inl (hiff.2 (key h))
  · exact Or.inr (Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 h))

/-! ### (17.65), Lemma 17.4.9 and (17.67)–(17.69): the functor `Ψ̄` on `G ⋉ ⊔_θ θ` -/

/-- The objects `(x, θ)`, `x ∈ θ ∈ F_{U(ō)}`, of `G ⋉ ⊔_{θ ∈ F_{U(ō)}} θ` (17.65). -/
def FacePt : Type u := {q : Ψ.1.O × Set Ψ.1.O // q.2 ∈ V.faces ∧ q.1 ∈ q.2}

variable (hT hS) in
/-- **`Ψ̄(x, θ) = Ψ_θ(x)`** (17.65). -/
noncomputable def barObj (q : V.FacePt) : S.BObj hT hS := V.faceObj hT hS q.2.1 q.1.1 q.2.2

theorem faceObj_congr₂ {θ θ' : Set Ψ.1.O} (h : θ = θ') {x x' : Ψ.1.O} (hxx : x = x')
    (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V.faces) (hx : x ∈ θ) (hx' : x' ∈ θ') :
    V.faceObj hT hS hθ x hx = V.faceObj hT hS hθ' x' hx' := by
  subst h hxx; rfl

/-- **2021 Lemma 17.4.9, p. 795**: `Ψ̄` is injective on objects, faithful
(`Ψ̄(g₁, (x, θ)) = Ψ̄(g₂, (x, θ))` forces `g₁ = g₂`) and full (every morphism
`Ψ̄(x, θ) → Ψ̄(x', θ')` is `Ψ̄(g, (x, θ))` with `g ∗ x = x'`, `g(θ) = θ'`). -/
theorem lemma_17_4_9 :
    Injective (V.barObj hT hS) ∧
    (∀ (q : V.FacePt) (g₁ g₂ : Ψ.1.G), (V.smulMor hT hS hc hfix q.2.1 g₁ q.1.1 q.2.2).mor =
      (V.smulMor hT hS hc hfix q.2.1 g₂ q.1.1 q.2.2).mor → g₁ = g₂) ∧
    ∀ (q q' : V.FacePt) (Φ : S.BMor hT hS), Φ.src = V.barObj hT hS q →
      Φ.tgt = V.barObj hT hS q' → ∃ g : Ψ.1.G, g • q.1.1 = q'.1.1 ∧ g • q.1.2 = q'.1.2 ∧
        Φ = V.smulMor hT hS hc hfix q.2.1 g q.1.1 q.2.2 := by
  refine ⟨fun q q' h => ?_, fun q g₁ g₂ h => ?_, fun q q' Φ hs ht => ?_⟩
  · obtain ⟨h1, h2⟩ := V.faceObj_inj h
    exact Subtype.ext (Prod.ext h1 h2)
  · exact congrArg Prod.fst (Ψ.1.toUniformizer.mor_injective h)
  · have hl : S.BLift (V.barObj hT hS q) Φ.mor (V.barObj hT hS q') := by
      have := Φ.lifts
      rw [hs, ht] at this
      exact this
    obtain ⟨g, hgx, hgm, hgθ⟩ := V.exists_smul_of_bLift hc hfix hl
    exact ⟨g, hgx, hgθ, BMor.ext_of_src hs hgm.symm⟩

/-- `(x, θ) ∼ (x', θ')` iff `g ∗ (x, θ) = (x', θ')` for some `g ∈ G`: the orbits of `G` on
`⊔_θ θ`. -/
def barSetoid : Setoid V.FacePt where
  r q q' := ∃ g : Ψ.1.G, g • q.1.1 = q'.1.1 ∧ g • q.1.2 = q'.1.2
  iseqv := ⟨fun _ => ⟨1, one_smul _ _, one_smul _ _⟩,
    fun ⟨g, h1, h2⟩ => ⟨g⁻¹, by rw [← h1, inv_smul_smul], by rw [← h2, inv_smul_smul]⟩,
    fun ⟨g, h1, h2⟩ ⟨g', h1', h2'⟩ => ⟨g' * g, by rw [mul_smul, h1, h1'],
      by rw [mul_smul, h2, h2']⟩⟩

/-- On one face the orbits are those of `G_θ`, so `G \ ⊔_θ θ = ⊔_i |θ_i|` (2021 p. 796). -/
theorem barSetoid_r_iff_of_eq {q q' : V.FacePt} (h : q.1.2 = q'.1.2) :
    (V.barSetoid).r q q' ↔ ∃ g ∈ faceStabilizer Ψ q.1.2, g • q.1.1 = q'.1.1 :=
  ⟨fun ⟨g, h1, h2⟩ => ⟨g, mem_faceStabilizer.2 (h2.trans h.symm), h1⟩,
    fun ⟨g, hg, h1⟩ => ⟨g, h1, (mem_faceStabilizer.1 hg).trans h⟩⟩

variable (hT hS) in
/-- **The map `|Ψ̄| : G \ ⊔_θ θ → |bC|`** of (17.67). -/
noncomputable def barOrbitMap : Quotient V.barSetoid → (S.bdryGroupoid hT hS).OrbitSpace :=
  Quotient.lift (fun q => (S.bdryGroupoid hT hS).π (V.barObj hT hS q)) fun q _ ⟨g, h1, h2⟩ =>
    ((S.bdryGroupoid hT hS).π_eq_π_iff).2 ⟨V.smulMor hT hS hc hfix q.2.1 g q.1.1 q.2.2, rfl,
      V.faceObj_congr₂ h2 h1 _ _ _ _⟩

/-- **(17.67): `|Ψ̄|` is injective** (2021 p. 796, "the map `|Ψ̄|` in (17.67) is injective"). -/
theorem barOrbitMap_injective : Injective (V.barOrbitMap hT hS hc hfix) := by
  rintro ⟨q⟩ ⟨q'⟩ h
  obtain ⟨Φ, hs, ht⟩ := ((S.bdryGroupoid hT hS).π_eq_π_iff).1 h
  have hl : S.BLift (V.barObj hT hS q) Φ.mor (V.barObj hT hS q') := by
    have := Φ.lifts
    rw [show Φ.src = _ from hs, show Φ.tgt = _ from ht] at this
    exact this
  obtain ⟨g, hgx, -, hgθ⟩ := V.exists_smul_of_bLift hc hfix hl
  exact Quotient.sound ⟨g, hgx, hgθ⟩

end GoodNbhd

/-- **Every object of `bC` over `Ψ(y)` is `ptObj q` for a face germ `q` at `y`.** -/
theorem exists_ptObj_eq {Ψ : S.Unif} (a : S.BObj hT hS) {y : Ψ.1.O} (hy : a.α = Ψ.1.obj y) :
    ∃ q : S.bO hT Ψ, bMap _ q = y ∧ S.ptObj hT hS q = a := by
  let h : S.Tr (S.bdryRefUnif hS a.α) Ψ :=
    ⟨S.refPt hS a.α, C.toGroupoidStr.unit a.α, y,
      (C.toGroupoidStr.src_unit _).trans (obj_refPt hS a.α).symm,
      (C.toGroupoidStr.tgt_unit _).trans hy⟩
  have hl := germLift_germPush h a.p a.bMap_p
  set q := germPush h a.p a.bMap_p
  have hq : bMap (S.hdU hT Ψ) q = y := hl.bMap_tgt
  refine ⟨q, hq, ?_⟩
  have hα : C.toGroupoidStr.tgt (C.toGroupoidStr.unit a.α) = (S.ptObj hT hS q).α := by
    rw [GroupoidStr.tgt_unit, ptObj_α, hq]; exact hy
  have hab : C.toGroupoidStr.src (S.ptTr hS Ψ (bMap _ q)).mor = C.toGroupoidStr.tgt h.mor := by
    change C.toGroupoidStr.src (C.toGroupoidStr.unit _) =
      C.toGroupoidStr.tgt (C.toGroupoidStr.unit a.α)
    rw [GroupoidStr.src_unit, GroupoidStr.tgt_unit, hq]; exact hy.symm
  have k := germLift_comp hab hq (hl) (germLift_ptObj (hS := hS) q)
  have he : (S.toTr (GroupoidStr.TransitionSet.comp (S.ptTr hS Ψ (bMap _ q)) h hab) :
      S.Tr (S.bdryRefUnif hS a.α) (S.bdryRefUnif hS (S.ptObj hT hS q).α)) =
      S.bdryRefTr hS (C.toGroupoidStr.unit a.α) (C.toGroupoidStr.src_unit _) hα := by
    refine GroupoidStr.TransitionSet.ext rfl ?_ rfl
    change C.toGroupoidStr.comp (C.toGroupoidStr.unit _) (C.toGroupoidStr.unit a.α) =
      C.toGroupoidStr.unit a.α
    exact GroupoidStr.unit_comp_of_eq hα
  exact ((BLift.unit a).unique ⟨C.toGroupoidStr.src_unit _, hα, by rw [← he]; exact k⟩).symm

namespace GoodNbhd

variable (V : S.GoodNbhd Ψ o) (hc : S.HatContinuous) (hfix : Ψ.1.FixesPoint o)

/-- **2021 (17.68)**: `image |Ψ̄| = |B_C|⁻¹(|Ψ(U(ō))|)`, with `U(ō) = V(ō) ∩ ∂O`. -/
theorem display_17_68 :
    range (V.barOrbitMap hT hS hc hfix) = (S.bdryFunctorC hT hS).orbitMap ⁻¹'
      (C.toGroupoidStr.π '' (Ψ.1.obj '' V.bdry)) := by
  ext z
  constructor
  · rintro ⟨⟨q⟩, rfl⟩
    change (S.bdryFunctorC hT hS).orbitMap ((S.bdryGroupoid hT hS).π (V.barObj hT hS q)) ∈
      C.toGroupoidStr.π '' (Ψ.1.obj '' V.bdry)
    rw [GroupoidFunctor.orbitMap_π]
    refine ⟨Ψ.1.obj q.1.1, ⟨q.1.1, V.subset_bdry q.2.1 q.2.2, rfl⟩, ?_⟩
    rw [bdryFunctorC_obj]
    exact congrArg _ (V.faceObj_α _ _ _).symm
  · induction z using Quotient.inductionOn with
    | h a =>
    rintro ⟨_, ⟨y, hy, rfl⟩, he⟩
    change C.toGroupoidStr.π (Ψ.1.obj y) = (S.bdryFunctorC hT hS).orbitMap
      ((S.bdryGroupoid hT hS).π a) at he
    rw [GroupoidFunctor.orbitMap_π, bdryFunctorC_obj] at he
    obtain ⟨φ, hs, ht⟩ := (C.toGroupoidStr.π_eq_π_iff).1 he.symm
    obtain ⟨b, hb⟩ := BLift.exists_of_src_eq a hs
    have hbα : b.α = Ψ.1.obj y := hb.tgt_eq.symm.trans ht
    obtain ⟨q, hqy, hqb⟩ := exists_ptObj_eq b hbα
    obtain ⟨θ, hθ, hx, hq⟩ := V.exists_faceGerm_eq q (by rw [hqy]; exact hy.1)
    refine ⟨⟦⟨(bMap _ q, θ), hθ, hx⟩⟧, ?_⟩
    change (S.bdryGroupoid hT hS).π (S.ptObj hT hS (V.faceGerm hT hθ _ hx)) =
      (S.bdryGroupoid hT hS).π a
    rw [hq, hqb]
    exact (((S.bdryGroupoid hT hS).π_eq_π_iff).2 ⟨⟨a, φ, b, hb⟩, rfl, rfl⟩).symm

include hc hfix in
/-- **2021 (17.69)**: `|Ψ̄|` is a bijection of `G \ ⊔_θ θ = ⊔_i |θ_i|` (`barSetoid_r_iff_of_eq`)
onto `|B_C|⁻¹(|Ψ(U(ō))|)`. -/
theorem display_17_69 :
    ∃ e : Quotient V.barSetoid ≃ ((S.bdryFunctorC hT hS).orbitMap ⁻¹'
      (C.toGroupoidStr.π '' (Ψ.1.obj '' V.bdry))),
      ∀ q, (e ⟦q⟧ : (S.bdryGroupoid hT hS).OrbitSpace) =
        (S.bdryGroupoid hT hS).π (V.barObj hT hS q) := by
  have hm : ∀ w, V.barOrbitMap hT hS hc hfix w ∈ (S.bdryFunctorC hT hS).orbitMap ⁻¹'
      (C.toGroupoidStr.π '' (Ψ.1.obj '' V.bdry)) := fun w => by
    rw [← V.display_17_68 hc hfix]; exact mem_range_self w
  refine ⟨Equiv.ofBijective (fun w => ⟨_, hm w⟩) ⟨fun w w' h => V.barOrbitMap_injective hc hfix
    (congrArg Subtype.val h), fun z => ?_⟩, fun q => rfl⟩
  have hz : (z : (S.bdryGroupoid hT hS).OrbitSpace) ∈ range (V.barOrbitMap hT hS hc hfix) := by
    rw [V.display_17_68 hc hfix]; exact z.2
  obtain ⟨w, hw⟩ := hz
  exact ⟨w, Subtype.ext hw⟩

end GoodNbhd

end FaceFunctor

/-! ### (17.64) with the book's choices, Lemmas 17.4.10, 17.4.11 and Definition 17.4.12 -/

section Transitions

variable {hT : S.IsTame} {hS : S.HasUniformizers}

/-- A tuple of (17.57) is the object `ptObj` of its face germ. -/
theorem BdryTuple.toBObj_eq_ptObj (t : S.BdryTuple) :
    t.toBObj hT hS = S.ptObj hT hS (t.germ hT) := by
  obtain ⟨α, Ψ, mem, o, obj_o, V, θ, face⟩ := t
  subst obj_o
  rfl

namespace GoodNbhd

variable {Ψ Ψ' : S.Unif} {o : Ψ.1.O} {o' : Ψ'.1.O} (V : S.GoodNbhd Ψ o) (V' : S.GoodNbhd Ψ' o')

theorem faceGerm_congr_pt {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) {x x' : Ψ.1.O} (h : x = x')
    (hx : x ∈ θ) (hx' : x' ∈ θ) : V.faceGerm hT hθ x hx = V.faceGerm hT hθ x' hx' := by
  subst h; rfl

/-- **2021 (17.64) with the book's choices**: `Ψ_θ(x) = [Ψ(x), Ψ'', U''(ō''), θ'']` whenever the
local sc-diffeomorphism of `h = (x, 1_{Ψ(x)}, ō'') ∈ M(Ψ, Ψ'')` carries `θ` near `x` to `θ''` near
`ō''`. -/
theorem faceObj_eq_toBObj (t : S.BdryTuple) {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) {x : Ψ.1.O}
    (hx : x ∈ θ) (hα : Ψ.1.obj x = t.α)
    (hl : S.GermLift hT (⟨x, C.toGroupoidStr.unit (Ψ.1.obj x), t.o, C.toGroupoidStr.src_unit _,
      (C.toGroupoidStr.tgt_unit _).trans (hα.trans t.obj_o.symm)⟩ : S.Tr Ψ t.unif)
      (V.faceGerm hT hθ x hx) (t.germ hT)) :
    V.faceObj hT hS hθ x hx = t.toBObj hT hS := by
  rw [BdryTuple.toBObj_eq_ptObj]
  have hb := (bLift_ptObj_iff (hS := hS) _ (V.bMap_faceGerm hθ x hx) rfl).2 hl
  have hu := BLift.unit (S.ptObj hT hS (V.faceGerm hT hθ x hx))
  rw [ptObj_α, bMap_faceGerm] at hu
  exact hu.unique hb

/-- **2021 p. 792**: for `Ψ'' ∈ F(Ψ(x))` with `Ψ''(ō'') = Ψ(x)` and a good neighbourhood
`U''(ō'')`, `h = (x, 1_{Ψ(x)}, ō'')` establishes a correspondence between `θ` and a uniquely
determined face `θ''` of `U''(ō'')`, and `Ψ_θ(x) = [Ψ(x), Ψ'', U''(ō''), θ'']` (17.64). -/
theorem display_17_64 {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) {x : Ψ.1.O} (hx : x ∈ θ)
    {Ψ'' : C.LocalUniformizer} (hΨ'' : Ψ'' ∈ S.F (Ψ.1.obj x)) {o'' : Ψ''.O}
    (ho'' : Ψ''.obj o'' = Ψ.1.obj x) (V'' : S.GoodNbhd ⟨Ψ'', _, hΨ''⟩ o'') :
    ∃ (θ'' : Set Ψ''.O) (hθ'' : θ'' ∈ V''.faces),
      S.GermLift hT (⟨x, C.toGroupoidStr.unit (Ψ.1.obj x), o'', C.toGroupoidStr.src_unit _,
        (C.toGroupoidStr.tgt_unit _).trans ho''.symm⟩ : S.Tr Ψ ⟨Ψ'', _, hΨ''⟩)
        (V.faceGerm hT hθ x hx) (V''.germ hT hθ'') ∧
      (∀ (θ₁ : Set Ψ''.O) (hθ₁ : θ₁ ∈ V''.faces),
        S.GermLift hT (⟨x, C.toGroupoidStr.unit (Ψ.1.obj x), o'', C.toGroupoidStr.src_unit _,
          (C.toGroupoidStr.tgt_unit _).trans ho''.symm⟩ : S.Tr Ψ ⟨Ψ'', _, hΨ''⟩)
          (V.faceGerm hT hθ x hx) (V''.germ hT hθ₁) → θ₁ = θ'') ∧
      V.faceObj hT hS hθ x hx =
        (⟨Ψ.1.obj x, Ψ'', hΨ'', o'', ho'', V'', θ'', hθ''⟩ : S.BdryTuple).toBObj hT hS := by
  set h : S.Tr Ψ ⟨Ψ'', _, hΨ''⟩ := ⟨x, C.toGroupoidStr.unit (Ψ.1.obj x), o'',
    C.toGroupoidStr.src_unit _, (C.toGroupoidStr.tgt_unit _).trans ho''.symm⟩
  have hl := germLift_germPush h (V.faceGerm hT hθ x hx) (V.bMap_faceGerm hθ x hx)
  obtain ⟨θ'', hθ'', hq⟩ := V''.exists_germ_eq hT _ hl.bMap_tgt
  rw [← hq] at hl
  refine ⟨θ'', hθ'', hl, fun θ₁ hθ₁ hl' => V''.germ_injective hT hθ₁ hθ''
    (germLift_unique hl' hl), ?_⟩
  exact V.faceObj_eq_toBObj _ hθ hx rfl hl

variable (hT hS) in
/-- **`M(Ψ_θ, Ψ'_{θ'})`** (2021 p. 797): the tuples `(x, Φ, x')` with `x ∈ θ`, `x' ∈ θ'` and
`Φ : Ψ_θ(x) → Ψ'_{θ'}(x')` a morphism of `bC`. -/
abbrev FaceTr {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) :
    Type u :=
  (S.bdryGroupoid hT hS).TransitionSet (fun x : θ => V.faceObj hT hS hθ x.1 x.2)
    (fun x : θ' => V'.faceObj hT hS hθ' x.1 x.2)

/-- `h̄ = (x, Φ, x') ↦ h = (x, φ, x') ∈ M(Ψ, Ψ')`. -/
def faceTrToTr {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} {hθ : θ ∈ V.faces} {hθ' : θ' ∈ V'.faces}
    (h : V.FaceTr hT hS V' hθ hθ') : S.Tr Ψ Ψ' :=
  ⟨h.src.1, h.mor.mor, h.tgt.1,
    h.mor.src_mor.trans ((congrArg BObj.α h.src_mor).trans (V.faceObj_α _ _ _)),
    h.mor.tgt_mor.trans ((congrArg BObj.α h.tgt_mor).trans (V'.faceObj_α _ _ _))⟩

/-- **2021 Lemma 17.4.10, p. 797**: (1) for `h̄ = (x, Φ, x') ∈ M(Ψ_θ, Ψ'_{θ'})` the local
sc-diffeomorphism `f` of `h = (x, φ, x')` maps `θ` near `x` to `θ'` near `x'`
(`θ' = f_*^{Ψ,Ψ'} θ`); (2) conversely, for `h = (x, φ, x') ∈ M(Ψ, Ψ')` with `x ∈ θ` (so
`d_O(x) ≥ 1`), `x' ∈ θ'` and `θ, θ'` corresponding under `f`, `Φ = (Ψ_θ(x), φ, Ψ'_{θ'}(x'))` is a
morphism of `bC` and `h̄ = (x, Φ, x') ∈ M(Ψ_θ, Ψ'_{θ'})`. -/
theorem lemma_17_4_10 {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    (∀ h : V.FaceTr hT hS V' hθ hθ', S.GermLift hT (V.faceTrToTr V' h)
      (V.faceGerm hT hθ h.src.1 h.src.2) (V'.faceGerm hT hθ' h.tgt.1 h.tgt.2)) ∧
    ∀ (a : S.Tr Ψ Ψ') (hx : a.src ∈ θ) (hx' : a.tgt ∈ θ'),
      S.GermLift hT a (V.faceGerm hT hθ a.src hx) (V'.faceGerm hT hθ' a.tgt hx') →
      S.BLift (V.faceObj hT hS hθ a.src hx) a.mor (V'.faceObj hT hS hθ' a.tgt hx') ∧
      ∃ h : V.FaceTr hT hS V' hθ hθ', h.src = ⟨a.src, hx⟩ ∧ h.tgt = ⟨a.tgt, hx'⟩ ∧
        V.faceTrToTr V' h = a := by
  refine ⟨fun h => ?_, fun a hx hx' hl => ?_⟩
  · refine (bLift_ptObj_iff (hS := hS) (V.faceTrToTr V' h) (V.bMap_faceGerm hθ _ _)
      (V'.bMap_faceGerm hθ' _ _)).1 ?_
    have := h.mor.lifts
    rw [show h.mor.src = _ from h.src_mor, show h.mor.tgt = _ from h.tgt_mor] at this
    exact this
  · have hb := (bLift_ptObj_iff (hS := hS) a (V.bMap_faceGerm hθ _ hx)
      (V'.bMap_faceGerm hθ' _ hx')).2 hl
    exact ⟨hb, ⟨⟨a.src, hx⟩, ⟨_, a.mor, _, hb⟩, ⟨a.tgt, hx'⟩, rfl, rfl⟩, rfl, rfl,
      GroupoidStr.TransitionSet.ext rfl rfl rfl⟩

/-- `M(Ψ, Ψ')_{U, U'} = {(q, φ, q') ∈ M(Ψ, Ψ') | q ∈ U, q' ∈ U'}` (2021 p. 798), with
`U = U(ō) ⊆ ∂O`. -/
def trUU : Set (S.Tr Ψ Ψ') := {a | a.src ∈ V.bdry ∧ a.tgt ∈ V'.bdry}

/-- **2021 Lemma 17.4.11, p. 798**: if `M(Ψ, Ψ')_{U, U'}` is empty, all `M(Ψ_θ, Ψ'_{θ'})` are
empty. -/
theorem lemma_17_4_11 (hU : V.trUU V' = ∅) {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) : IsEmpty (V.FaceTr hT hS V' hθ hθ') := by
  refine ⟨fun h => ?_⟩
  have hm : V.faceTrToTr V' h ∈ V.trUU V' := ⟨V.subset_bdry hθ h.src.2, V'.subset_bdry hθ' h.tgt.2⟩
  rw [hU] at hm
  exact hm

variable (hT) in
/-- **2021 Definition 17.4.12, (17.70), p. 798**: `M(Ψ, Ψ')*_{θ, θ'}`, the `h = (x, φ, x')` with
`x ∈ θ`, `x' ∈ θ'` and `h_*θ = θ'` (the local sc-diffeomorphism of `h` maps `θ` near `x` to `θ'`
near `x'`). -/
def transFaceSet {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V'.faces) :
    Set (S.Tr Ψ Ψ') :=
  {a | ∃ (hx : a.src ∈ θ) (hx' : a.tgt ∈ θ'),
    S.GermLift hT a (V.faceGerm hT hθ a.src hx) (V'.faceGerm hT hθ' a.tgt hx')}

/-- **2021 Definition 17.4.12 and the remarks around it (p. 798)**: (17.70)
`M(Ψ, Ψ')*_{θ, θ'} ⊆ M(Ψ, Ψ')_{U, U'}`; for `h ∈ M(Ψ, Ψ')_{U, U'}` with `x ∈ θ` the face `θ' = h_*θ`
exists and is unique; and `M(Ψ, Ψ')*_{θ, θ'}` is the image of `M(Ψ_θ, Ψ'_{θ'})` under
`(x, Φ, x') ↦ (x, φ, x')` (Lemma 17.4.10). -/
theorem definition_17_4_12 {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) :
    (∀ {θ' : Set Ψ'.1.O} (hθ' : θ' ∈ V'.faces), V.transFaceSet hT V' hθ hθ' ⊆ V.trUU V') ∧
    (∀ a ∈ V.trUU V', a.src ∈ θ → ∃ (θ' : Set Ψ'.1.O) (hθ' : θ' ∈ V'.faces),
      a ∈ V.transFaceSet hT V' hθ hθ') ∧
    (∀ (a : S.Tr Ψ Ψ') {θ₁ θ₂ : Set Ψ'.1.O} (h₁ : θ₁ ∈ V'.faces) (h₂ : θ₂ ∈ V'.faces),
      a ∈ V.transFaceSet hT V' hθ h₁ → a ∈ V.transFaceSet hT V' hθ h₂ → θ₁ = θ₂) ∧
    ∀ {θ' : Set Ψ'.1.O} (hθ' : θ' ∈ V'.faces),
      range (V.faceTrToTr V' (hT := hT) (hS := hS) (hθ := hθ) (hθ' := hθ')) =
        V.transFaceSet hT V' hθ hθ' := by
  refine ⟨fun hθ' a ⟨hx, hx', _⟩ => ⟨V.subset_bdry hθ hx, V'.subset_bdry hθ' hx'⟩,
    fun a ha hx => ?_, fun a θ₁ θ₂ h₁ h₂ ⟨hx, hx₁, hl₁⟩ ⟨_, hx₂, hl₂⟩ =>
      V'.eq_of_faceGerm_eq (germLift_unique hl₁ hl₂), fun hθ' => ?_⟩
  · have hl := germLift_germPush a (V.faceGerm hT hθ a.src hx) (V.bMap_faceGerm hθ _ hx)
    have hq : bMap (S.hdU hT Ψ') (germPush a (V.faceGerm hT hθ a.src hx)
        (V.bMap_faceGerm hθ _ hx)) = a.tgt := hl.bMap_tgt
    obtain ⟨θ', hθ', hx', hfq⟩ := V'.exists_faceGerm_eq _ (by rw [hq]; exact ha.2.1)
    have hx'' : a.tgt ∈ θ' := hq ▸ hx'
    refine ⟨θ', hθ', hx, hx'', ?_⟩
    rw [← V'.faceGerm_congr_pt hθ' hq hx' hx'', hfq]
    exact hl
  · ext a
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h.src.2, h.tgt.2, (V.lemma_17_4_10 V' (hS := hS) hθ hθ').1 h⟩
    · rintro ⟨hx, hx', hl⟩
      obtain ⟨-, h, -, -, he⟩ := (V.lemma_17_4_10 V' (hS := hS) hθ hθ').2 a hx hx' hl
      exact ⟨h, he⟩

end GoodNbhd

end Transitions

/-! ### Non-degeneracy: the quadrant `[0,∞)² ⊕ W` -/

section QuadrantWitness

open MPolyfold TameBoundaryExample

variable (W : ScBanach)

attribute [local instance] quadrantTrivialAction

/-- `Ψ̂` is continuous for the quadrant polyfold. -/
theorem quadrant_hatContinuous : (quadrantConstruction W).HatContinuous := by
  rintro ⟨L, x, hL⟩
  obtain rfl : L = _ := hL
  exact twist_continuous_hat _ _ x continuous_id

/-- The quadrant polyfold is centred. -/
theorem quadrant_isCentred : (quadrantConstruction W).IsCentred := by
  intro α Ψ hΨ
  rw [Set.mem_singleton_iff.1 hΨ]
  exact ⟨α, rfl, fun _ => rfl⟩

/-- **The non-degenerate witness of the hypotheses of this file**: the quadrant polyfold is tame,
has uniformizers, `Ψ̂` is continuous and every uniformizer is centred; over its corner lie two
objects of `bC`, and a good neighbourhood of the corner has two faces (so two functors `Ψ_θ`). -/
theorem quadrant_tameBoundaryUniformizer_witness :
    ∃ (hT : (quadrantConstruction W).IsTame) (hS : (quadrantConstruction W).HasUniformizers),
      (quadrantConstruction W).HatContinuous ∧ (quadrantConstruction W).IsCentred ∧
      {a : (quadrantConstruction W).BObj hT hS | a.α = quadrantCorner W}.encard = 2 ∧
      ∃ V : (quadrantConstruction W).GoodNbhd (quadrantUnif W) (quadrantCorner W),
        V.faces.encard = 2 := by
  have hT : (quadrantConstruction W).IsTame :=
    twistConstruction_isTame _ _ (quadrantPolyfold_isTame 2 W)
  have hS : (quadrantConstruction W).HasUniformizers := twistConstruction_hasUniformizers _ _
  have hd : (quadrantUnif W).1.P.degIndex (quadrantCorner W) = 2 :=
    quadrantPolyfold_degIndex_zero 2 W
  have hb : quadrantCorner W ∈ (quadrantUnif W).1.P.boundary := by
    change 1 ≤ _
    rw [hd]; decide
  obtain ⟨V, -⟩ := (quadrantConstruction W).exists_goodNbhd (Ψ := quadrantUnif W)
    (isTame_unif _ hT _) hb isOpen_univ (mem_univ _)
  refine ⟨hT, hS, quadrant_hatContinuous W, quadrant_isCentred W, ?_, V, ?_⟩
  · rw [encard_obj_preimage, definition_17_1_30 (α := quadrantCorner W) (Ψ := (quadrantUnif W).1)
      (Set.mem_singleton _) rfl]
    exact congrArg _ hd
  · rw [V.encard_faces, hd]; rfl

end QuadrantWitness

end GCT.PolyfoldConstruction

end Polyfold
