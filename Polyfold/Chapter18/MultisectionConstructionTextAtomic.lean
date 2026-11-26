import Polyfold.Chapter18.MultisectionConstructionTextLam
import Polyfold.Chapter18.MultisectionConstructionTextRep
import Polyfold.Chapter18.AuxiliaryNormsDirect
import Polyfold.Chapter18.FredholmSectionFunctors

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, §18.4: **the
functor `Λ` of the construction of p. 854 in the models `c ⊔ {Ψ̄}`**.  For every covering family
`c`, the pull-back `Γ̄^*Λ` of `textLam` to the model of `c ⊔ {Ψ̄}` is the multisection `mult` of
atomic data (Definition 13.5.1).  Used for Proposition 18.4.3 (2021 p. 855) in
`MultisectionConstructionText.lean`.

## Construction

In the model of `c ⊔ {Ψ̄}` (`BundleCoveringFamily.withUnif`) the uniformizer `Ψ̄` is the summand
`none`, and the morphisms between its points are those of `M(Ψ, Ψ)` (`pieceEmbedding`).  The
choices made in `Ψ̄` alone (`TextData`): a natural representation `R₀` of `G_{q̄}` in the model of
`{Ψ̄}` (Theorem 7.1.13), carried to every model `c ⊔ {Ψ̄}` (`TextData.rep`), on a neighbourhood
with the properness property of Proposition 17.1.11 that meets none of its translates `g ∗ U₀`,
`g ∉ G_{q̄}`; an invariant `V₀`; a `G_{q̄}`-invariant `Vt` with `cl Vt ⊂ V₀`; and `s₁` vanishing
off `Vt`.  The atomic data (`TextData.atomicData`) has the index set `G_x × G`, the seeds `s_g`
for `g ∈ G_{q̄}` (and `0` for the other `g`, whose translates vanish near `q̄`), and the
sections `s_{(k, g)}` the `k`-th translates of the seeds (Theorem 13.5.4's construction).  On
`U(x)`, `s_{(k, g)} = s_{γ g}` for a `γ ∈ G` depending on `k` and the point
(`TextData.natTerm_seed`), so the count of the atomic data is `|G|⁻¹·#{g | s_g(p(h)) = h}`
(`TextData.count_atomicData`).

## Main statements

* `exists_smul_modelMu`: a morphism of the model between points of one summand acts on `K` by an
  element of `G`.
* `hasPropernessProperty_objMk_image`: an open `U ⊂ O_λ` with the properness property of
  Proposition 17.1.11 has it in every model containing `Ψ_λ`.
* **`TextData.bundlePull_textLam`**: `Γ̄^*Λ = mult` in the model of `c ⊔ {Ψ̄}`, for every `c`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor SBLocalization StrongBundle
  StrongBundleUniformizerConstruction StrongBundleUniformizerData PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle}

/-! ### The uniformizer as a piece of the models `c ⊔ {Ψ̄}` -/

section Model

variable {S : C.PolyfoldConstruction} (Q : V.StrongPolyfoldBundleConstruction S)

/-- The family `{Ψ̄}` with one member. -/
abbrev unifFamily (Ψ : Q.Unif) : PUnit.{u + 1} → Q.Unif := fun _ => Ψ

/-- The model `X_{Ψ}` of the one uniformizer. -/
abbrev unifEp (Ψ : Q.Unif) := S.modelEpGroupoid (Q.modelBase (Q.unifFamily Ψ))

/-- The model `X_{c ⊔ Ψ}`. -/
abbrev withEp (c : Q.BundleCoveringFamily) (Ψ : Q.Unif) :=
  S.modelEpGroupoid (Q.modelBase (c.withUnif Ψ).Ψ)

variable {Q}

/-- `q ↦ (none, q)` on objects. -/
def pieceObj (c : Q.BundleCoveringFamily) (Ψ : Q.Unif) :
    S.ModelObj (Q.modelBase (Q.unifFamily Ψ)) → S.ModelObj (Q.modelBase (c.withUnif Ψ).Ψ) :=
  fun y => ⟨none, y.2⟩

theorem pieceObj_image (c : Q.BundleCoveringFamily) (Ψ : Q.Unif)
    (A : Set (S.ModelObj (Q.modelBase (Q.unifFamily Ψ)))) :
    pieceObj c Ψ '' A =
      Sigma.mk (β := fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.O) (none : (c.withUnif Ψ).ι) ''
        (Sigma.mk (β := fun _ : PUnit.{u + 1} => Ψ.1.base.O) PUnit.unit ⁻¹' A) := by
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, q⟩, hq, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨PUnit.unit, q⟩, hq, rfl⟩

/-- **The uniformizer `Ψ̄` is an open full piece of every model `c ⊔ {Ψ̄}`**: the inclusion of
`X_{Ψ}` as the summand `none`. -/
def pieceEmbedding (c : Q.BundleCoveringFamily) (Ψ : Q.Unif) (q₀ : Ψ.1.base.O) :
    EpGroupoid.PieceEmbedding (Q.unifEp Ψ) (Q.withEp c Ψ) where
  fo := pieceObj c Ψ
  fm a := ⟨(none, none), a.2⟩
  go y := ⟨PUnit.unit, sigmaProj (X := fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.O)
    none q₀ y⟩
  go_fo y := by
    obtain ⟨⟨⟩, q⟩ := y
    exact congrArg (Sigma.mk PUnit.unit)
      (sigmaProj_mk (X := fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.O) (none : (c.withUnif Ψ).ι) q₀ q)
  isOpenMap_fo A hA := by
    rw [pieceObj_image]
    exact isOpenMap_sigmaMk _ (hA.preimage continuous_sigmaMk)
  isScSmoothMap_fo := by
    change (MPolyfold.sigma _).IsScSmoothMap (MPolyfold.sigma _) _
    rw [MPolyfold.isScSmoothMap_sigma_iff]
    intro i
    exact MPolyfold.isScSmoothMap_sigmaMk (fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.P) (none : (c.withUnif Ψ).ι)
  isScSmoothOn_go := by
    change (MPolyfold.sigma _).IsScSmoothOn (MPolyfold.sigma _) _ _
    have hr : range (pieceObj c Ψ) = range (Sigma.mk
        (β := fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.O) (none : (c.withUnif Ψ).ι)) := by
      ext z
      constructor
      · rintro ⟨⟨⟨⟩, q⟩, rfl⟩
        exact ⟨q, rfl⟩
      · rintro ⟨q, rfl⟩
        exact ⟨⟨PUnit.unit, q⟩, rfl⟩
    rw [hr]
    have h2 : (MPolyfold.sigma fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.P).IsScSmoothOn
        Ψ.1.base.P (sigmaProj (X := fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.O)
          (none : (c.withUnif Ψ).ι) q₀)
        (range (Sigma.mk (β := fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.O)
          (none : (c.withUnif Ψ).ι))) :=
      MPolyfold.isScSmoothOn_sigmaProj (fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.P)
        (none : (c.withUnif Ψ).ι) q₀
    exact (MPolyfold.isScSmoothOn_sigmaMk_comp_iff (fun _ : PUnit.{u + 1} => Ψ.1.base.P)
      (i := PUnit.unit)).2 h2
  isScSmoothMap_fm := by
    change (MPolyfold.sigma _).IsScSmoothMap (MPolyfold.sigma _) _
    rw [MPolyfold.isScSmoothMap_sigma_iff]
    intro i
    exact MPolyfold.isScSmoothMap_sigmaMk (fun p : (c.withUnif Ψ).ι × (c.withUnif Ψ).ι =>
      S.transPolyfold (Q.modelBase (c.withUnif Ψ).Ψ p.1) (Q.modelBase (c.withUnif Ψ).Ψ p.2))
      ((none : (c.withUnif Ψ).ι), (none : (c.withUnif Ψ).ι))
  src_fm _ := rfl
  tgt_fm _ := rfl
  fm_comp a b h := by
    obtain ⟨⟨⟨⟩, ⟨⟩⟩, a⟩ := a
    obtain ⟨⟨⟨⟩, ⟨⟩⟩, b⟩ := b
    have h' : a.src = b.tgt := eq_of_heq (Sigma.mk.inj_iff.1 h).2
    have hc : C.toGroupoidStr.src a.mor = C.toGroupoidStr.tgt b.mor := by
      rw [a.src_mor, b.tgt_mor, h']
    change (⟨(none, none), ((S.modelGroupoid (Q.modelBase (Q.unifFamily Ψ))).comp
      ⟨(PUnit.unit, PUnit.unit), a⟩ ⟨(PUnit.unit, PUnit.unit), b⟩).2⟩ : S.ModelMor _) =
      (S.modelGroupoid (Q.modelBase (c.withUnif Ψ).Ψ)).comp ⟨(none, none), a⟩ ⟨(none, none), b⟩
    rw [modelGroupoid_comp_of (Ψ := Q.modelBase (Q.unifFamily Ψ)) a b hc,
      modelGroupoid_comp_of (Ψ := Q.modelBase (c.withUnif Ψ).Ψ) (i := none) (j := none)
        (j' := none) (k := none) a b hc]
    rfl
  injective_fm a b h := by
    obtain ⟨⟨⟨⟩, ⟨⟩⟩, a⟩ := a
    obtain ⟨⟨⟨⟩, ⟨⟩⟩, b⟩ := b
    have : a = b := eq_of_heq (Sigma.mk.inj_iff.1 h).2
    rw [this]
  exists_fm h hs ht := by
    obtain ⟨⟨o₁, o₂⟩, a⟩ := h
    obtain ⟨y, hy⟩ := hs
    obtain ⟨y', hy'⟩ := ht
    have h1 : o₁ = none := (congrArg Sigma.fst hy).symm
    have h2 : o₂ = none := (congrArg Sigma.fst hy').symm
    subst h1 h2
    exact ⟨⟨(PUnit.unit, PUnit.unit), a⟩, rfl⟩

end Model

section Model2
variable {S : C.PolyfoldConstruction} {Q : V.StrongPolyfoldBundleConstruction S}

theorem hasPropernessProperty_objMk_image {ι : Type u} (Ψ : ι → S.Unif) (i : ι)
    {U : Set (Ψ i).1.O} (hU : IsOpen U)
    (hprop : ∀ Ψ' : S.Unif, IsProperMap (((fun a : S.Tr (Ψ i) Ψ' => a.src) ⁻¹' closure U).domRestrict
      fun a : S.Tr (Ψ i) Ψ' => a.tgt)) :
    (S.modelEpGroupoid Ψ).HasPropernessProperty (S.objMk Ψ i '' U) := by
  refine ⟨isOpenMap_sigmaMk (σ := fun i => (Ψ i).1.O) _ hU, ?_⟩
  have hcl : closure (S.objMk Ψ i '' U) = S.objMk Ψ i '' closure U :=
    (IsClosedEmbedding.sigmaMk (σ := fun i => (Ψ i).1.O) (i := i)).closure_image_eq U
  unfold EpGroupoid.IsProperSubset
  rw [hcl]
  set D := (S.modelGroupoid Ψ).src ⁻¹' (S.objMk Ψ i '' closure U)
  have hD : ∀ p : ι × ι, (S.morMk Ψ p ⁻¹' D).Nonempty → p.1 = i := by
    rintro p ⟨a, q', -, hq'⟩
    exact ((Sigma.mk.inj_iff.1 hq').1).symm
  have hτ : ∀ p p' : ι × ι, (S.morMk Ψ p ⁻¹' D).Nonempty → (S.morMk Ψ p' ⁻¹' D).Nonempty →
      p.2 = p'.2 → p = p' := fun p p' hp hp' h => Prod.ext ((hD p hp).trans (hD p' hp').symm) h
  have hpiece : ∀ p : ι × ι, IsProperMap ((S.morMk Ψ p ⁻¹' D).domRestrict
      fun a : S.Tr (Ψ p.1) (Ψ p.2) => a.tgt) := by
    rintro ⟨i', j⟩
    by_cases hi : i' = i
    · subst hi
      have hDp : S.morMk Ψ (i', j) ⁻¹' D =
          (fun a : S.Tr (Ψ i') (Ψ j) => a.src) ⁻¹' closure U := by
        ext a
        constructor
        · rintro ⟨q', hq', he⟩
          have : q' = a.src := eq_of_heq (Sigma.mk.inj_iff.1 he).2
          change a.src ∈ closure U
          rw [← this]
          exact hq'
        · intro ha
          exact ⟨a.src, ha, rfl⟩
      rw [hDp]
      exact hprop (Ψ j)
    · have : IsEmpty (S.morMk Ψ (i', j) ⁻¹' D) :=
        ⟨fun a => hi (hD (i', j) ⟨a.1, a.2⟩)⟩
      exact isProperMap_of_isEmpty _
  exact isProperMap_domRestrict_sigmaMap (A := fun p : ι × ι => S.Tr (Ψ p.1) (Ψ p.2))
    (B := fun i => (Ψ i).1.O) Prod.snd (fun p a => a.tgt)
    (fun p => S.continuous_trTgt (Ψ p.1) (Ψ p.2)) D hτ hpiece

theorem pieceObj_closure (c : Q.BundleCoveringFamily) (Ψ : Q.Unif)
    (A : Set (S.ModelObj (Q.modelBase (Q.unifFamily Ψ)))) :
    closure (pieceObj c Ψ '' A) = pieceObj c Ψ '' closure A := by
  rw [pieceObj_image, pieceObj_image,
    (IsClosedEmbedding.sigmaMk (σ := fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.O)
      (i := (none : (c.withUnif Ψ).ι))).closure_image_eq]
  congr 1
  exact ((isOpenMap_sigmaMk (σ := fun _ : PUnit.{u + 1} => Ψ.1.base.O)).preimage_closure_eq_closure_preimage
      continuous_sigmaMk A).symm

end Model2

section Model3
variable {S : C.PolyfoldConstruction} {Q : V.StrongPolyfoldBundleConstruction S}

theorem exists_smul_modelMu {ι : Type u} (Ψb : ι → Q.Unif) {i : ι}
    (a : S.Tr (Q.modelBase Ψb i) (Q.modelBase Ψb i)) :
    ∃ γ : (Ψb i).1.base.G, γ • a.src = a.tgt ∧ ∀ (kk : (Ψb i).1.K)
      (h : (Q.modelSEP Ψb).P ⟨i, kk⟩ = (Q.modelSEP Ψb).X.src ⟨(i, i), a⟩),
      (Q.modelSEP Ψb).E.μ ⟨(⟨(i, i), a⟩, ⟨i, kk⟩), h⟩ = ⟨i, γ • kk⟩ := by
  obtain ⟨γ, hγ, hm⟩ := (Ψb i).1.base.exists_smul_eq_mor a.src_mor a.tgt_mor
  refine ⟨γ, hγ, fun kk h => ?_⟩
  have hk : (Ψb i).1.p kk = a.src := eq_of_heq (Sigma.mk.inj_iff.1 h).2
  apply Q.bundleModelObj_injective Ψb
  · refine ((Q.modelSEP Ψb).E.P_μ _).trans ?_
    change (⟨i, a.tgt⟩ : S.ModelObj (Q.modelBase Ψb)) = ⟨i, (Ψb i).1.p (γ • kk)⟩
    rw [(Ψb i).1.p_smul, hk, hγ]
  · refine (Q.bundleModelObj_modelMu Ψb _).trans ?_
    change V.act a.mor ((Ψb i).1.obj kk) _ = (Ψb i).1.obj (γ • kk)
    refine (act_congr (hm.symm.trans (by rw [hk])) rfl _ _).trans ((Ψb i).1.obj_smul' γ kk)

theorem exists_smul_modelMu_none (c : Q.BundleCoveringFamily) (Ψ : Q.Unif)
    (a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ)) :
    ∃ γ : Ψ.1.base.G, γ • a.src = a.tgt ∧ ∀ (kk : Ψ.1.K)
      (h : (Q.modelSEP (c.withUnif Ψ).Ψ).P ⟨none, kk⟩ =
        (Q.modelSEP (c.withUnif Ψ).Ψ).X.src ⟨((none : (c.withUnif Ψ).ι), none), a⟩),
      (Q.modelSEP (c.withUnif Ψ).Ψ).E.μ ⟨(⟨(none, none), a⟩, ⟨none, kk⟩), h⟩ = ⟨none, γ • kk⟩ :=
  exists_smul_modelMu (c.withUnif Ψ).Ψ (i := none) a

/-- **The choices of p. 854 made in `Ψ̄`**. -/
structure TextData (Ψ : Q.Unif) (q₀ : Ψ.1.base.O) where
  R₀ : (Q.unifEp Ψ).NaturalRep ⟨PUnit.unit, q₀⟩
  V₀ : Set (S.ModelObj (Q.modelBase (Q.unifFamily Ψ)))
  isOpen_V₀ : IsOpen V₀
  mem_V₀ : (⟨PUnit.unit, q₀⟩ : S.ModelObj (Q.modelBase (Q.unifFamily Ψ))) ∈ V₀
  mapsTo_V₀ : ∀ g, MapsTo (R₀.Φ g) V₀ V₀
  closure_V₀ : closure V₀ ⊆ R₀.U
  hasPropernessProperty : ∀ c : Q.BundleCoveringFamily,
    (Q.withEp c Ψ).HasPropernessProperty (pieceObj c Ψ '' R₀.U)
  Vt : Set Ψ.1.base.O
  mapsTo_Vt : ∀ g : Ψ.1.base.G, g • q₀ = q₀ → MapsTo (g • ·) Vt Vt
  disjoint_U : ∀ g : Ψ.1.base.G, g • q₀ ≠ q₀ → ∀ q : Ψ.1.base.O,
    (⟨PUnit.unit, q⟩ : S.ModelObj (Q.modelBase (Q.unifFamily Ψ))) ∈ R₀.U →
    (⟨PUnit.unit, g • q⟩ : S.ModelObj (Q.modelBase (Q.unifFamily Ψ))) ∉ R₀.U
  closure_Vt : closure Vt ⊆ Sigma.mk (β := fun _ : PUnit.{u + 1} => Ψ.1.base.O) PUnit.unit ⁻¹' V₀
  s₁ : Ψ.1.base.O → Ψ.1.K
  isScPlusSection_s₁ : Ψ.1.B.IsScPlusSection s₁
  vanish_s₁ : ∀ q ∉ Vt, s₁ q = fiberZero Ψ.1.p q

def pieceFun (c : Q.BundleCoveringFamily) (Ψ : Q.Unif) (t : Ψ.1.base.O → Ψ.1.K) :
    ∀ o : (c.withUnif Ψ).ι, ((c.withUnif Ψ).Ψ o).1.base.O → ((c.withUnif Ψ).Ψ o).1.K
  | none => t
  | some i => fiberZero ((c.withUnif Ψ).Ψ (some i)).1.p

theorem isScPlusSection_sigmaSection' {ι : Type u} (Ψb : ι → Q.Unif)
    (f : ∀ i, (Ψb i).1.base.O → (Ψb i).1.K) (hf : ∀ i, (Ψb i).1.B.IsScPlusSection (f i)) :
    (Q.modelSEP Ψb).B.IsScPlusSection (sigmaSection f) := by
  have h := fun i => ((Ψb i).1.B.isScPlusSection_iff (f i)).1 (hf i)
  choose hsec g₀ hg₀ hg₀s using h
  refine ((Q.modelSEP Ψb).B.isScPlusSection_iff _).2
    ⟨fun x => ?_, (sigmaOneEquiv (fun i => (Ψb i).1.B)).symm ∘ Sigma.map id g₀, ?_, ?_⟩
  · obtain ⟨i, x⟩ := x
    change (⟨i, (Ψb i).1.p (f i x)⟩ : Σ i, (Ψb i).1.base.O) = ⟨i, x⟩
    rw [hsec i x]
  · funext x
    obtain ⟨i, x⟩ := x
    change (⟨i, (Ψb i).1.B.oneVal (g₀ i x)⟩ : Σ i, (Ψb i).1.K) = ⟨i, f i x⟩
    rw [← hg₀ i]
    rfl
  · exact (isScSmoothMap_sigmaOneEquiv_symm _).comp
      (MPolyfold.isScSmoothMap_sigmaMap _ fun i => hg₀s i)

theorem isScPlusSection_pieceFun (c : Q.BundleCoveringFamily) (Ψ : Q.Unif)
    {t : Ψ.1.base.O → Ψ.1.K} (ht : Ψ.1.B.IsScPlusSection t) :
    (Q.modelSEP (c.withUnif Ψ).Ψ).B.IsScPlusSection (sigmaSection (pieceFun c Ψ t)) :=
  isScPlusSection_sigmaSection' _ _ fun o => match o with
    | none => ht
    | some i => isScPlusSection_fiberZero (B := ((c.withUnif Ψ).Ψ (some i)).1.B)

/-- `Γ̄(w) = 0` iff `w = 0`. -/
theorem bundleModelObj_eq_zero_iff {ι : Type u} (Ψb : ι → Q.Unif) (w : Q.ModelW Ψb) :
    Q.bundleModelObj Ψb w = V.objMk (V.base (Q.bundleModelObj Ψb w)) 0 ↔
      w = fiberZero (Q.modelSEP Ψb).P ((Q.modelSEP Ψb).P w) := by
  obtain ⟨i, h⟩ := w
  refine (obj_eq_zero_iff h).trans ?_
  constructor
  · intro e
    exact congrArg (Sigma.mk (β := fun i => (Ψb i).1.K) i) e
  · intro e
    exact eq_of_heq (Sigma.mk.inj_iff.1 e).2

namespace TextData

variable {Ψ : Q.Unif} {q₀ : Ψ.1.base.O} (T : TextData Ψ q₀) (c : Q.BundleCoveringFamily)

/-- The natural representation in the model of `c ⊔ {Ψ̄}`. -/
def rep : (Q.withEp c Ψ).NaturalRep ⟨none, q₀⟩ :=
  (pieceEmbedding c Ψ q₀).naturalRep T.R₀

/-- The neighbourhood `V(x)` in the model of `c ⊔ {Ψ̄}`. -/
def nbhd (c : Q.BundleCoveringFamily) : Set (Q.modelSEP (c.withUnif Ψ).Ψ).Obj := pieceObj c Ψ '' T.V₀

open Classical in
/-- `s_g` for `g` in the stabilizer `G_{q̄}`, `0` for the other `g`. -/
def stabTranslate (g : Ψ.1.base.G) : Ψ.1.base.O → Ψ.1.K :=
  if g • q₀ = q₀ then textTranslate Ψ.1 T.s₁ g else fiberZero Ψ.1.p

theorem isScPlusSection_stabTranslate (g : Ψ.1.base.G) :
    Ψ.1.B.IsScPlusSection (T.stabTranslate g) := by
  classical
  unfold stabTranslate
  split_ifs
  · exact isScPlusSection_textTranslate T.isScPlusSection_s₁ g
  · exact isScPlusSection_fiberZero

theorem stabTranslate_of_notMem (g : Ψ.1.base.G) {q : Ψ.1.base.O} (hq : q ∉ T.Vt) :
    T.stabTranslate g q = fiberZero Ψ.1.p q := by
  classical
  unfold stabTranslate
  split_ifs with hg
  · exact textTranslate_of_notMem' T.vanish_s₁ (T.mapsTo_Vt g hg) hq
  · rfl

/-- The seed `s_g` on the model of `c ⊔ {Ψ̄}` (`0` off `Ψ̄`, and `0` for `g ∉ G_{q̄}`). -/
def seed (g : Ψ.1.base.G) : (Q.modelSEP (c.withUnif Ψ).Ψ).Obj → (Q.modelSEP (c.withUnif Ψ).Ψ).W :=
  sigmaSection (pieceFun c Ψ (T.stabTranslate g))

theorem isScPlusSection_seed (g : Ψ.1.base.G) :
    (Q.modelSEP (c.withUnif Ψ).Ψ).B.IsScPlusSection (T.seed c g) :=
  isScPlusSection_pieceFun c Ψ (T.isScPlusSection_stabTranslate g)

theorem rep_U : (T.rep c).U = pieceObj c Ψ '' T.R₀.U := rfl

theorem isOpen_V : IsOpen (T.nbhd c) := (pieceEmbedding c Ψ q₀).isOpenMap_fo _ T.isOpen_V₀

theorem mem_V : (⟨none, q₀⟩ : (Q.modelSEP (c.withUnif Ψ).Ψ).Obj) ∈ T.nbhd c := ⟨_, T.mem_V₀, rfl⟩

theorem mapsTo_V (k) : MapsTo ((T.rep c).Φ k) (T.nbhd c) (T.nbhd c) := by
  rintro _ ⟨y, hy, rfl⟩
  have := (pieceEmbedding c Ψ q₀).naturalRep_Φ_fo T.R₀ k y
  exact ⟨_, T.mapsTo_V₀ _ hy, this.symm⟩

theorem closure_V : closure (T.nbhd c) ⊆ (T.rep c).U := by
  exact (pieceObj_closure c Ψ T.V₀).le.trans (image_mono T.closure_V₀)

theorem sectionSupport_seed (g : Ψ.1.base.G) :
    sectionSupport (Q.modelSEP (c.withUnif Ψ).Ψ).P (T.seed c g) ⊆ T.nbhd c := by
  have h1 : {x | T.seed c g x ≠ fiberZero (Q.modelSEP (c.withUnif Ψ).Ψ).P x} ⊆
      Sigma.mk (β := fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.O) (none : (c.withUnif Ψ).ι) ''
        T.Vt := by
    rintro ⟨o, q⟩ hx
    cases o with
    | none =>
      by_contra hq
      refine hx ?_
      have hq' : q ∉ T.Vt := fun h => hq ⟨q, h, rfl⟩
      exact congrArg (Sigma.mk (β := fun o => ((c.withUnif Ψ).Ψ o).1.K) none)
        (T.stabTranslate_of_notMem g hq')
    | some i => exact absurd rfl hx
  unfold sectionSupport nbhd
  refine (closure_mono h1).trans ?_
  refine ((IsClosedEmbedding.sigmaMk (σ := fun o => (Q.modelBase (c.withUnif Ψ).Ψ o).1.O)
      (i := (none : (c.withUnif Ψ).ι))).closure_image_eq T.Vt).le.trans ?_
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨⟨PUnit.unit, q⟩, T.closure_Vt hq, rfl⟩


/-- `G_x` acting on `G_x × G` by left multiplication on the first factor. -/
@[instance_reducible] def indexMulAction (c : Q.BundleCoveringFamily) (Ψ : Q.Unif) (q₀ : Ψ.1.base.O) :
    MulAction ((Q.withEp c Ψ).Isotropy ⟨none, q₀⟩) ((Q.withEp c Ψ).Isotropy ⟨none, q₀⟩ × Ψ.1.base.G) where
  smul k i := (k * i.1, i.2)
  one_smul _ := Prod.ext (one_mul _) rfl
  mul_smul _ _ _ := Prod.ext (mul_assoc _ _ _) rfl

/-- **The family `(s_{(k, g)})`**: `I = G_x × G`, `s_{(k,g)}` the `k`-th translate of the seed `s_g`. -/
def family : SymmetricFamily (Q.modelSEP (c.withUnif Ψ).Ψ) (T.rep c) where
  I := (Q.withEp c Ψ).Isotropy ⟨none, q₀⟩ × Ψ.1.base.G
  fintype := Fintype.ofFinite _
  mulAction := indexMulAction c Ψ q₀
  s i := EpStrongBundle.natTerm (Q.modelSEP (c.withUnif Ψ).Ψ).E (T.rep c)
    (T.isScPlusSection_seed c i.2).1 i.1
  isScPlusSection i := EpStrongBundle.isScPlusSection_natTerm (E := (Q.modelSEP (c.withUnif Ψ).Ψ).E)
    (T.rep c) (T.mapsTo_V c) (T.closure_V c) (T.isScPlusSection_seed c i.2)
    (T.sectionSupport_seed c i.2) i.1
  support_subset i := by
    refine (closure_minimal (fun y hy => ?_) isClosed_closure).trans (T.closure_V c)
    by_contra hyV
    exact hy (EpStrongBundle.natTerm_eq_zero (E := (Q.modelSEP (c.withUnif Ψ).Ψ).E) (T.rep c) _
      (subset_closure.trans (T.closure_V c)) (T.mapsTo_V c) (T.sectionSupport_seed c i.2) i.1
      fun h => hyV (subset_closure h))
  equivariant g i y hy := by
    change (Q.withEp c Ψ).Isotropy ⟨none, q₀⟩ at g
    have e := EpStrongBundle.natTerm_tgt (E := (Q.modelSEP (c.withUnif Ψ).Ψ).E) (T.rep c)
      (T.isScPlusSection_seed c i.2).1 (ψ := (T.rep c).Γ g y) ((T.rep c).Γ_mem_morOn g hy) i.1
    have h1 : (T.rep c).index ((T.rep c).Γ g y) * i.1 = g * i.1 :=
      congrArg (· * i.1) ((T.rep c).index_Γ g hy)
    have h2 := (T.rep c).tgt_Γ g y hy
    change EpStrongBundle.natTerm (Q.modelSEP (c.withUnif Ψ).Ψ).E (T.rep c)
      (T.isScPlusSection_seed c i.2).1 (g * i.1) ((T.rep c).Φ g y) = _
    refine (congrArg₂ (fun k z => EpStrongBundle.natTerm (Q.modelSEP (c.withUnif Ψ).Ψ).E (T.rep c)
      (T.isScPlusSection_seed c i.2).1 k z) h1.symm h2.symm).trans (e.trans ?_)
    exact (Q.modelSEP (c.withUnif Ψ).Ψ).E.μ_congr (Prod.ext rfl
      (congrArg (EpStrongBundle.natTerm (Q.modelSEP (c.withUnif Ψ).Ψ).E (T.rep c)
        (T.isScPlusSection_seed c i.2).1 i.1) ((T.rep c).src_Γ g y hy)))

/-- **The atomic data in the model of `c ⊔ {Ψ̄}`**. -/
def atomicData : AtomicData (Q.modelSEP (c.withUnif Ψ).Ψ) :=
  AtomicData.ofFamily (T.rep c) (T.hasPropernessProperty c) (T.family c) (T.isOpen_V c) (T.mem_V c)
    (T.mapsTo_V c) (T.closure_V c) fun i _ hy =>
      EpStrongBundle.natTerm_eq_zero (E := (Q.modelSEP (c.withUnif Ψ).Ψ).E) (T.rep c) _
        (subset_closure.trans (T.closure_V c)) (T.mapsTo_V c) (T.sectionSupport_seed c i.2) i.1 hy

instance : Nonempty (T.atomicData c).I := ⟨(1, 1)⟩

theorem Vt_subset {q : Ψ.1.base.O} (hq : q ∈ T.Vt) :
    (⟨PUnit.unit, q⟩ : S.ModelObj (Q.modelBase (Q.unifFamily Ψ))) ∈ T.R₀.U :=
  T.closure_V₀ (subset_closure (T.closure_Vt (subset_closure hq)))

/-- `γ ∗ s_g(q) = s_{γ g}(γ ∗ q)` on `U₀` (the translates for `g ∉ G_{q̄}` vanish there). -/
theorem smul_stabTranslate {γ g : Ψ.1.base.G} {q : Ψ.1.base.O}
    (hq : (⟨PUnit.unit, q⟩ : S.ModelObj (Q.modelBase (Q.unifFamily Ψ))) ∈ T.R₀.U) :
    γ • T.stabTranslate g q = textTranslate Ψ.1 T.s₁ (γ * g) (γ • q) := by
  classical
  unfold stabTranslate
  split_ifs with hg
  · exact smul_textTranslate γ g q
  · refine Eq.trans (smul_fiberZero γ q) (textTranslate_of_notMem T.vanish_s₁ ?_).symm
    rw [mul_inv_rev, mul_smul, inv_smul_smul]
    intro hv
    have := T.disjoint_U g hg _ (T.Vt_subset hv)
    rw [smul_inv_smul] at this
    exact this hq

/-- On `U(x)`, `s_{(k, g)}(q) = s_{γ g}(q)` for some `γ ∈ G` depending on `k` and `q`. -/
theorem natTerm_seed (k : (Q.withEp c Ψ).Isotropy ⟨none, q₀⟩) {q : Ψ.1.base.O}
    (hq : (⟨none, q⟩ : (Q.modelSEP (c.withUnif Ψ).Ψ).Obj) ∈ (T.rep c).U) :
    ∃ γ : Ψ.1.base.G, ∀ g, EpStrongBundle.natTerm (Q.modelSEP (c.withUnif Ψ).Ψ).E (T.rep c)
      (T.isScPlusSection_seed c g).1 k ⟨none, q⟩ = ⟨none, textTranslate Ψ.1 T.s₁ (γ * g) q⟩ := by
  set A := Q.modelSEP (c.withUnif Ψ).Ψ
  have key : ∀ φ : A.Mor, A.X.src φ ∈ (T.rep c).U → A.X.tgt φ = ⟨none, q⟩ →
      ∃ γ : Ψ.1.base.G, ∀ g, A.E.secAct (T.isScPlusSection_seed c g).1 φ =
        ⟨none, textTranslate Ψ.1 T.s₁ (γ * g) q⟩ := by
    rintro ⟨⟨o₁, o₂⟩, a⟩ ⟨⟨⟨⟩, q'⟩, hq'U, hq'⟩ ht
    obtain rfl : o₁ = none := (congrArg Sigma.fst hq').symm
    obtain rfl : o₂ = none := congrArg Sigma.fst ht
    have hat : a.tgt = q := eq_of_heq (Sigma.mk.inj_iff.1 ht).2
    have has : q' = a.src := eq_of_heq (Sigma.mk.inj_iff.1 hq').2
    subst has hat
    obtain ⟨γ, hγ, hμ⟩ := exists_smul_modelMu_none c Ψ a
    refine ⟨γ, fun g => ?_⟩
    refine (hμ (T.stabTranslate g a.src) _).trans ?_
    refine congrArg (Sigma.mk (β := fun o => ((c.withUnif Ψ).Ψ o).1.K) none) ?_
    rw [← hγ]
    exact T.smul_stabTranslate hq'U
  have hy := (T.rep c).mapsTo_Φ k⁻¹ hq
  obtain ⟨γ, hγ⟩ := key ((T.rep c).Γ k ((T.rep c).Φ k⁻¹ ⟨none, q⟩))
    (by
      have h := (T.rep c).src_Γ k _ hy
      exact h.symm ▸ hy)
    (EpStrongBundle.tgt_Γ_Φ_inv (T.rep c) k hq)
  exact ⟨γ, fun g => (EpStrongBundle.natTerm_of_mem (E := (Q.modelSEP (c.withUnif Ψ).Ψ).E) (T.rep c)
    (T.isScPlusSection_seed c g).1 k hq).trans (hγ g)⟩

theorem _root_.Polyfold.SBLocalization.AtomicData.count_eq_natCard {A : SEP.{u}} (D : AtomicData A)
    (w : A.W) :
    D.count w = (Nat.card D.I : ℚ≥0)⁻¹ * (Nat.card {i // D.s i (A.P w) = w} : ℚ≥0) := by
  classical
  unfold AtomicData.count
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **`|I_x|⁻¹·#{i | sᵢ(p(h)) = h} = |G|⁻¹·#{g | s_g(p(h)) = h}`** on `U(x)`. -/
theorem count_atomicData (h : Ψ.1.K)
    (hh : (⟨none, Ψ.1.p h⟩ : (Q.modelSEP (c.withUnif Ψ).Ψ).Obj) ∈ (T.rep c).U) :
    (T.atomicData c).count ⟨none, h⟩ = textLamK Ψ.1 T.s₁ h := by
  choose γ hγ using fun k => T.natTerm_seed c k hh
  refine (AtomicData.count_eq_natCard _ _).trans ?_
  have e1 : Nat.card {i // (T.atomicData c).s i ((Q.modelSEP (c.withUnif Ψ).Ψ).P ⟨none, h⟩) =
      ⟨none, h⟩} = Nat.card {i : (Q.withEp c Ψ).Isotropy ⟨none, q₀⟩ × Ψ.1.base.G //
        textTranslate Ψ.1 T.s₁ (γ i.1 * i.2) (Ψ.1.p h) = h} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ?_)
    have e := hγ i.1 i.2
    constructor
    · intro hi
      exact eq_of_heq (Sigma.mk.inj_iff.1 (e.symm.trans hi)).2
    · intro hi
      exact e.trans (congrArg (Sigma.mk (β := fun o => ((c.withUnif Ψ).Ψ o).1.K) none) hi)
  have e2 : Nat.card {i : (Q.withEp c Ψ).Isotropy ⟨none, q₀⟩ × Ψ.1.base.G //
        textTranslate Ψ.1 T.s₁ (γ i.1 * i.2) (Ψ.1.p h) = h} =
      Nat.card ((Q.withEp c Ψ).Isotropy ⟨none, q₀⟩ ×
        {g : Ψ.1.base.G // textTranslate Ψ.1 T.s₁ g (Ψ.1.p h) = h}) :=
    Nat.card_congr
      { toFun := fun i => (i.1.1, ⟨γ i.1.1 * i.1.2, i.2⟩)
        invFun := fun j => ⟨(j.1, (γ j.1)⁻¹ * j.2.1), by
          simp only [mul_inv_cancel_left]; exact j.2.2⟩
        left_inv := fun i => by
          ext <;> simp
        right_inv := fun j => by
          ext <;> simp }
  have e3 : Nat.card (T.atomicData c).I =
      Nat.card ((Q.withEp c Ψ).Isotropy ⟨none, q₀⟩) * Nat.card Ψ.1.base.G :=
    Nat.card_prod _ _
  rw [e1, e2, e3, Nat.card_prod]
  unfold textLamK
  have ha : (Nat.card ((Q.withEp c Ψ).Isotropy ⟨none, q₀⟩) : ℚ≥0) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [Nat.cast_mul, Nat.cast_mul, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ ha, one_mul]

theorem bundlePull_textLam_of_mem (w : (Q.modelSEP (c.withUnif Ψ).Ψ).W)
    (hw : (Q.modelSEP (c.withUnif Ψ).Ψ).P w ∈ (T.rep c).U) :
    Q.bundlePull (c.withUnif Ψ).Ψ (textLam Ψ.1 T.s₁) w = (T.atomicData c).count w := by
  obtain ⟨o, h⟩ := w
  have hw' := hw
  obtain ⟨⟨⟨⟩, q⟩, -, hq⟩ := hw'
  obtain rfl : o = none := (congrArg Sigma.fst hq).symm
  exact (textLam_obj h).trans (T.count_atomicData c h hw).symm

theorem bundlePull_textLam_of_not_reach (w : (Q.modelSEP (c.withUnif Ψ).Ψ).W)
    (hw : ¬ (T.atomicData c).Reach ((Q.modelSEP (c.withUnif Ψ).Ψ).P w)) :
    Q.bundlePull (c.withUnif Ψ).Ψ (textLam Ψ.1 T.s₁) w =
      zeroMultisection (Q.modelSEP (c.withUnif Ψ).Ψ) w := by
  classical
  have hz := bundleModelObj_eq_zero_iff (c.withUnif Ψ).Ψ w
  change textLam Ψ.1 T.s₁ (Q.bundleModelObj (c.withUnif Ψ).Ψ w) = _
  unfold zeroMultisection
  refine Eq.trans ?_ (if_congr hz rfl rfl)
  by_cases hr : ∃ r, TextReach Ψ.1 (Q.bundleModelObj (c.withUnif Ψ).Ψ w) r
  · obtain ⟨r, hr⟩ := hr
    rw [textLam_eq_textValue _ _ hr]
    have hq : ∀ g : Ψ.1.base.G, g⁻¹ • r.1 ∉ T.Vt := by
      intro g hg
      apply hw
      have hc : C.toGroupoidStr.src (Ψ.1.base.mor (g⁻¹, r.1)) = C.toGroupoidStr.tgt r.2 :=
        (Ψ.1.base.functor.src_mor _).trans hr.2.symm
      refine ⟨⟨(((Q.modelSEP (c.withUnif Ψ).Ψ).P w).1, none),
        ⟨((Q.modelSEP (c.withUnif Ψ).Ψ).P w).2,
          C.toGroupoidStr.comp (Ψ.1.base.mor (g⁻¹, r.1)) r.2, g⁻¹ • r.1,
          by rw [C.toGroupoidStr.src_comp _ _ hc]; exact hr.1,
          by rw [C.toGroupoidStr.tgt_comp _ _ hc]; exact Ψ.1.base.functor.tgt_mor _⟩⟩, rfl, ?_⟩
      exact ⟨⟨PUnit.unit, g⁻¹ • r.1⟩, T.Vt_subset hg, rfl⟩
    unfold textValue
    rw [textLamK_of_notMem T.vanish_s₁ (by rw [p_textLift]; exact hq)]
    refine if_congr ?_ rfl rfl
    rw [← obj_eq_zero_iff, obj_textLift, p_textLift]
    exact text_act_eq_objMk_zero_iff' r.2 _ _ hr.2
  · rw [textLam_of_not_reach _ hr]
    exact if_congr (objMk_zero_iff _).symm rfl rfl

/-- **`Γ̄^*Λ` is the multisection of the atomic data** in the model of `c ⊔ {Ψ̄}`. -/
theorem bundlePull_textLam :
    Q.bundlePull (c.withUnif Ψ).Ψ (textLam Ψ.1 T.s₁) = (T.atomicData c).mult := by
  funext w
  by_cases hr : (T.atomicData c).Reach ((Q.modelSEP (c.withUnif Ψ).Ψ).P w)
  · obtain ⟨φ, hs, ht⟩ := hr
    rw [(T.atomicData c).mult_eq hs.symm ht]
    refine (Q.isWFunctor_bundlePull (c.withUnif Ψ).Ψ isMorInvariant_textLam
      ⟨(φ, w), hs.symm⟩).symm.trans ?_
    exact T.bundlePull_textLam_of_mem c _ (by
      rw [(Q.modelSEP (c.withUnif Ψ).Ψ).E.P_μ]; exact ht)
  · rw [(T.atomicData c).mult_of_not_reach hr]
    exact T.bundlePull_textLam_of_not_reach c w hr

end TextData

end Model3

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
