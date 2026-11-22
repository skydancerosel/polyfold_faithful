import Polyfold.Chapter17.TameBoundaryTame

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.4 (pp. 809–811): **the ep-groupoid `Θ = ⊔_θ θ` and the diagrams (17.82), (17.83)**.

## The text, paraphrased

(pp. 809–810) Fix `α ∈ ∂C`, `Ψ ∈ F(α)` and a good open neighbourhood `U(ō)`.  For every face
`θ` of `U(ō)` Lemma 17.4.6 gives `Ψ_θ : G_θ ⋉ θ → bC`.  `Θ` is the disjoint union of the faces,
a tame M-polyfold; with the morphism M-polyfold `⊔_{θ,θ'} M(Ψ_θ, Ψ_{θ'})` it is an ep-groupoid.
`Ψ̂ : Θ → bC` sends `q ∈ θ` to `Ψ_θ(q)` and a morphism to the underlying morphism of `bC`;
the forgetful functor `F : Θ → G ⋉ O` makes the square (17.82) `B ∘ Ψ̂ = Ψ ∘ F` commute.  `F` is
determined by the rest of the diagram; it is sc-smooth on objects (`θ → O`) and on morphisms
(`M(Ψ_θ, Ψ_{θ'}) → M(Ψ, Ψ)*_{θ,θ'}` is an sc-diffeomorphism onto a sub-M-polyfold).  (p. 811,
(17.83)) With `V(ō)` in place of `O`, `F` is surjective (onto `U(ō)`) and
`|B|⁻¹(|Ψ(V)|) = |Ψ̂(Θ)|`.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `ftrIncl_isScSmoothMap`: for any choice of data `d, d'` with `L = Ψ_θ`, `L' = Ψ'_{θ'}`, the map
  `M(L, L') → M(Ψ, Ψ')`, `(x, Φ, x') ↦ (x, φ, x')` is sc-smooth (Definition 17.4.14 and (17.84)).
* For the fixed data `(Ψ, ō, U(ō))` (namespace `…GoodNbhd`):
  - `faceData` (the data of `Ψ_θ` for the face `θ`), `faceUnif_injective` (`θ ↦ Ψ_θ` is
    injective, so the data of `Ψ_θ` is determined by `Ψ_θ`);
  - `faceF`, **`faceConstruction`**: the polyfold construction on `bC` whose uniformizers are the
    `Ψ_θ`, `θ ∈ F_{U(ō)}`, with the transition M-polyfolds of Definition 17.4.14 *for the given
    data* (`faceDataAt_faceFamily`: the data used for `Ψ_θ` is `(Ψ, ō, U(ō), θ)`);
    `faceF_subset` (`F_{U(ō)} ⊆ F_bC` when `Ψ ∈ F(Ψ(ō))`), `faceConstruction_isTame`;
  - `faceFamily`, **`faceThetaEp`** (`Θ`, the model ep-groupoid of the family `(Ψ_θ)_θ`,
    Theorem 17.1.14), **`faceHat`** (`Ψ̂ : Θ → bC`), **`faceForget`** (`F : Θ → X_{(Ψ)}` as an
    ep-functor into the model of the one-element family `(Ψ)`, whose morphisms are those of
    `G ⋉ O` through `Ψ̂`, Lemma 17.1.15);
  - **`display_17_82_Theta`**: `Θ` is a tame ep-groupoid, `Ψ̂` is fully faithful, the square
    `Ψ ∘ F = B ∘ Ψ̂` commutes, `F` is the only functor making it commute, and (17.83):
    `F` maps the objects of `Θ` onto `U(ō)` and `|B|⁻¹(|Ψ(V(ō))|) = |Ψ̂|(|Θ|)`.
* Witness: `swap_display_17_82_Theta` (`ℤ/2 ⋉ ([0,∞)² ⊕ W)` at the corner: `Θ` has objects in
  two faces).

## Readings

* "`Θ` naturally has the structure of a tame M-polyfold … an ep-groupoid": `Θ` is read as the
  model ep-groupoid `X_{(Ψ_θ)_θ}` (Theorem 17.1.14) of a polyfold construction on the GCT `bC`
  whose uniformizers are the `Ψ_θ` for the fixed `U(ō)` and whose transition M-polyfolds are those
  of Definition 17.4.14 for the data `(Ψ, ō, U(ō), θ)`.  The polyfold structure `(F_bC, M)` of
  Theorem 17.4.26 chooses data for each of its uniformizers (`faceDataOf`); `faceConstruction`
  uses the given data instead, which `faceUnif_injective` makes canonical.
* `G ⋉ O` is read as the model `X_{(Ψ)}` of the one-element family; its objects are the points of
  `O` and its morphisms the elements of `M(Ψ, Ψ)`, which `Ψ̂` identifies with `G × O`
  (Lemma 17.1.15 and (17.3)).  `F` is an ep-functor (sc-smooth on objects and morphisms).
* (17.83): "surjective on objects" is read as: `F` maps the objects of `Θ` onto
  `U(ō) = V(ō) ∩ ∂O`, the part of `V(ō)` over `∂C` (as in `display_17_83`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

universe u

namespace Polyfold

open TameBoundary

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} (hT : S.IsTame) (hS : S.HasUniformizers)
  (hc : S.HatContinuous) (hcent : S.IsCentred)

/-- **`M(Ψ_θ, Ψ'_{θ'}) → M(Ψ, Ψ')` is sc-smooth for every choice of data** (2021 (17.84),
Definition 17.4.14). -/
theorem ftrIncl_isScSmoothMap : ∀ (L L' : (S.bdryGCT hT hS hc hcent).LocalUniformizer)
    (d d' : S.FaceData) (h : L = d.unif hT hS hc hcent) (h' : L' = d'.unif hT hS hc hcent),
    letI := ftrTopOf hT hS hc hcent L L' d d' h h'
    letI := ftrT2Of hT hS hc hcent L L' d d' h h'
    letI := ftrParaOf hT hS hc hcent L L' d d' h h'
    (ftrMOf hT hS hc hcent L L' d d' h h').IsScSmoothMap (S.transPolyfold d.Ψ d'.Ψ)
      (fun a => (ftrInclOf hT hS hc hcent L L' d d' h h' a).1)
  | _, _, d, d', rfl, rfl => (d.V.display_17_84 hT hS d'.V d.hθ d'.hθ).2.2.2.1

namespace GoodNbhd

variable {Ψ : S.Unif} {o : Ψ.1.O} (V : S.GoodNbhd Ψ o) (hfix : Ψ.1.FixesPoint o)

/-- The data `(Ψ, ō, U(ō), θ)` of the face uniformizer `Ψ_θ`. -/
def faceData {θ : Set Ψ.1.O} (hθ : θ ∈ V.faces) : S.FaceData := ⟨Ψ, o, V, hfix, θ, hθ⟩

/-- **`θ ↦ Ψ_θ` is injective** on the faces of `U(ō)`: `Ψ_θ(ō)` is the object of `bC` given by
the face germ of `θ` at `ō`, and distinct faces have distinct germs. -/
theorem faceUnif_injective {θ θ' : Set Ψ.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V.faces)
    (h : (V.faceData hfix hθ).unif hT hS hc hcent = (V.faceData hfix hθ').unif hT hS hc hcent) :
    θ = θ' := by
  have hr := congrArg (fun L : (S.bdryGCT hT hS hc hcent).LocalUniformizer =>
    Set.range L.functor.obj) h
  have hmem : V.faceObj hT hS hθ o (V.mem_of_mem_faces hθ) ∈
      Set.range ((V.faceData hfix hθ).unif hT hS hc hcent).functor.obj :=
    ⟨⟨o, V.mem_of_mem_faces hθ⟩, rfl⟩
  rw [hr] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ((V.faceObj_inj (hT := hT) (hS := hS) hy).2).symm

/-- **`F_{U(ō)}(ᾱ)`**: the face uniformizers `Ψ_θ`, `θ ∈ F_{U(ō)}`, with `Ψ_θ(ō) = ᾱ`. -/
def faceF (ᾱ : S.BObj hT hS) : Set (S.bdryGCT hT hS hc hcent).LocalUniformizer :=
  {L | ∃ (θ : Set Ψ.1.O) (hθ : θ ∈ V.faces), L = (V.faceData hfix hθ).unif hT hS hc hcent ∧
    V.faceObj hT hS hθ o (V.mem_of_mem_faces hθ) = ᾱ}

theorem exists_face_of_faceUnif
    (L : @GCT.Unif (S.bdryGCT hT hS hc hcent) (V.faceF hT hS hc hcent hfix)) :
    ∃ θ, ∃ hθ : θ ∈ V.faces, L.1 = (V.faceData hfix hθ).unif hT hS hc hcent := by
  obtain ⟨L, ᾱ, θ, hθ, rfl, -⟩ := L
  exact ⟨θ, hθ, rfl⟩

/-- The face `θ` of `L = Ψ_θ ∈ F_{U(ō)}` (unique, `faceUnif_injective`). -/
def faceOf (L : @GCT.Unif (S.bdryGCT hT hS hc hcent) (V.faceF hT hS hc hcent hfix)) :
    Set Ψ.1.O :=
  (V.exists_face_of_faceUnif hT hS hc hcent hfix L).choose

theorem faceOf_mem (L : @GCT.Unif (S.bdryGCT hT hS hc hcent) (V.faceF hT hS hc hcent hfix)) :
    V.faceOf hT hS hc hcent hfix L ∈ V.faces :=
  (V.exists_face_of_faceUnif hT hS hc hcent hfix L).choose_spec.choose

/-- The data `(Ψ, ō, U(ō), θ)` of `L = Ψ_θ ∈ F_{U(ō)}`. -/
def faceDataAt (L : @GCT.Unif (S.bdryGCT hT hS hc hcent) (V.faceF hT hS hc hcent hfix)) :
    S.FaceData :=
  V.faceData hfix (V.faceOf_mem hT hS hc hcent hfix L)

theorem faceDataAt_eq (L : @GCT.Unif (S.bdryGCT hT hS hc hcent) (V.faceF hT hS hc hcent hfix)) :
    L.1 = (V.faceDataAt hT hS hc hcent hfix L).unif hT hS hc hcent :=
  (V.exists_face_of_faceUnif hT hS hc hcent hfix L).choose_spec.choose_spec

/-- **The polyfold construction of the faces of `U(ō)`** on `bC`: the uniformizers `Ψ_θ`,
`θ ∈ F_{U(ō)}`, with the transition M-polyfolds `M(Ψ_θ, Ψ_{θ'})` of Definition 17.4.14 for the
data `(Ψ, ō, U(ō), θ)` (Theorem 17.4.16 for the structure maps). -/
def faceConstruction : (S.bdryGCT hT hS hc hcent).PolyfoldConstruction where
  F := V.faceF hT hS hc hcent hfix
  isAt ᾱ L hL := by
    obtain ⟨θ, hθ, rfl, he⟩ := hL
    exact ⟨⟨o, V.mem_of_mem_faces hθ⟩, he⟩
  topM L L' := ftrTopOf hT hS hc hcent L.1 L'.1 (V.faceDataAt hT hS hc hcent hfix L)
    (V.faceDataAt hT hS hc hcent hfix L') (V.faceDataAt_eq hT hS hc hcent hfix L)
    (V.faceDataAt_eq hT hS hc hcent hfix L')
  t2M L L' := ftrT2Of hT hS hc hcent L.1 L'.1 (V.faceDataAt hT hS hc hcent hfix L)
    (V.faceDataAt hT hS hc hcent hfix L') (V.faceDataAt_eq hT hS hc hcent hfix L)
    (V.faceDataAt_eq hT hS hc hcent hfix L')
  paraM L L' := ftrParaOf hT hS hc hcent L.1 L'.1 (V.faceDataAt hT hS hc hcent hfix L)
    (V.faceDataAt hT hS hc hcent hfix L') (V.faceDataAt_eq hT hS hc hcent hfix L)
    (V.faceDataAt_eq hT hS hc hcent hfix L')
  M L L' := ftrMOf hT hS hc hcent L.1 L'.1 (V.faceDataAt hT hS hc hcent hfix L)
    (V.faceDataAt hT hS hc hcent hfix L') (V.faceDataAt_eq hT hS hc hcent hfix L)
    (V.faceDataAt_eq hT hS hc hcent hfix L')
  isLocalScDiffeo_src L L' := ftrSrcOf hT hS hc hcent L.1 L'.1
    (V.faceDataAt hT hS hc hcent hfix L) (V.faceDataAt hT hS hc hcent hfix L')
    (V.faceDataAt_eq hT hS hc hcent hfix L) (V.faceDataAt_eq hT hS hc hcent hfix L')
  isLocalScDiffeo_tgt L L' := ftrTgtOf hT hS hc hcent L.1 L'.1
    (V.faceDataAt hT hS hc hcent hfix L) (V.faceDataAt hT hS hc hcent hfix L')
    (V.faceDataAt_eq hT hS hc hcent hfix L) (V.faceDataAt_eq hT hS hc hcent hfix L')
  isScSmoothMap_unit L := ftrUnitOf hT hS hc hcent L.1 (V.faceDataAt hT hS hc hcent hfix L)
    (V.faceDataAt_eq hT hS hc hcent hfix L)
  isScSmoothMap_inv L L' := ftrInvOf hT hS hc hcent L.1 L'.1
    (V.faceDataAt hT hS hc hcent hfix L) (V.faceDataAt hT hS hc hcent hfix L')
    (V.faceDataAt_eq hT hS hc hcent hfix L) (V.faceDataAt_eq hT hS hc hcent hfix L')
  isScSmoothMap_mul L L' L'' := ftrMulOf hT hS hc hcent L.1 L'.1 L''.1
    (V.faceDataAt hT hS hc hcent hfix L) (V.faceDataAt hT hS hc hcent hfix L')
    (V.faceDataAt hT hS hc hcent hfix L'') (V.faceDataAt_eq hT hS hc hcent hfix L)
    (V.faceDataAt_eq hT hS hc hcent hfix L') (V.faceDataAt_eq hT hS hc hcent hfix L'')

/-- **`F_{U(ō)}(ᾱ) ⊆ F_bC(ᾱ)`** (Theorem 17.4.26) when `Ψ ∈ F(Ψ(ō))`. -/
theorem faceF_subset (hΨ : Ψ.1 ∈ S.F (Ψ.1.obj o)) (ᾱ : S.BObj hT hS) :
    V.faceF hT hS hc hcent hfix ᾱ ⊆ S.bdryF hT hS hc hcent ᾱ := by
  rintro L ⟨θ, hθ, rfl, he⟩
  refine ⟨V.faceData hfix hθ, ?_, he, rfl⟩
  rw [← he, faceObj_α]
  exact hΨ

/-- The polyfold construction of the faces is tame (Definition 2.5.18 for the faces,
`isTame_faceSubPolyfold`). -/
theorem faceConstruction_isTame : (V.faceConstruction hT hS hc hcent hfix).IsTame := by
  rintro ᾱ L ⟨θ, hθ, rfl, -⟩
  exact V.isTame_faceSubPolyfold hT hθ

/-- The family `(Ψ_θ)_{θ ∈ F_{U(ō)}}`. -/
def faceFamily (θ : V.faces) : (V.faceConstruction hT hS hc hcent hfix).Unif :=
  ⟨(V.faceData hfix θ.2).unif hT hS hc hcent,
    V.faceObj hT hS θ.2 o (V.mem_of_mem_faces θ.2), θ.1, θ.2, rfl, rfl⟩

/-- **The data used for `Ψ_θ` is `(Ψ, ō, U(ō), θ)`**: the transition M-polyfolds of `Θ` are those
of Definition 17.4.14 for the given good neighbourhood. -/
theorem faceDataAt_faceFamily (θ : V.faces) :
    V.faceDataAt hT hS hc hcent hfix (V.faceFamily hT hS hc hcent hfix θ) =
      V.faceData hfix θ.2 := by
  have he : V.faceOf hT hS hc hcent hfix (V.faceFamily hT hS hc hcent hfix θ) = θ.1 :=
    V.faceUnif_injective hT hS hc hcent hfix (V.faceOf_mem hT hS hc hcent hfix _) θ.2
      (V.faceDataAt_eq hT hS hc hcent hfix (V.faceFamily hT hS hc hcent hfix θ)).symm
  unfold faceDataAt
  generalize V.faceOf_mem hT hS hc hcent hfix (V.faceFamily hT hS hc hcent hfix θ) = h
  revert h
  rw [he]
  intro h
  rfl

/-- **`Θ = ⊔_θ θ`** with the morphism M-polyfold `⊔_{θ,θ'} M(Ψ_θ, Ψ_{θ'})` (2021 p. 810): the model
ep-groupoid of the family `(Ψ_θ)_θ` (Theorem 17.1.14). -/
abbrev faceThetaEp :=
  (V.faceConstruction hT hS hc hcent hfix).modelEpGroupoid (V.faceFamily hT hS hc hcent hfix)

/-- **`Ψ̂ : Θ → bC`** (2021 p. 810): `q ∈ θ ↦ Ψ_θ(q)`, a morphism to the underlying morphism of
`bC`. -/
abbrev faceHat :=
  (V.faceConstruction hT hS hc hcent hfix).modelFunctor (V.faceFamily hT hS hc hcent hfix)

/-- The one-element family `(Ψ)`; its model `X_{(Ψ)}` has the objects `O` and the morphisms
`M(Ψ, Ψ)`, identified with `G ⋉ O` by `Ψ̂` (Lemma 17.1.15). -/
abbrev singleFamily : PUnit.{u + 1} → S.Unif := fun _ => Ψ

theorem faceForget_mor_comp {i j j' k : V.faces}
    (a : (V.faceConstruction hT hS hc hcent hfix).Tr (V.faceFamily hT hS hc hcent hfix j')
      (V.faceFamily hT hS hc hcent hfix k))
    (b : (V.faceConstruction hT hS hc hcent hfix).Tr (V.faceFamily hT hS hc hcent hfix i)
      (V.faceFamily hT hS hc hcent hfix j))
    (h : (S.bdryGroupoid hT hS).src a.mor = (S.bdryGroupoid hT hS).tgt b.mor) :
    V.faceTrToTr V (hT := hT) (hS := hS) (hθ := i.2) (hθ' := k.2)
        (GroupoidStr.TransitionSet.comp a b h) =
      GroupoidStr.TransitionSet.comp (V.faceTrToTr V (hT := hT) (hS := hS) (hθ := j'.2)
        (hθ' := k.2) a) (V.faceTrToTr V (hT := hT) (hS := hS) (hθ := i.2) (hθ' := j.2) b)
        (by
          change C.toGroupoidStr.src a.mor.mor = C.toGroupoidStr.tgt b.mor.mor
          rw [a.mor.src_mor, b.mor.tgt_mor]
          exact congrArg BObj.α h) :=
  GroupoidStr.TransitionSet.ext rfl (bdryGroupoid_comp_mor h) rfl

/-- **`F : Θ → G ⋉ O`** (2021 (17.82)): `(x, θ) ↦ x`,
`((x, θ), Ψ(g, x), (g ∗ x, g(θ))) ↦ (x, φ, g ∗ x)`, an ep-functor into the model `X_{(Ψ)}`. -/
def faceForget :
    EpFunctor (V.faceThetaEp hT hS hc hcent hfix) (S.modelEpGroupoid (singleFamily (Ψ := Ψ))) where
  obj z := ⟨PUnit.unit, z.2.1⟩
  mor m := ⟨(PUnit.unit, PUnit.unit),
    V.faceTrToTr V (hT := hT) (hS := hS) (hθ := m.1.1.2) (hθ' := m.1.2.2) m.2⟩
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp m m' h := by
    obtain ⟨⟨j', k⟩, a⟩ := m
    obtain ⟨⟨i, j⟩, b⟩ := m'
    have hc' : (S.bdryGroupoid hT hS).src a.mor = (S.bdryGroupoid hT hS).tgt b.mor :=
      a.src_mor.trans ((congrArg ((V.faceConstruction hT hS hc hcent hfix).modelObjMap
        (V.faceFamily hT hS hc hcent hfix)) h).trans b.tgt_mor.symm)
    have e₁ := modelGroupoid_comp_of (S := V.faceConstruction hT hS hc hcent hfix)
      (Ψ := V.faceFamily hT hS hc hcent hfix) a b hc'
    have e₂ := modelGroupoid_comp_of (S := S) (Ψ := singleFamily (Ψ := Ψ))
      (i := PUnit.unit) (j := PUnit.unit) (j' := PUnit.unit) (k := PUnit.unit)
      (V.faceTrToTr V (hT := hT) (hS := hS) (hθ := j'.2) (hθ' := k.2) a)
      (V.faceTrToTr V (hT := hT) (hS := hS) (hθ := i.2) (hθ' := j.2) b)
      (by
        change C.toGroupoidStr.src a.mor.mor = C.toGroupoidStr.tgt b.mor.mor
        rw [a.mor.src_mor, b.mor.tgt_mor]
        exact congrArg BObj.α hc')
    change _ = (S.modelGroupoid _).comp ⟨(PUnit.unit, PUnit.unit), _⟩ ⟨(PUnit.unit, PUnit.unit), _⟩
    rw [e₂]
    change (⟨(PUnit.unit, PUnit.unit), V.faceTrToTr V (hT := hT) (hS := hS)
      ((V.faceConstruction hT hS hc hcent hfix).modelGroupoid _ |>.comp ⟨(j', k), a⟩
        ⟨(i, j), b⟩).2⟩ : S.ModelMor (singleFamily (Ψ := Ψ))) = _
    rw [e₁]
    exact congrArg (Sigma.mk (PUnit.unit, PUnit.unit)) (V.faceForget_mor_comp hT hS hc hcent hfix
      a b hc')
  mor_unit z := congrArg (Sigma.mk (PUnit.unit, PUnit.unit)) (faceTrToTr_unit (V := V) z.2)
  isScSmoothMap_obj := by
    change (MPolyfold.sigma fun θ : V.faces => V.faceSubPolyfold hT θ.2).IsScSmoothMap
      (MPolyfold.sigma fun _ : PUnit.{u + 1} => Ψ.1.P)
      (Sigma.map (fun _ => PUnit.unit) fun θ (x : θ.1) => x.1)
    exact MPolyfold.isScSmoothMap_sigmaMap _ fun θ => (V.display_17_82 hT hS θ.2 θ.2).1
  isScSmoothMap_mor := by
    change (MPolyfold.sigma fun p : V.faces × V.faces =>
        (V.faceConstruction hT hS hc hcent hfix).transPolyfold
          (V.faceFamily hT hS hc hcent hfix p.1) (V.faceFamily hT hS hc hcent hfix p.2))
        |>.IsScSmoothMap
      (MPolyfold.sigma fun _ : PUnit.{u + 1} × PUnit.{u + 1} => S.transPolyfold Ψ Ψ)
      (Sigma.map (fun _ => (PUnit.unit, PUnit.unit)) fun p a =>
        V.faceTrToTr V (hT := hT) (hS := hS) (hθ := p.1.2) (hθ' := p.2.2) a)
    refine MPolyfold.isScSmoothMap_sigmaMap _ fun p => ?_
    have h := ftrIncl_isScSmoothMap hT hS hc hcent (V.faceFamily hT hS hc hcent hfix p.1).1
      (V.faceFamily hT hS hc hcent hfix p.2).1
      (V.faceDataAt hT hS hc hcent hfix (V.faceFamily hT hS hc hcent hfix p.1))
      (V.faceDataAt hT hS hc hcent hfix (V.faceFamily hT hS hc hcent hfix p.2))
      (V.faceDataAt_eq hT hS hc hcent hfix _) (V.faceDataAt_eq hT hS hc hcent hfix _)
    have hfun : (fun a => (ftrInclOf hT hS hc hcent (V.faceFamily hT hS hc hcent hfix p.1).1
        (V.faceFamily hT hS hc hcent hfix p.2).1
        (V.faceDataAt hT hS hc hcent hfix (V.faceFamily hT hS hc hcent hfix p.1))
        (V.faceDataAt hT hS hc hcent hfix (V.faceFamily hT hS hc hcent hfix p.2))
        (V.faceDataAt_eq hT hS hc hcent hfix _) (V.faceDataAt_eq hT hS hc hcent hfix _) a).1) =
        fun a => V.faceTrToTr V (hT := hT) (hS := hS) (hθ := p.1.2) (hθ' := p.2.2) a := by
      funext a
      obtain ⟨hm, hs, ht⟩ := (ftrInclOf_spec hT hS hc hcent _ _ _ _
        (V.faceDataAt_eq hT hS hc hcent hfix (V.faceFamily hT hS hc hcent hfix p.1))
        (V.faceDataAt_eq hT hS hc hcent hfix (V.faceFamily hT hS hc hcent hfix p.2))).2.2 a
      refine GroupoidStr.TransitionSet.ext (Ψ.1.injective_obj ?_) hm (Ψ.1.injective_obj ?_)
      · exact hs.trans (V.faceObj_α _ _ _)
      · exact ht.trans (V.faceObj_α _ _ _)
    rw [hfun] at h
    exact h

/-- `F` sends a point `x` of a face `θ` to `x ∈ O`. -/
theorem faceForget_obj (θ : V.faces) (x : Ψ.1.O) (hx : x ∈ θ.1) :
    (V.faceForget hT hS hc hcent hfix).obj ⟨θ, ⟨x, hx⟩⟩ = ⟨PUnit.unit, x⟩ := rfl

/-- **2021 (17.82), (17.83), pp. 810–811, for the ep-groupoid `Θ`**: `Θ = ⊔_θ θ` with the
morphisms `⊔ M(Ψ_θ, Ψ_{θ'})` is a tame ep-groupoid; `Ψ̂ : Θ → bC` is fully faithful; the square
`Ψ ∘ F = B ∘ Ψ̂` commutes; `F` is the only functor `Θ → G ⋉ O` making it commute ("`F` is uniquely
determined by the rest of the diagram"); `F` maps the objects of `Θ` onto `U(ō)`, and
`|B|⁻¹(|Ψ(V(ō))|) = |Ψ̂|(|Θ|)` ((17.83)). -/
theorem display_17_82_Theta :
    (V.faceThetaEp hT hS hc hcent hfix).IsTame ∧
    (V.faceHat hT hS hc hcent hfix).toFunctor.Full ∧
    (V.faceHat hT hS hc hcent hfix).toFunctor.Faithful ∧
    (S.modelFunctor (singleFamily (Ψ := Ψ))).comp
        (V.faceForget hT hS hc hcent hfix).toGroupoidFunctor =
      (S.bdryFunctorC hT hS).comp (V.faceHat hT hS hc hcent hfix) ∧
    (∀ F' : GroupoidFunctor (V.faceThetaEp hT hS hc hcent hfix).toGroupoidStr
        (S.modelEpGroupoid (singleFamily (Ψ := Ψ))).toGroupoidStr,
      (S.modelFunctor (singleFamily (Ψ := Ψ))).comp F' =
        (S.bdryFunctorC hT hS).comp (V.faceHat hT hS hc hcent hfix) →
      F' = (V.faceForget hT hS hc hcent hfix).toGroupoidFunctor) ∧
    range (V.faceForget hT hS hc hcent hfix).obj = {z | z.2 ∈ V.bdry} ∧
    S.bdrySigma hT hS ⁻¹' ((fun q : Ψ.1.O => C.toGroupoidStr.π (Ψ.1.obj q)) '' V.1.U) =
      range (V.faceHat hT hS hc hcent hfix).orbitMap := by
  have hsq : (S.modelFunctor (singleFamily (Ψ := Ψ))).comp
      (V.faceForget hT hS hc hcent hfix).toGroupoidFunctor =
      (S.bdryFunctorC hT hS).comp (V.faceHat hT hS hc hcent hfix) :=
    GroupoidFunctor.ext (funext fun z => (V.faceObj_α (hT := hT) (hS := hS) _ _ _).symm) rfl
  refine ⟨isTame_modelEpGroupoid _ _ (V.faceConstruction_isTame hT hS hc hcent hfix),
    modelFunctor_full _ _, modelFunctor_faithful _ _, hsq, fun F' hF' => ?_, ?_, ?_⟩
  · have hobj : ∀ z, F'.obj z = (V.faceForget hT hS hc hcent hfix).obj z := by
      intro z
      have h1 : Ψ.1.obj (F'.obj z).2 = Ψ.1.obj z.2.1 :=
        congrArg (fun G => G.obj z) (hF'.trans hsq.symm)
      exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (Ψ.1.injective_obj h1))
    refine GroupoidFunctor.ext (funext hobj) (funext fun m => ?_)
    refine (GroupoidFunctor.faithful_iff _).1 (S.modelFunctor_faithful _) _ _ ?_ ?_ ?_
    · exact (F'.src_mor m).trans ((hobj _).trans
        ((V.faceForget hT hS hc hcent hfix).src_mor m).symm)
    · exact (F'.tgt_mor m).trans ((hobj _).trans
        ((V.faceForget hT hS hc hcent hfix).tgt_mor m).symm)
    · exact congrArg (fun G => G.mor m) (hF'.trans hsq.symm)
  · ext z
    constructor
    · rintro ⟨⟨θ, x⟩, rfl⟩
      exact V.subset_bdry θ.2 x.2
    · intro hz
      obtain ⟨⟨⟩, x⟩ := z
      change x ∈ V.bdry at hz
      rw [← V.sUnion_faces] at hz
      obtain ⟨θ, hθ, hx⟩ := hz
      exact ⟨⟨⟨θ, hθ⟩, ⟨x, hx⟩⟩, rfl⟩
  · rw [(V.display_17_83 hT hS hc hfix).2]
    ext z
    constructor
    · intro hz
      obtain ⟨θ, hθ, hz⟩ := mem_iUnion₂.1 hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨(V.faceThetaEp hT hS hc hcent hfix).π ⟨⟨θ, hθ⟩, ⟨x, hx⟩⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      induction w using Quotient.inductionOn with
      | h z =>
        exact mem_iUnion₂.2 ⟨z.1.1, z.1.2, z.2.1, z.2.2, rfl⟩

end GoodNbhd

section SwapWitness

open MPolyfold TameBoundaryExample EpGroupoid.Examples Pointwise

variable (W : ScBanach)

set_option maxHeartbeats 800000 in
-- The statement unfolds the object type of the model ep-groupoid of the swap polyfold.
/-- **The hypotheses of `display_17_82_Theta` in a non-degenerate case**: for the swap polyfold
`ℤ/2 ⋉ ([0,∞)² ⊕ W)` (tame, with uniformizers, `Ψ̂` continuous, centred uniformizers) and the
corner uniformizer `Ψ₀` (which fixes the corner), a good neighbourhood `U(0)` has two faces
`θ ≠ θ' = (−1)·θ`; the corner gives an object of `Θ` in each of them, and `F` sends both to the
corner of `O`, so `Θ` has two components and `F` is not injective on objects. -/
theorem swap_display_17_82_Theta :
    ∃ (hT : (swapConstruction W).IsTame) (hS : (swapConstruction W).HasUniformizers)
      (hc : (swapConstruction W).HatContinuous) (hcent : (swapConstruction W).IsCentred)
      (V : (swapConstruction W).GoodNbhd (swapUnif₀ W) (swapCorner W))
      (hfix : (swapUnif₀ W).1.FixesPoint (swapCorner W)),
      V.faces.encard = 2 ∧
      ∃ (θ θ' : Set (swapUnif₀ W).1.O) (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V.faces), θ ≠ θ' ∧
        (V.faceForget hT hS hc hcent hfix).obj ⟨⟨θ, hθ⟩, ⟨swapCorner W, V.mem_of_mem_faces hθ⟩⟩ =
          ⟨PUnit.unit, swapCorner W⟩ ∧
        (V.faceForget hT hS hc hcent hfix).obj
            ⟨⟨θ', hθ'⟩, ⟨swapCorner W, V.mem_of_mem_faces hθ'⟩⟩ =
          ⟨PUnit.unit, swapCorner W⟩ := by
  have hT := swapConstruction_isTame W
  have hS := swapConstruction_hasUniformizers W
  have hc := swapConstruction_hatContinuous W
  have hcent := swapConstruction_isCentred W
  have hmem : (swapUnif₀ W).1 ∈ (swapConstruction W).F (corner W) :=
    ⟨swapSlice₀ W, Or.inl rfl, mem_univ _, fun k _ => by
      rcases Int.units_eq_one_or k with rfl | rfl
      · exact one_smul _ _
      · rw [neg_one_smul_eq]; exact swapQ_corner W, rfl⟩
  have hfix : (swapUnif₀ W).1.FixesPoint (swapCorner W) := hcent.fixesPoint hmem rfl
  have hd : (swapUnif₀ W).1.P.degIndex (swapCorner W) = 2 := by
    rw [degIndex_swapUnif₀]; exact quadrantPolyfold_degIndex_zero 2 W
  have hb : swapCorner W ∈ (swapUnif₀ W).1.P.boundary := by
    change 1 ≤ _
    rw [hd]; decide
  obtain ⟨V, -⟩ := (swapConstruction W).exists_goodNbhd (Ψ := swapUnif₀ W)
    (isTame_unif _ hT _) hb isOpen_univ (mem_univ _)
  have hV2 : V.faces.encard = 2 := by rw [V.encard_faces, hd]; rfl
  obtain ⟨θ, hθ⟩ : V.faces.Nonempty := by
    rw [← Set.encard_pos, hV2]; norm_num
  have hθ' := V.smul_mem_faces hfix (swapGen W) hθ
  refine ⟨hT, hS, hc, hcent, V, hfix, hV2, θ, _, hθ, hθ',
    (swapGen_smul_ne W (V.mem_faces_iff.1 hθ)).symm, ?_, ?_⟩
  · exact V.faceForget_obj hT hS hc hcent hfix ⟨θ, hθ⟩ (swapCorner W) (V.mem_of_mem_faces hθ)
  · exact V.faceForget_obj hT hS hc hcent hfix ⟨_, hθ'⟩ (swapCorner W) (V.mem_of_mem_faces hθ')

end SwapWitness

end GCT.PolyfoldConstruction

end Polyfold
