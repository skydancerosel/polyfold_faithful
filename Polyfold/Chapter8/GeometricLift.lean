import Polyfold.Chapter8.Basic
import Polyfold.Chapter8.SigmaPolyfold
import Polyfold.Chapter8.ProperCovering
import Polyfold.Chapter8.ProperCoveringLocal
import Polyfold.Chapter8.TangentLocal
import Polyfold.Chapter7.NonVacuity

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8: the discussion after **Definition 8.9** (pp. 280–281), **Proposition 8.3**
(pp. 281–282) and **Theorem 8.6** (pp. 283–284): the proper covering functor of a geometric lift,
and the local model of a proper covering functor (§8.4, pp. 279–284).  There is no 2014 preprint
of Part II; numbers and pages are the 2017 text's.  The definitions (`IsCoveringFunctor`,
`GeometricLift`, `EpFunctor.IsProperCovering`) are in `Polyfold/Chapter8/Basic.lean`, the
disjoint unions of M-polyfolds in `Polyfold/Chapter8/SigmaPolyfold.lean`, Theorem 8.5 and its
charts `EpFunctor.ProperCoveringChart` in `Polyfold/Chapter8/ProperCoveringLocal.lean`, the unique
lifting of Definition 8.8 (3) in `Polyfold/Chapter8/ProperCovering.lean`.

# Geometric lifts and the local model of a proper covering functor

## The text, paraphrased

(pp. 280–281) Let `f : D → C` be a covering functor (Definition 8.9), `x` the object of `C`, and
`τ : L_D → L_C ∘ f` a geometric lift.  Write `U(x) = L_C(x)` and `U(y) = L_D(y)`; `τ(y) : U(y) →
U(x)` is an sc-diffeomorphism, and so is `φ_{yy'}(ψ) = L_D(ψ) : U(y) → U(y')` for `ψ : y → y'`.
By functoriality `φ_{yy''}(ψ ∘ γ) = φ_{y'y''}(ψ) ∘ φ_{yy'}(γ)`.  The isotropy groups act by
`h ∗ z = L_D(h)(z)` (`h ∈ G_y`, `z ∈ U(y)`) and `g ∗ z = L_C(g)(z)` (`g ∈ G_x`, `z ∈ U(x)`), and
the naturality of `τ` gives `τ(y)(h ∗ z) = f(h) ∗ τ(y)(z)`: the `τ(y)` are equivariant along
`f : G_y → G_x`.

(Proposition 8.3) A covering functor with a geometric lift gives a natural proper covering
functor `F : Y → X` of ep-groupoids.  Proof: `X = G_x ⋉ U(x)`, with morphisms `G_x × U(x)`,
`s(g, z) = z`, `t(g, z) = g ∗ z`.  `Y` has the objects `⊔_{y ∈ D} U(y)` and the morphisms
`⊔_{(y, y')} mor(y, y') × U(y)`, both with natural M-polyfold structures; `s(ψ, z) = z` and
`t(ψ, z) = φ_{yy'}(ψ)(z)` are surjective local sc-diffeomorphisms; `(ψ, z') ∘ (γ, z) =
(ψ ∘ γ, z)` for `z' = φ_{yy'}(γ)(z)`, `u(z) = (1_y, z)`, `ι(ψ, z) = (ψ⁻¹, φ_{yy'}(ψ)(z))`; "one
verifies" that the composition is sc-smooth and that the properness property holds.
`F|U(y) = τ(y)` and `F(ψ, z) = (f(ψ), τ(y)(z))`; since `F⁻¹(U(x)) = Y`, `F` is a surjective
local sc-diffeomorphism on objects.  The map (8.16) `𝐘 → 𝐗 ₛ×_F Y`,
`(ψ, z) ↦ ((f(ψ), F(z)), z)`, is injective (by the bijectivity of `ψ ↦ (f(ψ), s(ψ))`),
surjective (take the `ψ` with `f(ψ) = g`, `s(ψ) = y`) and a local sc-diffeomorphism, hence an
sc-diffeomorphism.

(Theorem 8.6, Proper Covering II) Let `F : Y → X` be a proper covering functor and `x ∈ X`; `C`
is the full subcategory on `x` (morphisms `G_x`), `D` the full subcategory on the finite set
`F⁻¹(x)`.  Then `f = F|D : D → C` is a covering functor, and for `U(x)` as in Theorem 8.5 there
are a geometric lift `A : K → L` of `f` and fully faithful open embedding functors `Φ : L → X`,
`Ψ : K → Y`, the image of `Φ` the full subcategory on `U(x)`, that of `Ψ` the full subcategory on
`F⁻¹(U(x))`, with `F ∘ Ψ = Φ ∘ A`.  Proof: `L_C(x) = U(x)`, `L_C(g) = Φ(g)`; `L_D(y) = U(y)` and
`L_D(ψ) = t ∘ (s|𝐔(ψ₀))⁻¹` for `ψ : y → y'` in `𝐔(ψ₀)`, `ψ₀` the distinguished morphism; `τ(y) =
F|U(y)`; "one verifies" that this is a geometric lift.  `A : K → L` is its functor of
Proposition 8.3, `L = G_x ⋉ U(x)`, `K = ⊔ U(y)`, `𝐊 = ⊔ mor(y, y') × U(y)`, `A|U(y) = F|U(y)`,
`A(ψ, z) = (f(ψ), F(z))`.  `Φ` is the inclusion on objects and `Φ(g, z) = Γ(g, z)`; `Ψ` is the
inclusion on objects and `Ψ(ψ, z) = (s|𝐔(ψ₀))⁻¹(z)`.  The square commutes, and `A` is, up to `Φ`
and `Ψ`, a local model of `F` near `x` and `F⁻¹(x)`.

## What is formalized

* Covering functors: `IsCoveringFunctor.existsUnique_lift` (exactly one `ψ` with `s(ψ) = y` and
  `f(ψ) = g`), `IsCoveringFunctor.lift`, `map_lift`, `lift_map`; `isCoveringFunctor_of_isEmpty`.
* The data of a geometric lift (namespace `GeometricLift`): `Ux` (`U(x)`), `τy`, `τyInv`,
  `isScDiffeoOn_τy`; `φ`, `φInv`, `isScDiffeoOn_φ`; **functoriality** `φ_comp`, with `φ_id` and
  `φ_inv_φ`; the two actions, as scoped instances `instMulActionC` (`G = G_x` on `U(x)`,
  `smul_def`) and `instMulActionD` (`End y = G_y` on `U(y)`, `smul_def'`),
  `isScSmoothMap_smul`; naturality on points `τy_φ` (`τ(y')(φ(ψ)(z)) = f(ψ) ∗ τ(y)(z)`) and
  **equivariance** `τ_equivariant` (`τ(y)(h ∗ z) = f(h) ∗ τ(y)(z)`, p. 281).
* **`Y`**: the types `YObj`, `YMor`; the maps `ySrc`, `yTgt`, `yComp`, `yUnit`, `yInv` (with
  `homComp`, `homComp_mk`, `yComp_mk`, `composable_cases`); the groupoid `sourceStr`; the
  M-polyfolds `yObjPolyfold`, `yMorPolyfold`; `isLocalScDiffeo_ySrc`, `isLocalScDiffeo_yTgt`,
  `isScSmoothMap_yUnit`, `isScSmoothMap_yInv`, `isProperMap_yTgt`, `isScSmoothCompSheet_y`;
  **the ep-groupoid** `geometricLiftSource L`, with `geometricLiftSource_src`, `_tgt`,
  `_comp_mk`, `_unit`, `_inv`, `_PObj`, `_PMor`, `_surjective_src`, `_surjective_tgt`.
* **`X`**: the translation groupoid `geometricLiftTarget L` (Chapter 7's `actionEpGroupoid`),
  with `geometricLiftTarget_src`, `_tgt`, `_comp`, `_unit`, `_inv`, `_PObj`, `_PMor`.
* **`F`**: `geometricLiftFunctor L : EpFunctor (geometricLiftSource L) (geometricLiftTarget L)`,
  `geometricLiftFunctor_obj`, `_mor`.
* **Proposition 8.3**: `proposition_8_3 [Nonempty D] (hf : IsCoveringFunctor f) L :
  (geometricLiftFunctor L).IsProperCovering`, from `geometricLiftFunctor_surjective`,
  `_isLocalScDiffeo`, `_finite_fiber`, `_evenlyCovered`, and **(8.16)**
  `geometricLiftFunctor_isScDiffeo_fibredMap` (inverse `GeometricLift.fibredInv`,
  `isScSmoothMap_fibredInv`).  `geometricLiftFunctor_surjective_iff`: `F` is surjective on
  objects if and only if `D ≠ ∅` or `U(x) = ∅`.
* **Theorem 8.6.**  Full subcategories: `GroupoidStr.FullOb G A` with the groupoid structure
  `instGroupoidFullOb` (the morphisms of `G`), `FullOb.comp_val`, `FullOb.id_val`.  `D` is
  `EpFunctor.FiberCat F x`; `EpFunctor.fiberIsotropy` (`F(ψ) ∈ G_x`), `fiberIsotropy_id`,
  `fiberIsotropy_comp`; `f = F|D` is `EpFunctor.restrictFiber F x : D ⥤ SingleObj G_x`;
  **`EpFunctor.covering_restrict`** (`f` is a covering functor), `finite_fiberCat`,
  `finite_fiberCat_hom`, `nonempty_fiberCat`, `fintypeFiberCat`, `fintypeFiberCatHom`,
  `mem_morOn_of_hom`.  Open subsets in `Diff_sc`: `MPolyfoldCat.ofOpen`, `ScDiffeo.ofOpen`.
  `EpFunctor.IsFullyFaithfulOpenEmbedding` (with `isOpen_range_obj`, `isOpen_range_mor`) and
  `EpFunctor.faithful_of_injective_mor`.  For a chart `C : F.ProperCoveringChart x` of
  Theorem 8.5 (namespace `EpFunctor.ProperCoveringChart`): the inverses `σObj`, `σSrc`, `σTgt` of
  `F|U(y)`, `s|𝐔(ψ₀)`, `t|𝐔(ψ₀)`; `mor_σSrc` (`F(σ_ψ(z)) = Γ(f(ψ), F(z))`), `obj_tgt_σSrc`,
  `isScDiffeoOn_hat`, `hat_id`, `hat_comp`, `σSrc_comp`, `σSrc_id`; the lift `liftLD`, `liftLC`,
  `liftτ`, **`geometricLift`** (`geometricLift_τy_val`, `_φ_val`, `_LC_map_val`); **`Φ`** and
  **`Ψ hF`**, with `isFullyFaithfulOpenEmbedding_Φ`, `isFullyFaithfulOpenEmbedding_Ψ`,
  `range_Φ_obj`, `range_Φ_mor`, `range_Ψ_obj`, `range_Ψ_mor`; **`comp_Ψ`** (`F ∘ Ψ = Φ ∘ A`).
  **`EpFunctor.theorem_8_6`**: (a) `f` is a covering functor, (b) charts exist with `U(x)` in
  every open `V ∋ x` (Theorem 8.5), (c) for every chart there are `L`, `Φ`, `Ψ` with `A` a proper
  covering functor (Proposition 8.3), `Φ`, `Ψ` fully faithful open embeddings with the stated
  images, and `F ∘ Ψ = Φ ∘ A`.

## What the text leaves implicit, and the choices made

* **`D` nonempty.**  Definition 8.9 allows `D = ∅` (`isCoveringFunctor_of_isEmpty`: the map
  `ψ ↦ (f(ψ), s(ψ))` is then a bijection of empty sets); then `Y = ∅` while `U(x)` is arbitrary,
  and `F` is surjective on objects (Definition 8.8 (1)) only if `U(x) = ∅`
  (`geometricLiftFunctor_surjective_iff`).  The text does not say so; `proposition_8_3` assumes
  `[Nonempty D]`, used for the surjectivity only.  It holds in Theorem 8.6, where `D = F⁻¹(x)`.
* **`F : Y → X`.**  The proof's "the map `F : X → Y` is a surjective local sc-diffeomorphism
  between the object sets" is read as `F : Y → X` (possible misprint).  Definition 8.8 (2) holds
  with `U(x)` the whole object space of `X` and, for `w ∈ U(x)`, the summands `U(y)` around the
  points `(y, τ(y)⁻¹(w))` of `F⁻¹(w)`, one in each summand.
* **Finiteness** of Definition 8.9 ("finitely many objects and morphisms") enters as the
  hypotheses `[Fintype D] [∀ a b, Fintype (a ⟶ b)] [Fintype G]` (`IsCoveringFunctor` and
  `GeometricLift` do not carry them).  Finitely many morphisms of `D` make `t : 𝐘 → Y` proper,
  finitely many objects make the fibres `F⁻¹(w)` finite, and a finite `G` makes `G ⋉ U(x)` an
  ep-groupoid.
* **`X = G_x ⋉ U(x)`.**  `G_x = C` is the group `G` of `SingleObj G`, acting by
  `g ∗ z = L_C(g)(z)`; this is a left action (in `SingleObj G`, `g ≫ h = h * g`, and
  `L_C(g ≫ h) = L_C(h) ∘ L_C(g)`).  `G` carries a discrete topology (the hypotheses
  `[TopologicalSpace G] [DiscreteTopology G]`, satisfiable by `⊥`) and is lifted to the universe
  of `U(x)` (`ULift.{u} G`), since Chapter 7's translation groupoid takes its group and its space
  in one universe.
* **The M-polyfold structures of `Y`** are the disjoint-union structures of `SigmaPolyfold.lean`.
  `mor(y, y') × U(y)` is modelled as `⊔_{ψ : y → y'} U(y)`, the morphism type being
  `Σ ψ : (Σ a b, a ⟶ b), U(s(ψ))`; `isScDiffeoOn_prod_discrete_sigma` identifies this with the
  product of the discrete `mor(y, y')` and `U(y)`.
* **The composition of `Y`** is total, as Chapter 7's `GroupoidStr.comp`: `(ψ, z') ∘ (γ, z) =
  (ψ ∘ γ, z)`, with `ψ ∘ γ` the composite when `t(γ) = s(ψ)` and the junk value `γ` otherwise
  (`homComp`).  "One verifies" is carried out.  Sc-smoothness, in the sheet form of
  Definition 7.3 (4): near `(ψ₀, z₀)` the map `ψ ↦ σ(t ψ) ∘ ψ` is `(ψ₀, z) ↦ (γ₀ ∘ ψ₀, z)`, the
  summand index `γ₀` of `σ(t ψ)` being locally constant.  Properness: Definition 7.3 (3) holds
  with `V = Y`, since `t` is proper (finitely many summands, each mapped homeomorphically onto a
  summand).
* **(8.16).**  The text deduces the sc-diffeomorphism from "bijection and local
  sc-diffeomorphism"; we prove the sc-smoothness of the inverse directly: near
  `((g₀, q₀), (y₀, z₀))` it is `((g₀, q), (y₀, z)) ↦ (ψ₀, z)`, `ψ₀` the lift of `g₀` at `y₀`.
* Functoriality is stated with Mathlib's `γ ≫ ψ` for the text's `ψ ∘ γ`; the isotropy group
  `G_y` is Mathlib's monoid `End y` (`h * k = k ≫ h`, the text's `h ∘ k`), and `f : G_y → G_x`
  is `h ↦ f.map h`.
* **Theorem 8.6: universes.**  Definition 8.9 (`Basic.lean`) takes `D` and `G` in `Type` and
  `Diff_sc` in one universe, so Theorem 8.6 is stated for ep-groupoids whose object and morphism
  types are in `Type`.
* **`C` and `D`.**  `C`, the full subcategory on `x`, is `SingleObj G_x` (as in Definition 8.9).
  `D` is `GroupoidStr.FullOb` on `F⁻¹(x)`: objects the points of `F⁻¹(x)`, morphisms `y → y'` the
  morphisms of `Y` (Chapter 7's bridge `GroupoidStr.Ob`).  Its finiteness, from Definition 8.8,
  enters the statement as the local instances `fintypeFiberCat`, `fintypeFiberCatHom` and
  `Fintype.ofFinite` (Proposition 7.4); `D ≠ ∅`, needed in Proposition 8.3, is the surjectivity
  of `F`.
* **"A sufficiently small `U(x)` as in Theorem 8.5"** is a chart `C : F.ProperCoveringChart x`
  (`U(x) = C.R.U`); part (b) of `theorem_8_6` restates `theorem_8_5` (charts with `U(x)` inside
  every open `V ∋ x`), and part (c) holds for every chart.
* **`L_D` on morphisms.**  The morphisms of `D` are the distinguished morphisms `ψ₀` themselves, so
  "`ψ : y → y' ∈ 𝐔(ψ₀)`" is read as `ψ = ψ₀` and `L_D(ψ₀) = t ∘ (s|𝐔(ψ₀))⁻¹`; likewise
  `Ψ(ψ₀, z) = (s|𝐔(ψ₀))⁻¹(z)`.
* **"One verifies"** is carried out through `F`: on the sheets `F(σ_ψ(z)) = Γ(f(ψ), F(z))`
  (Theorem 8.5 (1), (4)), so `τ(y') ∘ L_D(ψ) = Φ(f(ψ)) ∘ τ(y)` (the naturality of `τ`), and the
  functoriality of `L_D` follows from that of `Φ` and the injectivity of `F` on each `U(y)`.  That
  `Ψ` preserves compositions and units uses the unique lifting of Definition 8.8 (3).
* **"Fully faithful open embedding"** is `EpFunctor.IsFullyFaithfulOpenEmbedding`: the functor of
  the underlying groupoids (`GroupoidFunctor.toFunctor`) is full and faithful, and on objects and
  on morphisms the functor is an injective local sc-diffeomorphism (an sc-diffeomorphism onto its
  image, which is open).  "The image of `Φ` is the full subcategory on `U(x)`" is
  `range Φ.obj = U(x)` and `range Φ.mor = {φ | s(φ), t(φ) ∈ U(x)}`; likewise for `Ψ` and
  `F⁻¹(U(x))`.  `L = G_x ⋉ U(x)` is `geometricLiftTarget`, `G_x` discrete (Chapter 7's scoped
  instance) and lifted by `ULift`.
* **Possible misprints in Theorem 8.6**, as we read it: "there exists exists" (a repeated word);
  "`τ(t) : L_D(y) → L_C ∘ f(y)`" for `τ(y)`; "`A(ψ, z) = (f(z), F(z))`" for `(f(ψ), F(z))`, as in
  Proposition 8.3's `F(ψ, z) = (f(ψ), τ(y)(z))`.
-/

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Maps into a sub-M-polyfold -/

section SubPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- A map into a sub-M-polyfold `A ⊆ Y` is sc-smooth into `A` as soon as it is sc-smooth into
`Y` (Proposition 2.21 (2): near `f(x)`, `f = (i⁻¹ ∘ r) ∘ i ∘ f`). -/
private theorem isScSmoothOn_subPolyfold_of_val {A : Set Y} (hA : Q.IsSubMPolyfold A)
    [ParacompactSpace A] {f : X → A} {U : Set X}
    (hf : P.IsScSmoothOn Q (fun x => (f x : Y)) U) :
    P.IsScSmoothOn (MPolyfold.subPolyfold hA) f U := by
  refine MPolyfold.IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : Y)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (MPolyfold.subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

end SubPolyfold

/-! ### Covering functors: unique lifts -/

namespace IsCoveringFunctor

variable {D : Type} [Groupoid.{0} D] {G : Type} [Group G] {f : D ⥤ SingleObj G}

/-- A covering functor has unique lifts: for `g ∈ G` and `y ∈ D` there is exactly one
`ψ : y → b` with `f(ψ) = g`. -/
theorem existsUnique_lift (hf : IsCoveringFunctor f) (g : G) (y : D) :
    ∃! ψ : Σ b : D, y ⟶ b, (f.map ψ.2 : G) = g := by
  obtain ⟨⟨a, b, ψ⟩, h⟩ := hf.2 (g, y)
  have h' : ((f.map ψ : G), a) = (g, y) := h
  obtain ⟨hg, rfl⟩ := Prod.mk_inj.1 h'
  refine ⟨⟨b, ψ⟩, hg, ?_⟩
  rintro ⟨b', ψ'⟩ hψ'
  have h' : coveringMap f ⟨a, b', ψ'⟩ = coveringMap f ⟨a, b, ψ⟩ :=
    Prod.ext (hψ'.trans hg.symm) rfl
  exact eq_of_heq (Sigma.mk.inj_iff.1 (hf.1 h')).2

/-- The lift `ψ : y → b` of `g` with `s(ψ) = y`. -/
def lift (hf : IsCoveringFunctor f) (g : G) (y : D) : Σ b : D, y ⟶ b :=
  (hf.existsUnique_lift g y).exists.choose

theorem map_lift (hf : IsCoveringFunctor f) (g : G) (y : D) :
    (f.map (hf.lift g y).2 : G) = g :=
  (hf.existsUnique_lift g y).exists.choose_spec

theorem lift_map (hf : IsCoveringFunctor f) {y b : D} (ψ : y ⟶ b) :
    hf.lift (f.map ψ : G) y = ⟨b, ψ⟩ :=
  (hf.existsUnique_lift _ y).unique (hf.map_lift _ _) rfl

end IsCoveringFunctor

/-- Definition 8.9 allows `D = ∅`: every functor out of an empty groupoid is a covering
functor. -/
theorem isCoveringFunctor_of_isEmpty {D : Type} [Groupoid.{0} D] [IsEmpty D] {G : Type} [Group G]
    (f : D ⥤ SingleObj G) : IsCoveringFunctor f :=
  ⟨fun a => isEmptyElim a.1, fun p => isEmptyElim p.2⟩

/-! ### The data of a geometric lift (pp. 280–281) -/

namespace GeometricLift

variable {D : Type} [Groupoid.{0} D] {G : Type} [Group G] {f : D ⥤ SingleObj G}
  (L : GeometricLift.{u} f)

/-- `U(x) = L_C(x)`. -/
abbrev Ux : Type u := (L.LC.obj (SingleObj.star G)).carrier

/-- `τ(y) : U(y) → U(x)`. -/
def τy (y : D) : (L.LD.obj y).carrier → L.Ux := (L.τ.app y).toFun

/-- The inverse of `τ(y)`. -/
def τyInv (y : D) : L.Ux → (L.LD.obj y).carrier := (L.τ.app y).invFun

/-- `τ(y) : U(y) → U(x)` is an sc-diffeomorphism (a morphism of `Diff_sc`; `f(y) = x`). -/
theorem isScDiffeoOn_τy (y : D) :
    (L.LD.obj y).P.IsScDiffeoOn (L.LC.obj (SingleObj.star G)).P (L.τy y) (L.τyInv y) univ univ :=
  (L.τ.app y).isScDiffeoOn

theorem τyInv_τy (y : D) (z : (L.LD.obj y).carrier) : L.τyInv y (L.τy y z) = z :=
  (L.isScDiffeoOn_τy y).left_inv z (mem_univ z)

theorem τy_τyInv (y : D) (w : L.Ux) : L.τy y (L.τyInv y w) = w :=
  (L.isScDiffeoOn_τy y).right_inv w (mem_univ w)

/-- `φ_{yy'}(ψ) = L_D(ψ) : U(y) → U(y')`. -/
def φ {y y' : D} (ψ : y ⟶ y') : (L.LD.obj y).carrier → (L.LD.obj y').carrier :=
  (L.LD.map ψ).toFun

/-- The inverse of `φ_{yy'}(ψ)`. -/
def φInv {y y' : D} (ψ : y ⟶ y') : (L.LD.obj y').carrier → (L.LD.obj y).carrier :=
  (L.LD.map ψ).invFun

/-- `φ_{yy'}(ψ) : U(y) → U(y')` is an sc-diffeomorphism. -/
theorem isScDiffeoOn_φ {y y' : D} (ψ : y ⟶ y') :
    (L.LD.obj y).P.IsScDiffeoOn (L.LD.obj y').P (L.φ ψ) (L.φInv ψ) univ univ :=
  (L.LD.map ψ).isScDiffeoOn

theorem φInv_φ {y y' : D} (ψ : y ⟶ y') (z : (L.LD.obj y).carrier) : L.φInv ψ (L.φ ψ z) = z :=
  (L.isScDiffeoOn_φ ψ).left_inv z (mem_univ z)

theorem φ_φInv {y y' : D} (ψ : y ⟶ y') (z : (L.LD.obj y').carrier) : L.φ ψ (L.φInv ψ z) = z :=
  (L.isScDiffeoOn_φ ψ).right_inv z (mem_univ z)

theorem continuous_φInv {y y' : D} (ψ : y ⟶ y') : Continuous (L.φInv ψ) :=
  continuousOn_univ.1 (L.isScDiffeoOn_φ ψ).isScSmoothOn_inv.continuousOn

theorem isLocalScDiffeo_φ {y y' : D} (ψ : y ⟶ y') :
    (L.LD.obj y).P.IsLocalScDiffeo (L.LD.obj y').P (L.φ ψ) :=
  fun z => ⟨univ, univ, L.φInv ψ, mem_univ z, L.isScDiffeoOn_φ ψ⟩

/-- **Functoriality** (p. 280): `φ_{yy''}(ψ ∘ γ) = φ_{y'y''}(ψ) ∘ φ_{yy'}(γ)` (Mathlib's `γ ≫ ψ`
is the text's `ψ ∘ γ`). -/
theorem φ_comp {y y' y'' : D} (γ : y ⟶ y') (ψ : y' ⟶ y'') :
    L.φ (γ ≫ ψ) = L.φ ψ ∘ L.φ γ := by
  unfold φ
  rw [L.LD.map_comp]
  rfl

theorem φ_id (y : D) : L.φ (𝟙 y) = id := by
  unfold φ
  rw [L.LD.map_id]
  rfl

theorem φ_inv_φ {y y' : D} (ψ : y ⟶ y') (z : (L.LD.obj y).carrier) :
    L.φ (Groupoid.inv ψ) (L.φ ψ z) = z := by
  change (L.φ (Groupoid.inv ψ) ∘ L.φ ψ) z = z
  rw [← L.φ_comp, Groupoid.comp_inv, L.φ_id]
  rfl

/-- **The action of `G_x` on `U(x)`** (p. 281): `g ∗ z = L_C(g)(z)`. -/
scoped instance instMulActionC : MulAction G L.Ux where
  smul g z := (L.LC.map (g : SingleObj.star G ⟶ SingleObj.star G)).toFun z
  one_smul z := by
    change (L.LC.map (𝟙 (SingleObj.star G))).toFun z = z
    rw [L.LC.map_id]
    rfl
  mul_smul g h z := by
    change (L.LC.map (CategoryStruct.comp (X := SingleObj.star G) (Y := SingleObj.star G)
      (Z := SingleObj.star G) h g)).toFun z = _
    rw [L.LC.map_comp]
    rfl

theorem smul_def (g : G) (z : L.Ux) :
    g • z = (L.LC.map (g : SingleObj.star G ⟶ SingleObj.star G)).toFun z := rfl

/-- `G_x` (lifted to `ULift G`) acts on `U(x)` by the sc-diffeomorphisms `L_C(g)`. -/
theorem isScSmoothMap_smul (g : ULift.{u} G) :
    (L.LC.obj (SingleObj.star G)).P.IsScSmoothMap (L.LC.obj (SingleObj.star G)).P
      fun z : L.Ux => g • z :=
  (L.LC.map (g.down : SingleObj.star G ⟶ SingleObj.star G)).isScDiffeoOn.isScSmoothOn

/-- **The action of `G_y` on `U(y)`** (p. 281): `h ∗ z = L_D(h)(z)` for `h ∈ G_y = End y`
(Mathlib's `h * k = k ≫ h`, the text's `h ∘ k`). -/
scoped instance instMulActionD (y : D) : MulAction (End y) (L.LD.obj y).carrier where
  smul h z := L.φ h z
  one_smul z := congrFun (L.φ_id y) z
  mul_smul h k z := congrFun (L.φ_comp k h) z

theorem smul_def' {y : D} (h : End y) (z : (L.LD.obj y).carrier) : h • z = L.φ h z := rfl

/-- Naturality of `τ`, applied to a point: `τ(y')(φ_{yy'}(ψ)(z)) = f(ψ) ∗ τ(y)(z)`. -/
theorem τy_φ {y y' : D} (ψ : y ⟶ y') (z : (L.LD.obj y).carrier) :
    L.τy y' (L.φ ψ z) = (f.map ψ : G) • L.τy y z :=
  congrFun (congrArg ScDiffeo.toFun (L.τ.naturality ψ)) z

/-- **Equivariance of `τ(y)`** (p. 281): `τ(y)(h ∗ z) = f(h) ∗ τ(y)(z)` for `h ∈ G_y`; the
sc-diffeomorphisms `τ(y) : U(y) → U(x)` are equivariant along `f : G_y → G_x`. -/
theorem τ_equivariant {y : D} (h : End y) (z : (L.LD.obj y).carrier) :
    L.τy y (h • z) = (f.map h : G) • L.τy y z :=
  L.τy_φ h z

/-! ### The object and morphism sets of `Y` -/

/-- The object set `Y = ⊔_{y ∈ D} U(y)`. -/
abbrev YObj : Type u := Σ y : D, (L.LD.obj y).carrier

/-- The morphism set `𝐘 = ⊔_{(y, y')} mor(y, y') × U(y)`, as `⊔_{ψ : y → y'} U(y)`. -/
abbrev YMor : Type u := Σ ψ : (Σ a b : D, a ⟶ b), (L.LD.obj ψ.1).carrier

end GeometricLift

open scoped Classical in
/-- The composite `ψ ∘ γ` (Mathlib's `γ ≫ ψ`) of morphisms of `D`, as a morphism out of `s(γ)`,
when `t(γ) = s(ψ)`; the junk value `γ` otherwise. -/
def homComp {D : Type} [Groupoid.{0} D] (ψ γ : Σ a b : D, a ⟶ b) : Σ b : D, γ.1 ⟶ b :=
  if h : γ.2.1 = ψ.1 then ⟨ψ.2.1, γ.2.2 ≫ eqToHom h ≫ ψ.2.2⟩ else γ.2

@[simp] theorem homComp_mk {D : Type} [Groupoid.{0} D] {a b c : D} (ψ : a ⟶ b) (γ : c ⟶ a) :
    homComp ⟨a, b, ψ⟩ ⟨c, a, γ⟩ = ⟨b, γ ≫ ψ⟩ := by
  rw [homComp, dif_pos rfl, eqToHom_refl, Category.id_comp]

namespace GeometricLift

variable {D : Type} [Groupoid.{0} D] {G : Type} [Group G] {f : D ⥤ SingleObj G}
  (L : GeometricLift.{u} f)

/-! ### The groupoid structure and the M-polyfolds of `Y` -/

/-- `s(ψ, z) = z`. -/
def ySrc (p : L.YMor) : L.YObj := ⟨p.1.1, p.2⟩

/-- `t(ψ, z) = φ_{yy'}(ψ)(z)`. -/
def yTgt (p : L.YMor) : L.YObj := ⟨p.1.2.1, L.φ p.1.2.2 p.2⟩

/-- `(ψ, z') ∘ (γ, z) = (ψ ∘ γ, z)` (total: `homComp` takes a junk value off composable
pairs). -/
def yComp (p q : L.YMor) : L.YMor := ⟨⟨q.1.1, homComp p.1 q.1⟩, q.2⟩

/-- `u(z) = (1_y, z)`. -/
def yUnit (x : L.YObj) : L.YMor := ⟨⟨x.1, x.1, 𝟙 x.1⟩, x.2⟩

/-- `ι(ψ, z) = (ψ⁻¹, φ_{yy'}(ψ)(z))`. -/
def yInv (p : L.YMor) : L.YMor := ⟨⟨p.1.2.1, p.1.1, Groupoid.inv p.1.2.2⟩, L.φ p.1.2.2 p.2⟩

theorem yComp_mk {a b c : D} (ψ : a ⟶ b) (γ : c ⟶ a) (z' : (L.LD.obj a).carrier)
    (z : (L.LD.obj c).carrier) :
    L.yComp ⟨⟨a, b, ψ⟩, z'⟩ ⟨⟨c, a, γ⟩, z⟩ = ⟨⟨c, b, γ ≫ ψ⟩, z⟩ := by
  rw [yComp, homComp_mk]

/-- Composable pairs `s(p) = t(q)` are `p = (ψ, φ(γ)(z))`, `q = (γ, z)`. -/
theorem composable_cases {P : L.YMor → L.YMor → Prop} {p q : L.YMor}
    (h : L.ySrc p = L.yTgt q)
    (H : ∀ (a b c : D) (ψ : a ⟶ b) (γ : c ⟶ a) (z : (L.LD.obj c).carrier),
      P ⟨⟨a, b, ψ⟩, L.φ γ z⟩ ⟨⟨c, a, γ⟩, z⟩) : P p q := by
  obtain ⟨⟨a, b, ψ⟩, z'⟩ := p
  obtain ⟨⟨c, d, γ⟩, z⟩ := q
  have h' : (⟨a, z'⟩ : L.YObj) = ⟨d, L.φ γ z⟩ := h
  obtain ⟨rfl, h''⟩ := Sigma.mk.inj_iff.1 h'
  obtain rfl := eq_of_heq h''
  exact H _ _ _ ψ γ z

/-- **The groupoid `Y`** (p. 281). -/
def sourceStr : GroupoidStr L.YObj L.YMor where
  src := L.ySrc
  tgt := L.yTgt
  comp := L.yComp
  unit := L.yUnit
  inv := L.yInv
  src_comp _ _ _ := rfl
  tgt_comp p q h := by
    refine L.composable_cases (P := fun p q => L.yTgt (L.yComp p q) = L.yTgt p) h ?_
    intro a b c ψ γ z
    rw [yComp_mk]
    simp only [yTgt, φ_comp, Function.comp_apply]
  comp_assoc p q r h₁ h₂ := by
    revert p h₁
    refine L.composable_cases (P := fun q r => ∀ p, L.ySrc p = L.yTgt q →
      L.yComp (L.yComp p q) r = L.yComp p (L.yComp q r)) h₂ ?_
    intro a b c ψ γ z p h₁
    obtain ⟨⟨a', b', ψ'⟩, z'⟩ := p
    have h' : (⟨a', z'⟩ : L.YObj) = ⟨b, L.φ ψ (L.φ γ z)⟩ := h₁
    obtain ⟨rfl, h''⟩ := Sigma.mk.inj_iff.1 h'
    obtain rfl := eq_of_heq h''
    rw [yComp_mk, yComp_mk, yComp_mk, yComp_mk, Category.assoc]
  src_unit _ := rfl
  tgt_unit x := by
    change (⟨x.1, L.φ (𝟙 x.1) x.2⟩ : L.YObj) = x
    rw [L.φ_id]
    rfl
  comp_unit p := by
    obtain ⟨⟨a, b, ψ⟩, z⟩ := p
    change L.yComp ⟨⟨a, b, ψ⟩, z⟩ ⟨⟨a, a, 𝟙 a⟩, z⟩ = _
    rw [yComp_mk, Category.id_comp]
  unit_comp p := by
    obtain ⟨⟨a, b, ψ⟩, z⟩ := p
    change L.yComp ⟨⟨b, b, 𝟙 b⟩, L.φ ψ z⟩ ⟨⟨a, b, ψ⟩, z⟩ = _
    rw [yComp_mk, Category.comp_id]
  src_inv _ := rfl
  tgt_inv p := by
    obtain ⟨⟨a, b, ψ⟩, z⟩ := p
    change (⟨a, L.φ (Groupoid.inv ψ) (L.φ ψ z)⟩ : L.YObj) = ⟨a, z⟩
    rw [L.φ_inv_φ]
  comp_inv p := by
    obtain ⟨⟨a, b, ψ⟩, z⟩ := p
    change L.yComp ⟨⟨a, b, ψ⟩, z⟩ ⟨⟨b, a, Groupoid.inv ψ⟩, L.φ ψ z⟩ = ⟨⟨b, b, 𝟙 b⟩, L.φ ψ z⟩
    rw [yComp_mk, Groupoid.inv_comp]
  inv_comp p := by
    obtain ⟨⟨a, b, ψ⟩, z⟩ := p
    change L.yComp ⟨⟨b, a, Groupoid.inv ψ⟩, L.φ ψ z⟩ ⟨⟨a, b, ψ⟩, z⟩ = ⟨⟨a, a, 𝟙 a⟩, z⟩
    rw [yComp_mk, Groupoid.comp_inv]

/-! ### The M-polyfold structures of `Y` -/

/-- The M-polyfold structure of `Y = ⊔ U(y)` (`MPolyfold.sigma`). -/
def yObjPolyfold : MPolyfold L.YObj := MPolyfold.sigma fun y : D => (L.LD.obj y).P

/-- The M-polyfold structure of `𝐘 = ⊔_{ψ} U(s(ψ))` (`MPolyfold.sigma`). -/
def yMorPolyfold : MPolyfold L.YMor :=
  MPolyfold.sigma fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P

/-- `s : 𝐘 → Y` is a local sc-diffeomorphism (the identity on each summand). -/
theorem isLocalScDiffeo_ySrc : L.yMorPolyfold.IsLocalScDiffeo L.yObjPolyfold L.ySrc :=
  MPolyfold.isLocalScDiffeo_sigmaMap (fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P)
    (R := fun y : D => (L.LD.obj y).P) (σ := fun ψ => ψ.1) (g := fun _ z => z)
    fun _ => MPolyfold.isLocalScDiffeo_id

/-- `t : 𝐘 → Y` is a local sc-diffeomorphism (`φ_{yy'}(ψ)` on the summand of `ψ`). -/
theorem isLocalScDiffeo_yTgt : L.yMorPolyfold.IsLocalScDiffeo L.yObjPolyfold L.yTgt :=
  MPolyfold.isLocalScDiffeo_sigmaMap (fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P)
    (R := fun y : D => (L.LD.obj y).P) (σ := fun ψ => ψ.2.1) (g := fun ψ z => L.φ ψ.2.2 z)
    fun ψ => L.isLocalScDiffeo_φ ψ.2.2

/-- `u : Y → 𝐘` is sc-smooth (the identity from the summand `y` to the summand `1_y`). -/
theorem isScSmoothMap_yUnit : L.yObjPolyfold.IsScSmoothMap L.yMorPolyfold L.yUnit :=
  MPolyfold.isScSmoothMap_sigmaMap (fun y : D => (L.LD.obj y).P)
    (R := fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P) (σ := fun y => ⟨y, y, 𝟙 y⟩)
    (g := fun _ z => z) fun _ => MPolyfold.isScSmoothMap_id

/-- `ι : 𝐘 → 𝐘` is sc-smooth (`φ_{yy'}(ψ)` from the summand `ψ` to the summand `ψ⁻¹`). -/
theorem isScSmoothMap_yInv : L.yMorPolyfold.IsScSmoothMap L.yMorPolyfold L.yInv :=
  MPolyfold.isScSmoothMap_sigmaMap (fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P)
    (R := fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P)
    (σ := fun ψ => ⟨ψ.2.1, ψ.1, Groupoid.inv ψ.2.2⟩) (g := fun ψ z => L.φ ψ.2.2 z)
    fun ψ => (L.isScDiffeoOn_φ ψ.2.2).isScSmoothOn

/-- `t : 𝐘 → Y` is proper: `D` has finitely many morphisms and each `φ_{yy'}(ψ)` is a
homeomorphism. -/
theorem isProperMap_yTgt [Finite (Σ a b : D, a ⟶ b)] : IsProperMap L.yTgt := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨L.isLocalScDiffeo_yTgt.continuous, fun C hC => ?_, fun x => ?_⟩
  · have hC' : L.yTgt '' C = ⋃ ψ : (Σ a b : D, a ⟶ b),
        Sigma.mk ψ.2.1 '' (L.φ ψ.2.2 '' (Sigma.mk ψ ⁻¹' C)) := by
      ext x
      simp only [mem_image, mem_iUnion, mem_preimage]
      constructor
      · rintro ⟨⟨ψ, z⟩, hz, rfl⟩
        exact ⟨ψ, _, ⟨z, hz, rfl⟩, rfl⟩
      · rintro ⟨ψ, _, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨⟨ψ, z⟩, hz, rfl⟩
    rw [hC']
    refine isClosed_iUnion_of_finite fun ψ => isClosedMap_sigmaMk _ ?_
    rw [image_eq_preimage_of_inverse (L.φInv_φ ψ.2.2) (L.φ_φInv ψ.2.2)]
    exact (hC.preimage continuous_sigmaMk).preimage (L.continuous_φInv ψ.2.2)
  · refine (Set.Finite.of_finite_image (f := Sigma.fst) (Set.toFinite _) ?_).isCompact
    rintro ⟨ψ, z⟩ hz ⟨ψ', z'⟩ hz' (h : ψ = ψ')
    subst h
    have h1 : (⟨ψ.2.1, L.φ ψ.2.2 z⟩ : L.YObj) = ⟨ψ.2.1, L.φ ψ.2.2 z'⟩ :=
      (hz : L.yTgt ⟨ψ, z⟩ = x).trans (hz' : L.yTgt ⟨ψ, z'⟩ = x).symm
    have h2 := eq_of_heq (Sigma.mk.inj_iff.1 h1).2
    rw [← L.φInv_φ ψ.2.2 z, h2, L.φInv_φ]

/-- Condition (4) for `Y`, in the sheet form: `ψ ↦ σ(t ψ) ∘ ψ` is, near every `ψ₀`, the map
`(ψ₀.1, z) ↦ (γ₀ ∘ ψ₀.1, z)` with the locally constant `γ₀ = σ(t ψ)`. -/
theorem isScSmoothCompSheet_y :
    IsScSmoothCompSheet L.yObjPolyfold L.yMorPolyfold L.ySrc L.yTgt L.yComp := by
  intro σ W V hd
  have htc : Continuous L.yTgt := L.isLocalScDiffeo_yTgt.continuous
  have hO : IsOpen (L.yTgt ⁻¹' V) := hd.isScSmoothOn_inv.isOpen.preimage htc
  refine MPolyfold.IsScSmoothOn.of_locally hO fun p₀ hp₀ => ?_
  set γ₀ := (σ (L.yTgt p₀)).1 with hγ₀
  have hσc : ContinuousOn (fun p => σ (L.yTgt p)) (L.yTgt ⁻¹' V) :=
    hd.isScSmoothOn_inv.continuousOn.comp htc.continuousOn fun _ h => h
  have hOo : IsOpen ((L.yTgt ⁻¹' V ∩ (fun p => σ (L.yTgt p)) ⁻¹' range (Sigma.mk γ₀)) ∩
      range (Sigma.mk p₀.1)) :=
    (hσc.isOpen_inter_preimage hO isOpen_range_sigmaMk).inter isOpen_range_sigmaMk
  refine ⟨_, hOo, ⟨⟨hp₀, (σ (L.yTgt p₀)).2, rfl⟩, p₀.2, rfl⟩, fun _ h => h.1.1, ?_⟩
  have hsm := MPolyfold.IsScSmoothOn.comp
    (MPolyfold.isScSmoothMap_sigmaMk (fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P)
      (⟨p₀.1.1, homComp γ₀ p₀.1⟩ : Σ a b : D, a ⟶ b))
    ((MPolyfold.isScSmoothOn_sigmaProj (fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P)
      p₀.1 p₀.2).mono hOo inter_subset_right) (mapsTo_univ _ _)
  refine hsm.congr ?_
  rintro ⟨ψ, z⟩ ⟨⟨-, w, hw⟩, z', hz'⟩
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 hz'
  have hγ : (σ (L.yTgt ⟨p₀.1, z⟩)).1 = γ₀ := (congrArg Sigma.fst hw).symm
  simp only [Function.comp_apply, sigmaProj_mk]
  change _ = (⟨⟨p₀.1.1, homComp (σ (L.yTgt ⟨p₀.1, z⟩)).1 p₀.1⟩, z⟩ : L.YMor)
  rw [hγ]

end GeometricLift

open GeometricLift

/-! ### The ep-groupoid `Y` -/

section Source

variable {D : Type} [Groupoid.{0} D] [Fintype D] [∀ a b : D, Fintype (a ⟶ b)]
  {G : Type} [Group G] {f : D ⥤ SingleObj G} (L : GeometricLift.{u} f)

/-- **The ep-groupoid `Y`** of Proposition 8.3 (p. 281): objects `⊔_{y ∈ D} U(y)`, morphisms
`⊔_{(y, y')} mor(y, y') × U(y)`, `s(ψ, z) = z`, `t(ψ, z) = φ_{yy'}(ψ)(z)`,
`(ψ, z') ∘ (γ, z) = (ψ ∘ γ, z)`, `u(z) = (1_y, z)`, `ι(ψ, z) = (ψ⁻¹, φ_{yy'}(ψ)(z))`. -/
def geometricLiftSource : EpGroupoid L.YObj L.YMor where
  toGroupoidStr := L.sourceStr
  PObj := L.yObjPolyfold
  PMor := L.yMorPolyfold
  isLocalScDiffeo_src := L.isLocalScDiffeo_ySrc
  isLocalScDiffeo_tgt := L.isLocalScDiffeo_yTgt
  isScSmoothMap_unit := L.isScSmoothMap_yUnit
  isScSmoothMap_inv := L.isScSmoothMap_yInv
  exists_isProperMap _ := ⟨univ, isOpen_univ, mem_univ _,
    L.isProperMap_yTgt.restrict (isClosed_closure.preimage L.isLocalScDiffeo_ySrc.continuous)⟩
  isScSmoothComp := (isScSmoothComp_iff_sheet _ _).2 L.isScSmoothCompSheet_y

@[simp] theorem geometricLiftSource_src (p : L.YMor) :
    (geometricLiftSource L).src p = ⟨p.1.1, p.2⟩ := rfl

@[simp] theorem geometricLiftSource_tgt (p : L.YMor) :
    (geometricLiftSource L).tgt p = ⟨p.1.2.1, L.φ p.1.2.2 p.2⟩ := rfl

theorem geometricLiftSource_comp_mk {a b c : D} (ψ : a ⟶ b) (γ : c ⟶ a)
    (z' : (L.LD.obj a).carrier) (z : (L.LD.obj c).carrier) :
    (geometricLiftSource L).comp ⟨⟨a, b, ψ⟩, z'⟩ ⟨⟨c, a, γ⟩, z⟩ = ⟨⟨c, b, γ ≫ ψ⟩, z⟩ :=
  L.yComp_mk ψ γ z' z

@[simp] theorem geometricLiftSource_unit (x : L.YObj) :
    (geometricLiftSource L).unit x = ⟨⟨x.1, x.1, 𝟙 x.1⟩, x.2⟩ := rfl

@[simp] theorem geometricLiftSource_inv (p : L.YMor) :
    (geometricLiftSource L).inv p =
      ⟨⟨p.1.2.1, p.1.1, Groupoid.inv p.1.2.2⟩, L.φ p.1.2.2 p.2⟩ := rfl

theorem geometricLiftSource_PObj :
    (geometricLiftSource L).PObj = MPolyfold.sigma fun y : D => (L.LD.obj y).P := rfl

theorem geometricLiftSource_PMor :
    (geometricLiftSource L).PMor =
      MPolyfold.sigma fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P := rfl

/-- `s : 𝐘 → Y` is surjective (p. 281). -/
theorem geometricLiftSource_surjective_src : Surjective (geometricLiftSource L).src :=
  fun x => ⟨_, (geometricLiftSource L).src_unit x⟩

/-- `t : 𝐘 → Y` is surjective (p. 281). -/
theorem geometricLiftSource_surjective_tgt : Surjective (geometricLiftSource L).tgt :=
  fun x => ⟨_, (geometricLiftSource L).tgt_unit x⟩

end Source

/-! ### The ep-groupoid `X = G_x ⋉ U(x)` -/

section Target

variable {D : Type} [Groupoid.{0} D] {G : Type} [Group G] [Fintype G] [TopologicalSpace G]
  [DiscreteTopology G] {f : D ⥤ SingleObj G} (L : GeometricLift.{u} f)

/-- **The translation groupoid `X = G_x ⋉ U(x)`** of Proposition 8.3 (p. 281): objects `U(x)`,
morphisms `G_x × U(x)` (`G_x = G` discrete, lifted to the universe of `U(x)`), `s(g, z) = z`,
`t(g, z) = g ∗ z`; Chapter 7's `actionEpGroupoid`. -/
def geometricLiftTarget : EpGroupoid L.Ux (ULift.{u} G × L.Ux) :=
  EpGroupoid.Examples.actionEpGroupoid L.isScSmoothMap_smul

@[simp] theorem geometricLiftTarget_src (p : ULift.{u} G × L.Ux) :
    (geometricLiftTarget L).src p = p.2 := rfl

@[simp] theorem geometricLiftTarget_tgt (p : ULift.{u} G × L.Ux) :
    (geometricLiftTarget L).tgt p = p.1.down • p.2 := rfl

@[simp] theorem geometricLiftTarget_comp (p q : ULift.{u} G × L.Ux) :
    (geometricLiftTarget L).comp p q = (p.1 * q.1, q.2) := rfl

@[simp] theorem geometricLiftTarget_unit (z : L.Ux) :
    (geometricLiftTarget L).unit z = (1, z) := rfl

@[simp] theorem geometricLiftTarget_inv (p : ULift.{u} G × L.Ux) :
    (geometricLiftTarget L).inv p = (p.1⁻¹, p.1.down • p.2) := rfl

theorem geometricLiftTarget_PObj :
    (geometricLiftTarget L).PObj = (L.LC.obj (SingleObj.star G)).P := rfl

theorem geometricLiftTarget_PMor :
    (geometricLiftTarget L).PMor =
      (discretePolyfold (ULift.{u} G)).prod (L.LC.obj (SingleObj.star G)).P := rfl

end Target

/-! ### The functor `F : Y → X` -/

section Functor

variable {D : Type} [Groupoid.{0} D] [Fintype D] [∀ a b : D, Fintype (a ⟶ b)]
  {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {f : D ⥤ SingleObj G} (L : GeometricLift.{u} f)

/-- **The functor `F : Y → X`** of Proposition 8.3 (p. 282): `F|U(y) = τ(y)` on objects,
`F(ψ, z) = (f(ψ), τ(y)(z))` on morphisms. -/
def geometricLiftFunctor : EpFunctor (geometricLiftSource L) (geometricLiftTarget L) where
  obj p := L.τy p.1 p.2
  mor p := (ULift.up (f.map p.1.2.2 : G), L.τy p.1.1 p.2)
  src_mor _ := rfl
  tgt_mor p := (L.τy_φ p.1.2.2 p.2).symm
  mor_comp p q h := by
    refine L.composable_cases (P := fun p q => ((ULift.up (f.map (L.yComp p q).1.2.2 : G),
      L.τy (L.yComp p q).1.1 (L.yComp p q).2) : ULift.{u} G × L.Ux) =
      (ULift.up (f.map p.1.2.2 : G) * ULift.up (f.map q.1.2.2 : G), L.τy q.1.1 q.2)) h ?_
    intro a b c ψ γ z
    rw [yComp_mk]
    refine Prod.ext (ULift.ext _ _ ?_) rfl
    change (f.map (γ ≫ ψ) : G) = (f.map ψ : G) * (f.map γ : G)
    rw [f.map_comp, SingleObj.comp_as_mul]
  mor_unit x := by
    refine Prod.ext (ULift.ext _ _ ?_) rfl
    change (f.map (𝟙 x.1) : G) = 1
    rw [f.map_id, SingleObj.id_as_one]
  isScSmoothMap_obj := (MPolyfold.isScSmoothMap_sigma_iff _).2 fun y =>
    (L.isScDiffeoOn_τy y).isScSmoothOn
  isScSmoothMap_mor := (MPolyfold.isScSmoothMap_sigma_iff _).2 fun ψ =>
    MPolyfold.IsScSmoothOn.prodMk (isScSmoothMap_const_discrete (ULift.up (f.map ψ.2.2 : G)))
      (L.isScDiffeoOn_τy ψ.1).isScSmoothOn

@[simp] theorem geometricLiftFunctor_obj (p : L.YObj) :
    (geometricLiftFunctor L).obj p = L.τy p.1 p.2 := rfl

@[simp] theorem geometricLiftFunctor_mor (p : L.YMor) :
    (geometricLiftFunctor L).mor p = (ULift.up (f.map p.1.2.2 : G), L.τy p.1.1 p.2) := rfl

end Functor


/-! ### Proposition 8.3 -/

section Proposition

variable {D : Type} [Groupoid.{0} D] [Fintype D] [∀ a b : D, Fintype (a ⟶ b)]
  {G : Type} [Group G] [Fintype G] [TopologicalSpace G] [DiscreteTopology G]
  {f : D ⥤ SingleObj G} (L : GeometricLift.{u} f)

/-- `F` is surjective on objects when `D` is nonempty. -/
theorem geometricLiftFunctor_surjective [Nonempty D] :
    Surjective (geometricLiftFunctor L).obj :=
  fun w => ⟨⟨Classical.arbitrary D, L.τyInv _ w⟩, L.τy_τyInv _ w⟩

/-- `F` is surjective on objects if and only if `D ≠ ∅` or `U(x) = ∅`: the hypothesis
`Nonempty D` of `proposition_8_3` cannot be dropped (`isCoveringFunctor_of_isEmpty`). -/
theorem geometricLiftFunctor_surjective_iff :
    Surjective (geometricLiftFunctor L).obj ↔ Nonempty D ∨ IsEmpty L.Ux := by
  constructor
  · intro h
    rcases isEmpty_or_nonempty D with hD | hD
    · exact Or.inr ⟨fun w => isEmptyElim (h w).choose.1⟩
    · exact Or.inl hD
  · rintro (hD | hU)
    · exact geometricLiftFunctor_surjective L
    · exact fun w => isEmptyElim w

/-- `F : Y → X` is a local sc-diffeomorphism on objects (each `τ(y)` is an sc-diffeomorphism). -/
theorem geometricLiftFunctor_isLocalScDiffeo :
    (geometricLiftSource L).PObj.IsLocalScDiffeo (geometricLiftTarget L).PObj
      (geometricLiftFunctor L).obj :=
  (MPolyfold.isLocalScDiffeo_sigma_iff (fun y : D => (L.LD.obj y).P)).2 fun y z =>
    ⟨univ, univ, L.τyInv y, mem_univ z, L.isScDiffeoOn_τy y⟩

/-- `F⁻¹(w) = {(y, τ(y)⁻¹(w)) | y ∈ D}` is finite. -/
theorem geometricLiftFunctor_finite_fiber (w : L.Ux) :
    ((geometricLiftFunctor L).obj ⁻¹' {w}).Finite := by
  refine (Set.finite_range fun y : D => (⟨y, L.τyInv y w⟩ : L.YObj)).subset ?_
  rintro ⟨y, z⟩ (hz : L.τy y z = w)
  exact ⟨y, show (⟨y, L.τyInv y w⟩ : L.YObj) = ⟨y, z⟩ by rw [← hz, L.τyInv_τy]⟩

/-- Definition 8.8 (2) for `F`: `U(w) = U(x)` and the summands `U(y)` (all of `F⁻¹(U(x)) = Y`). -/
theorem geometricLiftFunctor_evenlyCovered (w : L.Ux) :
    ∃ (U : Set L.Ux) (V : L.YObj → Set L.YObj) (σ : L.YObj → L.Ux → L.YObj),
      IsOpen U ∧ w ∈ U ∧ ((geometricLiftFunctor L).obj ⁻¹' {w}).PairwiseDisjoint V ∧
      (∀ y ∈ (geometricLiftFunctor L).obj ⁻¹' {w}, y ∈ V y ∧
        (geometricLiftSource L).PObj.IsScDiffeoOn (geometricLiftTarget L).PObj
          (geometricLiftFunctor L).obj (σ y) (V y) U) ∧
      (geometricLiftFunctor L).obj ⁻¹' U = ⋃ y ∈ (geometricLiftFunctor L).obj ⁻¹' {w}, V y := by
  refine ⟨univ, fun p => range (Sigma.mk p.1), fun p => Sigma.mk p.1 ∘ L.τyInv p.1, isOpen_univ,
    mem_univ w, ?_, ?_, ?_⟩
  · rintro ⟨y, z⟩ (hz : L.τy y z = w) ⟨y', z'⟩ (hz' : L.τy y' z' = w) hne
    by_cases hy : y = y'
    · subst hy
      have hzz : z = z' := by rw [← L.τyInv_τy _ z, ← L.τyInv_τy _ z', hz, hz']
      exact absurd (by rw [hzz]) hne
    · exact disjoint_range_sigmaMk hy
  · rintro ⟨y, z⟩ -
    refine ⟨mem_range_self z, ?_⟩
    refine ((L.isScDiffeoOn_τy y).comp (MPolyfold.isScDiffeoOn_sigmaMk
      (fun y : D => (L.LD.obj y).P) y z).symm).congr ?_
    rintro _ ⟨z', rfl⟩
    simp only [Function.comp_apply, sigmaProj_mk]
    rfl
  · refine preimage_univ.trans (eq_univ_of_forall fun p => ?_).symm
    exact mem_biUnion (x := (⟨p.1, L.τyInv p.1 w⟩ : L.YObj)) (L.τy_τyInv p.1 w) ⟨p.2, rfl⟩

/-- The inverse of (8.16), on `𝐗 × Y`: `((g, q), (y, z)) ↦ (ψ, z)` with `ψ` the unique morphism
with `f(ψ) = g` and `s(ψ) = y`. -/
def GeometricLift.fibredInv (hf : IsCoveringFunctor f) (q : (ULift.{u} G × L.Ux) × L.YObj) :
    L.YMor :=
  ⟨⟨q.2.1, hf.lift q.1.1.down q.2.1⟩, q.2.2⟩

/-- `fibredInv` is sc-smooth on `𝐗 × Y`: on the open piece `{g₀} × U(x) × U(y₀)` it is
`((g₀, q), (y₀, z)) ↦ (ψ₀, z)`. -/
theorem GeometricLift.isScSmoothMap_fibredInv (hf : IsCoveringFunctor f)
    [ParacompactSpace ((ULift.{u} G × L.Ux) × L.YObj)] :
    ((geometricLiftTarget L).PMor.prod (geometricLiftSource L).PObj).IsScSmoothMap
      (geometricLiftSource L).PMor (L.fibredInv hf) := by
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun q₀ _ => ?_
  have hc : Continuous fun q : (ULift.{u} G × L.Ux) × L.YObj => q.1.1 :=
    continuous_fst.comp continuous_fst
  have hOo : IsOpen ((fun q : (ULift.{u} G × L.Ux) × L.YObj => q.1.1) ⁻¹' {q₀.1.1} ∩
      Prod.snd ⁻¹' range (Sigma.mk q₀.2.1)) :=
    ((isOpen_discrete _).preimage hc).inter (isOpen_range_sigmaMk.preimage continuous_snd)
  refine ⟨_, hOo, ⟨rfl, q₀.2.2, rfl⟩, subset_univ _, ?_⟩
  have hsnd := (MPolyfold.isScSmoothMap_snd (geometricLiftTarget L).PMor
    (geometricLiftSource L).PObj).mono hOo (subset_univ _)
  have h1 := MPolyfold.IsScSmoothOn.comp (MPolyfold.isScSmoothOn_sigmaProj
    (fun y : D => (L.LD.obj y).P) q₀.2.1 q₀.2.2) hsnd fun q hq => hq.2
  have h2 := MPolyfold.IsScSmoothOn.comp (MPolyfold.isScSmoothMap_sigmaMk
    (fun ψ : (Σ a b : D, a ⟶ b) => (L.LD.obj ψ.1).P)
    (⟨q₀.2.1, hf.lift q₀.1.1.down q₀.2.1⟩ : Σ a b : D, a ⟶ b)) h1 (mapsTo_univ _ _)
  refine h2.congr ?_
  rintro ⟨⟨m, w⟩, ⟨y, z⟩⟩ ⟨hm, z', hz'⟩
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 hz'
  obtain rfl : m = q₀.1.1 := hm
  simp only [Function.comp_apply, sigmaProj_mk]
  rfl

/-- **(8.16)**: `𝐘 → 𝐗 ₛ×_F Y`, `(ψ, z) ↦ ((f(ψ), F(z)), z)`, is an sc-diffeomorphism onto the
fibred-product sub-M-polyfold. -/
theorem geometricLiftFunctor_isScDiffeo_fibredMap (hf : IsCoveringFunctor f) :
    letI := MPolyfold.paracompactSpace_prod (geometricLiftTarget L).PMor
      (geometricLiftSource L).PObj
    letI := ((geometricLiftTarget L).PMor.prod
      (geometricLiftSource L).PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct (geometricLiftTarget L).src (geometricLiftFunctor L).obj)
    ∃ g : MPolyfold.fibredProduct (geometricLiftTarget L).src (geometricLiftFunctor L).obj →
        L.YMor,
      (geometricLiftSource L).PMor.IsScDiffeoOn (MPolyfold.subPolyfold
        (MPolyfold.isSubMPolyfold_fibredProduct (geometricLiftTarget L).isLocalScDiffeo_src
          (geometricLiftFunctor L).isScSmoothMap_obj))
        (geometricLiftFunctor L).fibredMap g univ univ := by
  let _ := MPolyfold.paracompactSpace_prod (geometricLiftTarget L).PMor
    (geometricLiftSource L).PObj
  let _ := ((geometricLiftTarget L).PMor.prod (geometricLiftSource L).PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct (geometricLiftTarget L).src (geometricLiftFunctor L).obj)
  refine ⟨fun p => L.fibredInv hf p.1, ?_, ?_, mapsTo_univ _ _, mapsTo_univ _ _, ?_, ?_⟩
  · exact isScSmoothOn_subPolyfold_of_val _ (MPolyfold.IsScSmoothOn.prodMk
      (geometricLiftFunctor L).isScSmoothMap_mor (geometricLiftSource L).isScSmoothMap_src)
  · exact (L.isScSmoothMap_fibredInv hf).comp (MPolyfold.subPolyfold_inclusion_isScSmooth _)
  · rintro ⟨⟨a, b, ψ⟩, z⟩ -
    change (⟨⟨a, hf.lift (f.map ψ : G) a⟩, z⟩ : L.YMor) = ⟨⟨a, b, ψ⟩, z⟩
    rw [hf.lift_map ψ]
  · rintro ⟨⟨⟨m, w⟩, ⟨y, z⟩⟩, hp⟩ -
    exact Subtype.ext (Prod.ext (Prod.ext (ULift.ext _ _ (hf.map_lift m.down y)) hp.symm) rfl)

/-- **Proposition 8.3 (geometric lift)**: a covering functor `f : D → C` with a geometric lift
`τ : L_D → L_C ∘ f` gives a proper covering functor `F : Y → X` (Definition 8.8) from the
ep-groupoid `Y` (objects `⊔ U(y)`, morphisms `⊔ mor(y, y') × U(y)`) to the translation groupoid
`X = G_x ⋉ U(x)`, `F|U(y) = τ(y)`, `F(ψ, z) = (f(ψ), τ(y)(z))`; `D` nonempty (for the
surjectivity of `F`, `geometricLiftFunctor_surjective_iff`). -/
theorem proposition_8_3 [Nonempty D] (hf : IsCoveringFunctor f) (L : GeometricLift.{u} f) :
    (geometricLiftFunctor L).IsProperCovering where
  surjective := geometricLiftFunctor_surjective L
  isLocalScDiffeo := geometricLiftFunctor_isLocalScDiffeo L
  finite_fiber := geometricLiftFunctor_finite_fiber L
  evenlyCovered := geometricLiftFunctor_evenlyCovered L
  isScDiffeo_fibredMap := geometricLiftFunctor_isScDiffeo_fibredMap L hf

end Proposition

/-! ### Full subgroupoids -/

namespace GroupoidStr

variable {Obj Mor : Type u}

/-- An object of the full subcategory of `G` on `A ⊆ Obj`: a point of `A`. -/
@[ext]
structure FullOb (_G : GroupoidStr Obj Mor) (A : Set Obj) where
  /-- The point. -/
  val : Obj
  /-- `val ∈ A`. -/
  mem : val ∈ A

variable (G : GroupoidStr Obj Mor)

/-- **The full subcategory of `G` on `A`**: its morphisms `a → b` are those of `G`. -/
instance instGroupoidFullOb (A : Set Obj) : Groupoid.{u} (G.FullOb A) where
  Hom a b := G.toOb a.val ⟶ G.toOb b.val
  id a := 𝟙 (G.toOb a.val)
  comp f g := f ≫ g
  id_comp f := Category.id_comp (obj := G.Ob) f
  comp_id f := Category.comp_id (obj := G.Ob) f
  assoc f g h := Category.assoc (obj := G.Ob) f g h
  inv f := Groupoid.inv (obj := G.Ob) f
  inv_comp f := Groupoid.inv_comp (obj := G.Ob) f
  comp_inv f := Groupoid.comp_inv (obj := G.Ob) f

/-- Composition in the full subcategory is that of `G`. -/
theorem FullOb.comp_val {A : Set Obj} {a b c : G.FullOb A} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).1 = G.comp g.1 f.1 := rfl

/-- Units in the full subcategory are those of `G`. -/
theorem FullOb.id_val {A : Set Obj} (a : G.FullOb A) : (𝟙 a : a ⟶ a).1 = G.unit a.val := rfl

end GroupoidStr

/-! ### Open subsets as objects of `Diff_sc` -/

namespace MPolyfoldCat

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]

/-- An open subset `V ≠ ∅` of an M-polyfold, as an object of `Diff_sc` (Part I's
`restrictOpen`). -/
abbrev ofOpen (P : MPolyfold Z) {V : Set Z} (hV : IsOpen V) [Nonempty V] [ParacompactSpace V] :
    MPolyfoldCat.{u} :=
  { carrier := V, P := P.restrictOpen hV }

end MPolyfoldCat

namespace ScDiffeo

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold Z}
  {Z' : Type u} [TopologicalSpace Z'] [T2Space Z'] [ParacompactSpace Z'] {Q : MPolyfold Z'}
  {V : Set Z} (hV : IsOpen V) [Nonempty V] [ParacompactSpace V]
  {V' : Set Z'} (hV' : IsOpen V') [Nonempty V'] [ParacompactSpace V']

/-- An sc-diffeomorphism `f : V → V'` between open subsets, as a morphism of `Diff_sc`. -/
def ofOpen {f : Z → Z'} {g : Z' → Z} (h : P.IsScDiffeoOn Q f g V V') :
    ScDiffeo (MPolyfoldCat.ofOpen P hV) (MPolyfoldCat.ofOpen Q hV') where
  toFun z := ⟨f z.1, h.mapsTo z.2⟩
  invFun w := ⟨g w.1, h.mapsTo_inv w.2⟩
  isScDiffeoOn :=
    { isScSmoothOn := MPolyfold.IsScSmoothMap.codRestrict_restrictOpen hV'
        (h.isScSmoothOn.comp (MPolyfold.isScSmoothMap_subtypeVal hV) fun z _ => z.2) _
      isScSmoothOn_inv := MPolyfold.IsScSmoothMap.codRestrict_restrictOpen hV
        (h.isScSmoothOn_inv.comp (MPolyfold.isScSmoothMap_subtypeVal hV') fun z _ => z.2) _
      mapsTo := mapsTo_univ _ _
      mapsTo_inv := mapsTo_univ _ _
      left_inv := fun z _ => Subtype.ext (h.left_inv z.1 z.2)
      right_inv := fun w _ => Subtype.ext (h.right_inv w.1 w.2) }

@[simp] theorem ofOpen_toFun_val {f : Z → Z'} {g : Z' → Z} (h : P.IsScDiffeoOn Q f g V V')
    (z : V) : ((ofOpen hV hV' h).toFun z).1 = f z.1 := rfl

end ScDiffeo

/-! ### Fully faithful open embeddings -/

section OpenEmbedding

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- A **fully faithful open embedding functor** (Theorem 8.6): fully faithful as a functor of the
underlying groupoids, and on objects and on morphisms an injective local sc-diffeomorphism (an
sc-diffeomorphism onto its image, which is open). -/
structure EpFunctor.IsFullyFaithfulOpenEmbedding (Φ : EpFunctor X Y) : Prop where
  /-- `Φ` is full. -/
  full : Φ.toFunctor.Full
  /-- `Φ` is faithful. -/
  faithful : Φ.toFunctor.Faithful
  /-- `Φ` is injective on objects. -/
  injective_obj : Injective Φ.obj
  /-- `Φ` is a local sc-diffeomorphism on objects. -/
  isLocalScDiffeo_obj : X.PObj.IsLocalScDiffeo Y.PObj Φ.obj
  /-- `Φ` is injective on morphisms. -/
  injective_mor : Injective Φ.mor
  /-- `Φ` is a local sc-diffeomorphism on morphisms. -/
  isLocalScDiffeo_mor : X.PMor.IsLocalScDiffeo Y.PMor Φ.mor

namespace EpFunctor

/-- A functor injective on morphisms is faithful. -/
theorem faithful_of_injective_mor {Φ : EpFunctor X Y} (h : Injective Φ.mor) :
    Φ.toFunctor.Faithful :=
  ⟨fun {_ _} _ _ he => Subtype.ext (h (congrArg Subtype.val he))⟩

namespace IsFullyFaithfulOpenEmbedding

variable {Φ : EpFunctor X Y} (hΦ : Φ.IsFullyFaithfulOpenEmbedding)
include hΦ

/-- The image of the objects is open. -/
theorem isOpen_range_obj : IsOpen (range Φ.obj) := hΦ.isLocalScDiffeo_obj.isOpenMap.isOpen_range

/-- The image of the morphisms is open. -/
theorem isOpen_range_mor : IsOpen (range Φ.mor) := hΦ.isLocalScDiffeo_mor.isOpenMap.isOpen_range

end IsFullyFaithfulOpenEmbedding

end EpFunctor

end OpenEmbedding

/-! ### Theorem 8.6 -/

section Theorem86

open scoped EpGroupoid.NaturalRep

variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

namespace EpFunctor

section Restrict

variable (F : EpFunctor Y X) (x : ObjX)

/-- **The full subcategory `D` of `Y` on `F⁻¹(x)`** (Theorem 8.6). -/
abbrev FiberCat : Type := Y.toGroupoidStr.FullOb (F.obj ⁻¹' {x})

/-- `F(ψ) ∈ G_x` for a morphism `ψ` of `D` (Remark 8.2 (a)). -/
def fiberIsotropy {a b : F.FiberCat x} (ψ : a ⟶ b) : X.Isotropy x :=
  ⟨F.mor ψ.1, by rw [F.src_mor, show Y.src ψ.1 = a.val from ψ.2.1]; exact a.mem,
    by rw [F.tgt_mor, show Y.tgt ψ.1 = b.val from ψ.2.2]; exact b.mem⟩

variable {F x}

@[simp] theorem fiberIsotropy_val {a b : F.FiberCat x} (ψ : a ⟶ b) :
    (F.fiberIsotropy x ψ).val = F.mor ψ.1 := rfl

/-- `F(1_y) = 1`. -/
theorem fiberIsotropy_id (a : F.FiberCat x) : F.fiberIsotropy x (𝟙 a) = 1 :=
  GroupoidStr.Isotropy.ext (by
    change F.mor (Y.unit a.val) = X.unit x
    rw [F.mor_unit]
    exact congrArg X.unit (show F.obj a.val = x from a.mem))

/-- `F(ψ ∘ γ) = F(ψ) F(γ)`. -/
theorem fiberIsotropy_comp {a b c : F.FiberCat x} (γ : a ⟶ b) (ψ : b ⟶ c) :
    F.fiberIsotropy x (γ ≫ ψ) = F.fiberIsotropy x ψ * F.fiberIsotropy x γ :=
  GroupoidStr.Isotropy.ext (by
    change F.mor (Y.comp ψ.1 γ.1) = X.comp (F.mor ψ.1) (F.mor γ.1)
    exact F.mor_comp _ _ (ψ.2.1.trans γ.2.2.symm))

variable (F x)

/-- **`f = F|D : D → C`** (Theorem 8.6), `C = SingleObj G_x` the full subcategory on `x`:
`f(ψ) = F(ψ) ∈ G_x` (Remark 8.2 (a)). -/
def restrictFiber : F.FiberCat x ⥤ SingleObj (X.Isotropy x) where
  obj _ := SingleObj.star _
  map ψ := F.fiberIsotropy x ψ
  map_id a := fiberIsotropy_id a
  map_comp γ ψ := fiberIsotropy_comp γ ψ

variable {F x}

@[simp] theorem restrictFiber_map {a b : F.FiberCat x} (ψ : a ⟶ b) :
    ((F.restrictFiber x).map ψ : X.Isotropy x) = F.fiberIsotropy x ψ := rfl

variable (x)

/-- **Theorem 8.6, first part**: `f = F|D : D → C` is a covering functor (from Definition 8.8
(3), the unique lifting of `φ ∈ G_x` at `y ∈ F⁻¹(x)`). -/
theorem covering_restrict (hF : F.IsProperCovering) : IsCoveringFunctor (F.restrictFiber x) := by
  constructor
  · rintro ⟨a, b, φ⟩ ⟨a', b', φ'⟩ h
    have h1 : F.mor φ.1 = F.mor φ'.1 := congrArg (fun p => (p.1 : X.Isotropy x).val) h
    have h2 : a = a' := congrArg Prod.snd h
    subst h2
    have h3 : φ.1 = φ'.1 :=
      (hF.existsUnique_lift (φ := F.mor φ.1) (y := a.val) (by rw [F.src_mor, φ.2.1]; rfl)).unique
        ⟨rfl, φ.2.1⟩ ⟨h1.symm, φ'.2.1⟩
    have h4 : b = b' := GroupoidStr.FullOb.ext (φ.2.2.symm.trans ((congrArg Y.tgt h3).trans φ'.2.2))
    subst h4
    have h5 : φ = φ' := Subtype.ext h3
    subst h5
    rfl
  · rintro ⟨g, a⟩
    obtain ⟨ψ, ⟨hψm, hψs⟩, -⟩ := hF.existsUnique_lift (φ := g.val) (y := a.val)
      (by rw [g.src_val]; exact (show F.obj a.val = x from a.mem).symm)
    let b : F.FiberCat x := ⟨Y.tgt ψ, by
      change F.obj (Y.tgt ψ) = x
      rw [← F.tgt_mor, hψm, g.tgt_val]⟩
    exact ⟨⟨a, b, ⟨ψ, hψs, rfl⟩⟩, Prod.ext (GroupoidStr.Isotropy.ext hψm) rfl⟩

/-- `D = F⁻¹(x)` is finite (Definition 8.8 (2)). -/
theorem finite_fiberCat (hF : F.IsProperCovering) : Finite (F.FiberCat x) := by
  have := (hF.finite_fiber x).to_subtype
  exact Finite.of_injective (fun a : F.FiberCat x => (⟨a.val, a.mem⟩ : F.obj ⁻¹' {x}))
    fun a b h => GroupoidStr.FullOb.ext (congrArg Subtype.val h)

/-- `D` has finitely many morphisms (`#mor(F⁻¹(x)) = #G_x · #F⁻¹(x)`, p. 286). -/
theorem finite_fiberCat_hom (hF : F.IsProperCovering) (a b : F.FiberCat x) : Finite (a ⟶ b) := by
  have h : Y.mor a.val b.val ⊆ Y.morOn (F.obj ⁻¹' {x}) := fun φ hφ =>
    ⟨by rw [show Y.src φ = a.val from hφ.1]; exact a.mem,
      by rw [show Y.tgt φ = b.val from hφ.2]; exact b.mem⟩
  exact ((hF.finite_morOn_fiber x).subset h).to_subtype

/-- The `Fintype` structure of `D` (from `finite_fiberCat`). -/
@[instance_reducible] def fintypeFiberCat (hF : F.IsProperCovering) : Fintype (F.FiberCat x) :=
  haveI := finite_fiberCat x hF
  Fintype.ofFinite _

/-- The `Fintype` structures of the morphism sets of `D` (from `finite_fiberCat_hom`). -/
@[instance_reducible] def fintypeFiberCatHom (hF : F.IsProperCovering) (a b : F.FiberCat x) :
    Fintype (a ⟶ b) :=
  haveI := finite_fiberCat_hom x hF a b
  Fintype.ofFinite _

variable {x} in
/-- A morphism of `D` is a morphism of `Y` between points of `F⁻¹(x)`. -/
theorem mem_morOn_of_hom {a b : F.FiberCat x} (ψ : a ⟶ b) : ψ.1 ∈ Y.morOn (F.obj ⁻¹' {x}) :=
  ⟨by rw [show Y.src ψ.1 = a.val from ψ.2.1]; exact a.mem,
    by rw [show Y.tgt ψ.1 = b.val from ψ.2.2]; exact b.mem⟩

/-- `D ≠ ∅`: `F` is surjective on objects. -/
theorem nonempty_fiberCat (hF : F.IsProperCovering) : Nonempty (F.FiberCat x) := by
  obtain ⟨y, hy⟩ := hF.surjective x
  exact ⟨⟨y, hy⟩⟩

end Restrict

/-! #### The geometric lift of `f = F|D` built from a chart of Theorem 8.5 -/

namespace ProperCoveringChart

variable {F : EpFunctor Y X} {x : ObjX} (C : F.ProperCoveringChart x)

/-- `U(y) ≠ ∅`. -/
instance instNonemptyU (a : F.FiberCat x) : Nonempty (C.U a.val) := ⟨⟨a.val, C.mem_U _ a.mem⟩⟩

/-- `U(y)` is paracompact (a subspace of an M-polyfold). -/
instance instParacompactSpaceU (a : F.FiberCat x) : ParacompactSpace (C.U a.val) :=
  Y.PObj.paracompactSpace_subtype _

theorem isOpen_U' (a : F.FiberCat x) : IsOpen (C.U a.val) := C.isOpen_U _ a.mem

/-- The inverse `(F|U(y))⁻¹ : U(x) → U(y)`. -/
def σObj (a : F.FiberCat x) : ObjX → ObjY := (C.isScDiffeoOn_obj a.val a.mem).choose

/-- `F : U(y) → U(x)` is an sc-diffeomorphism with inverse `σObj` (Theorem 8.5 (0)). -/
theorem isScDiffeoOn_σObj (a : F.FiberCat x) :
    Y.PObj.IsScDiffeoOn X.PObj F.obj (C.σObj a) (C.U a.val) C.R.U :=
  (C.isScDiffeoOn_obj a.val a.mem).choose_spec

/-- `F` maps `U(y)` into `U(x)`. -/
theorem obj_mem {a : F.FiberCat x} {z : ObjY} (hz : z ∈ C.U a.val) : F.obj z ∈ C.R.U :=
  (C.isScDiffeoOn_σObj a).mapsTo hz

/-- `F` is injective on `U(y)`. -/
theorem injOn_obj (a : F.FiberCat x) : InjOn F.obj (C.U a.val) := fun w hw w' hw' h => by
  rw [← (C.isScDiffeoOn_σObj a).left_inv w hw, h, (C.isScDiffeoOn_σObj a).left_inv w' hw']

/-- The `U(y)`, `y ∈ F⁻¹(x)`, are disjoint. -/
theorem fiber_eq_of_mem {a a' : F.FiberCat x} {z : ObjY} (h : z ∈ C.U a.val)
    (h' : z ∈ C.U a'.val) : a = a' := by
  by_contra hne
  have hne' : a.val ≠ a'.val := fun he => hne (GroupoidStr.FullOb.ext he)
  exact Set.disjoint_left.1 (C.pairwiseDisjoint_U a.mem a'.mem hne') h h'

/-- `(s|𝐔(ψ₀))⁻¹ : U(y) → 𝐔(ψ₀)` for `ψ₀ : y → y'` in `D`. -/
def σSrc {a b : F.FiberCat x} (ψ : a ⟶ b) : ObjY → MorY :=
  (C.isScDiffeoOn_src ψ.1 (mem_morOn_of_hom ψ)).choose

/-- `s : 𝐔(ψ₀) → U(y)` is an sc-diffeomorphism with inverse `σSrc` (Theorem 8.5 (3)). -/
theorem isScDiffeoOn_σSrc {a b : F.FiberCat x} (ψ : a ⟶ b) :
    Y.PMor.IsScDiffeoOn Y.PObj Y.src (C.σSrc ψ) (C.sheet ψ.1) (C.U a.val) := by
  rw [← congrArg C.U (show Y.src ψ.1 = a.val from ψ.2.1)]
  exact (C.isScDiffeoOn_src ψ.1 (mem_morOn_of_hom ψ)).choose_spec

/-- `(t|𝐔(ψ₀))⁻¹ : U(y') → 𝐔(ψ₀)` for `ψ₀ : y → y'` in `D`. -/
def σTgt {a b : F.FiberCat x} (ψ : a ⟶ b) : ObjY → MorY :=
  (C.isScDiffeoOn_tgt ψ.1 (mem_morOn_of_hom ψ)).choose

/-- `t : 𝐔(ψ₀) → U(y')` is an sc-diffeomorphism with inverse `σTgt` (Theorem 8.5 (3)). -/
theorem isScDiffeoOn_σTgt {a b : F.FiberCat x} (ψ : a ⟶ b) :
    Y.PMor.IsScDiffeoOn Y.PObj Y.tgt (C.σTgt ψ) (C.sheet ψ.1) (C.U b.val) := by
  rw [← congrArg C.U (show Y.tgt ψ.1 = b.val from ψ.2.2)]
  exact (C.isScDiffeoOn_tgt ψ.1 (mem_morOn_of_hom ψ)).choose_spec

/-- `s(σ_ψ(z)) = z`. -/
theorem src_σSrc {a b : F.FiberCat x} (ψ : a ⟶ b) {z : ObjY} (hz : z ∈ C.U a.val) :
    Y.src (C.σSrc ψ z) = z :=
  (C.isScDiffeoOn_σSrc ψ).right_inv z hz

/-- **`F(σ_ψ(z)) = Γ(f(ψ), F(z))`**: on the sheet `𝐔(ψ₀)` the functor `F` lands in the sheet
`𝐔(f(ψ₀)) = Γ(f(ψ₀), U(x))` (Theorem 8.5 (1), (4)). -/
theorem mor_σSrc {a b : F.FiberCat x} (ψ : a ⟶ b) {z : ObjY} (hz : z ∈ C.U a.val) :
    F.mor (C.σSrc ψ z) = C.R.Γ (F.fiberIsotropy x ψ) (F.obj z) := by
  have hφ : C.σSrc ψ z ∈ C.sheet ψ.1 := (C.isScDiffeoOn_σSrc ψ).mapsTo_inv hz
  obtain ⟨G', hG'⟩ := C.isScDiffeoOn_mor ψ.1 (mem_morOn_of_hom ψ)
  have h1 : F.mor (C.σSrc ψ z) ∈
      connectedComponentIn (X.morOn C.R.U) (F.fiberIsotropy x ψ).val := hG'.mapsTo hφ
  rw [C.connectedComponentIn_eq] at h1
  obtain ⟨w, hw, hwe⟩ := h1
  have hsrc : X.src (F.mor (C.σSrc ψ z)) = F.obj z := by rw [F.src_mor, C.src_σSrc ψ hz]
  rw [← hwe, C.R.src_Γ _ w hw] at hsrc
  rw [← hwe, hsrc]

/-- `F(t(σ_ψ(z))) = Φ(f(ψ))(F(z))`. -/
theorem obj_tgt_σSrc {a b : F.FiberCat x} (ψ : a ⟶ b) {z : ObjY} (hz : z ∈ C.U a.val) :
    F.obj (Y.tgt (C.σSrc ψ z)) = C.R.Φ (F.fiberIsotropy x ψ) (F.obj z) := by
  rw [← F.tgt_mor, C.mor_σSrc ψ hz, C.R.tgt_Γ _ _ (C.obj_mem hz)]

/-- `L_D(ψ₀) = t ∘ (s|𝐔(ψ₀))⁻¹ : U(y) → U(y')` is an sc-diffeomorphism. -/
theorem isScDiffeoOn_hat {a b : F.FiberCat x} (ψ : a ⟶ b) :
    Y.PObj.IsScDiffeoOn Y.PObj (Y.tgt ∘ C.σSrc ψ) (Y.src ∘ C.σTgt ψ) (C.U a.val) (C.U b.val) :=
  (C.isScDiffeoOn_σTgt ψ).comp (C.isScDiffeoOn_σSrc ψ).symm

/-- `L_D(ψ₀)` maps `U(y)` into `U(y')`. -/
theorem tgt_σSrc_mem {a b : F.FiberCat x} (ψ : a ⟶ b) {z : ObjY} (hz : z ∈ C.U a.val) :
    Y.tgt (C.σSrc ψ z) ∈ C.U b.val :=
  (C.isScDiffeoOn_hat ψ).mapsTo hz

/-- `L_D(1_y) = 1`: `F` is injective on `U(y)` and `F ∘ L_D(1_y) = Φ(1) ∘ F = F`. -/
theorem hat_id (a : F.FiberCat x) {z : ObjY} (hz : z ∈ C.U a.val) :
    Y.tgt (C.σSrc (𝟙 a) z) = z := by
  refine C.injOn_obj a (C.tgt_σSrc_mem _ hz) hz ?_
  rw [C.obj_tgt_σSrc _ hz, fiberIsotropy_id, C.R.Φ_one _ (C.obj_mem hz)]

/-- `L_D(ψ ∘ γ) = L_D(ψ) ∘ L_D(γ)`: `F` is injective on `U(y'')` and both sides are
`Φ(f(ψ) f(γ)) ∘ F` after `F`. -/
theorem hat_comp {a b c : F.FiberCat x} (γ : a ⟶ b) (ψ : b ⟶ c) {z : ObjY} (hz : z ∈ C.U a.val) :
    Y.tgt (C.σSrc (γ ≫ ψ) z) = Y.tgt (C.σSrc ψ (Y.tgt (C.σSrc γ z))) := by
  refine C.injOn_obj c (C.tgt_σSrc_mem _ hz) (C.tgt_σSrc_mem _ (C.tgt_σSrc_mem _ hz)) ?_
  rw [C.obj_tgt_σSrc _ hz, C.obj_tgt_σSrc _ (C.tgt_σSrc_mem _ hz), C.obj_tgt_σSrc _ hz,
    fiberIsotropy_comp, C.R.Φ_mul _ _ _ (C.obj_mem hz)]

/-- `U(y)` as an object of `Diff_sc`. -/
abbrev objU (a : F.FiberCat x) : MPolyfoldCat.{0} := MPolyfoldCat.ofOpen Y.PObj (C.isOpen_U' a)

/-- `U(x)` as an object of `Diff_sc`. -/
abbrev objRU : MPolyfoldCat.{0} := MPolyfoldCat.ofOpen X.PObj C.R.isOpen_U

/-- **`L_D : D → Diff_sc`** (p. 283): `L_D(y) = U(y)`, `L_D(ψ₀) = t ∘ (s|𝐔(ψ₀))⁻¹`. -/
abbrev liftLD : F.FiberCat x ⥤ MPolyfoldCat.{0} where
  obj a := C.objU a
  map ψ := ScDiffeo.ofOpen (C.isOpen_U' _) (C.isOpen_U' _) (C.isScDiffeoOn_hat ψ)
  map_id a := ScDiffeo.ext (funext fun z => Subtype.ext (C.hat_id a z.2))
  map_comp γ ψ := ScDiffeo.ext (funext fun z => Subtype.ext (C.hat_comp γ ψ z.2))

/-- **`L_C : C → Diff_sc`** (p. 283): `L_C(x) = U(x)`, `L_C(g) = Φ(g)`. -/
abbrev liftLC : SingleObj (X.Isotropy x) ⥤ MPolyfoldCat.{0} where
  obj _ := C.objRU
  map g := ScDiffeo.ofOpen C.R.isOpen_U C.R.isOpen_U (C.R.isScDiffeoOn_Φ g)
  map_id _ := ScDiffeo.ext (funext fun z => Subtype.ext (C.R.Φ_one z.1 z.2))
  map_comp g h := ScDiffeo.ext (funext fun z => Subtype.ext (C.R.Φ_mul h g z.1 z.2))

/-- **`τ : L_D → L_C ∘ f`** (p. 284): `τ(y) = F|U(y) : U(y) → U(x)`. -/
abbrev liftτ : C.liftLD ⟶ F.restrictFiber x ⋙ C.liftLC where
  app a := ScDiffeo.ofOpen (C.isOpen_U' a) C.R.isOpen_U (C.isScDiffeoOn_σObj a)
  naturality _ _ ψ := ScDiffeo.ext (funext fun z => Subtype.ext (C.obj_tgt_σSrc ψ z.2))

/-- **The geometric lift of `f = F|D`** (Theorem 8.6, p. 283): `L_C(x) = U(x)`,
`L_C(g) = Φ(g)`; `L_D(y) = U(y)`, `L_D(ψ₀) = t ∘ (s|𝐔(ψ₀))⁻¹`; `τ(y) = F|U(y)`. -/
abbrev geometricLift : GeometricLift.{0} (F.restrictFiber x) := ⟨C.liftLD, C.liftLC, C.liftτ⟩

@[simp] theorem geometricLift_τy_val (a : F.FiberCat x) (z : C.U a.val) :
    (C.geometricLift.τy a z : C.R.U).1 = F.obj z.1 := rfl

@[simp] theorem geometricLift_φ_val {a b : F.FiberCat x} (ψ : a ⟶ b) (z : C.U a.val) :
    (C.geometricLift.φ ψ z : C.U b.val).1 = Y.tgt (C.σSrc ψ z.1) := rfl

@[simp] theorem geometricLift_LC_map_val (g : X.Isotropy x) (z : C.R.U) :
    ((C.geometricLift.LC.map (X := SingleObj.star _) (Y := SingleObj.star _) g).toFun z : C.R.U).1 =
      C.R.Φ g z.1 := rfl

/-! #### The functors `Φ : L → X` and `Ψ : K → Y` -/

section Embeddings

variable [Fintype (X.Isotropy x)]

/-- **`Φ : L = G_x ⋉ U(x) → X`** (p. 284): the inclusion on objects, `Φ(g, z) = Γ(g, z)` on
morphisms. -/
def Φ : EpFunctor (geometricLiftTarget C.geometricLift) X where
  obj z := (z : C.R.U).1
  mor p := C.R.Γ p.1.down (p.2 : C.R.U).1
  src_mor p := C.R.src_Γ _ _ (p.2 : C.R.U).2
  tgt_mor p := C.R.tgt_Γ _ _ (p.2 : C.R.U).2
  mor_comp p q h := by
    have h' : (p.2 : C.R.U).1 = C.R.Φ q.1.down (q.2 : C.R.U).1 := congrArg Subtype.val h
    change C.R.Γ (p.1.down * q.1.down) (q.2 : C.R.U).1 =
      X.comp (C.R.Γ p.1.down (p.2 : C.R.U).1) (C.R.Γ q.1.down (q.2 : C.R.U).1)
    rw [h', C.R.Γ_mul _ _ (q.2 : C.R.U).2]
  mor_unit z := C.R.Γ_one (z : C.R.U).2
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_subtypeVal C.R.isOpen_U
  isScSmoothMap_mor := isScSmoothMap_prod_discrete_iff.2 fun g =>
    (C.R.isScSmoothOn_Γ g.down).comp (MPolyfold.isScSmoothMap_subtypeVal C.R.isOpen_U)
      fun z _ => z.2

@[simp] theorem Φ_obj (z : C.R.U) : C.Φ.obj z = z.1 := rfl

@[simp] theorem Φ_mor (p : ULift (X.Isotropy x) × C.R.U) : C.Φ.mor p = C.R.Γ p.1.down p.2.1 :=
  rfl

/-- `Φ` is injective on morphisms: `s Γ(g, z) = z` and Theorem 7.1 (3). -/
theorem injective_Φ_mor : Injective C.Φ.mor := by
  rintro ⟨g, a⟩ ⟨g', a'⟩ h
  have h1 : X.src (C.R.Γ g.down (a : C.R.U).1) = X.src (C.R.Γ g'.down (a' : C.R.U).1) :=
    congrArg X.src h
  rw [C.R.src_Γ _ _ (a : C.R.U).2, C.R.src_Γ _ _ (a' : C.R.U).2] at h1
  obtain rfl : a = a' := Subtype.ext h1
  obtain rfl : g = g' := ULift.ext _ _ ((C.R.Γ_inj (a : C.R.U).2).1 h)
  rfl

/-- `Φ` is a local sc-diffeomorphism on morphisms: on the sheet `{g} × U(x)` it is
`Γ(g, ·) = (s|𝐔(g))⁻¹`. -/
theorem isLocalScDiffeo_Φ_mor :
    (geometricLiftTarget C.geometricLift).PMor.IsLocalScDiffeo X.PMor C.Φ.mor := by
  rintro ⟨g, a⟩
  refine ⟨{g} ×ˢ univ, C.R.Γ g.down '' C.R.U,
    (fun z => (g, z)) ∘ (MPolyfold.openRetraction C.R.U ∘ X.src), ⟨rfl, mem_univ _⟩, ?_⟩
  refine (((C.R.isScDiffeoOn_src_image g.down).symm.comp
    (MPolyfold.isScDiffeoOn_subtypeVal C.R.isOpen_U)).comp
      (isScDiffeoOn_snd_sheet (PX := (C.liftLC.obj (SingleObj.star _)).P) g)).congr_left ?_
  rintro ⟨g', a'⟩ ⟨hg', -⟩
  obtain rfl : g' = g := hg'
  rfl

/-- `Φ` is full: every morphism `φ` of `X` between points of `U(x)` is `Γ(g, s φ)`
(Theorem 7.1 (3)). -/
theorem full_Φ : C.Φ.toFunctor.Full where
  map_surjective {a b} φ := by
    let a' : C.R.U := a
    let b' : C.R.U := b
    have ha : X.src φ.1 = a'.1 := φ.2.1
    have hb : X.tgt φ.1 = b'.1 := φ.2.2
    obtain ⟨g, hg, -⟩ := C.R.existsUnique_Γ φ.1 (by rw [ha]; exact a'.2) (by rw [hb]; exact b'.2)
    rw [ha] at hg
    refine ⟨⟨(ULift.up g, a'), rfl, Subtype.ext ?_⟩, Subtype.ext hg⟩
    change C.R.Φ g a'.1 = b'.1
    rw [← C.R.tgt_Γ g a'.1 a'.2, hg, hb]

/-- **`Φ : L → X` is a fully faithful open embedding** (Theorem 8.6). -/
theorem isFullyFaithfulOpenEmbedding_Φ : C.Φ.IsFullyFaithfulOpenEmbedding where
  full := C.full_Φ
  faithful := faithful_of_injective_mor C.injective_Φ_mor
  injective_obj := Subtype.val_injective
  isLocalScDiffeo_obj := MPolyfold.isLocalScDiffeo_subtypeVal C.R.isOpen_U
  injective_mor := C.injective_Φ_mor
  isLocalScDiffeo_mor := C.isLocalScDiffeo_Φ_mor

/-- The image of `Φ` on objects is `U(x)`. -/
theorem range_Φ_obj : range C.Φ.obj = C.R.U := Subtype.range_coe

/-- The image of `Φ` on morphisms is `𝐔(x) = {φ | s(φ), t(φ) ∈ U(x)}`: the image of `Φ` is the
full subcategory on `U(x)`. -/
theorem range_Φ_mor : range C.Φ.mor = X.morOn C.R.U := by
  ext φ
  constructor
  · rintro ⟨⟨g, a⟩, rfl⟩
    exact C.R.Γ_mem_morOn g.down (a : C.R.U).2
  · intro hφ
    obtain ⟨g, hg⟩ := C.R.exists_Γ_eq hφ
    exact ⟨(ULift.up g, (⟨X.src φ, hφ.1⟩ : C.R.U)), hg⟩

end Embeddings

/-- `σ_{ψ ∘ γ}(z) = σ_ψ(t σ_γ(z)) ∘ σ_γ(z)`: both lift `Γ(f(ψ) f(γ), F(z))` at `z`
(Definition 8.8 (3)). -/
theorem σSrc_comp (hF : F.IsProperCovering) {a b c : F.FiberCat x} (γ : a ⟶ b) (ψ : b ⟶ c)
    {z : ObjY} (hz : z ∈ C.U a.val) :
    C.σSrc (γ ≫ ψ) z = Y.comp (C.σSrc ψ (Y.tgt (C.σSrc γ z))) (C.σSrc γ z) := by
  have hz' := C.tgt_σSrc_mem γ hz
  have hc : Y.src (C.σSrc ψ (Y.tgt (C.σSrc γ z))) = Y.tgt (C.σSrc γ z) := C.src_σSrc ψ hz'
  refine (hF.existsUnique_lift (φ := F.mor (C.σSrc (γ ≫ ψ) z)) (y := z)
    (by rw [F.src_mor, C.src_σSrc _ hz])).unique ⟨rfl, C.src_σSrc _ hz⟩ ⟨?_, ?_⟩
  · rw [F.mor_comp _ _ hc, C.mor_σSrc ψ hz', C.mor_σSrc γ hz, C.mor_σSrc (γ ≫ ψ) hz,
      C.obj_tgt_σSrc γ hz, C.R.Γ_mul _ _ (C.obj_mem hz), fiberIsotropy_comp]
  · rw [Y.src_comp _ _ hc, C.src_σSrc γ hz]

/-- `σ_{1_y}(z) = 1_z`: both lift `1_{F(z)}` at `z` (Definition 8.8 (3)). -/
theorem σSrc_id (hF : F.IsProperCovering) (a : F.FiberCat x) {z : ObjY} (hz : z ∈ C.U a.val) :
    C.σSrc (𝟙 a) z = Y.unit z := by
  refine (hF.existsUnique_lift (φ := X.unit (F.obj z)) (y := z) (X.src_unit _)).unique
    ⟨?_, C.src_σSrc _ hz⟩ ⟨F.mor_unit z, Y.src_unit z⟩
  rw [C.mor_σSrc _ hz, fiberIsotropy_id, C.R.Γ_one (C.obj_mem hz)]

section Embeddings

variable [Fintype (F.FiberCat x)] [∀ a b : F.FiberCat x, Fintype (a ⟶ b)]

/-- **`Ψ : K → Y`** (p. 284): the inclusion on objects; `(ψ₀, z) ↦ (s|𝐔(ψ₀))⁻¹(z)` on
morphisms. -/
def Ψ (hF : F.IsProperCovering) : EpFunctor (geometricLiftSource C.geometricLift) Y where
  obj p := (p.2 : C.U p.1.val).1
  mor p := C.σSrc p.1.2.2 (p.2 : C.U p.1.1.val).1
  src_mor p := C.src_σSrc p.1.2.2 (p.2 : C.U p.1.1.val).2
  tgt_mor _ := rfl
  mor_comp p q h := by
    obtain ⟨⟨a, b, ψ⟩, z'⟩ := p
    obtain ⟨⟨c, d, γ⟩, z⟩ := q
    have h' : (⟨a, z'⟩ : C.geometricLift.YObj) = ⟨d, C.geometricLift.φ γ z⟩ := h
    obtain ⟨rfl, h''⟩ := Sigma.mk.inj_iff.1 h'
    obtain rfl := eq_of_heq h''
    change C.σSrc ((geometricLiftSource C.geometricLift).comp _ _).1.2.2 _ = _
    rw [geometricLiftSource_comp_mk]
    exact C.σSrc_comp hF γ ψ (z : C.U c.val).2
  mor_unit p := C.σSrc_id hF p.1 (p.2 : C.U p.1.val).2
  isScSmoothMap_obj := (MPolyfold.isScSmoothMap_sigma_iff _).2 fun a =>
    MPolyfold.isScSmoothMap_subtypeVal (C.isOpen_U' a)
  isScSmoothMap_mor := (MPolyfold.isScSmoothMap_sigma_iff _).2 fun ψ =>
    (C.isScDiffeoOn_σSrc ψ.2.2).isScSmoothOn_inv.comp
      (MPolyfold.isScSmoothMap_subtypeVal (C.isOpen_U' ψ.1)) fun z _ => z.2

variable (hF : F.IsProperCovering)

@[simp] theorem Ψ_obj (p : C.geometricLift.YObj) : (C.Ψ hF).obj p = (p.2 : C.U p.1.val).1 := rfl

@[simp] theorem Ψ_mor (p : C.geometricLift.YMor) :
    (C.Ψ hF).mor p = C.σSrc p.1.2.2 (p.2 : C.U p.1.1.val).1 := rfl

/-- `Ψ` is injective on objects: the `U(y)` are disjoint. -/
theorem injective_Ψ_obj : Injective (C.Ψ hF).obj := by
  rintro ⟨a, z⟩ ⟨a', z'⟩ h
  have h' : (z : C.U a.val).1 = (z' : C.U a'.val).1 := h
  obtain rfl := C.fiber_eq_of_mem (z : C.U a.val).2 (h' ▸ (z' : C.U a'.val).2)
  obtain rfl : z = z' := Subtype.ext h'
  rfl

/-- `Ψ` is injective on morphisms: the `𝐔(ψ₀)` are disjoint and `s` is injective on each. -/
theorem injective_Ψ_mor : Injective (C.Ψ hF).mor := by
  rintro ⟨⟨a, b, ψ⟩, z⟩ ⟨⟨a', b', ψ'⟩, z'⟩ h
  have h : C.σSrc ψ (z : C.U a.val).1 = C.σSrc ψ' (z' : C.U a'.val).1 := h
  have hs : (z : C.U a.val).1 = (z' : C.U a'.val).1 := by
    rw [← C.src_σSrc ψ (z : C.U a.val).2, h, C.src_σSrc ψ' (z' : C.U a'.val).2]
  obtain rfl := C.fiber_eq_of_mem (z : C.U a.val).2 (hs ▸ (z' : C.U a'.val).2)
  obtain rfl : z = z' := Subtype.ext hs
  have hψ : ψ.1 = ψ'.1 := by
    by_contra hne
    exact Set.disjoint_left.1 (C.pairwiseDisjoint_sheet (mem_morOn_of_hom ψ)
      (mem_morOn_of_hom ψ') hne) ((C.isScDiffeoOn_σSrc ψ).mapsTo_inv (z : C.U a.val).2)
      (h ▸ (C.isScDiffeoOn_σSrc ψ').mapsTo_inv (z : C.U a.val).2)
  obtain rfl : b = b' :=
    GroupoidStr.FullOb.ext (ψ.2.2.symm.trans ((congrArg Y.tgt hψ).trans ψ'.2.2))
  obtain rfl : ψ = ψ' := Subtype.ext hψ
  rfl

/-- `Ψ` is a local sc-diffeomorphism on morphisms: `(s|𝐔(ψ₀))⁻¹` on the summand `ψ₀`. -/
theorem isLocalScDiffeo_Ψ_mor :
    (geometricLiftSource C.geometricLift).PMor.IsLocalScDiffeo Y.PMor (C.Ψ hF).mor :=
  (MPolyfold.isLocalScDiffeo_sigma_iff _).2 fun ψ _ =>
    ⟨univ, C.sheet ψ.2.2.1, MPolyfold.openRetraction _ ∘ Y.src, mem_univ _,
      (C.isScDiffeoOn_σSrc ψ.2.2).symm.comp (MPolyfold.isScDiffeoOn_subtypeVal (C.isOpen_U' ψ.1))⟩

/-- `Ψ` is full: a morphism `φ` of `Y` from `z ∈ U(y)` to `z' ∈ U(y')` lies in a sheet `𝐔(ψ₀)`,
`ψ₀ : y → y'` (Theorem 8.5 (2)), and is `(s|𝐔(ψ₀))⁻¹(z)`. -/
theorem full_Ψ : (C.Ψ hF).toFunctor.Full where
  map_surjective {p p'} φ := by
    let q : C.geometricLift.YObj := p
    let q' : C.geometricLift.YObj := p'
    have hs : Y.src φ.1 = (q.2 : C.U q.1.val).1 := φ.2.1
    have ht : Y.tgt φ.1 = (q'.2 : C.U q'.1.val).1 := φ.2.2
    have hmem : φ.1 ∈ {ψ | Y.src ψ ∈ C.U q.1.val ∧ Y.tgt ψ ∈ C.U q'.1.val} :=
      ⟨hs ▸ (q.2 : C.U q.1.val).2, ht ▸ (q'.2 : C.U q'.1.val).2⟩
    rw [C.morOn_U_eq _ q.1.mem _ q'.1.mem] at hmem
    obtain ⟨ψ₀, hψ₀, hφ⟩ := mem_iUnion₂.1 hmem
    let ψ : q.1 ⟶ q'.1 := ⟨ψ₀, hψ₀⟩
    have h1 : C.σSrc ψ (q.2 : C.U q.1.val).1 = φ.1 := by
      rw [← hs]
      exact (C.isScDiffeoOn_σSrc ψ).left_inv φ.1 hφ
    refine ⟨⟨⟨⟨q.1, q'.1, ψ⟩, q.2⟩, rfl, ?_⟩, Subtype.ext h1⟩
    refine Sigma.ext rfl (heq_of_eq (Subtype.ext ?_))
    change Y.tgt (C.σSrc ψ (q.2 : C.U q.1.val).1) = (q'.2 : C.U q'.1.val).1
    rw [h1, ht]

/-- **`Ψ : K → Y` is a fully faithful open embedding** (Theorem 8.6). -/
theorem isFullyFaithfulOpenEmbedding_Ψ : (C.Ψ hF).IsFullyFaithfulOpenEmbedding where
  full := C.full_Ψ hF
  faithful := faithful_of_injective_mor (C.injective_Ψ_mor hF)
  injective_obj := C.injective_Ψ_obj hF
  isLocalScDiffeo_obj := (MPolyfold.isLocalScDiffeo_sigma_iff _).2 fun a =>
    MPolyfold.isLocalScDiffeo_subtypeVal (C.isOpen_U' a)
  injective_mor := C.injective_Ψ_mor hF
  isLocalScDiffeo_mor := C.isLocalScDiffeo_Ψ_mor hF

/-- The image of `Ψ` on objects is `F⁻¹(U(x)) = ⋃ U(y)`. -/
theorem range_Ψ_obj : range (C.Ψ hF).obj = F.obj ⁻¹' C.R.U := by
  rw [C.preimage_eq]
  ext w
  simp only [mem_range, mem_iUnion]
  constructor
  · rintro ⟨⟨a, z⟩, rfl⟩
    exact ⟨a.val, a.mem, (z : C.U a.val).2⟩
  · rintro ⟨y, hy, hw⟩
    exact ⟨⟨⟨y, hy⟩, (⟨w, hw⟩ : C.U y)⟩, rfl⟩

/-- The image of `Ψ` on morphisms is `{φ | s(φ), t(φ) ∈ F⁻¹(U(x))}`: the image of `Ψ` is the
full subcategory on `F⁻¹(U(x))`. -/
theorem range_Ψ_mor : range (C.Ψ hF).mor = Y.morOn (F.obj ⁻¹' C.R.U) := by
  ext φ
  constructor
  · rintro ⟨⟨⟨a, b, ψ⟩, z⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change F.obj (Y.src (C.σSrc ψ (z : C.U a.val).1)) ∈ C.R.U
      rw [C.src_σSrc ψ (z : C.U a.val).2]
      exact C.obj_mem (z : C.U a.val).2
    · exact C.obj_mem (C.tgt_σSrc_mem ψ (z : C.U a.val).2)
  · rintro ⟨hs, ht⟩
    rw [C.preimage_eq] at hs ht
    obtain ⟨a, ha, hsa⟩ := mem_iUnion₂.1 hs
    obtain ⟨b, hb, htb⟩ := mem_iUnion₂.1 ht
    have hmem : φ ∈ {ψ | Y.src ψ ∈ C.U a ∧ Y.tgt ψ ∈ C.U b} := ⟨hsa, htb⟩
    rw [C.morOn_U_eq a ha b hb] at hmem
    obtain ⟨ψ₀, hψ₀, hφ⟩ := mem_iUnion₂.1 hmem
    let ψ : (⟨a, ha⟩ : F.FiberCat x) ⟶ ⟨b, hb⟩ := ⟨ψ₀, hψ₀⟩
    exact ⟨⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ψ⟩, (⟨Y.src φ, hsa⟩ : C.U a)⟩,
      (C.isScDiffeoOn_σSrc ψ).left_inv φ hφ⟩

variable [Fintype (X.Isotropy x)]

/-- **The square of Theorem 8.6 commutes**: `F ∘ Ψ = Φ ∘ A`, `A : K → L` the functor of
Proposition 8.3 for the geometric lift `C.geometricLift`. -/
theorem comp_Ψ : F.comp (C.Ψ hF) = C.Φ.comp (geometricLiftFunctor C.geometricLift) :=
  EpFunctor.ext rfl (funext fun p => C.mor_σSrc p.1.2.2 (p.2 : C.U p.1.1.val).2)

end Embeddings

end ProperCoveringChart

/-! #### Theorem 8.6 -/

/-- **Theorem 8.6 (Proper Covering II)**: let `F : Y → X` be a proper covering functor and
`x ∈ X`; `C = SingleObj G_x` is the full subcategory on `x`, `D` the full subcategory on the
finite set `F⁻¹(x)`.  Then (a) `f = F|D : D → C` is a covering functor; (b) there are
neighbourhoods `U(x)` as in Theorem 8.5 inside every open `V ∋ x`; and (c) for every such `U(x)`
(a chart `C` of Theorem 8.5) there are a geometric lift `L` of `f`, with associated proper
covering functor `A : K → L` (Proposition 8.3), and fully faithful open embedding functors
`Φ : L → X`, `Ψ : K → Y`, the image of `Φ` the full subcategory on `U(x)` and the image of `Ψ`
the full subcategory on `F⁻¹(U(x))`, with `F ∘ Ψ = Φ ∘ A`.  The witnesses are
`C.geometricLift`, `C.Φ`, `C.Ψ hF`. -/
theorem theorem_8_6 {F : EpFunctor Y X} (hF : F.IsProperCovering) (x : ObjX) :
    IsCoveringFunctor (F.restrictFiber x) ∧
      (∀ V : Set ObjX, IsOpen V → x ∈ V → ∃ C : F.ProperCoveringChart x, C.R.U ⊆ V) ∧
      ∀ C : F.ProperCoveringChart x,
        letI := fintypeFiberCat x hF
        letI := fintypeFiberCatHom x hF
        letI : Fintype (X.Isotropy x) := Fintype.ofFinite _
        ∃ (L : GeometricLift.{0} (F.restrictFiber x))
          (Φ : EpFunctor (geometricLiftTarget L) X) (Ψ : EpFunctor (geometricLiftSource L) Y),
          (geometricLiftFunctor L).IsProperCovering ∧
          Φ.IsFullyFaithfulOpenEmbedding ∧ Ψ.IsFullyFaithfulOpenEmbedding ∧
          range Φ.obj = C.R.U ∧ range Φ.mor = X.morOn C.R.U ∧
          range Ψ.obj = F.obj ⁻¹' C.R.U ∧ range Ψ.mor = Y.morOn (F.obj ⁻¹' C.R.U) ∧
          F.comp Ψ = Φ.comp (geometricLiftFunctor L) := by
  refine ⟨covering_restrict x hF, fun V hV hx => theorem_8_5 hF x hV hx, fun C => ?_⟩
  let _ := fintypeFiberCat x hF
  let _ := fintypeFiberCatHom x hF
  let _ : Fintype (X.Isotropy x) := Fintype.ofFinite _
  have := nonempty_fiberCat x hF
  exact ⟨C.geometricLift, C.Φ, C.Ψ hF, proposition_8_3 (covering_restrict x hF) _,
    C.isFullyFaithfulOpenEmbedding_Φ, C.isFullyFaithfulOpenEmbedding_Ψ hF, C.range_Φ_obj,
    C.range_Φ_mor, C.range_Ψ_obj hF, C.range_Ψ_mor hF, C.comp_Ψ hF⟩

end EpFunctor

end Theorem86

end Polyfold
