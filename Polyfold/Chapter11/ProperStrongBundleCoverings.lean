import Polyfold.Chapter11.ProperCoveringLocalization
import Polyfold.Chapter10.StrongBundleEquivalenceNat
import Polyfold.Chapter8.Book2021
import Polyfold.Chapter10.StrongBundleLocalizationCategory
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The category `SBPC` of proper strong bundle coverings (2021 Remark 11.6.9)

**2021 Remark 11.6.9, pp. 563–566 (2017: Remark 11.27).**  The remark views a strong bundle
`P : W → Y` over an ep-groupoid as a functor of ep-groupoids, recalls Definition 8.5.9 for a
pair `(A, F)` and describes the category `SBPC`: objects are proper coverings between strong
bundles `(A, F)`, morphisms are commutative cubes, and a class of equivalences gives the
localization `SBPC[E⁻¹_SBPC]`, the details being left to the reader.

## Main declarations

* `SBPC`: an object `(A, F)`: strong bundles `W → Y` and `V → X` (objects of `SEP`), a strong
  bundle functor `A` covering `F` (a morphism of `SEP`), and Definition 8.5.9 for its object map.
* `SBPC.Hom`, `instCategorySBPC`: the commutative cubes.
* `SBPC.forget`: the functor `SBPC → PC`, `(A, F) ↦ F`.
* `SBPC.equivalences`: the class `E_SBPC`, multiplicative; `forget` maps it into `E_PC`.
* `SBPC.Loc`, `SBPC.Q`: the localization `SBPC[E⁻¹_SBPC]` (Mathlib's construction), with
  `isLocalization_Q`, `lift`, `fac`, `uniq`.
* `SBPC.toPCLoc`, `SBPC.toPCLoc_fac`: `forget` descends to `SBPC[E⁻¹] → PC[E⁻¹_PC]`.
* `SBPC.toSEPLocW`, `SBPC.toSEPLocV` (with `_fac`): the two bundles descend to `SEP(F⁻¹)`.
* `SBPC.ofSEP`: the identity covering of a strong bundle, an object of `SBPC`.

## Readings

* A morphism of `SBPC` is a pair of `SEP` morphisms `W → W'`, `V → V'` with `A' ∘ a = b ∘ A` in
  `SEP`.  The equation in `SEP` is the top face (on total spaces) and the bottom face (on bases)
  of the cube; the side faces commute because `SEP` morphisms are strong bundle functors.
* "A class of equivalences" is not defined in the text.  We take `E_SBPC` to consist of the
  morphisms whose two `SEP` components are strong bundle equivalences (the class `F` of
  Definition 10.4.11) and whose underlying `PC` morphism lies in `E_PC` (Definition 11.6.4 (2)).
* `SBPC[E⁻¹_SBPC]` is the localization in the sense of its universal property; we use Mathlib's
  construction.  The description by diagrams as for `PC`, with Theorem 11.6.6 for strong
  bundles, is in `StrongBundleCoveringPullback.lean`, `StrongBundleCoveringFibredProduct.lean` (`SBPC.theorem_11_6_6`) and
  `StrongBundleCoveringLocalization.lean` (`SBPCLoc`, `SBPCLoc.fromLoc`).  There `SBPC.equivalences_iff`
  shows that the third clause of `E_SBPC` (base face in `E_PC`) follows from the first two.
-/

open CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-- **2021 Remark 11.6.9, p. 565 (2017: Remark 11.27)**: an object `(A, F)` of `SBPC`.  `W` is
the strong bundle over `Y`, `V` the one over `X`, `A : W → V` a strong bundle functor covering
`F : Y → X`, and Definition 8.5.9 holds for the object map of `A`. -/
structure SBPC : Type (u + 1) where
  /-- The strong bundle `P : W → Y`. -/
  W : SEP.{u}
  /-- The strong bundle `Q : V → X`. -/
  V : SEP.{u}
  /-- The strong bundle functor `A` covering `F`. -/
  A : W ⟶ V
  /-- Definition 8.5.9 for `(A, F)`. -/
  isProper : W.E.IsProperStrongBundleCovering2021 V.E A.ϕ A.Φ.obj

namespace SBPC

/-- **2021 Remark 11.6.9, p. 566**: a morphism `(A, F) → (A', F')` of `SBPC`, a commutative cube:
`a : W → W'`, `b : V → V'` in `SEP` with `A' ∘ a = b ∘ A`. -/
@[ext]
structure Hom (P P' : SBPC.{u}) where
  /-- The functor `W → W'` (with its base `Y → Y'`). -/
  a : P.W ⟶ P'.W
  /-- The functor `V → V'` (with its base `X → X'`). -/
  b : P.V ⟶ P'.V
  comm : P.A ≫ b = a ≫ P'.A

/-- The identity cube. -/
def Hom.id (P : SBPC.{u}) : Hom P P :=
  ⟨𝟙 _, 𝟙 _, by rw [Category.comp_id, Category.id_comp]⟩

/-- The composition of cubes. -/
def Hom.comp {P P' P'' : SBPC.{u}} (f : Hom P P') (g : Hom P' P'') : Hom P P'' :=
  ⟨f.a ≫ g.a, f.b ≫ g.b, by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, Category.assoc]⟩

end SBPC

/-- **2021 Remark 11.6.9, p. 566 (2017: Remark 11.27)**: the category `SBPC`. -/
instance instCategorySBPC : LargeCategory SBPC.{u} where
  Hom := SBPC.Hom
  id := SBPC.Hom.id
  comp := SBPC.Hom.comp
  id_comp f := SBPC.Hom.ext (Category.id_comp f.a) (Category.id_comp f.b)
  comp_id f := SBPC.Hom.ext (Category.comp_id f.a) (Category.comp_id f.b)
  assoc f g h := SBPC.Hom.ext (Category.assoc f.a g.a h.a) (Category.assoc f.b g.b h.b)

namespace SBPC

@[ext]
theorem hom_ext {P P' : SBPC.{u}} {f g : P ⟶ P'} (ha : Hom.a f = Hom.a g)
    (hb : Hom.b f = Hom.b g) : f = g :=
  Hom.ext ha hb

@[simp] theorem id_a (P : SBPC.{u}) : Hom.a (𝟙 P) = 𝟙 P.W := rfl
@[simp] theorem id_b (P : SBPC.{u}) : Hom.b (𝟙 P) = 𝟙 P.V := rfl

@[simp] theorem comp_a {P P' P'' : SBPC.{u}} (f : P ⟶ P') (g : P' ⟶ P'') :
    Hom.a (f ≫ g) = Hom.a f ≫ Hom.a g := rfl

@[simp] theorem comp_b {P P' P'' : SBPC.{u}} (f : P ⟶ P') (g : P' ⟶ P'') :
    Hom.b (f ≫ g) = Hom.b f ≫ Hom.b g := rfl

/-- The underlying proper covering `F : Y → X` of `(A, F)`. -/
def toPC (P : SBPC.{u}) : PC.{u} :=
  ⟨SEP.toEP.obj P.W, SEP.toEP.obj P.V, P.A.ϕ, P.isProper.isProperCovering⟩

/-- The base face of a cube commutes on objects: `Φ ∘ F = F' ∘ Ψ`. -/
theorem comm_obj {P P' : SBPC.{u}} (f : P ⟶ P') (y : P.W.Obj) :
    (Hom.b f).ϕ.obj (P.A.ϕ.obj y) = P'.A.ϕ.obj ((Hom.a f).ϕ.obj y) :=
  congrArg (fun h : P.W ⟶ P'.V => h.ϕ.obj y) (Hom.comm f)

/-- The base face of a cube commutes on morphisms. -/
theorem comm_mor {P P' : SBPC.{u}} (f : P ⟶ P') (ψ : P.W.Mor) :
    (Hom.b f).ϕ.mor (P.A.ϕ.mor ψ) = P'.A.ϕ.mor ((Hom.a f).ϕ.mor ψ) :=
  congrArg (fun h : P.W ⟶ P'.V => h.ϕ.mor ψ) (Hom.comm f)

/-- The top face of a cube commutes on the total spaces: `b(A(w)) = A'(a(w))`. -/
theorem comm_total {P P' : SBPC.{u}} (f : P ⟶ P') (w : P.W.W) :
    (Hom.b f).Φ.obj (P.A.Φ.obj w) = P'.A.Φ.obj ((Hom.a f).Φ.obj w) :=
  congrArg (fun h : P.W ⟶ P'.V => h.Φ.obj w) (Hom.comm f)

/-- The base face of a cube, a morphism of `PC`. -/
def baseHom {P P' : SBPC.{u}} (f : P ⟶ P') : P.toPC ⟶ P'.toPC :=
  (⟨(Hom.a f).ϕ, (Hom.b f).ϕ, comm_obj f, comm_mor f⟩ : ProperCoveringHom P.A.ϕ P'.A.ϕ)

/-- **The forgetful functor `SBPC → PC`**, `(A, F) ↦ F`. -/
def forget : SBPC.{u} ⥤ PC.{u} where
  obj := toPC
  map := baseHom
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem forget_map_Ψ {P P' : SBPC.{u}} (f : P ⟶ P') :
    ProperCoveringHom.Ψ (forget.map f) = (Hom.a f).ϕ := rfl

@[simp] theorem forget_map_Φ {P P' : SBPC.{u}} (f : P ⟶ P') :
    ProperCoveringHom.Φ (forget.map f) = (Hom.b f).ϕ := rfl

/-- The functor `SBPC → SEP`, `(A, F) ↦ (P : W → Y)`. -/
def sourceSEP : SBPC.{u} ⥤ SEP.{u} where
  obj P := P.W
  map f := Hom.a f

/-- The functor `SBPC → SEP`, `(A, F) ↦ (Q : V → X)`. -/
def targetSEP : SBPC.{u} ⥤ SEP.{u} where
  obj P := P.V
  map f := Hom.b f

/-- **The class `E_SBPC` of equivalences** (2021 Remark 11.6.9, p. 566; not defined in the text):
both `SEP` components are strong bundle equivalences (Definition 10.4.11) and the base face lies
in `E_PC` (Definition 11.6.4 (2)). -/
def equivalences : MorphismProperty SBPC.{u} := fun _ _ f =>
  SEP.equivalences (Hom.a f) ∧ SEP.equivalences (Hom.b f) ∧ PC.equivalences (forget.map f)

instance : equivalences.{u}.IsMultiplicative where
  id_mem P := ⟨MorphismProperty.id_mem _ P.W, MorphismProperty.id_mem _ P.V, by
    rw [forget.map_id]; exact MorphismProperty.id_mem _ _⟩
  comp_mem f g hf hg := ⟨MorphismProperty.comp_mem _ _ _ hf.1 hg.1,
    MorphismProperty.comp_mem _ _ _ hf.2.1 hg.2.1, by
      rw [forget.map_comp]; exact MorphismProperty.comp_mem _ _ _ hf.2.2 hg.2.2⟩

/-- `forget` maps `E_SBPC` into `E_PC`. -/
theorem forget_map_mem {P P' : SBPC.{u}} {f : P ⟶ P'} (hf : equivalences f) :
    PC.equivalences (forget.map f) :=
  hf.2.2

/-- **The localization `SBPC[E⁻¹_SBPC]`** (2021 Remark 11.6.9, p. 566). -/
abbrev Loc : Type (u + 1) := equivalences.{u}.Localization

/-- The localization functor `SBPC → SBPC[E⁻¹_SBPC]`. -/
abbrev Q : SBPC.{u} ⥤ Loc.{u} := equivalences.{u}.Q

/-- `Q` is a localization functor for `E_SBPC`. -/
instance isLocalization_Q : Q.{u}.IsLocalization equivalences.{u} := by
  unfold Q; infer_instance

/-- `Q` inverts `E_SBPC`. -/
theorem isIso_Q_map {P P' : SBPC.{u}} (f : P ⟶ P') (hf : equivalences f) : IsIso (Q.map f) :=
  Localization.inverts Q equivalences f hf

variable {D : Type*} [Category D]

/-- **Universal property, existence**: a functor inverting `E_SBPC` factors through `Q`. -/
def lift (G : SBPC.{u} ⥤ D) (hG : equivalences.{u}.IsInvertedBy G) : Loc.{u} ⥤ D :=
  Localization.Construction.lift G hG

theorem fac (G : SBPC.{u} ⥤ D) (hG : equivalences.{u}.IsInvertedBy G) : Q ⋙ lift G hG = G :=
  Localization.Construction.fac G hG

/-- **Universal property, uniqueness**. -/
theorem uniq (G₁ G₂ : Loc.{u} ⥤ D) (h : Q ⋙ G₁ = Q ⋙ G₂) : G₁ = G₂ :=
  Localization.Construction.uniq G₁ G₂ h

/-- `forget ⋙ I : SBPC → PC[E⁻¹_PC]` inverts `E_SBPC`. -/
theorem isInvertedBy_forget_I : equivalences.{u}.IsInvertedBy (forget ⋙ PCLoc.I) :=
  fun _ _ f hf => PCLoc.isIso_I_map (forget.map f) (forget_map_mem hf)

/-- **The forgetful functor on localizations** `SBPC[E⁻¹_SBPC] → PC[E⁻¹_PC]`. -/
def toPCLoc : Loc.{u} ⥤ PCLoc.{u} := lift (forget ⋙ PCLoc.I) isInvertedBy_forget_I

/-- The square `SBPC → PC → PC[E⁻¹_PC]` = `SBPC → SBPC[E⁻¹] → PC[E⁻¹_PC]` commutes. -/
theorem toPCLoc_fac : Q ⋙ toPCLoc.{u} = forget ⋙ PCLoc.I :=
  fac _ _

/-- `sourceSEP` maps `E_SBPC` into the class `F` of `SEP`. -/
theorem sourceSEP_map_mem {P P' : SBPC.{u}} {f : P ⟶ P'} (hf : equivalences f) :
    SEP.equivalences (sourceSEP.map f) :=
  hf.1

/-- `targetSEP` maps `E_SBPC` into the class `F` of `SEP`. -/
theorem targetSEP_map_mem {P P' : SBPC.{u}} {f : P ⟶ P'} (hf : equivalences f) :
    SEP.equivalences (targetSEP.map f) :=
  hf.2.1

open SBLocalization in
/-- **`(A, F) ↦ (P : W → Y)` on localizations**, `SBPC[E⁻¹_SBPC] → SEP(F⁻¹)`. -/
def toSEPLocW : Loc.{u} ⥤ SEPLoc.{u} :=
  lift (sourceSEP ⋙ SEPLoc.localizationFunctor)
    fun _ _ _ hf => SEPLoc.isInvertedBy_localizationFunctor _ (sourceSEP_map_mem hf)

open SBLocalization in
theorem toSEPLocW_fac : Q ⋙ toSEPLocW.{u} = sourceSEP ⋙ SEPLoc.localizationFunctor :=
  fac _ _

open SBLocalization in
/-- **`(A, F) ↦ (Q : V → X)` on localizations**, `SBPC[E⁻¹_SBPC] → SEP(F⁻¹)`. -/
def toSEPLocV : Loc.{u} ⥤ SEPLoc.{u} :=
  lift (targetSEP ⋙ SEPLoc.localizationFunctor)
    fun _ _ _ hf => SEPLoc.isInvertedBy_localizationFunctor _ (targetSEP_map_mem hf)

open SBLocalization in
theorem toSEPLocV_fac : Q ⋙ toSEPLocV.{u} = targetSEP ⋙ SEPLoc.localizationFunctor :=
  fac _ _

/-- **The identity covering** `(id, id)` of a strong bundle (Definition 8.5.9 holds by
`isProperStrongBundleCovering2021_id`): `SBPC` is not empty. -/
def ofSEP (S : SEP.{u}) : SBPC.{u} :=
  ⟨S, S, 𝟙 S, S.E.isProperStrongBundleCovering2021_id⟩

instance [Nonempty SEP.{u}] : Nonempty SBPC.{u} :=
  ⟨ofSEP (Classical.arbitrary _)⟩

/-- The identity cube lies in `E_SBPC`: the class is not empty. -/
theorem equivalences_id (P : SBPC.{u}) : equivalences (𝟙 P) :=
  MorphismProperty.id_mem _ P

end SBPC

end Polyfold

end
