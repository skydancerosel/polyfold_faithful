import Polyfold.Chapter16.TangentPolyfold
import Polyfold.Chapter10.EquivalenceReduced
import Polyfold.Chapter8.EpFormsFunctor
import Polyfold.Chapter7.SmoothRegularAssembly
import Polyfold.Chapter7.ZhouLevels

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.2, pp. 715 and 717:
the polyfolds `(Z, c)ⁱ` obtained by raising the index, and the tangent projection
`τ_Z : T(Z, c) → (Z, c)¹`.

# Raised polyfolds and the tangent projection

## The text, paraphrased

(p. 715) For a polyfold `(Z, c)` with structure `(X, β)`, `mI(z)` is the maximal level of a
representative of `z`, `Z_i = {z | mI(z) ≥ i}`, and `Z_i` carries a natural polyfold structure
`c_i`; `(Z, c)ⁱ := (Z_i, c_i)` is obtained by raising the index by `i`.  (p. 717) The tangent
space comes with the projection `τ_Z : T(Z, c) → (Z, c)¹`, `[[(z, (X, α), h)]] ↦ z`, and for
every `(X, α) ∈ c` the square `τ_Z ∘ Tα = α ∘ |τ_X|` commutes, `τ_X : TX → X¹`.

## What is formalized

* `Diagram.liftOne`, `EPLoc.liftOneHom`: the index raise `f¹ = [X¹ ←F¹ A¹ →Φ¹ Y¹]` of a
  generalized map (`liftOneHom_id`, `liftOneHom_comp`, `isGeneralizedIso_liftOneHom`), and
  `orbitIncl_orbitMap_liftOneHom`: `|f¹|` is `|f|` on `|X¹| ⊆ |X|` (no hypothesis: `|X¹| → |X|`
  is injective).
* `PolyfoldClass.RaisedSpace c` (`= |X₀¹|` for `(X₀, α₀) = c.out`, as `TangentSpace c` is
  `|TX₀|`), `raiseMap q hq : |X¹| → RaisedSpace c` (the map `α¹`, independent of the choice:
  `raiseMap_eq`, and `raiseMap_comp`, the analogue of (16.5)), `raiseStructure` (the polyfold
  structure `(X¹, α¹)`; `X¹` has (ZHOU) and paracompact orbit space), `raiseStructure_equiv`,
  **`PolyfoldClass.raise c`** (the class `c₁`) with `raise_eq` (every `(X¹, α¹)`, `(X, α) ∈ c`,
  is in it).
* `raiseIncl c : RaisedSpace c → Z`, injective and continuous, with `raiseIncl ∘ α¹ = α ∘ |X¹ → X|`
  and range `Z₁ = α(|X₁|)` for every `(X, α) ∈ c`: so `(Z, c)¹` is the set `Z₁` with the structure
  `c₁`.  `PolyfoldClass.raiseN c i` iterates: `(Z, c)ⁱ` (`raiseN_zero`, `raiseN_succ`).
* **`PolyfoldClass.tangentProj c : T(Z, c) → (Z, c)¹`** (`τ_Z`) and **`tangentProj_tangentMap`**:
  `τ_Z ∘ Tα = α¹ ∘ |τ_X|` for every `(X, α) ∈ c` (the commutative square on p. 717), from the
  naturality of `τ` for generalized maps (`orbitMap_tangentProj_tangentHom`).

## Reading

* `(Z, c)ⁱ` is read as a space with an injection into `Z` whose image is `Zᵢ`; its topology is the
  one of `|Xⁱ|`, finer than the subspace topology of `Zᵢ ⊆ Z` in general (as the text's
  "natural polyfold structure" requires).  `mI` itself is not introduced: `Zᵢ = α(|Xᵢ|)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Index raise of functors -/

namespace EpFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {W : EpGroupoid Obj'' Mor''}

theorem liftOne_comp (G : EpFunctor Y W) (F : EpFunctor X Y) :
    (G.comp F).liftOne = G.liftOne.comp F.liftOne :=
  EpFunctor.ext (funext fun _ => MPolyfold.level_ext rfl) (funext fun _ => MPolyfold.level_ext rfl)

theorem liftOne_id (X : EpGroupoid Obj Mor) : (EpFunctor.id X).liftOne = EpFunctor.id X.liftOne :=
  EpFunctor.ext (funext fun _ => MPolyfold.level_ext rfl) (funext fun _ => MPolyfold.level_ext rfl)

/-- `|F¹|` is `|F|` on `|X¹| ⊆ |X|`. -/
theorem orbitIncl_orbitMap_liftOne (F : EpFunctor X Y) (q : X.liftOne.OrbitSpace) :
    Y.orbitIncl (F.liftOne.orbitMap q) = F.orbitMap (X.orbitIncl q) := by
  induction q using Quotient.inductionOn with | h x => rfl

/-- **`τ` is natural**: `|τ_Y| ∘ |TF| = |F¹| ∘ |τ_X|` (`τ_X : TX → X¹`, Theorem 8.1.1). -/
theorem orbitMap_tangentProj_tangent (F : EpFunctor X Y) (q : X.tangentEpGroupoid.OrbitSpace) :
    Y.tangentProjFunctor.orbitMap (F.tangent.orbitMap q) =
      F.liftOne.orbitMap (X.tangentProjFunctor.orbitMap q) := by
  induction q using Quotient.inductionOn with | h v => ?_
  change Y.liftOne.π (Y.tangentProjFunctor.obj (F.tangent.obj v)) =
    Y.liftOne.π (F.liftOne.obj (X.tangentProjFunctor.obj v))
  congr 1
  exact MPolyfold.level_ext (MPolyfold.levelVal_tangentProj_tangentMap F.isScSmoothMap_obj v)

end EpFunctor

namespace EPLocalization

open WeakFibredProduct

namespace Diagram

variable {X Y Z : EP.{u}}

/-- **The raised diagram** `X¹ ←F¹ A¹ →Φ¹ Y¹` of `d : X ←F A →Φ Y` (Proposition 10.1.18). -/
def liftOne (d : Diagram X Y) : Diagram X.liftOne Y.liftOne :=
  ⟨d.A.liftOne, d.F.liftOne, d.isEquivalence_F.liftOne, d.Φ.liftOne⟩

theorem IsRefinement.liftOne {d d' : Diagram X Y} (h : d'.IsRefinement d) :
    d'.liftOne.IsRefinement d.liftOne := by
  obtain ⟨H, hH, ⟨σ⟩, ⟨τ⟩⟩ := h
  exact ⟨H.liftOne, hH.liftOne, ⟨σ.liftOne.castEq (EpFunctor.liftOne_comp _ _) rfl⟩,
    ⟨τ.liftOne.castEq (EpFunctor.liftOne_comp _ _) rfl⟩⟩

theorem Equiv.liftOne {d d' : Diagram X Y} (h : Equiv d d') : Equiv d.liftOne d'.liftOne := by
  obtain ⟨d'', h₁, h₂⟩ := h
  exact ⟨d''.liftOne, h₁.liftOne, h₂.liftOne⟩

theorem isRefinement_liftOne_id (X : EP.{u}) :
    (Diagram.id X).liftOne.IsRefinement (Diagram.id X.liftOne) := by
  refine ⟨EpFunctor.id _, EpFunctor.IsEquivalence.id _, .of_eq ?_, .of_eq ?_⟩ <;>
  · change EpFunctor.id _ = (EpFunctor.id X.X).liftOne
    rw [EpFunctor.liftOne_id]

/-- `(d ∘ e)¹` refines `d¹ ∘ e¹` (as `isRefinement_tangentAny_comp`). -/
theorem isRefinement_liftOne_comp (d : Diagram X Y) (e : Diagram Y Z) :
    (d.comp e).liftOne.IsRefinement (d.liftOne.comp e.liftOne) := by
  have h := d.admissible e
  have h' : Admissible d.Φ.liftOne e.F.liftOne :=
    .of_isEquivalence_right e.isEquivalence_F.liftOne
  let πA := projLeft d.Φ e.F (d.admissible e)
  let πB := projRight d.Φ e.F (d.admissible e)
  let τ : EpNatTrans (d.Φ.liftOne.comp πA.liftOne) (e.F.liftOne.comp πB.liftOne) :=
    (natTrans d.Φ e.F (d.admissible e)).liftOne.castEq (EpFunctor.liftOne_comp _ _)
      (EpFunctor.liftOne_comp _ _)
  let L := wfpLift πA.liftOne πB.liftOne τ h'
  have hL : L.IsEquivalence :=
    EpFunctor.IsEquivalence.of_comp_left
      (isEquivalence_projLeft e.isEquivalence_F.liftOne h')
      (by
        rw [projLeft_comp_wfpLift]
        exact (isEquivalence_projLeft e.isEquivalence_F h).liftOne)
  refine ⟨L, hL, .of_eq ?_, .of_eq ?_⟩
  · exact EpFunctor.ext (funext fun _ => MPolyfold.level_ext rfl)
      (funext fun _ => MPolyfold.level_ext rfl)
  · exact EpFunctor.ext (funext fun _ => MPolyfold.level_ext rfl)
      (funext fun _ => MPolyfold.level_ext rfl)

/-- `|d¹|` is `|d|` on `|X¹| ⊆ |X|`. -/
theorem orbitIncl_orbitMap_liftOne (d : Diagram X Y) (q : X.liftOne.X.OrbitSpace) :
    Y.X.orbitIncl (d.liftOne.orbitMap q) = d.orbitMap (X.X.orbitIncl q) := by
  obtain ⟨r, rfl⟩ := d.liftOne.isEquivalence_F.isHomeomorph_orbitMap.surjective q
  rw [orbitMap_orbitMap_F]
  calc Y.X.orbitIncl (d.liftOne.Φ.orbitMap r) = d.Φ.orbitMap (d.A.X.orbitIncl r) :=
        EpFunctor.orbitIncl_orbitMap_liftOne d.Φ r
    _ = d.orbitMap (d.F.orbitMap (d.A.X.orbitIncl r)) := (orbitMap_orbitMap_F d _).symm
    _ = d.orbitMap (X.X.orbitIncl (d.liftOne.F.orbitMap r)) :=
        congrArg d.orbitMap (EpFunctor.orbitIncl_orbitMap_liftOne d.F r).symm

/-- `|τ_Y| ∘ |Td| = |d¹| ∘ |τ_X|` for a diagram `d`. -/
theorem orbitMap_tangentProj_tangentAny (d : Diagram X Y) (q : X.tangentAny.X.OrbitSpace) :
    Y.X.tangentProjFunctor.orbitMap (d.tangentAny.orbitMap q) =
      d.liftOne.orbitMap (X.X.tangentProjFunctor.orbitMap q) := by
  obtain ⟨r, rfl⟩ := d.tangentAny.isEquivalence_F.isHomeomorph_orbitMap.surjective q
  rw [orbitMap_orbitMap_F]
  exact (EpFunctor.orbitMap_tangentProj_tangent d.Φ r).trans
    ((orbitMap_orbitMap_F d.liftOne (d.A.X.tangentProjFunctor.orbitMap r)).symm.trans
      (congrArg d.liftOne.orbitMap (EpFunctor.orbitMap_tangentProj_tangent d.F r).symm))

end Diagram

namespace EPLoc

variable {X Y Z : EP.{u}}

/-- **The index raise `f¹` of a generalized map** `f = [X ←F A →Φ Y]`. -/
def liftOneHom (f : of X ⟶ of Y) : of X.liftOne ⟶ of Y.liftOne :=
  Quotient.map Diagram.liftOne (fun _ _ h => Diagram.Equiv.liftOne h) f

@[simp] theorem liftOneHom_homMk (d : Diagram X Y) : liftOneHom (homMk d) = homMk d.liftOne :=
  rfl

theorem liftOneHom_id (X : EP.{u}) : liftOneHom (𝟙 (of X)) = 𝟙 (of X.liftOne) :=
  Quotient.sound (Diagram.isRefinement_liftOne_id X).equiv

theorem liftOneHom_comp (f : of X ⟶ of Y) (g : of Y ⟶ of Z) :
    liftOneHom (f ≫ g) = liftOneHom f ≫ liftOneHom g :=
  Quotient.inductionOn₂ (motive := fun (f : of X ⟶ of Y) (g : of Y ⟶ of Z) =>
    liftOneHom (f ≫ g) = liftOneHom f ≫ liftOneHom g) f g fun d e =>
      Quotient.sound (Diagram.isRefinement_liftOne_comp d e).equiv

/-- The raise of a generalized isomorphism is a generalized isomorphism. -/
theorem isGeneralizedIso_liftOneHom {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    IsGeneralizedIso (liftOneHom f) := by
  obtain ⟨g, hfg, hgf⟩ := hf
  exact ⟨liftOneHom g, by rw [← liftOneHom_comp, hfg, liftOneHom_id],
    by rw [← liftOneHom_comp, hgf, liftOneHom_id]⟩

/-- **`|f¹|` is `|f|` on `|X¹| ⊆ |X|`**: `|Y¹ → Y| ∘ |f¹| = |f| ∘ |X¹ → X|`. -/
theorem orbitIncl_orbitMap_liftOneHom (f : of X ⟶ of Y) :
    Y.X.orbitIncl ∘ orbitMap (liftOneHom f) = orbitMap f ∘ X.X.orbitIncl :=
  Quotient.inductionOn (motive := fun f : of X ⟶ of Y =>
    Y.X.orbitIncl ∘ orbitMap (liftOneHom f) = orbitMap f ∘ X.X.orbitIncl) f
    fun d => funext fun q => Diagram.orbitIncl_orbitMap_liftOne d q

/-- **`|f¹|` is determined by `|f|`** (`|Y¹| → |Y|` is injective). -/
theorem orbitMap_liftOneHom_eq {f f' : of X ⟶ of Y} (h : orbitMap f = orbitMap f') :
    orbitMap (liftOneHom f) = orbitMap (liftOneHom f') := by
  funext q
  apply Y.X.orbitIncl_injective
  exact (congrFun (orbitIncl_orbitMap_liftOneHom f) q).trans
    ((congrArg (fun g => g (X.X.orbitIncl q)) h).trans
      (congrFun (orbitIncl_orbitMap_liftOneHom f') q).symm)

/-- **The tangent projection is natural for generalized maps**: `|τ_Y| ∘ |Tf| = |f¹| ∘ |τ_X|`. -/
theorem orbitMap_tangentProj_tangentHom (f : of X ⟶ of Y) :
    Y.X.tangentProjFunctor.orbitMap ∘ orbitMap (tangentHom f) =
      orbitMap (liftOneHom f) ∘ X.X.tangentProjFunctor.orbitMap :=
  Quotient.inductionOn (motive := fun f : of X ⟶ of Y =>
    Y.X.tangentProjFunctor.orbitMap ∘ orbitMap (tangentHom f) =
      orbitMap (liftOneHom f) ∘ X.X.tangentProjFunctor.orbitMap) f
    fun d => funext fun q => Diagram.orbitMap_tangentProj_tangentAny d q

end EPLoc

end EPLocalization

open EPLocalization EPLocalization.EPLoc

namespace PolyfoldStructure

variable {Z : Type u} [TopologicalSpace Z]

/-- `X¹` has a paracompact orbit space (Proposition 7.5.3). -/
theorem liftOne_paracompact (p : PolyfoldStructure Z) : p.X.liftOne.X.HasParacompactOrbitSpace :=
  p.X.X.proposition_7_5_3 p.paracompact

/-- `X¹` satisfies (ZHOU) (Propositions 7.4.8, 7.4.9). -/
theorem liftOne_isZhou (p : PolyfoldStructure Z) : p.X.liftOne.X.IsZhou :=
  p.X.liftOne.X.proposition_7_4_8_unconditional.2
    (p.X.X.isZhou'_liftOne (p.X.X.proposition_7_4_8_unconditional.1 p.isZhou))

end PolyfoldStructure

namespace PolyfoldClass

variable {Z : Type u} [TopologicalSpace Z] {c : PolyfoldClass Z}

/-! ### The raised polyfold `(Z, c)¹` -/

/-- **The space of `(Z, c)¹`** (2021 p. 715), as `|X₀¹|` for `(X₀, α₀) = c.out`; it maps
injectively onto `Z₁ ⊆ Z` (`raiseIncl`). -/
def RaisedSpace (c : PolyfoldClass Z) : Type u := c.out.X.liftOne.X.OrbitSpace

instance raisedSpaceTopology (c : PolyfoldClass Z) : TopologicalSpace (RaisedSpace c) :=
  inferInstanceAs (TopologicalSpace c.out.X.liftOne.X.OrbitSpace)

/-- **`α¹ : |X¹| → (Z, c)¹`** for `(X, α) ∈ c`: `|𝔣¹|` for a generalized isomorphism
`𝔣 : X → X₀` with `α₀ ∘ |𝔣| = α`. -/
def raiseMap (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    q.X.liftOne.X.OrbitSpace → RaisedSpace c :=
  orbitMap (liftOneHom (ScForm.exists_iso hq (Quotient.out_eq c)).choose)

/-- `α¹ = |𝔣¹|` for every `𝔣 : X → X₀` with `α₀ ∘ |𝔣| = α`. -/
theorem raiseMap_eq (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c)
    {𝔣 : EPLoc.of q.X ⟶ EPLoc.of c.out.X} (hβ : ⇑q.β = ⇑c.out.β ∘ orbitMap 𝔣) :
    raiseMap q hq = orbitMap (liftOneHom 𝔣) := by
  have h := (ScForm.exists_iso hq (Quotient.out_eq c)).choose_spec
  exact orbitMap_liftOneHom_eq ((PolyfoldStructure.orbitMap_eq_of_equiv h.2).trans
    (PolyfoldStructure.orbitMap_eq_of_equiv hβ).symm)

/-- **The analogue of (16.5)**: `β¹ ∘ |h¹| = α¹` for every generalized isomorphism `h : X → Y`
with `β ∘ |h| = α`. -/
theorem raiseMap_comp {p q : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hq : (⟦q⟧ : PolyfoldClass Z) = c) {h : EPLoc.of p.X ⟶ EPLoc.of q.X}
    (hβ : ⇑p.β = ⇑q.β ∘ orbitMap h) :
    raiseMap q hq ∘ orbitMap (liftOneHom h) = raiseMap p hp := by
  obtain ⟨𝔣, -, hβ𝔣⟩ := ScForm.exists_iso hq (Quotient.out_eq c)
  rw [raiseMap_eq q hq hβ𝔣, raiseMap_eq p hp (𝔣 := h ≫ 𝔣)
      (by rw [hβ, hβ𝔣, proposition_10_3_11]; rfl),
    liftOneHom_comp, proposition_10_3_11]
  rfl

/-- `α¹` is a homeomorphism. -/
theorem isHomeomorph_raiseMap (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    IsHomeomorph (raiseMap q hq) :=
  isHomeomorph_orbitMap_of_isGeneralizedIso
    (isGeneralizedIso_liftOneHom (ScForm.exists_iso hq (Quotient.out_eq c)).choose_spec.1)

/-- `α¹` as a homeomorphism `|X¹| ≃ₜ (Z, c)¹`. -/
def raiseHomeomorph (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    q.X.liftOne.X.OrbitSpace ≃ₜ RaisedSpace c :=
  (isHomeomorph_raiseMap q hq).homeomorph

@[simp] theorem raiseHomeomorph_apply (q : PolyfoldStructure Z)
    (hq : (⟦q⟧ : PolyfoldClass Z) = c) (v : q.X.liftOne.X.OrbitSpace) :
    raiseHomeomorph q hq v = raiseMap q hq v :=
  rfl

/-- **The polyfold structure `(X¹, α¹)` on `(Z, c)¹`** (2021 p. 715). -/
def raiseStructure (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    PolyfoldStructure (RaisedSpace c) where
  X := q.X.liftOne
  paracompact := q.liftOne_paracompact
  isZhou := q.liftOne_isZhou
  β := raiseHomeomorph q hq

/-- `(X¹, α¹)` and `(Y¹, β¹)` are equivalent, via `h¹`. -/
theorem raiseStructure_equiv {p q : PolyfoldStructure Z} (hp : (⟦p⟧ : PolyfoldClass Z) = c)
    (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    PolyfoldStructure.Equiv (raiseStructure p hp) (raiseStructure q hq) := by
  obtain ⟨h, hh, hβ⟩ := ScForm.exists_iso hp hq
  exact ⟨liftOneHom h, isGeneralizedIso_liftOneHom hh, (raiseMap_comp hp hq hβ).symm⟩

/-- **The structure `c₁` of `(Z, c)¹`** (2021 p. 715): the class of the `(X¹, α¹)`. -/
def raise (c : PolyfoldClass Z) : PolyfoldClass (RaisedSpace c) :=
  ⟦raiseStructure c.out (Quotient.out_eq c)⟧

/-- `c₁` is well defined: `(X¹, α¹) ∈ c₁` for every `(X, α) ∈ c`. -/
theorem raise_eq (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    (⟦raiseStructure q hq⟧ : PolyfoldClass (RaisedSpace c)) = c.raise :=
  Quotient.sound (raiseStructure_equiv hq (Quotient.out_eq c))

/-- **`(Z, c)¹ → Z`**, `|x|₁ ↦ α₀(|x|)`. -/
def raiseIncl (c : PolyfoldClass Z) : RaisedSpace c → Z :=
  c.out.β ∘ c.out.X.X.orbitIncl

theorem raiseIncl_injective (c : PolyfoldClass Z) : Injective (raiseIncl c) :=
  c.out.β.injective.comp c.out.X.X.orbitIncl_injective

theorem continuous_raiseIncl (c : PolyfoldClass Z) : Continuous (raiseIncl c) :=
  c.out.β.continuous.comp c.out.X.X.continuous_orbitIncl

/-- `raiseIncl ∘ α¹ = α ∘ |X¹ → X|` for every `(X, α) ∈ c`. -/
theorem raiseIncl_raiseMap (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    raiseIncl c ∘ raiseMap q hq = q.β ∘ q.X.X.orbitIncl := by
  obtain ⟨𝔣, -, hβ⟩ := ScForm.exists_iso hq (Quotient.out_eq c)
  rw [raiseMap_eq q hq hβ]
  funext v
  exact (congrArg c.out.β (congrFun (orbitIncl_orbitMap_liftOneHom 𝔣) v)).trans
    (congrFun hβ _).symm

/-- **The image of `(Z, c)¹` in `Z` is `Z₁ = α(|X₁|)`**, for every `(X, α) ∈ c`. -/
theorem range_raiseIncl (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    range (raiseIncl c) = q.β '' q.X.X.orbitLevel 1 := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := (isHomeomorph_raiseMap q hq).surjective w
    refine ⟨q.X.X.orbitIncl v, by rw [← q.X.X.range_orbitIncl]; exact mem_range_self v, ?_⟩
    exact (congrFun (raiseIncl_raiseMap q hq) v).symm
  · rintro ⟨o, ho, rfl⟩
    rw [← q.X.X.range_orbitIncl] at ho
    obtain ⟨v, rfl⟩ := ho
    exact ⟨raiseMap q hq v, congrFun (raiseIncl_raiseMap q hq) v⟩

/-! ### `(Z, c)ⁱ` -/

/-- A polyfold: a space with a topology and a polyfold class. -/
structure PolyfoldPair : Type (u + 1) where
  /-- The space. -/
  W : Type u
  [top : TopologicalSpace W]
  /-- The class. -/
  c : PolyfoldClass W

attribute [instance] PolyfoldPair.top

/-- One index raise of a polyfold. -/
def PolyfoldPair.raise (P : PolyfoldPair.{u}) : PolyfoldPair.{u} := ⟨RaisedSpace P.c, P.c.raise⟩

/-- **`(Z, c)ⁱ`** (2021 p. 715), obtained by raising the index `i` times. -/
def raiseN (c : PolyfoldClass Z) (i : ℕ) : PolyfoldPair.{u} :=
  PolyfoldPair.raise^[i] ⟨Z, c⟩

theorem raiseN_zero (c : PolyfoldClass Z) : raiseN c 0 = ⟨Z, c⟩ := rfl

theorem raiseN_succ (c : PolyfoldClass Z) (i : ℕ) :
    raiseN c (i + 1) = (raiseN c i).raise :=
  Function.iterate_succ_apply' _ _ _

/-! ### The tangent projection `τ_Z` -/

/-- **`τ_Z : T(Z, c) → (Z, c)¹`** (2021 p. 717), `|τ_{X₀}| : |TX₀| → |X₀¹|`. -/
def tangentProj (c : PolyfoldClass Z) : TangentSpace c → RaisedSpace c :=
  c.out.X.X.tangentProjFunctor.orbitMap

theorem continuous_tangentProj (c : PolyfoldClass Z) : Continuous (tangentProj c) :=
  c.out.X.X.tangentProjFunctor.continuous_orbitMap

/-- **The square on p. 717**: `τ_Z ∘ Tα = α¹ ∘ |τ_X|` for every `(X, α) ∈ c`. -/
theorem tangentProj_tangentMap (q : PolyfoldStructure Z) (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    tangentProj c ∘ tangentMap q hq = raiseMap q hq ∘ q.X.X.tangentProjFunctor.orbitMap := by
  obtain ⟨𝔣, h𝔣, hβ⟩ := ScForm.exists_iso hq (Quotient.out_eq c)
  rw [tangentMap_eq q hq h𝔣 hβ, raiseMap_eq q hq hβ]
  exact orbitMap_tangentProj_tangentHom 𝔣

/-- `raiseIncl ∘ τ_Z ∘ Tα = α ∘ |X¹ → X| ∘ |τ_X|`: `τ_Z [[(z, (X, α), h)]] = z`. -/
theorem raiseIncl_tangentProj_tangentMap (q : PolyfoldStructure Z)
    (hq : (⟦q⟧ : PolyfoldClass Z) = c) :
    raiseIncl c ∘ tangentProj c ∘ tangentMap q hq =
      q.β ∘ q.X.X.orbitIncl ∘ q.X.X.tangentProjFunctor.orbitMap := by
  funext v
  exact (congrArg (raiseIncl c) (congrFun (tangentProj_tangentMap q hq) v)).trans
    (congrFun (raiseIncl_raiseMap q hq) _)

/-- Witness: the raised polyfold of `[ℤ/3 ⋉ ℝ]` (the construction is not vacuous). -/
example : PolyfoldClass (RaisedSpace PolyfoldStructure.z3Polyfold) :=
  PolyfoldStructure.z3Polyfold.raise

end PolyfoldClass

end Polyfold
