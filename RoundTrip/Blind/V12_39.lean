import Polyfold
/-! Blind formalization of V12_39 (the text's Part II, §12.5, Theorem 12.5.7, pp. 595–597 of the
Springer 2021 book; 2017: Theorem 12.12).

Text: strong bundles over tame ep-groupoids, a generalized strong bundle isomorphism `𝔣̄` over
`𝔣`, an sc-Fredholm section functor `f` of `W` and its push-forward `f'`.  (1) `𝔣̄` induces a
fibre-preserving homeomorphism `|O_f| → |O_{f'}|` over `|X_∞| → |X'_∞|`, functorially.  (2) A
continuous orientation section `o` of `σ` has a push-forward `𝔣̄_* o`, which is continuous.

Choices:
- Setting as in `RoundTrip/Blind/V10_67.lean`: strong bundles over ep-groupoids are bundled
  `A : SEP.{0}` (universe 0); generalized strong bundle maps are the project's `GenSBMap A A'`
  (classes of diagrams `W ← V → W'`), "generalized strong bundle isomorphism" is
  `GenSBMap.IsGeneralizedIso` (2021 Definition 10.5.2), the push-forward of section functors
  `GenSBMap.pushforward` (2021 p. 507), composition `GenSBMap.comp` (`F.comp G` is `G ∘ F`),
  the identity the class of `SDiagram.id`.  Base ep-groupoids tame (`A.X.IsTame`); `f` an
  sc-Fredholm section functor of `A`, `f' = 𝔣̄_* f`, and (as the claim needs `O_{f'}`) `f'` an
  sc-Fredholm section functor of `A'` (quantified, it is a property of `f'`).
- `O_f`, `σ`, `|O_f| = Quot (E.OrRel …)`, `|X_∞| = Quot X.SmoothRel`, `|σ| = E.orbitProj`, the
  topology of `O_f` (Part I's, `orTopology (orLocalTransport …)`) and the quotient topologies as
  in `RoundTrip/Blind/V12_24.lean`, `V12_26.lean`; for every bundle involved B quantifies over
  the extra hypotheses the project's topology needs (bump functions, `IsScFredholmSectionTame`,
  `HasScPlusSectionsThrough`, paracompactness instances).
- "the map `|O_f| → |O_{f'}|` induced by `𝔣̄`" and "`|X_∞| → |X'_∞|`": the project's
  `GenSBMap.orbitOrMap` and `GenSBMap.smoothOrbitMap` (docstrings: `|f̄|_*` computed with a
  representative `W ← V → W'` of strong bundle equivalences, `|(a, o)| ↦ |(ϕ(a), …)|`, the map of
  every representative; and `|f| : |X_∞| → |X'_∞|`).  I could not define the induced map on
  orientations independently (it needs the transfer of orientations along local strong bundle
  isomorphisms), so I trust these maps and state the properties the text claims for them:
  (1a) `orbitOrMap` is a homeomorphism; (1b) `|σ'| ∘ orbitOrMap = smoothOrbitMap ∘ |σ|`
  (fibre-preserving over `|X_∞| → |X'_∞|`); (1c) functoriality: the identity induces the
  identity, and `G ∘ F` induces the composite of the induced maps (for `G ∘ F` a generalized
  isomorphism and `f'' = G_* f' = (G ∘ F)_* f`, the latter equalities taken as hypotheses).
- (2) "continuous orientation section `o` of `σ`": an orientation of `f` as in V12_26
  (continuous section `X_∞ → O_f`, invariant under morphisms).  "has a push-forward `𝔣̄_* o`,
  which is continuous": there is an orientation `o'` of `f'` (continuous and invariant) with
  `|(a', o'_{a'})| = |𝔣̄|_* |(a, o_a)|` whenever `|𝔣|(|a|) = |a'|`; this relation determines `o'`
  (it is the push-forward), and its existence includes the continuity.
- B is the conjunction (1a)–(1c), (2).  Nothing looks doubtful to me.
-/
namespace RoundTrip.V12_39
open Polyfold Polyfold.SBLocalization

/-- The paracompactness instances the project's orientation topology needs, for a bundle `A`. -/
class ParaHyps (A : SEP.{0}) : Prop where
  h1 : ∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × A.Obj)
  h2 : ∀ n : ℕ, ParacompactSpace (pullbackSpace A.P (Prod.snd : (Fin n → ℝ) × A.Obj → A.Obj))
  h3 : ∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × (Fin n → ℝ) × A.Obj)
  h4 : ∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj A.P (Prod.snd : (Fin n → ℝ) × A.Obj → A.Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × A.Obj) → (Fin n → ℝ) × A.Obj))

attribute [instance] ParaHyps.h1 ParaHyps.h2 ParaHyps.h3 ParaHyps.h4

/-- The data needed for Part I's topology on `O_f` of a section functor `f` of `A`: tameness,
bump functions, tame Fredholm germs, sc⁺-sections through smooth fibre points. -/
structure TopData (A : SEP.{0}) (f : A.Obj → A.W) : Prop where
  tame : A.X.IsTame
  bump : A.X.PObj.AdmitsBumpFunctions
  fredT : A.B.IsScFredholmSectionTame f
  sec : A.B.HasScPlusSectionsThrough

/-- Part I's topology on `O_f` (Theorem 6.6.17), for the object bundle of `A`. -/
noncomputable abbrev topO {A : SEP.{0}} [ParaHyps A] {f : A.Obj → A.W} (D : TopData A f)
    (hf : A.B.IsScFredholmSection f) : TopologicalSpace (OrSpace f hf) :=
  orTopology (hf := hf) (orLocalTransport D.tame D.bump D.fredT D.sec)

/-- **An orientation of `f`** (Definition 12.5.4, as in V12_26) for a topology `t` on `O_f`. -/
def IsOrientationB {A : SEP.{0}} {f : A.Obj → A.W} (hF : A.E.IsScFredholmSectionFunctor f)
    (hsec : A.B.HasScPlusSectionsThrough) (t : TopologicalSpace (OrSpace f hF.2))
    (o : (x : A.Obj) → (hs : x ∈ A.X.PObj.smoothSet) → Orx f hF.2 x hs) : Prop :=
  @Continuous A.X.PObj.SmoothLevel (OrSpace f hF.2) _ t
      (fun y => (Sigma.mk y (o y.1 y.2) : OrSpace f hF.2)) ∧
    ∀ (φ : A.Mor) {x x' : A.Obj} (hx : A.X.src φ = x) (hx' : A.X.tgt φ = x')
      (hs : x ∈ A.X.PObj.smoothSet) (hs' : x' ∈ A.X.PObj.smoothSet),
      A.E.orMor hF hsec φ hx hx' hs hs' (o x hs) = o x' hs'

/-- The class `|(a, o_a)| ∈ |O_f|` of a smooth object `a` with the value of a section `o`. -/
def clsOr {A : SEP.{0}} {f : A.Obj → A.W} (hF : A.E.IsScFredholmSectionFunctor f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : (x : A.Obj) → (hs : x ∈ A.X.PObj.smoothSet) → Orx f hF.2 x hs)
    (a : A.Obj) (ha : a ∈ A.X.PObj.smoothSet) : Quot (A.E.OrRel hF hsec) :=
  Quot.mk _ (Sigma.mk (Subtype.mk a ha) (o a ha) : OrSpace f hF.2)

/-- The class `|a| ∈ |X_∞|` of a smooth object. -/
def clsX {A : SEP.{0}} (a : A.Obj) (ha : a ∈ A.X.PObj.smoothSet) : Quot A.X.SmoothRel :=
  Quot.mk _ (Subtype.mk a ha)

/-- **Theorem 12.5.7**: naturality of the orientation bundle under generalized strong bundle
isomorphisms. -/
def B : Prop :=
  -- (1a), (1b), (2) for one generalized strong bundle isomorphism
  (∀ (A A' : SEP.{0}) [ParaHyps A] [ParaHyps A'] (F : GenSBMap A A') (hFi : F.IsGeneralizedIso)
    (f : A.Obj → A.W) (hF : A.E.IsScFredholmSectionFunctor f) (D : TopData A f)
    (f' : A'.Obj → A'.W) (hF' : A'.E.IsScFredholmSectionFunctor f') (D' : TopData A' f')
    (hpush : f' = GenSBMap.pushforward hFi f),
    letI : TopologicalSpace (OrSpace f hF.2) := topO D hF.2
    letI : TopologicalSpace (OrSpace f' hF'.2) := topO D' hF'.2
    -- (1a) a homeomorphism
    IsHomeomorph (GenSBMap.orbitOrMap hFi hF hF' hpush D.sec D'.sec) ∧
    -- (1b) fibre-preserving over `|X_∞| → |X'_∞|`
    (∀ d, A'.E.orbitProj hF' D'.sec (GenSBMap.orbitOrMap hFi hF hF' hpush D.sec D'.sec d) =
      GenSBMap.smoothOrbitMap hFi (A.E.orbitProj hF D.sec d)) ∧
    -- (2) the push-forward of an orientation is a (continuous) orientation
    (∀ o : (x : A.Obj) → (hs : x ∈ A.X.PObj.smoothSet) → Orx f hF.2 x hs,
      IsOrientationB hF D.sec inferInstance o →
      ∃ o' : (x : A'.Obj) → (hs : x ∈ A'.X.PObj.smoothSet) → Orx f' hF'.2 x hs,
        IsOrientationB hF' D'.sec inferInstance o' ∧
        ∀ (a : A.Obj) (ha : a ∈ A.X.PObj.smoothSet) (a' : A'.Obj)
          (ha' : a' ∈ A'.X.PObj.smoothSet),
          GenSBMap.smoothOrbitMap hFi (clsX a ha) = clsX a' ha' →
          GenSBMap.orbitOrMap hFi hF hF' hpush D.sec D'.sec (clsOr hF D.sec o a ha) =
            clsOr hF' D'.sec o' a' ha')) ∧
  -- (1c) functoriality: the identity
  (∀ (A : SEP.{0}) (hid : (SDiagram.id A).cls.IsGeneralizedIso) (f : A.Obj → A.W)
    (hF : A.E.IsScFredholmSectionFunctor f) (hsec : A.B.HasScPlusSectionsThrough)
    (hpush : f = GenSBMap.pushforward hid f),
    GenSBMap.orbitOrMap hid hF hF hpush hsec hsec = id) ∧
  -- (1c) functoriality: composition
  (∀ (A A' A'' : SEP.{0}) (F : GenSBMap A A') (G : GenSBMap A' A'')
    (hFi : F.IsGeneralizedIso) (hGi : G.IsGeneralizedIso) (hGF : (F.comp G).IsGeneralizedIso)
    (f : A.Obj → A.W) (f' : A'.Obj → A'.W) (f'' : A''.Obj → A''.W)
    (hF : A.E.IsScFredholmSectionFunctor f) (hF' : A'.E.IsScFredholmSectionFunctor f')
    (hF'' : A''.E.IsScFredholmSectionFunctor f'')
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : A'.B.HasScPlusSectionsThrough)
    (hsec'' : A''.B.HasScPlusSectionsThrough)
    (h₁ : f' = GenSBMap.pushforward hFi f) (h₂ : f'' = GenSBMap.pushforward hGi f')
    (h₃ : f'' = GenSBMap.pushforward hGF f),
    GenSBMap.orbitOrMap hGF hF hF'' h₃ hsec hsec'' =
      GenSBMap.orbitOrMap hGi hF' hF'' h₂ hsec' hsec'' ∘
        GenSBMap.orbitOrMap hFi hF hF' h₁ hsec hsec')

end RoundTrip.V12_39
