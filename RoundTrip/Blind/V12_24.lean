import Polyfold
/-! Blind formalization of V12_24 (the text's Part II, §12.5, Theorem 12.5.3, p. 594 of the
Springer 2021 book; 2017: Theorem 12.11).

Text: for a tame ep-groupoid and an sc-Fredholm section functor, `σ : O_f → X_∞` is a local
homeomorphism with two-point fibres, the local sections `ô^(x)` are continuous, and for a
morphism `φ` the local `Φ̂` pushes continuous local sections to continuous local sections.

Choices:
- Setting as in `RoundTrip/Blind/V12_4.lean` (universe 0, `E : EpStrongBundle X B`, `μ = E.μ`,
  paracompactness of `𝐗 ₛ×_P W` as an instance hypothesis); `X` tame (`X.IsTame`); `f` an
  sc-Fredholm section functor (`E.IsScFredholmSectionFunctor f`, Definition 8.3.4 (3)).
- `O_f` (Definition 12.5.2): the pairs `(x, o)`, `x ∈ X_∞`, `o` an orientation of `DET(f, x)`,
  i.e. Part I's orientation space of `f` as a section of the object bundle: the project's
  `OrSpace f hf` (read with `#print`: `Σ x : X_∞, Or_x^f`, `Or_x^f = Orx f hf x` read in a chosen
  chart point), `σ = orProj` (`(x, o) ↦ x`).  `X_∞` is `X.PObj.SmoothLevel` (the smooth points
  with the topology induced from `X`).
- The topology of `O_f` is Part I's (2021 Theorem 6.6.17), applied to `W → X`: the project's
  `orTopology` of the local transport data `orLocalTransport` (read with `#print`: `𝒲` is open iff
  `{y ∈ U_∞ | (y, o_y) ∈ 𝒲}` is open for every section `o` over an open `U` which is carried
  along by the transport along sc-smooth paths in `U`).  The project builds `orLocalTransport`
  only under further hypotheses, which B therefore quantifies over (they are not in the quoted
  statement): `X.PObj.AdmitsBumpFunctions`, `B.IsScFredholmSectionTame f` (tame germ data; for
  tame `X` I expect it to follow from sc-Fredholm), `B.HasScPlusSectionsThrough` (sc⁺-sections
  through smooth fibre points; Lemma 5.3.3 of Part I under bump functions), and four families of
  paracompactness instances (true, as in `RoundTrip/Blind/V6_58.lean`).
- (1) local homeomorphism: `IsLocalHomeomorph σ`.  (2) two-point fibres: every fibre
  `σ⁻¹(x)` has exactly two elements (`Set.ncard = 2`).
- (3) "the local sections `ô^(x)`": the sections `y ↦ (y, o_y)` over `U_∞`, `U` open, obtained by
  transporting an orientation along sc-smooth paths in `U` (Part I's continuous orientations,
  `LocalTransport.IsContOn`).  I state: through every `(x, o)` there is such a section (they
  exist), and every such section is continuous `U_∞ → O_f` (`IsContLocSec`, which also records
  the trivial `σ ∘ ô = id`).
- (4) "for a morphism `φ` the local `Φ̂`": `φ` lies in a sheet `S` (`X.Sheet`, read with `#print`:
  an open set of morphisms on which `s` and `t` are sc-diffeomorphisms onto `S.srcSet`,
  `S.tgtSet`); `Φ = t ∘ (s|S)⁻¹ : S.srcSet → S.tgtSet` and `Φ̂(y, o) = (Φ(y), (ψ_y)_* o)` with
  `ψ_y ∈ S`, `s(ψ_y) = y`, where `ψ_*` is the project's `EpStrongBundle.orMor` (`φ_* : Or_x^f →
  Or_{x'}^f`, p. 593; trusted from its docstring, it needs `hsec` too).  "pushes continuous local
  sections to continuous local sections": for every sheet `S`, every open `V ⊆ S.srcSet` and
  every continuous section `τ` of `σ` over `V_∞`, the pushed section over
  `Φ(V)_∞ = t(S ∩ s⁻¹V)_∞`, characterized by `τ'(t ψ) = ψ_* τ(s ψ)` for `ψ ∈ S`, exists and is
  continuous (`∃ τ'` continuous with that relation; the relation determines `τ'`).
- B is the conjunction (1)–(4).  Nothing looks doubtful to me.
-/
namespace RoundTrip.V12_24
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × (Fin n → ℝ) × Obj)]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
  {f : Obj → W}

/-- Part I's topology on `O_f` (Theorem 6.6.17), for the object bundle `W → X`. -/
noncomputable abbrev topO (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions)
    (hfT : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough)
    (hf : B.IsScFredholmSection f) : TopologicalSpace (OrSpace f hf) :=
  orTopology (hf := hf) (orLocalTransport hX hbump hfT hsec)

/-- `τ` is a continuous section of `σ : O_f → X_∞` over `V_∞` (for a given topology on `O_f`). -/
def IsContLocSec (hf : B.IsScFredholmSection f) (t : TopologicalSpace (OrSpace f hf))
    (V : Set Obj) (τ : ↥(X.PObj.smoothVal ⁻¹' V) → OrSpace f hf) : Prop :=
  @Continuous _ _ _ t τ ∧ ∀ y, (τ y).1 = y.1

end

/-- **Theorem 12.5.3**: `σ : O_f → X_∞` is a local homeomorphism with two-point fibres, the
transport sections are continuous, and the maps `Φ̂` of morphisms carry continuous local
sections to continuous local sections. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × (Fin n → ℝ) × Obj)]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
    (hX : X.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (f : Obj → W)
    (hF : E.IsScFredholmSectionFunctor f) (hfT : B.IsScFredholmSectionTame f)
    (hsec : B.HasScPlusSectionsThrough),
    letI : TopologicalSpace (OrSpace f hF.2) := topO hX hbump hfT hsec hF.2
    -- (1) `σ` is a local homeomorphism
    IsLocalHomeomorph (orProj f hF.2) ∧
    -- (2) its fibres have two points
    (∀ x : X.PObj.SmoothLevel, (orProj f hF.2 ⁻¹' {x}).ncard = 2) ∧
    -- (3) the transport sections `ô^(x)` exist through every point and are continuous
    (∀ (x : Obj) (hx : x ∈ X.PObj.smoothSet) (ox : Orx f hF.2 x hx),
      ∃ (U : Set Obj) (o : (y : Obj) → (hy : y ∈ X.PObj.smoothSet) → Orx f hF.2 y hy),
        x ∈ U ∧ (orLocalTransport hX hbump hfT hsec).IsContOn U o ∧ o x hx = ox) ∧
    (∀ (U : Set Obj) (o : (y : Obj) → (hy : y ∈ X.PObj.smoothSet) → Orx f hF.2 y hy),
      (orLocalTransport hX hbump hfT hsec).IsContOn U o →
      IsContLocSec hF.2 inferInstance U (fun y => Sigma.mk y.1 (o y.1.1 y.1.2))) ∧
    -- (4) `Φ̂` of a sheet pushes continuous local sections to continuous local sections
    (∀ (S : X.Sheet) (V : Set Obj), IsOpen V → V ⊆ S.srcSet →
      ∀ τ : ↥(X.PObj.smoothVal ⁻¹' V) → OrSpace f hF.2, IsContLocSec hF.2 inferInstance V τ →
        ∃ τ' : ↥(X.PObj.smoothVal ⁻¹' (X.tgt '' (S.carrier ∩ X.src ⁻¹' V))) → OrSpace f hF.2,
          IsContLocSec hF.2 inferInstance _ τ' ∧
          ∀ ψ ∈ S.carrier, ∀ y y' (hx : X.src ψ = X.PObj.smoothVal (τ y).1)
            (hx' : X.tgt ψ = X.PObj.smoothVal (τ' y').1),
            E.orMor hF hsec ψ hx hx' (τ y).1.2 (τ' y').1.2 (τ y).2 = (τ' y').2)

end RoundTrip.V12_24
