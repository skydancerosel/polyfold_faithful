import Polyfold
/-! Blind formalization of V7_3 (the text's Part II, §7.1, Definition 7.3, pp. 226–227 of the
2017 book).

Text: an ep-groupoid is a groupoid `(X, 𝐗)` with M-polyfold structures on `X` and on `𝐗` such that
(1) (étale) `s, t : 𝐗 → X` are local sc-diffeomorphisms; (2) `u` and `ι` are sc-smooth;
(3) (properness) every `x ∈ X` has an open neighbourhood `V(x)` with `t : s⁻¹(cl_X(V(x))) → X`
proper; since `s` is a local sc-diffeomorphism, `𝐗 ₛ×ₜ 𝐗` is in a natural way an M-polyfold
(Lemma 2.8 in [38]), and (4) `m : 𝐗 ₛ×ₜ 𝐗 → 𝐗` is sc-smooth.  In particular all structure maps
`(s, t, m, u, ι)` are sc-smooth.

Choices:
- This item is a definition (plus a presupposition and an "in particular").  Setting: `Obj Mor :
  Type` (universe 0; the project's `EpGroupoid` has both in one universe `u`), each with a
  topology, Hausdorff and paracompact (required by the project's `MPolyfold`, Definition 2.13:
  `RoundTrip/Blind/V2_12.lean`); the groupoid is a project `GroupoidStr` (characterized as the
  text's groupoid in `RoundTrip/Blind/V7_1.lean`); `P : MPolyfold Obj`, `Q : MPolyfold Mor`.
- (1): the project's `MPolyfold.IsLocalScDiffeo` (checked with `#print`: every point has `U ∋ x`,
  `V`, `h` with `IsScDiffeoOn f h U V`, i.e. `f : U → V` sc-smooth with sc-smooth inverse
  `h : V → U`, `U`, `V` open; see `RoundTrip/Blind/V2_28.lean`).  (2): `MPolyfold.IsScSmoothMap`
  (Definition 2.14).
- (3): "proper" read in its usual meaning: continuous with compact preimages of compact sets
  (`IsProperB`); the domain `s⁻¹(cl V)` carries the subspace topology of `𝐗`.  (Equivalent to
  Mathlib's `IsProperMap` here, since `X` is metrizable, hence compactly generated Hausdorff.)
- (4): "the natural M-polyfold structure" of the fibred product `𝐗 ₛ×ₜ 𝐗 = {(φ, ψ) | s φ = t ψ}`
  (the project's `MPolyfold.fibredProduct src tgt`, checked) is read as its structure as a
  sub-M-polyfold of the product `𝐗 × 𝐗` (Lemma 2.8 of [38] = the book's fibred-product
  proposition: for `f` a local sc-diffeomorphism and `g` sc-smooth, `X ₓ×_g Y ⊆ X × Y` is a
  sub-M-polyfold).  I use the project's `MPolyfold.prod` (product charts) and
  `MPolyfold.subPolyfold` (the induced charts `φ|_{W ∩ A}` of Proposition 2.21) for these; both
  take paracompactness of the product resp. of the subset as instance arguments, which I
  existentially quantify (true, as M-polyfolds are metrizable).  The structure does not depend on
  the proof `hA` (proof irrelevance).  `m` is `(φ, ψ) ↦ comp φ ψ` on the subtype.
- The presupposition "since `s` is a local sc-diffeomorphism, `𝐗 ₛ×ₜ 𝐗` is an M-polyfold" is
  asserted as conjunct (c), under (1).
- B (a)/(b): the project's `EpGroupoid` (fields read with `#print`) is exactly a `GroupoidStr`
  with `P`, `Q` satisfying my (1)–(4); (d) "in particular": `s`, `t` are sc-smooth (`u`, `ι`, `m`
  are sc-smooth by (2), (4)).
- Nothing looks false to me.
-/
namespace RoundTrip.V7_3
open Polyfold

/-- A proper map: continuous, with compact preimages of compact sets. -/
def IsProperB {α β : Type} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) : Prop :=
  Continuous f ∧ ∀ K : Set β, IsCompact K → IsCompact (f ⁻¹' K)

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Definition 7.3 (4)**: `m(φ, ψ) = φ ∘ ψ` is sc-smooth on `𝐗 ₛ×ₜ 𝐗` with its natural
M-polyfold structure, that of a sub-M-polyfold of `𝐗 × 𝐗`. -/
def IsScSmoothMulB (G : GroupoidStr Obj Mor) (Q : MPolyfold Mor) : Prop :=
  ∃ (_ : ParacompactSpace (Mor × Mor))
    (hA : (Q.prod Q).IsSubMPolyfold (MPolyfold.fibredProduct G.src G.tgt))
    (_ : ParacompactSpace ↥(MPolyfold.fibredProduct G.src G.tgt)),
    ((Q.prod Q).subPolyfold hA).IsScSmoothMap Q (fun p => G.comp p.1.1 p.1.2)

/-- **Definition 7.3**: the groupoid `G` with the M-polyfold structures `P` on `X` and `Q` on `𝐗`
is an ep-groupoid. -/
def IsEpGroupoidB (G : GroupoidStr Obj Mor) (P : MPolyfold Obj) (Q : MPolyfold Mor) : Prop :=
  -- (1) étale
  Q.IsLocalScDiffeo P G.src ∧ Q.IsLocalScDiffeo P G.tgt ∧
  -- (2) `u`, `ι` sc-smooth
  P.IsScSmoothMap Q G.unit ∧ Q.IsScSmoothMap Q G.inv ∧
  -- (3) properness
  (∀ x : Obj, ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧
    IsProperB ((G.src ⁻¹' closure V).domRestrict G.tgt)) ∧
  -- (4) `m` sc-smooth on the fibred product
  IsScSmoothMulB G Q

end

/-- Definition 7.3: the project's ep-groupoids are exactly the text's; the fibred product is a
sub-M-polyfold of `𝐗 × 𝐗` when `s`, `t` are local sc-diffeomorphisms; all structure maps are
sc-smooth. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor],
    -- (a) every project ep-groupoid is an ep-groupoid in the text's sense
    (∀ X : EpGroupoid Obj Mor, IsEpGroupoidB X.toGroupoidStr X.PObj X.PMor) ∧
    -- (b) every ep-groupoid in the text's sense is a project ep-groupoid
    (∀ (G : GroupoidStr Obj Mor) (P : MPolyfold Obj) (Q : MPolyfold Mor),
      IsEpGroupoidB G P Q →
        ∃ X : EpGroupoid Obj Mor, X.toGroupoidStr = G ∧ X.PObj = P ∧ X.PMor = Q) ∧
    -- (c) presupposition of (4): the fibred product is in a natural way an M-polyfold
    (∀ (G : GroupoidStr Obj Mor) (P : MPolyfold Obj) (Q : MPolyfold Mor),
      Q.IsLocalScDiffeo P G.src → Q.IsLocalScDiffeo P G.tgt →
        ∃ _ : ParacompactSpace (Mor × Mor),
          (Q.prod Q).IsSubMPolyfold (MPolyfold.fibredProduct G.src G.tgt) ∧
          ParacompactSpace ↥(MPolyfold.fibredProduct G.src G.tgt)) ∧
    -- (d) in particular `s` and `t` are sc-smooth
    (∀ X : EpGroupoid Obj Mor,
      X.PMor.IsScSmoothMap X.PObj X.src ∧ X.PMor.IsScSmoothMap X.PObj X.tgt)

end RoundTrip.V7_3
