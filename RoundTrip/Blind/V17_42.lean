import Polyfold
/-! Blind formalization of V17_42 (the text's §17.2, Proposition 17.2.5, p. 770, (17.32) of the
Springer 2021 book; 2017: Proposition 17.2).

Text: `α ↦ T_αC`, `φ ↦ Tφ` is a well-defined functor `C_1 → Ban`.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`.  Objects of `C_1` at which tangent spaces are formed: `α` with
  `S.TangentObj α` (`#print`ed: regularity `≥ 1` and `F(α) ≠ ∅`; the text forms `T_αC` from some
  `Ψ ∈ F(α)`, pp. 767–769); a morphism of `C_1` is a `φ : α → α'` between such objects.
- `T_αC` = the project's `S.TangentSpaceAt α` (Definition 17.2.3, the classes `[α, Ψ, h]`), and
  `S_Ψ : T_αC → T_qO` = the project's `S.tangentChart Ψ hΨ x hx` (p. 769) for `Ψ ∈ F(α)` and the
  level-`1` point `q = x` with `Ψ(q) = α`.  `Tσ(q)` for `(q, φ, q') ∈ M(Ψ, Ψ')` = the project's
  `S.transTangentCLM (S.morTr q φ q' …)` (the tangent at `q` of `σ = t ∘ (s|U)⁻¹`, a bounded
  operator `T_qO → T_{q'}O'`).
- `Tφ` ((17.31): `Tφ[α, Ψ, h] = [α', Ψ', Tσ(h)]`): existentially quantified as a family
  `T φ : T_αC → T_{α'}C` (indexed by `φ` and the proofs `s(φ) = α`, `t(φ) = α'`; junk where `α`
  or `α'` carries no tangent space), required to satisfy (17.31) read through the charts:
  `S_{Ψ'}(Tφ v) = Tσ(q)(S_Ψ v)` for EVERY `Ψ ∈ F(α)`, `q`, EVERY `Ψ' ∈ F(α')`, `q'`, and every
  `v`.  Since `S_Ψ([α, Ψ, h]) = h`, this is exactly "the formula (17.31) gives the same class
  for every representative `(α, Ψ, h)` and every choice of `Ψ'`" ("well-defined").  The project's
  `tangentMorAt`/`tangentMorCLE` are not used.
- "into `Ban`": the same identity shows that, in the charts `S_Ψ`, `S_{Ψ'}` (which define the
  Banachable structure of `T_αC`, Proposition 17.2.4), `Tφ` is the bounded linear operator
  `Tσ(q)`; so it is a morphism of `Ban`.  This needs no extra conjunct.
- "functor": `T(1_α) = id` and `T(ψ ∘ φ) = Tψ ∘ Tφ` for composable `φ : α → α'`,
  `ψ : α' → α''` (the project's `comp ψ φ` is `ψ ∘ φ`, `src ψ = tgt φ`).  The proofs
  `s(1_α) = α`, `s(ψ ∘ φ) = α`, … are universally quantified hypotheses (they hold).
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_42
open Polyfold

/-- Proposition 17.2.5: `Tφ` given by (17.31) is well defined (independent of representatives
and of the choice of `Ψ'`), is a bounded operator in the charts, and `α ↦ T_αC`, `φ ↦ Tφ` is a
functor. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction),
    ∃ T : ∀ {α α' : C.Obj} (φ : C.Mor), C.toGroupoidStr.src φ = α → C.toGroupoidStr.tgt φ = α' →
        S.TangentSpaceAt α → S.TangentSpaceAt α',
      -- (17.31), for every representative and every choice of `Ψ'`
      (∀ (α α' : C.Obj) (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
          (ht : C.toGroupoidStr.tgt φ = α'), S.TangentObj α → S.TangentObj α' →
        ∀ (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
          (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α)
          (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α') (x' : Ψ'.1.P.Level 1)
          (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α') (v : S.TangentSpaceAt α),
          S.tangentChart Ψ' hΨ' x' hx' (T φ hs ht v) =
            S.transTangentCLM
              (S.morTr (Ψ.1.P.levelVal 1 x) φ (Ψ'.1.P.levelVal 1 x') hx hs hx' ht) rfl rfl
              (S.tangentChart Ψ hΨ x hx v)) ∧
      -- `T(1_α) = id`
      (∀ (α : C.Obj), S.TangentObj α →
        ∀ (h₁ : C.toGroupoidStr.src (C.toGroupoidStr.unit α) = α)
          (h₂ : C.toGroupoidStr.tgt (C.toGroupoidStr.unit α) = α),
          T (C.toGroupoidStr.unit α) h₁ h₂ = id) ∧
      -- `T(ψ ∘ φ) = Tψ ∘ Tφ`
      (∀ (α α' α'' : C.Obj) (φ ψ : C.Mor), S.TangentObj α → S.TangentObj α' →
          S.TangentObj α'' →
        ∀ (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α')
          (hs' : C.toGroupoidStr.src ψ = α') (ht' : C.toGroupoidStr.tgt ψ = α'')
          (h₁ : C.toGroupoidStr.src (C.toGroupoidStr.comp ψ φ) = α)
          (h₂ : C.toGroupoidStr.tgt (C.toGroupoidStr.comp ψ φ) = α''),
          T (C.toGroupoidStr.comp ψ φ) h₁ h₂ = T ψ hs' ht' ∘ T φ hs ht)

end RoundTrip.V17_42
