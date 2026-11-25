import Polyfold
/-! Blind formalization of V17_41 (the text's §17.2, Proposition 17.2.4, p. 769 of the Springer
2021 book; 2017: Proposition 17.1).

Text: `T_αC` is a Banachable space, `S_Ψ : T_αC → T_qO` a topological linear isomorphism with
`S_{Ψ'} ∘ S_Ψ⁻¹ = Tσ(q)`; for smooth `α` it is sc-Banachable.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure
  `S : C.PolyfoldConstruction`, and an object `α` of regularity `≥ 1` (`S.HasRegularity 1 α`,
  i.e. `α ∈ C_1`) with `F(α) ≠ ∅`: the objects at which the text defines tangent vectors
  (pp. 767–769).
- `T_αC` = the project's set of classes `[α, Ψ, h]` (`S.TangentSpaceAt α`, Definition 17.2.3),
  wrapped in my own type synonym `TC` so that no project instance on it is used; the linear and
  topological structure is existentially quantified in B.
- `S_Ψ` = the project's bijection `S.tangentChart Ψ hΨ x hx` (`[α, Ψ', h'] ↦ Tσ(h')`, p. 769),
  for every `Ψ ∈ F(α)` and the level-`1` point `q = x` with `Ψ(q) = α`; `T_qO` = the project's
  tangent fibre `Ψ.P.tangentFiber x` with its (Chapter 2) linear structure and topology.
- `Tσ(q)` = the project's `S.transTangentCLM` of `(q, 1_α, q') ∈ M(Ψ, Ψ')` (`S.unitTr`), the
  tangent at `q` of the local sc-diffeomorphism `σ = t ∘ (s|U)⁻¹`.
- "Banachable" = the project's `IsBanachable` (linearly homeomorphic to a Banach space).
  "`S_Ψ` a topological linear isomorphism": `S_Ψ` is the underlying map of a `≃L[ℝ]` for the
  structure on `T_αC`.  One structure must serve all `Ψ` simultaneously.
- "sc-Banachable" (for smooth `α`, `S.IsSmoothObj α`): my reading: there are an sc-Banach space
  `E` and a topological linear isomorphism `e : T_αC ≃ E₀` such that for every `Ψ ∈ F(α)`, `q`,
  and every chart `φ` of `O` around `q`, the map `Tφ ∘ S_Ψ ∘ e⁻¹ : E₀ → T_{φ(q)}O ⊆ F₀`
  (`F` the sc-Banach space of the chart's local model) is an sc-isomorphism onto the
  sc-subspace `T_{φ(q)}O` (defined myself as `IsScIsoOnto`: on every level `m` it restricts to a
  topological linear isomorphism `E_m ≃ T_{φ(q)}O ∩ F_m`).  This says the sc-structure of
  `T_qO` transported by `S_Ψ` does not depend on `Ψ`.
- B is the conjunction of these claims.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_41
open Polyfold

/-- `T_αC`, as a bare type. -/
def TC {C : GCT.{0}} (S : C.PolyfoldConstruction) (α : C.Obj) : Type 1 := S.TangentSpaceAt α

/-- `T : E₀ → F₀` is an sc-isomorphism of `E` onto the sc-subspace `A ⊆ F`: on every level `m`
it restricts to a topological linear isomorphism `E_m ≃ A ∩ F_m`. -/
def IsScIsoOnto (E F : ScBanach) (A : Submodule ℝ (F.lvl 0)) (T : E.lvl 0 → F.lvl 0) : Prop :=
  ∃ j : (m : ℕ) → E.lvl m ≃L[ℝ] ↥(F.levelSub A m),
    ∀ (m : ℕ) (y : E.lvl m), F.toBase m ((j m y : F.lvl m)) = T (E.toBase m y)

/-- Proposition 17.2.4: `T_αC` is Banachable, the charts `S_Ψ` are topological linear
isomorphisms with transition maps `Tσ(q)`, and `T_αC` is sc-Banachable for smooth `α`. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (α : C.Obj),
    S.HasRegularity 1 α → (S.F α).Nonempty →
    ∃ (_ : AddCommGroup (TC S α)) (_ : Module ℝ (TC S α)) (_ : TopologicalSpace (TC S α)),
      IsBanachable (TC S α) ∧
      (∀ (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
          (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α),
        ∃ L : TC S α ≃L[ℝ] ↑(Ψ.1.P.tangentFiber x), ⇑L = ⇑(S.tangentChart Ψ hΨ x hx)) ∧
      (∀ (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
          (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α)
          (Ψ' : S.Unif) (hΨ' : Ψ'.1 ∈ S.F α) (x' : Ψ'.1.P.Level 1)
          (hx' : Ψ'.1.obj (Ψ'.1.P.levelVal 1 x') = α) (v : ↑(Ψ.1.P.tangentFiber x)),
        S.tangentChart Ψ' hΨ' x' hx' ((S.tangentChart Ψ hΨ x hx).symm v) =
          S.transTangentCLM (S.unitTr (Ψ.1.P.levelVal 1 x) (Ψ'.1.P.levelVal 1 x') hx hx')
            rfl rfl v) ∧
      (S.IsSmoothObj α →
        ∃ (E : ScBanach) (e : TC S α ≃L[ℝ] E.lvl 0),
          ∀ (Ψ : S.Unif) (hΨ : Ψ.1 ∈ S.F α) (x : Ψ.1.P.Level 1)
            (hx : Ψ.1.obj (Ψ.1.P.levelVal 1 x) = α) (φ : MChart Ψ.1.O) (hφ : Ψ.1.P.IsChart φ)
            (hq : Ψ.1.P.levelVal 1 x ∈ φ.source),
            IsScIsoOnto E φ.model.E (MPolyfold.tangentFiberModel hφ hq)
              (fun y => ((Ψ.1.P.tangentFiberContinuousLinearEquiv hφ hq
                (S.tangentChart Ψ hΨ x hx (e.symm y)) : _) : φ.model.E.lvl 0)))

end RoundTrip.V17_41
