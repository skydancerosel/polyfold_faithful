import Polyfold
/-! Blind formalization of V6_19 (the text's §6.3, Definition 6.16, p. 214). Choices:
- Setting: real Banach spaces `E F E' F' : Type` (universe 0); `T : E → F`, `S : E' → F'`
  bounded and Fredholm (Mathlib's `ContinuousLinearMap.IsFredholm`, which for Banach spaces is the
  text's notion: finite-dimensional kernel, closed range of finite codimension).
  `T ⊕ S` is `T.prodMap S : E × E' → F × F'`.
- B is the conjunction of (1) `T ⊕ S` is Fredholm, and (2) the existence of a linear isomorphism
  `Ψ : det(T) ⊗ det(S) ≅ det(T ⊕ S)` ("the natural isomorphism") given by the text's formula for
  EVERY choice of bases: for bases `a` of `ker T`, `d` of `coker T`, `a'` of `ker S`, `d'` of
  `coker S`, `Ψ((a₁∧…∧aₙ ⊗ (d₁∧…∧d_l)*) ⊗ (a'₁∧…∧a'ₙ' ⊗ (d'₁∧…∧d'_l')*))
  = (a₁∧…∧aₙ∧a'₁∧…∧a'ₙ') ⊗ (d₁∧…∧d_l∧d'₁∧…∧d'_l')*`, where in `ker(T ⊕ S)` the vectors are
  `(aᵢ, 0)`, `(0, a'ⱼ)` and in `coker(T ⊕ S)` the classes of `(dᵢ, 0)`, `(0, d'ⱼ)`.  The claim
  hidden in the definition is that this formula is independent of the bases (one `Ψ` for all).
- Bases are indexed by `Fin (dim)`.  The appended families have `dim ker T + dim ker S` and
  `dim coker T + dim coker S` members; the equalities of these numbers with `dim ker(T ⊕ S)`,
  `dim coker(T ⊕ S)` (true) are taken as hypotheses `hk`, `hc` (needed only to form the wedges).
- Project definitions used (checked with `#print`): `fredholmDet T = λ(ker T) ⊗ λ*(coker T)`
  (`coker T = F ⧸ range T`, `λ = maxPow` the top exterior power, `λ* = maxPowDual` its dual),
  `wedge v _ = v₁ ∧ … ∧ vₖ` (Mathlib's `ιMulti`), `dualVec v = v*` (the functional with
  `v*(v) = 1` on the line `λ`), `kerInl`/`kerInr` (`a ↦ (a,0)`, `a' ↦ (0,a')`),
  `cokerInl`/`cokerInr` (`[d] ↦ [(d,0)]`, `[d'] ↦ [(0,d')]`).
- Nothing looks false to me.
-/
namespace RoundTrip.V6_19
open Polyfold

/-- Definition 6.16: `T ⊕ S` is Fredholm and the natural isomorphism
`det(T) ⊗ det(S) → det(T ⊕ S)` is given by `(a ⊗ d*) ⊗ (a' ⊗ d'*) ↦ (a ∧ a') ⊗ (d ∧ d')*`. -/
def B : Prop :=
  ∀ {E F E' F' : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
    (T : E →L[ℝ] F) (S : E' →L[ℝ] F'), T.IsFredholm → S.IsFredholm →
    (T.prodMap S).IsFredholm ∧
    ∃ Ψ : TensorProduct ℝ (fredholmDet T) (fredholmDet S) ≃ₗ[ℝ] fredholmDet (T.prodMap S),
      ∀ (a : Module.Basis (Fin (Module.finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))) ℝ
              (LinearMap.ker (T : E →ₗ[ℝ] F)))
        (d : Module.Basis (Fin (Module.finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))) ℝ
              (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
        (a' : Module.Basis (Fin (Module.finrank ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F')))) ℝ
              (LinearMap.ker (S : E' →ₗ[ℝ] F')))
        (d' : Module.Basis (Fin (Module.finrank ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')))) ℝ
              (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F')))
        (hk : Module.finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F))
              + Module.finrank ℝ (LinearMap.ker (S : E' →ₗ[ℝ] F'))
            = Module.finrank ℝ
                (LinearMap.ker ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F')))
        (hc : Module.finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))
              + Module.finrank ℝ (F' ⧸ LinearMap.range (S : E' →ₗ[ℝ] F'))
            = Module.finrank ℝ ((F × F') ⧸
                LinearMap.range ((T.prodMap S : E × E' →L[ℝ] F × F') : E × E' →ₗ[ℝ] F × F'))),
        Ψ ((wedge (⇑a) rfl ⊗ₜ[ℝ] dualVec (wedge (⇑d) rfl)) ⊗ₜ[ℝ]
            (wedge (⇑a') rfl ⊗ₜ[ℝ] dualVec (wedge (⇑d') rfl)))
          = wedge (Fin.append (fun i => kerInl T S (a i)) (fun j => kerInr T S (a' j))) hk
              ⊗ₜ[ℝ] dualVec
                (wedge (Fin.append (fun i => cokerInl T S (d i)) (fun j => cokerInr T S (d' j))) hc)

end RoundTrip.V6_19
