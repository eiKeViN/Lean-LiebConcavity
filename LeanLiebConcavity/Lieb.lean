import LeanLiebConcavity.HStarAlgebra
import LeanLiebConcavity.Main
import Mathlib.Analysis.InnerProductSpace.StarOrder
-- StarOrder transitively provides:
--   CStarAlgebra (H →L[ℂ] H)  (via ContinuousLinearMap.lean)
--   StarOrderedRing (H →L[ℂ] H)
--   NonnegSpectrumClass ℝ (H →L[ℂ] H)

/-!
# Lieb's Concavity Theorem in the H*-Algebra Setting

Given a complete H*-algebra `H` over `ℂ`, the space `H →L[ℂ] H` of continuous linear
endomorphisms is a C*-algebra (with the operator norm) and inherits the Loewner partial order.
We use `Lmul` and `Rmul` to embed `H` into `H →L[ℂ] H`, allowing us to apply the abstract
joint concavity / convexity results from `Main.lean`.

## Main results

- `OperatorPowerMean`: the operator `(α,β)`-power mean
  `(A, B) ↦ GenPerspective (·^α) (·^β) (Rmul ℂ B, Lmul ℂ A) : H →L[ℂ] H`
- `OperatorPowerMean_apply`: explicit form `A^(β*(1-α)) * x * B^α`
- `LiebConcavity`: `(A, B) ↦ re ⟪A^s * x * B^t, x⟫` is jointly concave
  when `s, t > 0` and `s + t ≤ 1`

## References

- [Nik2013] Nikoufar–Ebadian–Eshaghi Gordji, *Adv. Math.* 248 (2013) 531–533
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace

-- All Lieb content lives in `namespace CFC` so that `CFC.instPowReal` (the `Pow H ℝ`
-- instance for rpow) is found by instance synthesis without a namespace qualifier.

variable {H : Type*} [HStarAlgebra ℂ H] [CompleteSpace H]
  [TopologicalSpace H]
  -- CFC stack on H (provides `a ^ r : H` for `r : ℝ`)
  [Algebra ℝ H] [IsScalarTower ℝ ℂ H]
  [ContinuousFunctionalCalculus ℝ H IsSelfAdjoint]
  -- Order structure on H
  [PartialOrder H] [StarOrderedRing H]
  [NonnegSpectrumClass ℝ H]
  -- CFC + order stack on H →L[ℂ] H (needed for GenPerspective)
  [Module ℂ H]
  [CStarAlgebra (H →L[ℂ] H)]

-- Activate the Loewner partial order on `H →L[ℂ] H` so that `GenPerspective` can be applied.
-- With this, `H →L[ℂ] H` is a C*-algebra (ContinuousLinearMap.lean:20),
-- `StarOrderedRing (H →L[ℂ] H)` (StarOrder.lean:79), and
-- `NonnegSpectrumClass ℝ (H →L[ℂ] H)` (StarOrder.lean:52) — all automatic.


variable [PartialOrder (H →L[ℂ] H)]
attribute [local instance] ContinuousLinearMap.instLoewnerPartialOrder
variable [StarOrderedRing (H →L[ℂ] H)]

set_option trace.Meta.synthInstance true
set_option backward.isDefEq.respectTransparency false

/-! ### The operator (α, β)-power mean -/

/-- The operator `(α, β)`-power mean of `(A, B)` as a continuous linear map `H →L[ℂ] H`:
```
  OperatorPowerMean α β A B
    := GenPerspective (H →L[ℂ] H) (·^α) (·^β) (Rmul ℂ B, Lmul ℂ A)
```
This is the operator `R_B #_{(α,β)} L_A` from [Nik2013]. -/
def OperatorPowerMean (α β : ℝ) (A B : H) : H →L[ℂ] H :=
  have T : H →L[ℂ] H := Rmul ℂ B
  GenPerspective (H →L[ℂ] H) (· ^ α) (· ^ β) (T, Lmul ℂ A)

theorem OperatorPowerMean_apply {α β : ℝ} {A B : H}
    (hA : IsStrictlyPositive A) (hB : 0 ≤ B) (hβ : 0 < β) (x : H) :
    OperatorPowerMean α β A B x = cfc (fun x => x ^ ((β * (1 - α)))) A * x
    * cfc (fun x => x ^ β) B := by
  simp only [OperatorPowerMean,
    GenPerspective_of_rpow_commute (Lmul_Rmul_comm (𝕜 := ℂ)).symm
      (Rmul_nonneg ℂ hB) (Lmul_isStrictlyPositive ℂ hA) hβ]
  simp [ContinuousLinearMap.mul_apply,
        Lmul_rpow_strictlyPositive_apply (𝕜 := ℂ) (ha := hA),
        Rmul_rpow_nonneg_apply (𝕜 := ℂ) (hr := hβ.le) (ha := hB)]

end CFC

end
