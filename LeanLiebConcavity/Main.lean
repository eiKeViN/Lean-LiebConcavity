import LeanLiebConcavity.Jensen

/-- now need properties of Hermitian matrices -/
example : 1 = 1 := rfl

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f g : ℝ → ℝ)

theorem
