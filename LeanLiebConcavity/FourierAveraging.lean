/-
Copyright (c) 2026 Keyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keyu Zhao
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Algebra.Star.Unitary

/-!
# Fourier averaging for matrix algebras

Given a primitive `m`-th root of unity `ζ : ℂ` (with `m ≠ 0`), we define the
Fourier diagonal matrices

  `FourierMatrix ζ A k : Matrix (Fin m) (Fin m) A`,  `k : Fin m`,

with entry `i` equal to `(ζ^(k·i) : ℂ) • (1 : A)`, and prove the averaging formula

  `(1/m) • ∑ k : Fin m, star(FourierMatrix ζ A k) * M * FourierMatrix ζ A k = diagonal(diag M)`.

i.e. extracts the diagonal of any `M : Matrix (Fin m) (Fin m) A`.
-/

@[expose] public section

open Complex

/-! ### The Fourier diagonal matrix -/

/-- The `k`-th Fourier diagonal matrix over `Fin m`:
the entry at index `i : Fin m` is `(ζ^(k·i) : ℂ) • (1 : A)`. -/
noncomputable def FourierMatrix (ζ : ℂ) (A : Type*) [Ring A] [Algebra ℂ A]
    {m : ℕ} (k : Fin m) : Matrix (Fin m) (Fin m) A :=
  Matrix.diagonal fun i => (ζ ^ (k.val * i.val) : ℂ) • (1 : A)

variable {ζ : ℂ} {m : ℕ}

section Scalar

variable {n : ℕ}

@[simp]
lemma ζ_normSq_pow (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0) :
    normSq (ζ ^ n) = 1 := by
  rw [map_pow, normSq_eq_norm_sq, hζ.norm'_eq_one hm, one_pow, one_pow]

@[simp]
lemma ζ_star_mul (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0) :
    star (ζ ^ n) * ζ ^ n = 1 := by
  rw [star_def, ← normSq_eq_conj_mul_self]
  exact_mod_cast ζ_normSq_pow hζ hm

@[simp]
lemma ζ_mul_star (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0) :
    ζ ^ n * star (ζ ^ n) = 1 := by
  simpa only [mul_comm] using ζ_star_mul hζ hm

@[simp]
lemma ζ_ne_zero (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0) : ζ ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [hζ.norm'_eq_one hm]; norm_num)

@[simp]
lemma ζ_star_eq_zpow (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0) :
    starRingEnd ℂ (ζ ^ n) = ζ ^ (-(n : ℤ)) := by
  have hconj : starRingEnd ℂ ζ = ζ⁻¹ := by
    rw [inv_def, normSq_eq_norm_sq, hζ.norm'_eq_one hm, one_pow, inv_one]
    push_cast; ring
  rw [map_pow, hconj, zpow_neg, zpow_natCast, inv_pow]

end Scalar

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

lemma smul_conj_mul (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0)
    {a b : ℕ} {x : A} :
    star (ζ ^ a • 1) * x * (ζ ^ b • 1) = (ζ ^ ((b : ℤ) - (a : ℤ))) • x := by
  simp only [star_smul, star_one]
  rw [show star (ζ ^ a) = starRingEnd ℂ (ζ ^ a) from rfl,
      ζ_star_eq_zpow hζ hm, smul_one_mul, mul_smul_one, smul_smul]
  congr 1
  rw [← zpow_natCast ζ b, ← zpow_add₀ (ζ_ne_zero hζ hm)]; ring_nf

/-! ### Unitarity of `FourierMatrix` -/

section Unitary

variable {k : Fin m}

/-- `FourierMatrix ζ A k` belongs to the unitary subgroup of `Matrix (Fin m) (Fin m) A`. -/
theorem FourierMatrix_mem_unitary
    (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0) :
    FourierMatrix ζ A k ∈ unitary (Matrix (Fin m) (Fin m) A) := by
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩
  all_goals
    rw [FourierMatrix, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i
    simp_rw [Pi.star_def, star_smul, smul_mul_smul_comm]
    try rw [ζ_star_mul hζ hm]
    try rw [ζ_mul_star hζ hm]
    rw [one_smul, star_one, mul_one]

end Unitary

/-! ### Discrete Fourier orthogonality and Averaging formulas -/

section Fourier

lemma Fin_dvd_iff {i j : Fin m} :
    (m : ℤ) ∣ (j.val - i.val) ↔ i = j := by
  constructor
  · intro hdvd
    have : (j.val : ℤ) - i.val = 0 := by
      refine abs_eq_zero.mp
        <| Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg _) ?_ ((dvd_abs _ _).mpr hdvd)
      rw [abs_lt]; omega
    exact Fin.ext (by exact_mod_cast (sub_eq_zero.mp this).symm)
  · rintro rfl; simp

/-- DFT orthogonality: `∑ k : Fin m, ζ^(k·d) = m` if `m ∣ d`, else `0`. -/
theorem geom_sum_primitive_root (hζ : IsPrimitiveRoot ζ m) (d : ℤ) :
    ∑ k : Fin m, ζ ^ (k.val * d) = if (m : ℤ) ∣ d then (m : ℂ) else 0 := by
  simp_rw [show ∀ k : Fin m, ζ ^ (k.val * d) = (ζ ^ d) ^ (k.val : ℤ) from
              fun k => by rw [← zpow_mul, mul_comm]]
  rw [Fin.sum_univ_eq_sum_range (fun i => (ζ ^ d) ^ (i : ℤ)) m]
  split_ifs with hdvd
  · simp [(hζ.zpow_eq_one_iff_dvd d).mpr (by exact_mod_cast hdvd)]
  · rw [Finset.sum_congr rfl (fun i _ => zpow_natCast _ i)]
    apply eq_zero_of_ne_zero_of_mul_right_eq_zero
    · exact sub_ne_zero.mpr <| fun h => hdvd <| (hζ.zpow_eq_one_iff_dvd d).mp h
    · rw [geom_sum_mul, ← zpow_natCast, ← zpow_mul,
          mul_comm, zpow_mul, hζ.zpow_eq_one, one_zpow, sub_self]

/-- Entry formula: conjugating `M` by `FourierMatrix ζ A k` scales entry `(i, j)` by
`ζ^(k · (j − i))`. -/
lemma FourierMatrix_conj_apply (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0)
    (M : Matrix (Fin m) (Fin m) A) {i j k : Fin m} :
    (star (FourierMatrix ζ A k) * M * FourierMatrix ζ A k) i j =
      ζ ^ (k.val * ((j.val : ℤ) - i.val)) • M i j := by
  simp only [FourierMatrix, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring_nf
  exact smul_conj_mul hζ hm

/-- Fourier sum: diagonal entry is `(m : ℂ) • M i i`, off-diagonal entry is `0`. -/
theorem FourierAvg_apply (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0)
    (M : Matrix (Fin m) (Fin m) A) {i j : Fin m} :
    ∑ k : Fin m, (star (FourierMatrix ζ A k) * M * FourierMatrix ζ A k) i j =
      if i = j then (m : ℂ) • M i j else (0 : A) := by
  simp_rw [FourierMatrix_conj_apply hζ hm, ← Finset.sum_smul,
    geom_sum_primitive_root hζ, Fin_dvd_iff]
  split <;> simp

/-- **Fourier averaging**: `(1/m) • ∑ k, star(FourierMatrix k) * M * FourierMatrix k =
diagonal(diag M)`. -/
theorem FourierAvg_eq_diagonal (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 0)
    (M : Matrix (Fin m) (Fin m) A) :
    ∑ k : Fin m, (1 / (m : ℝ)) • (star (FourierMatrix ζ A k) * M * FourierMatrix ζ A k)
      = Matrix.diagonal M.diag := by
  let Mconj := fun k => star (FourierMatrix ζ A k) * M * FourierMatrix ζ A k
  simp only [Mconj, show ∀ k, (1 / (m : ℝ)) • Mconj k = (1 / (m : ℂ)) • Mconj k from
                      fun _ => (by ext i j; simp [← coe_smul])]
  ext i j
  simp_rw [Matrix.sum_apply, Matrix.smul_apply,
    Finset.smul_sum.symm, FourierAvg_apply hζ hm, Matrix.diagonal_apply, Matrix.diag]
  split_ifs with hij
  · subst hij
    rw [← mul_smul, one_div, inv_mul_cancel₀ (by exact_mod_cast hm), one_smul]
  · simp

end Fourier
