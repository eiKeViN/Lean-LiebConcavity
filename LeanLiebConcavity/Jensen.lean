import LeanLiebConcavity.Defs
import LeanLiebConcavity.ConjugateWeightedSum
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.RingTheory.RootsOfUnity.Complex

noncomputable section




universe u
variable {A : Type u} [CStarAlgebra A]
variable {f : ℝ → ℝ} {I : Set ℝ}

/-! ## Sub-goal 2: The unitary `u` -/
open scoped Matrix

namespace CStarMatrix
/-- The Li–Wu unitary matrix in `CStarMatrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A`.
Constructed from `b : Fin n → A` with `∑ star (b i) * b i = 1`. -/
private def liWuUnitary {n : ℕ} (b : Fin n → A) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A :=
  Matrix.fromBlocks
    (Matrix.of fun i j => if i = j then 1 - b i * star (b j) else -(b i * star (b j)))
    (Matrix.of fun i _ => b i)
    (Matrix.of fun _ j => -(star (b j)))
    (Matrix.of fun _ _ => (0 : A))

private lemma liWuUnitary_star {n : ℕ} (b : Fin n → A) :
    star (liWuUnitary b) = Matrix.fromBlocks
      (Matrix.of fun i j => if i = j then 1 - b i * star (b j) else -(b i * star (b j)))
      (Matrix.of fun i _ => -(b i))
      (Matrix.of fun _ j => star (b j))
      (Matrix.of fun _ _ => (0 : A)) := by
    let X := Matrix.of fun i j => if i = j then 1 - b i * star (b j) else -(b i * star (b j))
    let Y := Matrix.of fun i (_ : Unit) => b i
    let Z := Matrix.of fun (_ : Unit) j => -(star (b j))
    let W := Matrix.of fun (_ _ : Unit) => (0 : A)
    have hX : Xᴴ
        = (Matrix.of fun i j => if i = j then 1 - b i * star (b j) else -(b i * star (b j))) := by
      ext i j
      simp only [X, Matrix.conjTranspose_apply, Matrix.of_apply,
        apply_ite, ite_eq_left_iff, ite_eq_right_iff,
        star_sub, star_one, star_mul, star_star, star_neg, sub_eq_neg_self]
      split_ifs with h_eq <;> grind only
    have hZ : Zᴴ
        = (Matrix.of fun i _ => -(b i)) := by
      ext i j
      simp only [Z, Matrix.conjTranspose_apply, Matrix.of_apply, star_neg, star_star]
    have hY : Yᴴ
        = (Matrix.of fun _ j => star (b j)) := by
      ext i j
      simp only [Y, Matrix.conjTranspose_apply, Matrix.of_apply]
    have hW : Wᴴ
        = (Matrix.of fun _ _ => (0 : A)) := by
      ext i j
      simp only [W, Matrix.conjTranspose_apply, Matrix.of_apply, star_zero]
    simpa only [hX, hZ, hY, hW] using Matrix.fromBlocks_conjTranspose X Y Z W


/-- `star u * u = 1` for the Li–Wu unitary, using `∑ star (b i) * b i = 1`. -/
private lemma liWuUnitary_star_mul_self' {n : ℕ} {b : Fin n → A}
    (hb : ∑ i, star (b i) * b i = 1) :
    star (liWuUnitary b) * liWuUnitary b = 1 := by
  rw [liWuUnitary_star, liWuUnitary, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  -- After fromBlocks_multiply, goal is: fromBlocks TL TR BL BR = fromBlocks 1 0 0 1
  refine ⟨?_tl, ?_tr, ?_bl, ?_br⟩
  · -- Top-left: (δ - P) * (δ - P) + P = δ,  where P_{ij} = b i * star (b j)
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
      neg_mul, mul_neg, neg_neg, Matrix.one_apply]
    have : ∀ k : Fin n,
        (if i = k then 1 - b i * star (b k) else -(b i * star (b k)))
        * (if k = j then 1 - b k * star (b j) else -(b k * star (b j)))
        = (if i = k then if k = j then 1 else 0 else 0)
          - (if i = k then b k * star (b j) else 0)
          - (if k = j then b i * star (b k) else 0)
          + b i * (star (b k) * b k) * star (b j) := by
      intro _
      split_ifs with _ _ <;> simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
      · abel
      · simp only [mul_neg]; abel
      · simp only [neg_mul, mul_assoc]; abel
      · simp only [neg_mul, mul_assoc]; noncomm_ring
    open Finset in
    simp only [this, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, hb,
              sum_ite_eq, sum_ite_eq', mem_univ, univ_unique, sum_const, card_singleton,
              if_true, sub_add_cancel, one_smul, mul_one]
  · -- Top-right: (δ - P) * Y + (-Y_col) * 0 = 0
    -- Goal: ∑ x, (if i = x then 1 - b i * star(b x) else -(b i * star(b x))) * b x = 0
    ext i (_ : Unit)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
      mul_zero, Finset.sum_const_zero, add_zero]
    have : ∀ x : Fin n,
        (if i = x then 1 - b i * star (b x) else -(b i * star (b x))) * b x
        = (if i = x then b x else 0) - b i * (star (b x) * b x) := by
      intro x; split_ifs with h
      · subst h; simp only [sub_mul, one_mul, mul_assoc]
      · simp only [neg_mul, mul_assoc, zero_sub]
    simp_rw [this, Finset.sum_sub_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum, hb, mul_one, sub_self, Matrix.zero_apply]
  · -- Bottom-left: Z' * (δ - P) + 0 * (-Z') = 0
    -- Goal: ∑ x, star(b x) * (if x = j then 1 - b x * star(b j) else -(b x * star(b j))) = 0
    ext (_ : Unit) j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
              zero_mul, Finset.sum_const_zero, add_zero]
    have : ∀ x : Fin n,
        star (b x) * (if x = j then 1 - b x * star (b j) else -(b x * star (b j)))
        = (if x = j then star (b x) else 0) - star (b x) * b x * star (b j) := by
      intro x; split_ifs with h
      · subst h; simp only [mul_sub, mul_one, mul_assoc]
      · simp only [mul_neg, mul_assoc, zero_sub]
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
             ← Finset.sum_mul, hb, one_mul, sub_self, Matrix.zero_apply]
  · -- Bottom-right: Z' * Y + 0 * 0 = 1
    ext (_ : Unit) (_ : Unit)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
              hb, Finset.univ_unique, mul_zero]
    simp only [Finset.sum_const_zero, add_zero, Matrix.one_apply_eq]

/-- `u * star u = 1` for the Li–Wu unitary, using `∑ star (b i) * b i = 1`. -/
private lemma liWuUnitary_mul_star_self' {n : ℕ} {b : Fin n → A}
    (hb : ∑ i, star (b i) * b i = 1) :
    liWuUnitary b * star (liWuUnitary b) = 1 := by
  rw [liWuUnitary_star, liWuUnitary, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨?_tl, ?_tr, ?_bl, ?_br⟩
  · -- Top-left: X*X + Y*(-Z') = δ,  same algebra as before
    -- X_{ij} = δ_{ij} - P_{ij},  Y_{i,*} = b i,  (-Z')_{*,j} = star(b j)
    -- (X*X)_{ij} = ∑_k X_{ik}*X_{kj}, (Y*(-Z'))_{ij} = b i * star(b j) = P_{ij}
    -- same as TL of star u * u
    ext i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    have : ∀ k : Fin n,
        (if i = k then 1 - b i * star (b k) else -(b i * star (b k)))
        * (if k = j then 1 - b k * star (b j) else -(b k * star (b j)))
        = (if i = k then if k = j then 1 else 0 else 0)
          - (if i = k then b k * star (b j) else 0)
          - (if k = j then b i * star (b k) else 0)
          + b i * (star (b k) * b k) * star (b j) := by
      intro _
      split_ifs with _ _ <;> simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
      · abel
      · simp only [mul_neg]; abel
      · simp only [neg_mul, mul_assoc]; abel
      · simp only [neg_mul, mul_assoc]; noncomm_ring
    open Finset in
    simp only [this, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, hb,
              sum_ite_eq, sum_ite_eq', mem_univ, univ_unique, sum_const, card_singleton,
              if_true, sub_add_cancel, one_smul, mul_one]
  · -- Top-right: X*(-Y) + Y*0 = 0
    -- Goal: ∑ x X_{ix} * (-b x) + b i * 0 = 0, i.e. -∑ x X_{ix} * b x = 0
    -- same sum as TR of star u * u (proved zero), negated
    ext i (_ : Unit)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
      mul_zero, Finset.sum_const_zero, add_zero]
    have : ∀ x : Fin n,
        (if i = x then 1 - b i * star (b x) else -(b i * star (b x))) * (-b x)
        = -(if i = x then b x else 0) + b i * (star (b x) * b x) := by
      intro _; split_ifs with h
      · subst h; simp only [mul_neg, sub_mul, one_mul, mul_assoc]; abel
      · simp only [mul_neg, neg_mul, mul_assoc]; abel
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.mul_sum, hb, mul_one, neg_add_cancel, Matrix.zero_apply]
  · -- Bottom-left: Z*X + 0*(-Z') = 0
    -- Goal: ∑ x (-star(b x)) * X_{xj} = 0, i.e. -∑ x star(b x) * X_{xj} = 0
    -- same sum as BL of star u * u (proved zero), negated
    ext (_ : Unit) j
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
      zero_mul, Finset.sum_const_zero, add_zero]
    have : ∀ x : Fin n,
        (-star (b x)) * (if x = j then 1 - b x * star (b j) else -(b x * star (b j)))
        = -(if x = j then star (b x) else 0) + star (b x) * b x * star (b j) := by
      intro _; split_ifs with h
      · subst h; simp only [neg_mul, mul_sub, mul_one, mul_assoc]; abel
      · simp only [neg_mul, mul_neg, mul_assoc]; abel
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true,
      ← Finset.sum_mul, hb, one_mul, neg_add_cancel, Matrix.zero_apply]
  · -- Bottom-right: Z*(-Y) + 0*0 = 1
    -- Goal: ∑ x (-star(b x)) * (-b x) = 1, i.e. ∑ x star(b x) * b x = 1
    ext (_ : Unit) (_ : Unit)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq,
              neg_mul, mul_neg, neg_neg, zero_mul, Finset.sum_const_zero, add_zero,]
    exact hb

/-- The Li–Wu diagonal matrix: `diag(a_1, ..., a_n, c)` as a block-diagonal matrix
over `Fin n ⊕ Unit`. The last entry `c` is arbitrary; it does not affect the BR corner. -/
private def liWuDiag {n : ℕ} (a : Fin n → A) (c : A) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A :=
  Matrix.diagonal (Sum.elim a (fun _ => c))

/-- The bottom-right `(Unit, Unit)` corner of `star u * diag(a, c) * u` equals
`∑ i, star (b i) * a i * b i`, regardless of the last diagonal entry `c`. -/
private lemma liWuUnitary_BR_corner {n : ℕ} {b : Fin n → A} (a : Fin n → A) (c : A) :
    (star (liWuUnitary b) * liWuDiag a c * liWuUnitary b) (Sum.inr ()) (Sum.inr ()) =
      ∑ i, star (b i) * a i * b i := by
  rw [liWuUnitary_star, liWuUnitary]
  simp only [Matrix.mul_apply, liWuDiag, Matrix.diagonal_apply, Fintype.sum_sum_type]
  -- evaluate fromBlocks entries
  simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
             Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  -- the Unit-indexed terms vanish (inr () entry of u's last col is 0)
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
             Finset.univ_unique, Sum.inl.injEq]
  congr 1; ext x
  simp_rw [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ## Sub-goal 3 (Fourier averaging): the `v k` Fourier matrices and their unitarity -/

open Complex

/-- The primitive `(n+1)`-th root of unity used in the Fourier averaging step.
Defined as `exp(2πi/(n+1))`, matching `Complex.isPrimitiveRoot_exp`. -/
private def liWuTheta (n : ℕ) : ℂ :=
  exp (2 * Real.pi * Complex.I / (n + 1 : ℂ))

private lemma liWuTheta_isPrimitiveRoot (n : ℕ) :
    IsPrimitiveRoot (liWuTheta n) (n + 1) := by
  have : liWuTheta n = exp (2 * ↑Real.pi * Complex.I / ↑(n + 1)) := by
    simp only [liWuTheta, Nat.cast_add, Nat.cast_one]
  simpa [this] using isPrimitiveRoot_exp (n + 1) (by omega)

/-- `‖θ^m‖ = 1` for the `(n+1)`-th root of unity `θ`. -/
private lemma liWuTheta_norm (n : ℕ) : ‖liWuTheta n‖ = 1 := by
  dsimp only [liWuTheta]
  have : exp (2 * ↑Real.pi * Complex.I / (↑n + 1)) =
      exp (↑(2 * Real.pi / (↑n + 1)) * Complex.I) := by
    push_cast; ring_nf
  rw [this, norm_exp_ofReal_mul_I]

private lemma liWuTheta_norm_pow (n m : ℕ) : ‖liWuTheta n ^ m‖ = 1 := by
  rw [norm_pow, liWuTheta_norm, one_pow]

/-- The `k`-th Fourier diagonal matrix over `Fin n ⊕ Unit`.
Entry at `inl j` is `θ^(k*j) • 1`, entry at `inr ()` is `θ^(k*n) • 1`. -/
private def liWuFourier {n : ℕ} (k : Fin (n + 1)) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A :=
  Matrix.diagonal fun i => match i with
    | Sum.inl j => (liWuTheta n ^ (k.val * j.val) : ℂ) • (1 : A)
    | Sum.inr () => (liWuTheta n ^ (k.val * n) : ℂ) • (1 : A)

/-- `normSq (θ^m) = 1`, since `‖θ‖ = 1`. -/
private lemma liWuTheta_normSq_pow (n m : ℕ) : normSq (liWuTheta n ^ m) = 1 := by
  rw [map_pow, normSq_eq_norm_sq, liWuTheta_norm, one_pow, one_pow]

/-- `star(θ^m) * θ^m = 1` in `ℂ`, since `|θ| = 1`. -/
private lemma liWuTheta_star_mul (n m : ℕ) :
    star (liWuTheta n ^ m) * liWuTheta n ^ m = 1 := by
  rw [Complex.star_def, ← normSq_eq_conj_mul_self]
  exact_mod_cast liWuTheta_normSq_pow n m

/-- `θ^m * star(θ^m) = 1` in `ℂ`, since `|θ| = 1`. -/
private lemma liWuTheta_mul_star (n m : ℕ) :
    liWuTheta n ^ m * star (liWuTheta n ^ m) = 1 := by
  simpa [mul_comm] using liWuTheta_star_mul n m

/-- `star(θ^m) = θ^{-m}` in `ℂ`: conjugation inverts on the unit circle. -/
private lemma liWuTheta_star_eq_zpow (n m : ℕ) :
    starRingEnd ℂ (liWuTheta n ^ m) = liWuTheta n ^ (-(m : ℤ)) := by
  have hconj : starRingEnd ℂ (liWuTheta n) = (liWuTheta n)⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, liWuTheta_norm, one_pow, inv_one]
    push_cast; ring
  rw [map_pow, hconj, zpow_neg, zpow_natCast, inv_pow]

/-- `liWuTheta n ≠ 0`, since `‖liWuTheta n‖ = 1`. -/
private lemma liWuTheta_ne_zero (n : ℕ) : liWuTheta n ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [liWuTheta_norm]; norm_num)

/-- Integer index of a `Fin n ⊕ Unit` element: `inl j ↦ j.val`, `inr () ↦ n`. -/
private def liWuIdx (n : ℕ) : Fin n ⊕ Unit → ℕ
  | Sum.inl j => j.val
  | Sum.inr () => n

/-- Key scalar identity: `star(θ^a • 1) * x * (θ^b • 1) = θ^(b-a) • x` in any C⋆-algebra. -/
private lemma liWuTheta_smul_conj_mul {n : ℕ} (a b : ℕ) (x : A) :
    star ((liWuTheta n ^ a : ℂ) • (1 : A)) * x * ((liWuTheta n ^ b : ℂ) • (1 : A)) =
      (liWuTheta n ^ ((b : ℤ) - (a : ℤ))) • x := by
  simp only [star_smul, star_one]
  rw [show star (liWuTheta n ^ a) = starRingEnd ℂ (liWuTheta n ^ a) from rfl,
      liWuTheta_star_eq_zpow, smul_one_mul, mul_smul_one, smul_smul]
  congr 1
  rw [← zpow_natCast (liWuTheta n) b, ← zpow_add₀ (liWuTheta_ne_zero n)]; ring_nf

/-- Entry formula: conjugating any matrix `M` by the `k`-th Fourier matrix scales entry `(i,j)`
by `θ^{k·(idx j - idx i)}`. -/
private lemma liWuFourier_conj_apply {n : ℕ} (k : Fin (n + 1))
    (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A) (i j : Fin n ⊕ Unit) :
    (star (liWuFourier (A := A) k) * M * liWuFourier (A := A) k) i j =
      (liWuTheta n ^ ((k.val * liWuIdx n j : ℤ) - (k.val * liWuIdx n i : ℤ))) • M i j := by
  simp only [liWuFourier, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_def]
  match i, j with
  | Sum.inl i, Sum.inl j => simp only [liWuIdx]; exact liWuTheta_smul_conj_mul _ _ _
  | Sum.inl i, Sum.inr () => simp only [liWuIdx]; exact liWuTheta_smul_conj_mul _ _ _
  | Sum.inr (), Sum.inl j => simp only [liWuIdx]; exact liWuTheta_smul_conj_mul _ _ _
  | Sum.inr (), Sum.inr () => simp only [liWuIdx]; exact liWuTheta_smul_conj_mul _ _ _

/-- `liWuFourier k` is unitary part 1: `star (v k) * v k = 1`. -/
private lemma liWuFourier_star_mul_self {n : ℕ} (k : Fin (n + 1)) :
    star (liWuFourier (A := A) k) * liWuFourier k = 1 := by
  dsimp only [liWuFourier]
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext i
  match i with
  | Sum.inl i =>
    simp only [Pi.star_def, star_smul, smul_mul_smul_comm]
    rw [liWuTheta_star_mul, one_smul, star_one, one_mul]
  | Sum.inr () =>
    simp only [Pi.star_def, star_smul, smul_mul_smul_comm]
    rw [liWuTheta_star_mul, one_smul, star_one, one_mul]

/-- `liWuFourier k` is unitary part 2: `v k * star (v k) = 1`. -/
private lemma liWuFourier_mul_star_self {n : ℕ} (k : Fin (n + 1)) :
    liWuFourier (A := A) k * star (liWuFourier k) = 1 := by
  dsimp only [liWuFourier]
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext i
  match i with
  | Sum.inl i =>
    simp only [Pi.star_def, star_smul, smul_mul_smul_comm]
    rw [liWuTheta_mul_star, one_smul, star_one, mul_one]
  | Sum.inr () =>
    simp only [Pi.star_def, star_smul, smul_mul_smul_comm]
    rw [liWuTheta_mul_star, one_smul, star_one, mul_one]

/-! ### Discrete Fourier orthogonality -/

/-- Discrete Fourier orthogonality: summing `θ^(k*d)` over `k : Fin (n+1)` gives `n+1` if
`(n+1) ∣ d`, and `0` otherwise. -/
private lemma liWuTheta_geom_sum (n : ℕ) (d : ℤ) :
    ∑ k : Fin (n + 1), liWuTheta n ^ (k.val * d) =
      if (n + 1 : ℤ) ∣ d then (n + 1 : ℂ) else 0 := by
  -- Rewrite each term as (θ^d)^k, then convert to a range sum
  have : ∀ k : Fin (n + 1), liWuTheta n ^ (k.val * d) = (liWuTheta n ^ d) ^ (k.val : ℤ) := by
    intro k
    rw [← zpow_mul, mul_comm]
  simp_rw [this]
  -- Convert Fin sum to range sum
  rw [show (∑ k : Fin (n + 1), (liWuTheta n ^ d) ^ (k.val : ℤ)) =
      ∑ i ∈ Finset.range (n + 1), (liWuTheta n ^ d) ^ (i : ℤ) from
    Fin.sum_univ_eq_sum_range (fun i => (liWuTheta n ^ d) ^ (i : ℤ)) (n + 1)]
  split_ifs with hdvd
  · -- Case: (n+1) ∣ d, so θ^d = 1
    have h1 : liWuTheta n ^ d = 1 := by
      rw [(liWuTheta_isPrimitiveRoot n).zpow_eq_one_iff_dvd]
      exact_mod_cast hdvd
    simp [h1]
  · -- Case: (n+1) ∤ d, so θ^d ≠ 1
    have hne : liWuTheta n ^ d ≠ 1 := by
      intro h
      exact hdvd ((liWuTheta_isPrimitiveRoot n).zpow_eq_one_iff_dvd d |>.mp h)
    -- (θ^d)^(n+1) = 1, because θ^(n+1) = 1
    have hpow1 : (liWuTheta n ^ d) ^ (n + 1) = 1 := by
      rw [← zpow_natCast (liWuTheta n ^ d), ← zpow_mul, mul_comm,
          zpow_mul, (liWuTheta_isPrimitiveRoot n).zpow_eq_one, one_zpow]
    -- Convert zpow to npow in the range sum
    have hrange : ∀ i ∈ Finset.range (n + 1), (liWuTheta n ^ d) ^ (i : ℤ) =
        (liWuTheta n ^ d) ^ i := fun i _ => zpow_natCast _ _
    rw [Finset.sum_congr rfl hrange]
    -- Use ∑ r^i * (r - 1) = r^(n+1) - 1 and cancel (θ^d - 1) ≠ 0
    apply eq_zero_of_ne_zero_of_mul_right_eq_zero <| sub_ne_zero.mpr hne
    rw [geom_sum_mul, hpow1, sub_self]

/-! ### Fourier averaging formula -/

/-- `liWuIdx` maps into `{0,...,n}`. -/
private lemma liWuIdx_le {n : ℕ} (x : Fin n ⊕ Unit) : liWuIdx n x ≤ n := by
  cases x with
  | inl x => simp only [liWuIdx]; omega
  | inr u => cases u; simp [liWuIdx]

/-- `liWuIdx` is injective. -/
private lemma liWuIdx_injective {n : ℕ} {x y : Fin n ⊕ Unit}
    (h : liWuIdx n x = liWuIdx n y) : x = y := by
  cases x with
  | inl x => cases y with
    | inl y => simp only [liWuIdx] at h; exact congrArg Sum.inl (Fin.ext h)
    | inr u => cases u; simp only [liWuIdx] at h; omega
  | inr u => cases u; cases y with
    | inl y => simp only [liWuIdx] at h; omega
    | inr u => cases u; rfl

/-- `(n+1) ∣ (idx j - idx i)` iff `i = j`, since both indices lie in `{0,...,n}`. -/
private lemma liWuIdx_dvd_iff {n : ℕ} (i j : Fin n ⊕ Unit) :
    (↑n + 1 : ℤ) ∣ ((liWuIdx n j : ℤ) - liWuIdx n i) ↔ i = j := by
  constructor
  · intro hdvd
    apply liWuIdx_injective
    have ha' : (liWuIdx n i : ℤ) ≤ n := by exact_mod_cast liWuIdx_le i
    have hb' : (liWuIdx n j : ℤ) ≤ n := by exact_mod_cast liWuIdx_le j
    have ha0 : (0 : ℤ) ≤ liWuIdx n i := Int.natCast_nonneg _
    have hb0 : (0 : ℤ) ≤ liWuIdx n j := Int.natCast_nonneg _
    have habs_lt : |(liWuIdx n j : ℤ) - liWuIdx n i| < ↑n + 1 := by
      rw [abs_lt]; constructor <;> linarith
    have hdiff0 : |(liWuIdx n j : ℤ) - liWuIdx n i| = 0 :=
      Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg _) habs_lt ((dvd_abs _ _).mpr hdvd)
    exact_mod_cast (by linarith [abs_eq_zero.mp hdiff0] : (liWuIdx n i : ℤ) = liWuIdx n j)
  · rintro rfl; simp

/-- Fourier averaging: summing the Fourier conjugates of `M` over all `k : Fin (n+1)` gives
`(n+1) • M i j` on the diagonal and `0` off it. -/
private lemma liWuFourier_avg_apply {n : ℕ}
    (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) A) (i j : Fin n ⊕ Unit) :
    ∑ k : Fin (n + 1), (star (liWuFourier (A := A) k) * M * liWuFourier (A := A) k) i j =
      if i = j then (↑(n + 1) : ℂ) • M i j else 0 := by
  -- Step 1: plug in the entry formula
  simp_rw [show ∀ k : Fin (n + 1),
      (star (liWuFourier (A := A) k) * M * liWuFourier (A := A) k) i j =
      (liWuTheta n ^ ((↑k.val * ↑(liWuIdx n j) : ℤ) - (↑k.val * ↑(liWuIdx n i) : ℤ))) • M i j
      from fun k => liWuFourier_conj_apply k M i j]
  -- Step 2: factor M i j out of the sum; rewrite exponents; apply orthogonality
  rw [← Finset.sum_smul]
  simp_rw [show ∀ k : Fin (n + 1),
      liWuTheta n ^ ((↑k.val * ↑(liWuIdx n j) : ℤ) - (↑k.val * ↑(liWuIdx n i) : ℤ)) =
      liWuTheta n ^ (↑k.val * ((liWuIdx n j : ℤ) - liWuIdx n i))
      from fun k => by congr 1; ring,
    liWuTheta_geom_sum, liWuIdx_dvd_iff]
  -- Step 3: reduce the remaining if-then-else
  split_ifs with hij
  · push_cast; rfl
  · simp

end CStarMatrix

variable [PartialOrder A] [StarOrderedRing A]
/-! ## General (arbitrary n) Jensen's Operator Inequality -/

/-- **Jensen's Operator Inequality** (Li–Wu 2012, Theorem 2.2, general n):

Let `A` be an ordered unital C⋆-algebra and `f : ℝ → ℝ` a continuous operator convex
function on a convex set `I`.
Suppose:
1. `a : Fin n → A` are self-adjoint with `spectrum ℝ (a i) ⊆ I`.
2. `b : Fin n → A` satisfy `∑ i, star (b i) * b i = 1`.

Then:
`cfc f (∑ i, star (b i) * a i * b i) ≤ ∑ i, star (b i) * cfc f (a i) * b i`.
-/
-- [thm:jensen_2012] Li-Wu 2012, Theorem 2.2 (general n)
theorem JensenOperator_convex_general
    {n : ℕ} {a b : Fin n → A}
    (hI : Convex ℝ I)
    (hf : ContinuousOn f I) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : ∀ i, IsSelfAdjoint (a i))
    (ha_spec : ∀ i, spectrum ℝ (a i) ⊆ I)
    (hb : ∑ i, star (b i) * b i = 1) :
    cfc f (∑ i, star (b i) * a i * b i) ≤
      ∑ i, star (b i) * cfc f (a i) * b i := by
  sorry

-- [thm:jensen_2012'] Li-Wu 2012, Corollary 2.4 (general n)
/-- **Jensen's Operator Inequality, sub-unital version** (Li–Wu 2012, Corollary 2.4):

Same as `JensenOperator_convex_general` but with the weaker hypothesis
`∑ i, star (b i) * b i ≤ 1` and extra conditions `0 ∈ I` and `f 0 ≤ 0`.

Proof idea: extend to `n+1` elements with `b_{n+1} = (1 - ∑ b*b)^{1/2}` and `a_{n+1} = 0`,
apply the `= 1` version, then drop the last term using `f 0 ≤ 0`. -/
theorem JensenOperator_convex_general'
    {n : ℕ} {a b : Fin n → A}
    (hI : Convex ℝ I ∧ 0 ∈ I)
    (hf : ContinuousOn f I ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : ∀ i, IsSelfAdjoint (a i))
    (ha_spec : ∀ i, spectrum ℝ (a i) ⊆ I)
    (hb : ∑ i, star (b i) * b i ≤ 1) :
    cfc f (∑ i, star (b i) * a i * b i) ≤
      ∑ i, star (b i) * cfc f (a i) * b i := by
  sorry

/-! ## n = 2 specializations -/

open Matrix
open Fin
variable {a₁ a₂ b₁ b₂ : A}

/-- Strong Jensen's Operator Inequality, n = 2 case.
Specialization of `JensenOperator_convex_general` to two summands. -/
theorem JensenOperator_convex
    (hI : Convex ℝ I)
    (hf : ContinuousOn f I) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ = 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ := by
  have := JensenOperator_convex_general hI hf hf_opconvex
    (a := ![a₁, a₂]) (b := ![b₁, b₂])
    (by intro i; fin_cases i <;> simp_all [cons_val_zero, cons_val_one])
    (by intro i; fin_cases i <;> simp_all [cons_val_zero, cons_val_one])
    (by simpa only [sum_univ_two] using hb)
  simpa only [sum_univ_two] using this

/-- Sub-unital Jensen's Operator Inequality, n = 2 case.
Specialization of `JensenOperator_convex_general'` to two summands. -/
theorem JensenOperator_convex'
    (hI : Convex ℝ I ∧ 0 ∈ I)
    (hf : ContinuousOn f I ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ := by
  have := JensenOperator_convex_general' hI hf hf_opconvex
    (a := ![a₁, a₂]) (b := ![b₁, b₂])
    (by intro i; fin_cases i <;> simp_all [cons_val_zero, cons_val_one])
    (by intro i; fin_cases i <;> simp_all [cons_val_zero, cons_val_one])
    (by simpa only [sum_univ_two] using hb)
  simpa only [sum_univ_two] using this

/-! ## Concave versions (derived by negation) -/

theorem JensenOperator_concave
    (hI : Convex ℝ I)
    (hf : ContinuousOn f I) (hf_opconcave : OperatorConcaveOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ = 1) :
    star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) := by
  have h := JensenOperator_convex hI hf.neg
    (operatorConcaveOn_neg_iff_convexOn.mp hf_opconcave) ha ha_spec hb
  simp only [cfc_neg, mul_neg, neg_mul, ← neg_add] at h
  exact neg_le_neg_iff.mp h


theorem JensenOperator_concave'
    (hI : Convex ℝ I ∧ 0 ∈ I)
    (hf : ContinuousOn f I ∧ f 0 ≥ 0) (hf_opconcave : OperatorConcaveOn.{u} I f)
    (ha : IsSelfAdjoint a₁ ∧ IsSelfAdjoint a₂)
    (ha_spec : spectrum ℝ a₁ ⊆ I ∧ spectrum ℝ a₂ ⊆ I)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) := by
  have h := JensenOperator_convex' hI
    ⟨hf.1.neg, neg_nonpos.mpr hf.2⟩
    (operatorConcaveOn_neg_iff_convexOn.mp hf_opconcave) ha ha_spec hb
  simp only [cfc_neg, mul_neg, neg_mul, ← neg_add] at h
  exact neg_le_neg_iff.mp h

open NNReal
open Set

/-- A version applies to nonnegative elements of the C* algebra,
which is useful for our application.
A positive element is always self-adjoint. -/
theorem JensenOperator_convex_nonneg
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≤ 0) (hf_opconvex : OperatorConvexOn.{u} (Ici 0) f)
    (ha : 0 ≤ a₁ ∧ 0 ≤ a₂)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
    cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) ≤
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ :=
  JensenOperator_convex'
    ⟨convex_Ici 0, Set.self_mem_Ici⟩
    hf hf_opconvex
    ⟨IsSelfAdjoint.of_nonneg ha.1, IsSelfAdjoint.of_nonneg ha.2⟩
    ⟨fun _ h => spectrum_nonneg_of_nonneg ha.1 h, fun _ h => spectrum_nonneg_of_nonneg ha.2 h⟩
    hb

theorem JensenOperator_concave_nonneg
    (hf : ContinuousOn f (Ici 0) ∧ f 0 ≥ 0) (hf_opconcave : OperatorConcaveOn.{u} (Ici 0) f)
    (ha : 0 ≤ a₁ ∧ 0 ≤ a₂)
    (hb : star b₁ * b₁ + star b₂ * b₂ ≤ 1) :
      star b₁ * cfc f a₁ * b₁ + star b₂ * cfc f a₂ * b₂ ≤
      cfc f (star b₁ * a₁ * b₁ + star b₂ * a₂ * b₂) :=
  JensenOperator_concave'
    ⟨convex_Ici 0, Set.self_mem_Ici⟩
    hf hf_opconcave
    ⟨IsSelfAdjoint.of_nonneg ha.1, IsSelfAdjoint.of_nonneg ha.2⟩
    ⟨fun _ h => spectrum_nonneg_of_nonneg ha.1 h, fun _ h => spectrum_nonneg_of_nonneg ha.2 h⟩
    hb
