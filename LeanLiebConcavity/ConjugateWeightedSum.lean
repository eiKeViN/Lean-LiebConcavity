module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

@[expose] public section

/-!
# Conjugate-weighted sums

Lemmas for sums of the form `∑ i, star (b i) * a i * b i` subject to
`∑ i, star (b i) * b i = 1` — the non-commutative analogue of a convex combination.

## Main result

- `spectrum_sum_conj_subset`: if each `a i` has spectrum in `I` (convex) and the
  `b i` satisfy the unit constraint, then `∑ star (b i) * a i * b i` also has spectrum in `I`.
  This is Sub-goal 1 of the Jensen proof.
-/

section Finset

variable {ι : Type*} {s : Set ℝ} {t : Finset ι} {f : ι → ℝ}

/-- The `inf'` of a finite family is a member of any set that contains all the family values,
since `inf'` is achieved at some member. -/
protected lemma Finset.inf'_mem_of_forall_mem (ht : t.Nonempty) (hf : ∀ i ∈ t, f i ∈ s) :
    t.inf' ht f ∈ s := by
  obtain ⟨j, hj, hj_eq⟩ := Finset.exists_mem_eq_inf' ht f
  exact hj_eq ▸ hf j hj

/-- The `sup'` of a finite family is a member of any set that contains all the family values,
since `sup'` is achieved at some member. -/
protected lemma Finset.sup'_mem_of_forall_mem (ht : t.Nonempty) (hf : ∀ i ∈ t, f i ∈ s) :
    t.sup' ht f ∈ s := by
  obtain ⟨j, hj, hj_eq⟩ := Finset.exists_mem_eq_sup' ht f
  exact hj_eq ▸ hf j hj

end Finset

section AlgebraMap

variable {A : Type*}

/-- If `∑ i, star (b i) * b i = 1`, then any scalar `algebraMap r` equals
`∑ i, star (b i) * algebraMap r * b i`. -/
lemma algebraMap_eq_sum_conj [Semiring A] [StarMul A] [Algebra ℝ A]
    {n : ℕ} {b : Fin n → A} (hb : ∑ i, star (b i) * b i = 1) (r : ℝ) :
    algebraMap ℝ A r = ∑ i, star (b i) * algebraMap ℝ A r * b i := by
  conv_lhs => rw [← one_mul (algebraMap ℝ A r), ← hb]
  simp only [Finset.sum_mul, mul_assoc, Algebra.commutes r]

/-- A conjugate-weighted sum `∑ i, star (b i) * a i * b i` is self-adjoint
whenever each `a i` is self-adjoint. -/
lemma isSelfAdjoint_sum_conj [NonUnitalSemiring A] [StarRing A]
    {n : ℕ} {a : Fin n → A} (ha : ∀ i, IsSelfAdjoint (a i)) (b : Fin n → A) :
    IsSelfAdjoint (∑ i, star (b i) * a i * b i) :=
  isSelfAdjoint_sum Finset.univ fun i _ => (ha i).conjugate' (b i)

variable [Semiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℝ A]
variable {n : ℕ} {a b : Fin n → A} {r : ℝ}

/-- If `algebraMap r ≤ a i` for all `i`, and `∑ star (b i) * b i = 1`, then
`algebraMap r ≤ ∑ i, star (b i) * a i * b i`. -/
lemma algebraMap_le_sum_conj (hb : ∑ i, star (b i) * b i = 1)
    (hle : ∀ i, algebraMap ℝ A r ≤ a i) :
    algebraMap ℝ A r ≤ ∑ i, star (b i) * a i * b i := by
  rw [algebraMap_eq_sum_conj hb r]
  exact Finset.sum_le_sum fun i _ => star_left_conjugate_le_conjugate (hle i) (b i)

/-- If `a i ≤ algebraMap r` for all `i`, and `∑ star (b i) * b i = 1`, then
`∑ i, star (b i) * a i * b i ≤ algebraMap r`. -/
lemma sum_conj_le_algebraMap (hb : ∑ i, star (b i) * b i = 1)
    (hle : ∀ i, a i ≤ algebraMap ℝ A r) :
    ∑ i, star (b i) * a i * b i ≤ algebraMap ℝ A r := by
  rw [algebraMap_eq_sum_conj hb r]
  exact Finset.sum_le_sum fun i _ => star_left_conjugate_le_conjugate (hle i) (b i)

end AlgebraMap

variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A] [PartialOrder A]
    [StarOrderedRing A] [Algebra ℝ A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- If each `a i` has `spectrum ℝ (a i) ⊆ I` and `∑ i, star (b i) * b i = 1`,
then `spectrum ℝ (∑ i, star (b i) * a i * b i) ⊆ I`. -/
theorem spectrum_sum_conj_subset {I : Set ℝ} (hI : Convex ℝ I)
    {n : ℕ} {a b : Fin n → A}
    (ha : ∀ i, IsSelfAdjoint (a i)) (ha_spec : ∀ i, spectrum ℝ (a i) ⊆ I)
    (hb : ∑ i, star (b i) * b i = 1) :
    spectrum ℝ (∑ i, star (b i) * a i * b i) ⊆ I := by
  by_cases hA : Nontrivial A
  swap
  · rw [not_nontrivial_iff_subsingleton] at hA; simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at hb
  have hsa := isSelfAdjoint_sum_conj ha b
  have hcompact := fun i => ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) (a i)
  have hnonempty := fun i => CFC.spectrum_nonempty ℝ (a i)
  have hne : (Finset.univ (α := Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  -- take the inf and sup of all σ (a i)
  let α := Finset.univ.inf' hne (fun i => sInf (spectrum ℝ (a i)))
  let β := Finset.univ.sup' hne (fun i => sSup (spectrum ℝ (a i)))
  have lower : algebraMap ℝ A α ≤ ∑ i, star (b i) * a i * b i := by
    exact algebraMap_le_sum_conj hb fun i =>
      (algebraMap_le_iff_le_spectrum (ha i)).mpr fun _ hx =>
        Finset.inf'_le _ (Finset.mem_univ i) |>.trans <| csInf_le (hcompact i).bddBelow hx
  have upper : ∑ i, star (b i) * a i * b i ≤ algebraMap ℝ A β :=
    sum_conj_le_algebraMap hb fun i =>
      (le_algebraMap_iff_spectrum_le (ha i)).mpr fun _ hx =>
        le_csSup (hcompact i).bddAbove hx |>.trans <|
          Finset.le_sup' (fun i => sSup (spectrum ℝ (a i))) (Finset.mem_univ i)
  intro t ht
  refine hI.ordConnected.out ?_ ?_
    ⟨(algebraMap_le_iff_le_spectrum hsa).mp lower t ht,
     (le_algebraMap_iff_spectrum_le hsa).mp upper t ht⟩
  · exact Finset.inf'_mem_of_forall_mem hne
      fun i _ => ha_spec i <| (hcompact i).sInf_mem (hnonempty i)
  · exact Finset.sup'_mem_of_forall_mem hne
      fun i _ => ha_spec i <| (hcompact i).sSup_mem (hnonempty i)
