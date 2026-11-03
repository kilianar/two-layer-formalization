module

public import TwoHiddenLayers.Defs

/-!
# Maxima of linear forms

If `W` is a finite set of points lying in an affine subspace of dimension `d`, then
`x ↦ max_{w ∈ W} ⟪w, x⟫` is a linear combination of maxima of at most `d + 1` linear forms.
The proof uses Radon's theorem: if `W` is affinely dependent and `I` is a Radon partition, then
`max_W = ∑_{∅ ≠ S ⊆ I} (-1)^{|S|+1} max_{W \ S}`.
-/

open Finset

@[expose] public noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The maximum over the empty set is `0` by convention. -/
theorem maxLin_empty : maxLin (∅ : Finset (ι → ℝ)) = 0 := by
  funext x; simp [maxLin]

/-- The maximum of a single linear form is that linear form. -/
theorem maxLin_singleton (t : ι → ℝ) : maxLin {t} = fun x ↦ t ⬝ᵥ x := by
  funext x; simp [maxLin]

/-- Unfolding `maxLin` for a nonempty set. -/
theorem maxLin_eq_sup' {W : Finset (ι → ℝ)} (hW : W.Nonempty) (x : ι → ℝ) :
    maxLin W x = W.sup' hW (· ⬝ᵥ x) := by
  simp [maxLin, hW]

/-- A maximum of at most `k` linear forms lies in `maxSpan ι k`. -/
theorem maxLin_mem_maxSpan_of_card_le {W : Finset (ι → ℝ)} (hW : W.Nonempty) {k : ℕ}
    (hk : W.card ≤ k) : maxLin W ∈ maxSpan ι k :=
  Submodule.subset_span ⟨W, hW, hk, rfl⟩

/-- Linear forms lie in `maxSpan ι k` for `k ≥ 1`. -/
theorem linear_mem_maxSpan (t : ι → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (fun x ↦ t ⬝ᵥ x) ∈ maxSpan ι k := by
  rw [← maxLin_singleton]
  exact maxLin_mem_maxSpan_of_card_le (singleton_nonempty t) (by simpa using hk)

/-- Removing a point does not change the maximum if another point is at least as large. -/
theorem maxLin_erase_apply [DecidableEq (ι → ℝ)] {V : Finset (ι → ℝ)} {i j : ι → ℝ} {x : ι → ℝ}
    (hj : j ∈ V) (hji : j ≠ i) (h : i ⬝ᵥ x ≤ j ⬝ᵥ x) : maxLin (V.erase i) x = maxLin V x := by
  have hne : (V.erase i).Nonempty := ⟨j, mem_erase.2 ⟨hji, hj⟩⟩
  rw [maxLin_eq_sup' hne, maxLin_eq_sup' (hne.mono (erase_subset i V))]
  refine le_antisymm (sup'_mono _ (erase_subset i V) hne) (sup'_le _ _ fun v hv ↦ ?_)
  by_cases hvi : v = i
  · subst hvi
    exact h.trans (le_sup' (· ⬝ᵥ x) (mem_erase.2 ⟨hji, hj⟩))
  · exact le_sup' (· ⬝ᵥ x) (mem_erase.2 ⟨hvi, hv⟩)

/-- The inclusion–exclusion identity for a Radon partition `W = I ∪ (W \ I)`. -/
theorem maxLin_eq_neg_sum_of_radon [DecidableEq (ι → ℝ)] {W I : Finset (ι → ℝ)}
    {z : ι → ℝ} (hz₁ : z ∈ convexHull ℝ (I : Set (ι → ℝ)))
    (hz₂ : z ∈ convexHull ℝ ((W \ I : Finset (ι → ℝ)) : Set (ι → ℝ))) :
    maxLin W = -∑ S ∈ I.powerset.erase ∅, (-1 : ℝ) ^ S.card • maxLin (W \ S) := by
  funext x
  have hne : (W \ I).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [h] at hz₂
  set M := maxLin (W \ I) x
  have hlin : IsLinearMap ℝ fun p : ι → ℝ ↦ p ⬝ᵥ x :=
    ⟨fun p q ↦ add_dotProduct p q x, fun c p ↦ smul_dotProduct c p x⟩
  obtain ⟨i₀, hi₀I, hi₀⟩ : ∃ i₀ ∈ I, i₀ ⬝ᵥ x ≤ M := by
    by_contra! h
    have h₁ : z ⬝ᵥ x ≤ M :=
      convexHull_min (fun w hw ↦ (le_sup' (· ⬝ᵥ x) hw).trans_eq (maxLin_eq_sup' hne x).symm)
        (convex_halfSpace_le hlin M) hz₂
    have h₂ : M < z ⬝ᵥ x := convexHull_min (fun w hw ↦ h w hw) (convex_halfSpace_gt hlin M) hz₁
    linarith
  obtain ⟨j, hj, hjM⟩ := exists_mem_eq_sup' hne (· ⬝ᵥ x)
  rw [← maxLin_eq_sup'] at hjM
  have hji : j ≠ i₀ := fun h ↦ (mem_sdiff.1 hj).2 (h ▸ hi₀I)
  have hsum : ∑ S ∈ I.powerset, (-1 : ℝ) ^ S.card * maxLin (W \ S) x = 0 := by
    rw [← insert_erase hi₀I, sum_powerset_insert (notMem_erase i₀ I), ← sum_add_distrib]
    refine sum_eq_zero fun t ht ↦ ?_
    have hti : i₀ ∉ t := fun h ↦ notMem_erase i₀ I (mem_powerset.1 ht h)
    have htI : t ⊆ I := (mem_powerset.1 ht).trans (erase_subset _ _)
    have hjt : j ∈ W \ t := mem_sdiff.2 ⟨(mem_sdiff.1 hj).1, fun h ↦ (mem_sdiff.1 hj).2 (htI h)⟩
    rw [card_insert_of_notMem hti, pow_succ, sdiff_insert,
      maxLin_erase_apply hjt hji (hjM ▸ hi₀)]
    ring
  rw [← add_sum_erase _ _ (empty_mem_powerset I)] at hsum
  simp only [card_empty, pow_zero, one_mul, sdiff_empty] at hsum
  rw [Pi.neg_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  linarith

/-- If `W` lies in an affine subspace of dimension at most `d`, then `max_{w ∈ W} ⟪w, ·⟫` is a
linear combination of maxima of at most `d + 1` linear forms. -/
theorem maxLin_mem_maxSpan (W : Finset (ι → ℝ)) (A : AffineSubspace ℝ (ι → ℝ))
    (hW : (W : Set (ι → ℝ)) ⊆ A) {d : ℕ} (hA : Module.finrank ℝ A.direction ≤ d) :
    maxLin W ∈ maxSpan ι (d + 1) := by
  classical
  induction W using Finset.strongInduction with
  | H W ih =>
  rcases W.eq_empty_or_nonempty with rfl | hne
  · rw [maxLin_empty]; exact zero_mem _
  by_cases hai : AffineIndependent ℝ ((↑) : W → ι → ℝ)
  · refine maxLin_mem_maxSpan_of_card_le hne ?_
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero hne.card_pos.ne'
    have h₁ := hai.finrank_vectorSpan (n := n) (by simpa using hn)
    have h₂ : vectorSpan ℝ (Set.range ((↑) : W → ι → ℝ)) ≤ A.direction := by
      rw [Subtype.range_coe_subtype]
      exact vectorSpan_mono ℝ hW
    have h₃ := Submodule.finrank_mono h₂
    omega
  obtain ⟨I, z, hz₁, hz₂⟩ := Convex.radon_partition hai
  set I' : Finset (ι → ℝ) := W.filter fun w ↦ ∃ h : w ∈ W, (⟨w, h⟩ : W) ∈ I
  have hI' : ((↑) : W → ι → ℝ) '' I = I' := by
    ext w; simp [I']
  have hI'c : ((↑) : W → ι → ℝ) '' Iᶜ = ↑(W \ I') := by
    ext w
    simp only [Set.mem_image, Set.mem_compl_iff, Subtype.exists, exists_and_right,
      exists_eq_right, coe_sdiff, coe_filter, and_exists_self, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_ofPred_eq, not_exists, I']
    exact ⟨fun ⟨h, h'⟩ ↦ ⟨h, fun _ ↦ h'⟩, fun ⟨h, h'⟩ ↦ ⟨h, h' h⟩⟩
  rw [hI'] at hz₁
  rw [hI'c] at hz₂
  rw [maxLin_eq_neg_sum_of_radon hz₁ hz₂]
  refine neg_mem (sum_mem fun S hS ↦
    Submodule.smul_mem _ _ (ih _ ?_ ((coe_subset.2 sdiff_subset).trans hW)))
  obtain ⟨hS0, hS⟩ := mem_erase.1 hS
  exact sdiff_ssubset ((mem_powerset.1 hS).trans (filter_subset _ _)) (nonempty_iff_ne_empty.2 hS0)

end
