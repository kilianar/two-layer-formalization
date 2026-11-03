module

public import TwoHiddenLayers.Defs

/-!
# Support functions

Basic properties of `supportFun`, and the valuation property for a single hyperplane cut:
for a compact convex set `K` and a hyperplane `{⟪a, p⟫ = b}`,
`h_K = h_{K ∩ {⟪a,p⟫ ≤ b}} + h_{K ∩ {⟪a,p⟫ ≥ b}} - h_{K ∩ {⟪a,p⟫ = b}}`.
-/

open Finset

@[expose] public noncomputable section

variable {ι : Type*} [Fintype ι]

@[simp]
theorem supportFun_empty : supportFun (∅ : Set (ι → ℝ)) = 0 := by
  funext x; simp [supportFun]

/-- The linear form `p ↦ ⟪p, x⟫` is continuous. -/
theorem continuous_dotProduct_left (x : ι → ℝ) : Continuous fun p : ι → ℝ ↦ p ⬝ᵥ x :=
  continuous_id.dotProduct continuous_const

/-- A bounded set has a bounded-above image under `p ↦ ⟪p, x⟫`. -/
theorem bddAbove_image_dotProduct {K : Set (ι → ℝ)} (hK : Bornology.IsBounded K)
    (x : ι → ℝ) : BddAbove ((fun p ↦ p ⬝ᵥ x) '' K) :=
  ((hK.isCompact_closure.image (continuous_dotProduct_left x)).bddAbove).mono
    (Set.image_mono subset_closure)

/-- Every point of a bounded set is bounded by the support function. -/
theorem le_supportFun {K : Set (ι → ℝ)} (hK : Bornology.IsBounded K) {p : ι → ℝ} (hp : p ∈ K)
    (x : ι → ℝ) : p ⬝ᵥ x ≤ supportFun K x :=
  le_csSup (bddAbove_image_dotProduct hK x) ⟨p, hp, rfl⟩

/-- An upper bound on a nonempty set bounds its support function. -/
theorem supportFun_le {K : Set (ι → ℝ)} (hK : K.Nonempty) {x : ι → ℝ} {c : ℝ}
    (h : ∀ p ∈ K, p ⬝ᵥ x ≤ c) : supportFun K x ≤ c :=
  csSup_le (hK.image _) (by rintro _ ⟨p, hp, rfl⟩; exact h p hp)

/-- On a nonempty compact set, the supremum defining the support function is attained. -/
theorem IsCompact.exists_supportFun_eq {K : Set (ι → ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (x : ι → ℝ) : ∃ p ∈ K, supportFun K x = p ⬝ᵥ x := by
  obtain ⟨p, hp, h⟩ := (hK.image (continuous_dotProduct_left x)).sSup_mem (hne.image _)
  exact ⟨p, hp, h.symm⟩

/-- Support function of a dilated and translated set. -/
theorem supportFun_image_smul_add {K : Set (ι → ℝ)} (hK : Bornology.IsBounded K)
    (hne : K.Nonempty) {r : ℝ} (hr : 0 < r) (t x : ι → ℝ) :
    supportFun ((fun p ↦ r • p + t) '' K) x = r * supportFun K x + t ⬝ᵥ x := by
  have key : ∀ p, (r • p + t) ⬝ᵥ x = r * (p ⬝ᵥ x) + t ⬝ᵥ x := fun p ↦ by
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hK' : Bornology.IsBounded ((fun p ↦ r • p + t) '' K) := by
    have hc : Continuous fun p : ι → ℝ ↦ r • p + t := by fun_prop
    exact (hK.isCompact_closure.image hc).isBounded.subset (Set.image_mono subset_closure)
  apply le_antisymm
  · refine supportFun_le (hne.image _) ?_
    rintro _ ⟨p, hp, rfl⟩
    rw [key]
    gcongr
    exact le_supportFun hK hp x
  · have : supportFun K x ≤ (supportFun ((fun p ↦ r • p + t) '' K) x - t ⬝ᵥ x) / r := by
      refine supportFun_le hne fun p hp ↦ ?_
      rw [le_div_iff₀ hr, le_sub_iff_add_le, mul_comm, ← key]
      exact le_supportFun hK' ⟨p, hp, rfl⟩ x
    rw [le_div_iff₀ hr] at this
    linarith

/-- If `p, q ∈ K` lie on opposite sides of the hyperplane `{⟪a, ·⟫ = b}`, then the segment
`[p, q]` meets the hyperplane in a point `z` with `⟪z, x⟫ ≥ min ⟪p, x⟫ ⟪q, x⟫`. -/
theorem exists_mem_cut_le {K : Set (ι → ℝ)} (hconv : Convex ℝ K) {a : ι → ℝ} {b : ℝ}
    {p q : ι → ℝ} (hp : p ∈ K) (hq : q ∈ K) (hpa : a ⬝ᵥ p ≤ b) (hqa : b ≤ a ⬝ᵥ q) (x : ι → ℝ) :
    ∃ z ∈ K ∩ {p | a ⬝ᵥ p = b}, min (p ⬝ᵥ x) (q ⬝ᵥ x) ≤ z ⬝ᵥ x := by
  rcases hpa.eq_or_lt with hpa | hpa
  · exact ⟨p, ⟨hp, hpa⟩, min_le_left _ _⟩
  set t := (b - a ⬝ᵥ p) / (a ⬝ᵥ q - a ⬝ᵥ p)
  have hd : 0 < a ⬝ᵥ q - a ⬝ᵥ p := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).2 (by linarith)
  have hlin : ∀ y : ι → ℝ, y ⬝ᵥ ((1 - t) • p + t • q) = (1 - t) * (y ⬝ᵥ p) + t * (y ⬝ᵥ q) :=
    fun y ↦ by rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  refine ⟨(1 - t) • p + t • q, ⟨hconv hp hq (by linarith) ht0 (by ring), ?_⟩, ?_⟩
  · change a ⬝ᵥ _ = b
    rw [hlin]
    have : t * (a ⬝ᵥ q - a ⬝ᵥ p) = b - a ⬝ᵥ p := div_mul_cancel₀ _ hd.ne'
    linear_combination this
  · rw [dotProduct_comm ((1 - t) • p + t • q) x, hlin, dotProduct_comm x p, dotProduct_comm x q]
    have h1 := min_le_left (p ⬝ᵥ x) (q ⬝ᵥ x)
    have h2 := min_le_right (p ⬝ᵥ x) (q ⬝ᵥ x)
    nlinarith

/-- The valuation property of support functions for a single hyperplane cut. -/
theorem supportFun_cut {K : Set (ι → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (a : ι → ℝ) (b : ℝ) :
    supportFun K = supportFun (K ∩ {p | a ⬝ᵥ p ≤ b}) + supportFun (K ∩ {p | b ≤ a ⬝ᵥ p}) -
      supportFun (K ∩ {p | a ⬝ᵥ p = b}) := by
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  set L := K ∩ {p | a ⬝ᵥ p ≤ b}
  set U := K ∩ {p | b ≤ a ⬝ᵥ p}
  set Z := K ∩ {p | a ⬝ᵥ p = b}
  have hc : Continuous fun p : ι → ℝ ↦ a ⬝ᵥ p := continuous_const.dotProduct continuous_id
  have hL : IsCompact L := hK.inter_right (isClosed_le hc continuous_const)
  have hU : IsCompact U := hK.inter_right (isClosed_le continuous_const hc)
  have hZL : Z ⊆ L := fun p hp ↦ ⟨hp.1, hp.2.le⟩
  have hZU : Z ⊆ U := fun p hp ↦ ⟨hp.1, hp.2.ge⟩
  rcases L.eq_empty_or_nonempty with hL0 | hLne
  · have hZ0 : Z = ∅ := Set.subset_eq_empty hZL hL0
    have hUK : U = K := Set.inter_eq_left.2 fun p hp ↦ by
      by_contra h
      have : p ∈ L := ⟨hp, by simp only [Set.mem_ofPred_eq] at h ⊢; linarith⟩
      simp [hL0] at this
    rw [hL0, hZ0, hUK]
    simp
  rcases U.eq_empty_or_nonempty with hU0 | hUne
  · have hZ0 : Z = ∅ := Set.subset_eq_empty hZU hU0
    have hLK : L = K := Set.inter_eq_left.2 fun p hp ↦ by
      by_contra h
      have : p ∈ U := ⟨hp, by simp only [Set.mem_ofPred_eq] at h ⊢; linarith⟩
      simp [hU0] at this
    rw [hU0, hZ0, hLK]
    simp
  obtain ⟨p, hpL, hp⟩ := hL.exists_supportFun_eq hLne x
  obtain ⟨q, hqU, hq⟩ := hU.exists_supportFun_eq hUne x
  obtain ⟨z, hzZ, hz⟩ := exists_mem_cut_le hconv hpL.1 hqU.1 hpL.2 hqU.2 x
  have hmax : supportFun K x = max (supportFun L x) (supportFun U x) := by
    apply le_antisymm
    · refine supportFun_le (hLne.mono Set.inter_subset_left) fun r hr ↦ ?_
      rcases le_total (a ⬝ᵥ r) b with h | h
      · exact (le_supportFun hL.isBounded ⟨hr, h⟩ x).trans (le_max_left _ _)
      · exact (le_supportFun hU.isBounded ⟨hr, h⟩ x).trans (le_max_right _ _)
    · rw [hp, hq]
      exact max_le (le_supportFun hK.isBounded hpL.1 x) (le_supportFun hK.isBounded hqU.1 x)
  have hmin : supportFun Z x = min (supportFun L x) (supportFun U x) := by
    apply le_antisymm
    · exact supportFun_le ⟨z, hzZ⟩ fun r hr ↦
        le_min (le_supportFun hL.isBounded (hZL hr) x) (le_supportFun hU.isBounded (hZU hr) x)
    · rw [hp, hq]
      exact hz.trans (le_supportFun (hL.isBounded.subset hZL) hzZ x)
  rw [hmax, hmin]
  linarith [min_add_max (supportFun L x) (supportFun U x)]

end
