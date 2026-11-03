module

public import TwoHiddenLayers.Pyramid

/-!
# The simplex and the coned dilated facets

* `supportFun_simplex`: the support function of the standard simplex is `max (x₁, …, xₙ)`.
* `subdivision`: for `∅ ≠ R ⊊ ι` with complement `C`, the pyramids `pyr_{e_v}(Q_{v,R})` for
  `v ∈ C` are translates of `|C| T_v`, where the simplices `T_v = {p ∈ Δ | p_v ≤ p_w ∀ w ∈ C}`
  subdivide `Δ`. Hence `∑_{v ∈ C} h_{pyr_{e_v}(Q_{v,R})} ≡ |C| h_Δ`.
-/

open Finset

@[expose] public noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Membership in the standard simplex. -/
theorem mem_simplex_iff {p : ι → ℝ} :
    p ∈ (simplex : Set (ι → ℝ)) ↔ ∑ i, p i = 1 ∧ ∀ i, 0 ≤ p i := by
  simp [simplex, simplexCons, hpoly, neg_dotProduct, single_dotProduct]

/-- The standard simplex is bounded. -/
theorem isBounded_simplex : Bornology.IsBounded (simplex : Set (ι → ℝ)) := by
  refine (Metric.isBounded_Icc (0 : ι → ℝ) 1).subset fun p hp ↦ ?_
  rw [mem_simplex_iff] at hp
  refine ⟨fun i ↦ hp.2 i, fun i ↦ ?_⟩
  rw [Pi.one_apply, ← hp.1]
  exact single_le_sum (fun j _ ↦ hp.2 j) (mem_univ i)

omit [Fintype ι] in
@[simp]
theorem Constraint.homog_b (v : ι) (c : Constraint ι) : (c.homog v).b = c.b := rfl

/-- Homogenizing the constraint `-p_i ≤ b` with respect to `v ≠ i`. -/
theorem homog_neg_single_dotProduct {v i : ι} (hi : i ≠ v) (b : ℝ) (p : ι → ℝ) :
    (Constraint.homog v ⟨-Pi.single i 1, b⟩).a ⬝ᵥ p = -p i + b * p v := by
  have : Function.update (-Pi.single i 1 : ι → ℝ) v b = -Pi.single i 1 + Pi.single v b := by
    ext j
    rcases eq_or_ne j v with rfl | hj
    · simp [hi]
    · simp [hj]
  simp [Constraint.homog, this, add_dotProduct, neg_dotProduct, single_dotProduct]

/-- Membership in the pyramid `pyr_{e_v}(Q_{v,R})`. -/
theorem mem_pyr_qCons_iff {v : ι} {R : Finset ι} {p : ι → ℝ} :
    p ∈ pyr v (qCons v R) ↔ ∑ i, p i = 1 ∧ 0 ≤ p v ∧ p v ≤ 1 ∧
      ∀ i, i ≠ v → (i ∈ R → 0 ≤ p i) ∧ (i ∉ R → p v - 1 ≤ p i) := by
  simp only [pyr, pyrCons, hpoly, Set.mem_ofPred_eq, forall_mem_insert, qCons, image_image,
    forall_mem_image, mem_erase, mem_univ, and_true, Function.comp_apply]
  simp only [neg_dotProduct, single_dotProduct, one_mul, neg_nonpos]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun i ↦ ?_)))
  refine imp_congr_right fun hi ↦ ?_
  split_ifs with h
  · simp [homog_neg_single_dotProduct hi, h]
  · rw [homog_neg_single_dotProduct hi, Constraint.homog_b]
    constructor
    · intro h'
      exact ⟨fun hR ↦ absurd hR h, fun _ ↦ by linarith⟩
    · rintro ⟨-, h'⟩
      linarith [h' h]

/-- Membership in `T_v = {p ∈ Δ | p_v ≤ p_w ∀ w ∈ C}`. -/
theorem mem_hpoly_tCons_iff {C : Finset ι} {v : ι} {p : ι → ℝ} :
    p ∈ hpoly (tCons C v) ↔ p ∈ (simplex : Set (ι → ℝ)) ∧ ∀ w ∈ C.erase v, p v ≤ p w := by
  simp only [mem_erase, mem_simplex_iff]
  simp only [tCons, hpoly, simplexCons, Set.mem_ofPred_eq, mem_union, mem_image, mem_univ,
    true_and, mem_erase]
  constructor
  · rintro ⟨hs, h⟩
    refine ⟨⟨hs, fun i ↦ ?_⟩, fun w ⟨hw, hwC⟩ ↦ ?_⟩
    · simpa [neg_dotProduct, single_dotProduct] using h _ (Or.inl ⟨i, rfl⟩)
    · simpa [sub_dotProduct, single_dotProduct] using h _ (Or.inr ⟨w, ⟨hw, hwC⟩, rfl⟩)
  · rintro ⟨⟨hs, h0⟩, h⟩
    refine ⟨hs, ?_⟩
    rintro c (⟨i, rfl⟩ | ⟨w, ⟨hw, hwC⟩, rfl⟩)
    · simpa [neg_dotProduct, single_dotProduct] using h0 i
    · simpa [sub_dotProduct, single_dotProduct] using h w ⟨hw, hwC⟩

omit [Fintype ι] in
/-- Unit vectors are nonnegative. -/
theorem single_one_nonneg (i j : ι) : 0 ≤ (Pi.single i (1 : ℝ) : ι → ℝ) j := by
  rw [Pi.single_apply]
  split_ifs <;> norm_num

/-- The unit vectors lie in the simplex. -/
theorem single_mem_simplex (i : ι) : (Pi.single i 1 : ι → ℝ) ∈ (simplex : Set (ι → ℝ)) :=
  mem_simplex_iff.2 ⟨by simp, fun j ↦ single_one_nonneg i j⟩

theorem supportFun_simplex [Nonempty ι] (x : ι → ℝ) :
    supportFun (simplex : Set (ι → ℝ)) x = univ.sup' univ_nonempty x := by
  apply le_antisymm
  · obtain ⟨i⟩ := ‹Nonempty ι›
    refine supportFun_le ⟨_, single_mem_simplex i⟩ fun p hp ↦ ?_
    rw [mem_simplex_iff] at hp
    calc p ⬝ᵥ x = ∑ j, p j * x j := rfl
      _ ≤ ∑ j, p j * univ.sup' univ_nonempty x :=
        sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (le_sup' x (mem_univ j)) (hp.2 j)
      _ = _ := by rw [← sum_mul, hp.1, one_mul]
  · refine sup'_le _ _ fun i _ ↦ ?_
    simpa [single_dotProduct] using le_supportFun isBounded_simplex (single_mem_simplex i) x

theorem facetPoly_qCons_nonempty {v : ι} (hn : 2 ≤ Fintype.card ι) (R : Finset ι) :
    (facetPoly v (qCons v R)).Nonempty := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
  refine ⟨Pi.single w 1, by simp, by simp [hw.symm], fun c hc ↦ ?_⟩
  obtain ⟨i, -, rfl⟩ := mem_image.1 hc
  have := single_one_nonneg i w
  split_ifs <;> simp <;> linarith

theorem isBounded_facetPoly_qCons (v : ι) (R : Finset ι) :
    Bornology.IsBounded (facetPoly v (qCons v R)) := by
  refine (Metric.isBounded_Icc (-1 : ι → ℝ) (fun _ ↦ (Fintype.card ι : ℝ))).subset
    fun p hp ↦ ?_
  obtain ⟨hs, hv, hc⟩ := hp
  have hge : ∀ i, -1 ≤ p i := by
    intro i
    rcases eq_or_ne i v with rfl | hi
    · rw [hv]; norm_num
    have := hc _ (mem_image_of_mem _ (mem_erase.2 ⟨hi, mem_univ i⟩))
    split_ifs at this <;> simp [neg_dotProduct, single_dotProduct] at this <;> linarith
  refine ⟨fun i ↦ by simpa using hge i, fun i ↦ ?_⟩
  have : p i + 1 ≤ ∑ j, (p j + 1) :=
    single_le_sum (f := fun j ↦ p j + 1) (fun j _ ↦ by linarith [hge j]) (mem_univ i)
  rw [sum_add_distrib, hs] at this
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at this
  change p i ≤ (Fintype.card ι : ℝ)
  linarith

/-- The coordinate sum of an indicator vector. -/
theorem sum_indVec (S : Finset ι) : ∑ i, indVec S i = S.card := by
  simp [indVec]

/-- The pyramid `pyr_{e_v}(Q_{v,R})` is a translate of `|C| T_v`, where `C = Rᶜ`. -/
theorem pyr_qCons_eq {R : Finset ι} {v : ι} (hv : v ∈ Rᶜ) :
    pyr v (qCons v R) =
      (fun l ↦ (#Rᶜ : ℝ) • l + -indVec (Rᶜ.erase v)) '' hpoly (tCons Rᶜ v) := by
  set k : ℝ := (#Rᶜ : ℝ)
  have hk0 : 0 < k := by simpa [k] using card_pos.2 ⟨v, hv⟩
  have hk : (#(Rᶜ.erase v) : ℝ) = k - 1 := by
    rw [card_erase_of_mem hv, Nat.cast_sub (card_pos.2 ⟨v, hv⟩), Nat.cast_one]
  have hiv : indVec (Rᶜ.erase v) v = 0 := by simp [indVec]
  have hiR : ∀ i ∈ R, indVec (Rᶜ.erase v) i = 0 := fun i hi ↦ by simp [indVec, hi]
  have hiC : ∀ i, i ≠ v → i ∉ R → indVec (Rᶜ.erase v) i = 1 := fun i h1 h2 ↦ by
    simp [indVec, h1, h2]
  ext p
  constructor
  · intro hp
    obtain ⟨hs, h0, h1, hi⟩ := mem_pyr_qCons_iff.1 hp
    refine ⟨k⁻¹ • (p + indVec (Rᶜ.erase v)), ?_, ?_⟩
    · rw [mem_hpoly_tCons_iff, mem_simplex_iff]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      refine ⟨⟨?_, fun i ↦ ?_⟩, fun w hw ↦ ?_⟩
      · rw [← mul_sum, sum_add_distrib, hs, sum_indVec, hk]
        field_simp
        ring
      · refine mul_nonneg (inv_nonneg.2 hk0.le) ?_
        rcases eq_or_ne i v with rfl | hiv'
        · rw [hiv]; linarith
        by_cases hR : i ∈ R
        · rw [hiR i hR]; linarith [(hi i hiv').1 hR]
        · rw [hiC i hiv' hR]; linarith [(hi i hiv').2 hR]
      · obtain ⟨hwv, hwC⟩ := mem_erase.1 hw
        have hwR := mem_compl.1 hwC
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hk0.le)
        rw [hiv, hiC w hwv hwR]
        linarith [(hi w hwv).2 hwR]
    · ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      field_simp
      ring
  · rintro ⟨l, hl, rfl⟩
    rw [mem_hpoly_tCons_iff, mem_simplex_iff] at hl
    obtain ⟨⟨hs, h0⟩, hle⟩ := hl
    have hCsum : k * l v ≤ 1 :=
      calc k * l v = ∑ _w ∈ Rᶜ, l v := by simp [k]
        _ ≤ ∑ w ∈ Rᶜ, l w := sum_le_sum fun w hw ↦ by
          rcases eq_or_ne w v with rfl | hwv
          · exact le_rfl
          · exact hle w (mem_erase.2 ⟨hwv, hw⟩)
        _ ≤ ∑ w, l w := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun w _ _ ↦ h0 w
        _ = 1 := hs
    rw [mem_pyr_qCons_iff]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hiv, neg_zero, add_zero]
    refine ⟨?_, mul_nonneg hk0.le (h0 v), hCsum, fun i hiv' ↦ ⟨fun hR ↦ ?_, fun hR ↦ ?_⟩⟩
    · rw [sum_add_distrib, ← mul_sum, hs, sum_neg_distrib, sum_indVec, hk]
      ring
    · rw [hiR i hR, neg_zero, add_zero]
      exact mul_nonneg hk0.le (h0 i)
    · rw [hiC i hiv' hR]
      have := hle i (mem_erase.2 ⟨hiv', mem_compl.2 hR⟩)
      nlinarith

/-- The simplices `T_v` are bounded. -/
theorem isBounded_hpoly_tCons (C : Finset ι) (v : ι) : Bornology.IsBounded (hpoly (tCons C v)) :=
  isBounded_simplex.subset fun _ hp ↦ (mem_hpoly_tCons_iff.1 hp).1

/-- `h_{pyr_{e_v}(Q_{v,R})} = |C| h_{T_v} - ⟪1_{C \ v}, ·⟫`. -/
theorem supportFun_pyr_qCons {R : Finset ι} (hR : R.Nonempty) {v : ι} (hv : v ∈ Rᶜ) :
    supportFun (pyr v (qCons v R)) = (#Rᶜ : ℝ) • supportFun (hpoly (tCons Rᶜ v)) +
      fun x ↦ (-indVec (Rᶜ.erase v)) ⬝ᵥ x := by
  obtain ⟨w, hw⟩ := hR
  have hne : (hpoly (tCons Rᶜ v)).Nonempty := by
    refine ⟨Pi.single w 1, mem_hpoly_tCons_iff.2 ⟨single_mem_simplex w, fun u hu ↦ ?_⟩⟩
    have hvw : v ≠ w := fun h ↦ mem_compl.1 hv (h ▸ hw)
    simp [Pi.single_apply, hvw]
    split_ifs <;> norm_num
  ext x
  rw [pyr_qCons_eq hv, supportFun_image_smul_add (isBounded_hpoly_tCons _ _) hne
    (by simpa using card_pos.2 ⟨v, hv⟩)]
  rfl

/-- The simplices `T_v`, `v ∈ C`, subdivide `Δ`: off the hyperplanes `p_v = p_w`, a point of `Δ`
lies in exactly one `T_v`. -/
theorem sum_indicator_tCons_sub_simplex {C : Finset ι} (hC : C.Nonempty) {p : ι → ℝ}
    (hpG : ∀ v ∈ C, ∀ w ∈ C, v ≠ w → p v ≠ p w) :
    -1 * (simplex : Set (ι → ℝ)).indicator (1 : (ι → ℝ) → ℝ) p +
      ∑ v ∈ C, 1 * (hpoly (tCons C v)).indicator (1 : (ι → ℝ) → ℝ) p = 0 := by
  by_cases hp : p ∈ (simplex : Set (ι → ℝ))
  · obtain ⟨v₀, hv₀, hmin⟩ := exists_min_image C p hC
    have hmem : p ∈ hpoly (tCons C v₀) :=
      mem_hpoly_tCons_iff.2 ⟨hp, fun w hw ↦ hmin w (mem_of_mem_erase hw)⟩
    rw [sum_eq_single v₀]
    · simp [Set.indicator_of_mem hp, Set.indicator_of_mem hmem]
    · intro u hu hne
      rw [Set.indicator_of_notMem, mul_zero]
      intro hpu
      have h1 := (mem_hpoly_tCons_iff.1 hpu).2 v₀ (mem_erase.2 ⟨hne.symm, hv₀⟩)
      exact hpG u hu v₀ hv₀ hne (le_antisymm h1 (hmin u hu))
    · exact fun h ↦ absurd hv₀ h
  · rw [Set.indicator_of_notMem hp, sum_eq_zero]
    · simp
    · intro u _
      rw [Set.indicator_of_notMem, mul_zero]
      exact fun h ↦ hp (mem_hpoly_tCons_iff.1 h).1

theorem subdivision {R : Finset ι} (hR : R.Nonempty) (hRu : R ≠ univ) :
    ∑ v ∈ Rᶜ, supportFun (pyr v (qCons v R)) - (Rᶜ.card : ℝ) • supportFun simplex ∈
      maxSpan ι (Fintype.card ι - 1) := by
  have hC : Rᶜ.Nonempty := (compl_ne_univ_iff_nonempty Rᶜ).1 (by rwa [compl_compl])
  have hn : 1 < Fintype.card ι := by
    obtain ⟨w, hw⟩ := hR
    obtain ⟨v, hv⟩ := hC
    exact Fintype.one_lt_card_iff.2 ⟨v, w, fun h ↦ mem_compl.1 hv (h ▸ hw)⟩
  set G : Finset (Constraint ι) := simplexCons ∪ Rᶜ.biUnion (tCons Rᶜ) with hG_def
  have hS : ∀ g ∈ (simplexCons : Finset (Constraint ι)), g.IsNonconst := by
    intro g hg
    obtain ⟨i, -, rfl⟩ := mem_image.1 hg
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hn i
    exact ⟨i, j, by simp [hj]⟩
  have hG : ∀ g ∈ G, g.IsNonconst := by
    intro g hg
    simp only [G, mem_union, mem_biUnion] at hg
    obtain hg | ⟨v, -, hg⟩ := hg
    · exact hS g hg
    simp only [tCons, mem_union, mem_image] at hg
    obtain hg | ⟨w, hw, rfl⟩ := hg
    · exact hS g hg
    · have hwv := ne_of_mem_erase hw
      exact ⟨v, w, by norm_num [hwv, hwv.symm]⟩
  have ht := transfer (κ := Option ι) (insertNone Rᶜ) (fun o ↦ o.elim (-1) fun _ ↦ 1)
    (fun o ↦ o.elim simplexCons (tCons Rᶜ)) G hG ?_ ?_ ?_
  rotate_left
  · intro o ho
    cases o with
    | none => exact subset_union_left
    | some v =>
      exact (subset_biUnion_of_mem (tCons Rᶜ) (some_mem_insertNone.1 ho)).trans
        subset_union_right
  · intro o _
    cases o with
    | none => exact isBounded_simplex
    | some v => exact isBounded_hpoly_tCons _ _
  · intro p _ hpG
    rw [sum_insertNone]
    simp only [Option.elim]
    refine sum_indicator_tCons_sub_simplex hC fun v hv w hw hvw h ↦ ?_
    refine hpG ⟨Pi.single v 1 - Pi.single w 1, 0⟩ ?_ ?_
    · refine mem_union_right _ (mem_biUnion.2 ⟨v, hv, mem_union_right _ ?_⟩)
      exact mem_image.2 ⟨w, mem_erase.2 ⟨hvw.symm, hw⟩, rfl⟩
    · simp [sub_dotProduct, single_dotProduct, h]
  rw [sum_insertNone] at ht
  simp only [Option.elim] at ht
  have key : ∑ v ∈ Rᶜ, supportFun (pyr v (qCons v R)) - (Rᶜ.card : ℝ) • supportFun simplex =
      (#Rᶜ : ℝ) • ((-1 : ℝ) • supportFun simplex +
        ∑ v ∈ Rᶜ, (1 : ℝ) • supportFun (hpoly (tCons Rᶜ v))) +
      ∑ v ∈ Rᶜ, fun x ↦ (-indVec (Rᶜ.erase v)) ⬝ᵥ x := by
    rw [sum_congr rfl fun v hv ↦ supportFun_pyr_qCons hR hv, sum_add_distrib, ← smul_sum]
    simp only [one_smul, neg_one_smul, smul_add, smul_neg]
    abel
  rw [key]
  exact add_mem (Submodule.smul_mem _ _ ht)
    (sum_mem fun v _ ↦ linear_mem_maxSpan _ (by omega))

end
