module

public import TwoHiddenLayers.HPolytope

/-!
# Pyramids over facet polytopes

For a polytope `B = facetPoly v cs` in the facet hyperplane `{∑ pᵢ = 1, p_v = 0}` we study the
pyramid `pyr v cs = conv ({e_v} ∪ B)`, given by homogenized inequalities. We show:

* `pyr_eq`: `pyr v cs = {t e_v + (1 - t) q | t ∈ [0, 1], q ∈ B}` if `B` is bounded and nonempty;
* `supportFun_pyr`: `h_{pyr v cs}(x) = max (x_v, h_B(x))`;
* `pyr_generic`: an identity of indicator functions at generic points of the facet transfers to
  the pyramids (coning).
-/

open Finset

@[expose] public noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem isClosed_facetPoly (v : ι) (cs : Finset (Constraint ι)) : IsClosed (facetPoly v cs) := by
  have hdot : ∀ a : ι → ℝ, Continuous fun p : ι → ℝ ↦ a ⬝ᵥ p := fun a ↦ by
    unfold dotProduct; fun_prop
  have : facetPoly v cs = {p | ∑ i, p i = 1} ∩ ({p | p v = 0} ∩
      ⋂ c ∈ cs, {p | c.a ⬝ᵥ p ≤ c.b}) := by
    ext p; simp [facetPoly]
  rw [this]
  refine IsClosed.inter (isClosed_eq (by fun_prop) continuous_const)
    (IsClosed.inter (isClosed_eq (continuous_apply v) continuous_const)
    (isClosed_biInter fun c _ ↦ isClosed_le (hdot c.a) continuous_const))

/-- The normal vector of a homogenized constraint, evaluated at any point. -/
theorem Constraint.homog_a_dotProduct (v : ι) (c : Constraint ι) (p : ι → ℝ) :
    (c.homog v).a ⬝ᵥ p = c.a ⬝ᵥ p + (c.b - c.a v) * p v := by
  have : (c.homog v).a = c.a + Pi.single v (c.b - c.a v) := by
    funext i
    by_cases h : i = v
    · subst h; simp [Constraint.homog]
    · simp [Constraint.homog, h]
  rw [this, add_dotProduct, single_dotProduct]

/-- The normal vector of a homogenized constraint, evaluated at a point of the cone over the
facet. -/
theorem Constraint.homog_a_dotProduct_cone (v : ι) (c : Constraint ι) (t : ℝ) {q : ι → ℝ}
    (hq : q v = 0) :
    (c.homog v).a ⬝ᵥ (t • Pi.single v 1 + (1 - t) • q) = c.b * t + (1 - t) * (c.a ⬝ᵥ q) := by
  rw [Constraint.homog_a_dotProduct]
  simp only [dotProduct_add, dotProduct_smul, dotProduct_single, Pi.add_apply, Pi.smul_apply,
    Pi.single_eq_same, hq, smul_eq_mul]
  ring

theorem mem_pyr_iff {v : ι} {cs : Finset (Constraint ι)} {p : ι → ℝ} :
    p ∈ pyr v cs ↔ ∑ i, p i = 1 ∧ 0 ≤ p v ∧ p v ≤ 1 ∧
      ∀ c ∈ cs, (c.homog v).a ⬝ᵥ p ≤ c.b := by
  simp only [pyr, hpoly, pyrCons, Set.mem_ofPred_eq, Finset.forall_mem_insert,
    Finset.forall_mem_image, neg_dotProduct, single_dotProduct, one_mul, neg_nonpos]
  exact Iff.rfl

/-- Writing a point with `p v ≠ 1` as a point of the cone over the facet `{p_v = 0}`. -/
theorem exists_cone_decomp {v : ι} {p : ι → ℝ} (hp : p v ≠ 1) :
    ∃ q : ι → ℝ, q v = 0 ∧ (∑ i, p i = 1 → ∑ i, q i = 1) ∧
      p = p v • Pi.single v 1 + (1 - p v) • q := by
  have h1 : 1 - p v ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  refine ⟨(1 - p v)⁻¹ • (p - p v • Pi.single v 1), by simp, fun hs ↦ ?_, ?_⟩
  · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_pi_single', Finset.mem_univ,
      ite_true, hs, mul_one]
    field_simp
  · rw [smul_smul, mul_inv_cancel₀ h1, one_smul]; abel

/-- Membership in the pyramid for a point of the cone over the facet below the apex. -/
theorem mem_pyr_iff_of_cone {v : ι} {cs : Finset (Constraint ι)} {t : ℝ} {q : ι → ℝ}
    (hq : q v = 0) (hqs : ∑ i, q i = 1) (ht : t < 1) :
    t • Pi.single v 1 + (1 - t) • q ∈ pyr v cs ↔ 0 ≤ t ∧ q ∈ facetPoly v cs := by
  have ht' : 0 < 1 - t := sub_pos.mpr ht
  have hsum : ∑ i, (t • Pi.single v 1 + (1 - t) • q : ι → ℝ) i = 1 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_pi_single', Finset.mem_univ, ite_true, hqs]
    ring
  have hv : (t • Pi.single v 1 + (1 - t) • q : ι → ℝ) v = t := by simp [hq]
  rw [mem_pyr_iff, hv]
  simp only [hsum, true_and, facetPoly, Set.mem_ofPred_eq, hqs, hq,
    Constraint.homog_a_dotProduct_cone v _ t hq, ht.le]
  refine and_congr_right fun _ ↦ forall₂_congr fun c _ ↦ ?_
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem pyr_eq {v : ι} {cs : Finset (Constraint ι)} (hne : (facetPoly v cs).Nonempty)
    (hb : Bornology.IsBounded (facetPoly v cs)) :
    pyr v cs = {p | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ q ∈ facetPoly v cs,
      p = t • Pi.single v 1 + (1 - t) • q} := by
  ext p
  constructor
  · intro hp
    obtain ⟨hs, h0, h1, hc⟩ := mem_pyr_iff.mp hp
    rcases h1.lt_or_eq with h1 | h1
    · obtain ⟨q, hqv, hqs, hpq⟩ := exists_cone_decomp h1.ne
      have := (mem_pyr_iff_of_cone (cs := cs) hqv (hqs hs) h1).mp (by rw [← hpq]; exact hp)
      exact ⟨_, ⟨h0, h1.le⟩, q, this.2, hpq⟩
    · -- `p v = 1`: the direction `d = p - e_v` is a recession direction of the facet polytope
      obtain ⟨q₀, hq₀⟩ := hne
      set d := p - Pi.single v 1 with hd
      have hdv : d v = 0 := by simp [hd, h1]
      have hds : ∑ i, d i = 0 := by
        simp [hd, Finset.sum_sub_distrib, hs]
      have hdc : ∀ c ∈ cs, c.a ⬝ᵥ d ≤ 0 := by
        intro c hcs
        have := hc c hcs
        rw [Constraint.homog_a_dotProduct, h1] at this
        simp only [hd, dotProduct_sub, dotProduct_single, mul_one]
        linarith
      have hmem : ∀ s : ℝ, 0 ≤ s → q₀ + s • d ∈ facetPoly v cs := by
        intro s hs0
        obtain ⟨h1', h2', h3'⟩ := hq₀
        refine ⟨?_, ?_, fun c hcs ↦ ?_⟩
        · simp [Finset.sum_add_distrib, ← Finset.mul_sum, h1', hds]
        · simp [h2', hdv]
        · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
          nlinarith [h3' c hcs, hdc c hcs]
      obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
      have hd0 : d = 0 := by
        by_contra hne0
        have hpos : 0 < ‖d‖ := norm_pos_iff.mpr hne0
        set s := (C + ‖q₀‖ + 1) / ‖d‖
        have hs0 : 0 ≤ s := by
          have : 0 ≤ C := (norm_nonneg _).trans (hC _ (hmem 0 le_rfl))
          positivity
        have h := hC _ (hmem s hs0)
        have h2 : ‖s • d‖ ≤ ‖q₀ + s • d‖ + ‖q₀‖ := by
          have := norm_sub_le (q₀ + s • d) q₀
          simpa using this
        rw [norm_smul, Real.norm_of_nonneg hs0, div_mul_cancel₀ _ hpos.ne'] at h2
        linarith
      refine ⟨1, ⟨zero_le_one, le_rfl⟩, q₀, hq₀, ?_⟩
      rw [sub_self, zero_smul, add_zero, one_smul]
      exact sub_eq_zero.mp hd0
  · rintro ⟨t, ⟨h0, h1⟩, q, ⟨hqs, hqv, hqc⟩, rfl⟩
    rcases h1.lt_or_eq with h1 | rfl
    · exact (mem_pyr_iff_of_cone hqv hqs h1).mpr ⟨h0, hqs, hqv, hqc⟩
    · rw [sub_self, zero_smul, add_zero, one_smul, mem_pyr_iff]
      refine ⟨by simp [Finset.sum_pi_single'], by simp, by simp, fun c _ ↦ ?_⟩
      rw [Constraint.homog_a_dotProduct]
      simp

theorem isBounded_pyr {v : ι} {cs : Finset (Constraint ι)} (hne : (facetPoly v cs).Nonempty)
    (hb : Bornology.IsBounded (facetPoly v cs)) : Bornology.IsBounded (pyr v cs) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  refine isBounded_iff_forall_norm_le.mpr ⟨‖(Pi.single v 1 : ι → ℝ)‖ + C, ?_⟩
  rw [pyr_eq hne hb]
  rintro _ ⟨t, ⟨h0, h1⟩, q, hq, rfl⟩
  have h1' : 0 ≤ 1 - t := sub_nonneg.mpr h1
  calc ‖t • Pi.single v 1 + (1 - t) • q‖
      ≤ ‖t • (Pi.single v 1 : ι → ℝ)‖ + ‖(1 - t) • q‖ := norm_add_le _ _
    _ = t * ‖(Pi.single v 1 : ι → ℝ)‖ + (1 - t) * ‖q‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h0, Real.norm_of_nonneg h1']
    _ ≤ 1 * ‖(Pi.single v 1 : ι → ℝ)‖ + 1 * C := by
        have hC0 : 0 ≤ C := (norm_nonneg q).trans (hC q hq)
        have ha := mul_le_mul_of_nonneg_right h1 (norm_nonneg (Pi.single v 1 : ι → ℝ))
        have hb := mul_le_mul_of_nonneg_left (hC q hq) h1'
        have hc := mul_le_mul_of_nonneg_right (by linarith : 1 - t ≤ 1) hC0
        linarith
    _ = _ := by ring

theorem supportFun_pyr {v : ι} {cs : Finset (Constraint ι)} (hne : (facetPoly v cs).Nonempty)
    (hb : Bornology.IsBounded (facetPoly v cs)) (x : ι → ℝ) :
    supportFun (pyr v cs) x = max (x v) (supportFun (facetPoly v cs) x) := by
  have hpb := isBounded_pyr hne hb
  have heq := pyr_eq hne hb
  obtain ⟨q₀, hq₀⟩ := hne
  have hapex : Pi.single v 1 ∈ pyr v cs := by
    rw [heq]; exact ⟨1, ⟨zero_le_one, le_rfl⟩, q₀, hq₀, by simp⟩
  have hsub : ∀ q ∈ facetPoly v cs, q ∈ pyr v cs := fun q hq ↦ by
    rw [heq]; exact ⟨0, ⟨le_rfl, zero_le_one⟩, q, hq, by simp⟩
  refine le_antisymm (supportFun_le ⟨_, hapex⟩ fun p hp ↦ ?_) (max_le ?_ ?_)
  · rw [heq] at hp
    obtain ⟨t, ⟨h0, h1⟩, q, hq, rfl⟩ := hp
    have hq' := le_supportFun hb hq x
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, single_dotProduct, one_mul,
      smul_eq_mul, smul_eq_mul]
    have h1' : 0 ≤ 1 - t := sub_nonneg.mpr h1
    calc t * x v + (1 - t) * (q ⬝ᵥ x)
        ≤ t * max (x v) (supportFun (facetPoly v cs) x) +
          (1 - t) * max (x v) (supportFun (facetPoly v cs) x) := by
          gcongr
          · exact le_max_left _ _
          · exact hq'.trans (le_max_right _ _)
      _ = _ := by ring
  · simpa [single_dotProduct] using le_supportFun hpb hapex x
  · exact supportFun_le ⟨q₀, hq₀⟩ fun q hq ↦ le_supportFun hpb (hsub q hq) x

omit [Fintype ι] in
theorem pyrCons_mono {v : ι} {cs cs' : Finset (Constraint ι)} (h : cs ⊆ cs') :
    pyrCons v cs ⊆ pyrCons v cs' :=
  Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.image_subset_image h))

/-- The constraints of a pyramid are nonconstant if the facet constraints are nonconstant
on the coordinates different from the apex. -/
theorem isNonconst_of_mem_pyrCons {v : ι} {G : Finset (Constraint ι)}
    (hG : ∀ g ∈ G, ∃ i j, i ≠ v ∧ j ≠ v ∧ g.a i ≠ g.a j) (hn : 2 ≤ Fintype.card ι) :
    ∀ g ∈ pyrCons v G, g.IsNonconst := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hn v
  intro g hg
  simp only [pyrCons, Finset.mem_insert, Finset.mem_image] at hg
  rcases hg with rfl | rfl | ⟨c, hc, rfl⟩
  · exact ⟨v, w, by simp [hw]⟩
  · exact ⟨v, w, by simp [hw]⟩
  · obtain ⟨i, j, hi, hj, hij⟩ := hG c hc
    exact ⟨i, j, by simpa [Constraint.homog, Function.update_of_ne hi,
      Function.update_of_ne hj] using hij⟩

/-- **Coning.** An identity between indicator functions of facet polytopes at generic points of
the facet gives the same identity for the pyramids at generic points of `∑ pᵢ = 1`. -/
theorem pyr_generic {κ : Type*} (v : ι) (s : Finset κ) (c : κ → ℝ)
    (cs : κ → Finset (Constraint ι)) (G : Finset (Constraint ι))
    (hgen : ∀ q : ι → ℝ, ∑ j, q j = 1 → q v = 0 → (∀ g ∈ G, g.a ⬝ᵥ q ≠ g.b) →
      ∑ i ∈ s, c i * (facetPoly v (cs i)).indicator 1 q = 0)
    (p : ι → ℝ) (hp : ∑ j, p j = 1) (hpG : ∀ g ∈ pyrCons v G, g.a ⬝ᵥ p ≠ g.b) :
    ∑ i ∈ s, c i * (pyr v (cs i)).indicator 1 p = 0 := by
  have h0 : p v ≠ 0 := by
    have := hpG ⟨-Pi.single v 1, 0⟩ (by simp [pyrCons])
    simpa [neg_dotProduct, single_dotProduct] using this
  have h1 : p v ≠ 1 := by
    have := hpG ⟨Pi.single v 1, 1⟩ (by simp [pyrCons])
    simpa [single_dotProduct] using this
  by_cases hin : 0 < p v ∧ p v < 1
  · obtain ⟨q, hqv, hqs, hpq⟩ := exists_cone_decomp h1
    have hqs := hqs hp
    have hq : ∀ g ∈ G, g.a ⬝ᵥ q ≠ g.b := by
      intro g hg hgq
      have := hpG (g.homog v) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ hg)))
      rw [hpq, Constraint.homog_a_dotProduct_cone v g _ hqv, hgq] at this
      exact this (by simp only [Constraint.homog]; ring)
    rw [← hgen q hqs hqv hq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    have hiff : p ∈ pyr v (cs i) ↔ q ∈ facetPoly v (cs i) := by
      rw [hpq, mem_pyr_iff_of_cone hqv hqs hin.2]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hin.1.le, h⟩⟩
    by_cases hmem : q ∈ facetPoly v (cs i)
    · rw [Set.indicator_of_mem (hiff.mpr hmem), Set.indicator_of_mem hmem, Pi.one_apply,
        Pi.one_apply]
    · rw [Set.indicator_of_notMem (mt hiff.mp hmem), Set.indicator_of_notMem hmem]
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Set.indicator_of_notMem, mul_zero]
    intro hmem
    obtain ⟨-, ha, hb, -⟩ := mem_pyr_iff.mp hmem
    exact hin ⟨lt_of_le_of_ne ha (Ne.symm h0), lt_of_le_of_ne hb h1⟩

end
