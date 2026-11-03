module

public import TwoHiddenLayers.Support
public import TwoHiddenLayers.MaxSpan

/-!
# Polytopes given by inequalities and the transfer principle

For polytopes `hpoly cs` in the hyperplane `∑ pᵢ = 1` we prove:

* `supportFun_mem_maxSpan_of_subset`: a bounded polytope lying in a hyperplane `{⟪a,p⟫ = b}`
  which is not parallel to `∑ pᵢ = 1` has a support function in `maxSpan ι (card ι - 1)`.
  (Its extreme points are finitely many and span an affine space of dimension `card ι - 2`.)
* `transfer`: if a signed sum of indicator functions of polytopes vanishes at all generic points,
  then the corresponding signed sum of support functions lies in `maxSpan ι (card ι - 1)`.
-/

open Finset Filter Topology

@[expose] public noncomputable section

variable {ι : Type*} [Fintype ι]

theorem convex_hpoly (cs : Finset (Constraint ι)) : Convex ℝ (hpoly cs) := by
  intro p hp q hq s t hs ht hst
  refine ⟨?_, fun c hc ↦ ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hp.1, hq.1,
      mul_one, hst]
  · rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    calc s * (c.a ⬝ᵥ p) + t * (c.a ⬝ᵥ q) ≤ s * c.b + t * c.b := by
          gcongr
          exacts [hp.2 c hc, hq.2 c hc]
      _ = c.b := by rw [← add_mul, hst, one_mul]

theorem isClosed_hpoly (cs : Finset (Constraint ι)) : IsClosed (hpoly cs) := by
  have h1 : IsClosed {p : ι → ℝ | ∑ i, p i = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have h2 : IsClosed {p : ι → ℝ | ∀ c ∈ cs, c.a ⬝ᵥ p ≤ c.b} := by
    simp only [Set.ofPred_forall]
    exact isClosed_biInter fun c _ ↦
      isClosed_le (continuous_const.dotProduct continuous_id) continuous_const
  exact h1.inter h2

theorem isCompact_hpoly {cs : Finset (Constraint ι)} (hb : Bornology.IsBounded (hpoly cs)) :
    IsCompact (hpoly cs) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_hpoly cs) hb

/-- Distinct extreme points of `hpoly cs` have distinct sets of tight constraints. -/
theorem eq_of_extremePoints_of_tight_eq {cs : Finset (Constraint ι)} {p q : ι → ℝ}
    (hp : p ∈ (hpoly cs).extremePoints ℝ) (hq : q ∈ (hpoly cs).extremePoints ℝ)
    (h : ∀ c ∈ cs, c.a ⬝ᵥ p = c.b ↔ c.a ⬝ᵥ q = c.b) : q = p := by
  have hpK := hp.1
  have hqK := hq.1
  set φ : ℝ → ι → ℝ := fun ε ↦ p - ε • (q - p) with hφ
  have hcont : Continuous φ := by fun_prop
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ φ ε ∈ hpoly cs := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ c ∈ cs, c.a ⬝ᵥ p ≠ c.b → c.a ⬝ᵥ φ ε < c.b := by
      rw [eventually_all_finset]
      intro c hc
      by_cases hcp : c.a ⬝ᵥ p = c.b
      · exact Eventually.of_forall fun _ h ↦ absurd hcp h
      · have hlt : c.a ⬝ᵥ φ 0 < c.b := by
          simp only [hφ, zero_smul, sub_zero]
          exact lt_of_le_of_ne (hpK.2 c hc) hcp
        have hc' : Continuous fun ε ↦ c.a ⬝ᵥ φ ε := continuous_const.dotProduct hcont
        filter_upwards [hc'.continuousAt.eventually_lt continuousAt_const hlt] with ε hε
        exact fun _ ↦ hε
    filter_upwards [h1, nhdsWithin_le_nhds h2] with ε hε1 hε2
    refine ⟨hε1, ?_, fun c hc ↦ ?_⟩
    · simp only [hφ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sum_sub_distrib, ← mul_sum,
        hpK.1, hqK.1, sub_self, mul_zero, sub_zero]
    · by_cases hcp : c.a ⬝ᵥ p = c.b
      · have hcq := (h c hc).1 hcp
        simp only [hφ, dotProduct_sub, dotProduct_smul, hcp, hcq, sub_self, smul_zero, sub_zero,
          le_refl]
      · exact (hε2 c hc hcp).le
  obtain ⟨ε, hε0, hεK⟩ := hev.exists
  have hseg : p ∈ openSegment ℝ (φ ε) q := by
    refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, by field_simp, ?_⟩
    simp only [hφ]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  exact ((mem_extremePoints.1 hp).2 _ hεK _ hqK hseg).2

theorem finite_extremePoints_hpoly (cs : Finset (Constraint ι)) :
    ((hpoly cs).extremePoints ℝ).Finite := by
  classical
  let T : (ι → ℝ) → Finset (Constraint ι) := fun p ↦ cs.filter fun c ↦ c.a ⬝ᵥ p = c.b
  refine Set.Finite.of_finite_image (f := T) ((cs.powerset.finite_toSet).subset ?_) ?_
  · rintro _ ⟨p, -, rfl⟩
    simp only [T, coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_filter]
    exact fun c hc ↦ hc.1
  · intro p hp q hq hpq
    refine (eq_of_extremePoints_of_tight_eq hp hq fun c hc ↦ ?_).symm
    have := congrArg (c ∈ ·) hpq
    simpa [T, hc] using this

/-- The support function of a compact convex set with finitely many extreme points is the
maximum of the linear forms given by its extreme points. -/
theorem supportFun_eq_maxLin_of_finite {K : Set (ι → ℝ)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hfin : (K.extremePoints ℝ).Finite) :
    supportFun K = maxLin hfin.toFinset := by
  have hKM := closure_convexHull_extremePoints hK hconv
  have hEne : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact hK.extremePoints_nonempty hne
  ext x
  simp only [maxLin, hEne, ↓reduceDIte]
  apply le_antisymm
  · refine supportFun_le hne fun p hp ↦ ?_
    rw [← hKM] at hp
    have hhalf : Convex ℝ {q : ι → ℝ | q ⬝ᵥ x ≤ hfin.toFinset.sup' hEne (· ⬝ᵥ x)} :=
      convex_halfSpace_le ⟨fun _ _ ↦ add_dotProduct _ _ _, fun _ _ ↦ smul_dotProduct _ _ _⟩ _
    have hcl : IsClosed {q : ι → ℝ | q ⬝ᵥ x ≤ hfin.toFinset.sup' hEne (· ⬝ᵥ x)} :=
      isClosed_le (continuous_id.dotProduct continuous_const) continuous_const
    refine closure_minimal (convexHull_min (fun q hq ↦ ?_) hhalf) hcl hp
    exact le_sup' (· ⬝ᵥ x) (by simpa using hq)
  · obtain ⟨e, he, heq⟩ := exists_mem_eq_sup' hEne (· ⬝ᵥ x)
    rw [heq]
    exact le_supportFun hK.isBounded (extremePoints_subset (by simpa using he)) x

theorem supportFun_mem_maxSpan_of_subset {cs : Finset (Constraint ι)}
    (hb : Bornology.IsBounded (hpoly cs)) {g : Constraint ι} (hg : g.IsNonconst)
    (hsub : hpoly cs ⊆ {p | g.a ⬝ᵥ p = g.b}) :
    supportFun (hpoly cs) ∈ maxSpan ι (Fintype.card ι - 1) := by
  classical
  rcases (hpoly cs).eq_empty_or_nonempty with hemp | ⟨p₀, hp₀⟩
  · rw [hemp, supportFun_empty]
    exact zero_mem _
  obtain ⟨i, j, hij⟩ := hg
  have hij' : i ≠ j := fun h ↦ hij (h ▸ rfl)
  have hcard : 2 ≤ Fintype.card ι := Fintype.one_lt_card_iff.2 ⟨i, j, hij'⟩
  let L : (ι → ℝ) →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun d ↦ (∑ k, d k, g.a ⬝ᵥ d)
      map_add' := fun d e ↦ by simp [sum_add_distrib, dotProduct_add]
      map_smul' := fun r d ↦ by simp [mul_sum, dotProduct_smul] }
  have hL : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨s, t⟩
    have hne : g.a i - g.a j ≠ 0 := sub_ne_zero.2 hij
    refine ⟨s • Pi.single i 1 + ((t - s * g.a i) / (g.a i - g.a j)) •
      (Pi.single i 1 - Pi.single j 1), ?_⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq]
    constructor
    · simp [sum_add_distrib, sum_sub_distrib, ← mul_sum]
    · simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, dotProduct_single, smul_eq_mul]
      field_simp
      ring
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  rw [hL, finrank_top, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card] at hrank
  let A : AffineSubspace ℝ (ι → ℝ) := AffineSubspace.mk' p₀ (LinearMap.ker L)
  have hK := isCompact_hpoly hb
  have hfin := finite_extremePoints_hpoly cs
  rw [supportFun_eq_maxLin_of_finite hK (convex_hpoly cs) ⟨p₀, hp₀⟩ hfin]
  have hEA : (hfin.toFinset : Set (ι → ℝ)) ⊆ A := by
    intro e he
    have heK : e ∈ hpoly cs := extremePoints_subset (by simpa using he)
    have h1 : g.a ⬝ᵥ e = g.b := hsub heK
    have h2 : g.a ⬝ᵥ p₀ = g.b := hsub hp₀
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', LinearMap.mem_ker]
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, vsub_eq_sub, Pi.sub_apply, sum_sub_distrib,
      heK.1, hp₀.1, sub_self, dotProduct_sub, h1, h2, Prod.mk_zero_zero]
  have hdim : Module.finrank ℝ A.direction ≤ Fintype.card ι - 2 := by
    rw [AffineSubspace.direction_mk']
    omega
  have := maxLin_mem_maxSpan _ A hEA hdim
  rwa [show Fintype.card ι - 2 + 1 = Fintype.card ι - 1 by omega] at this


/-! ### Cells of a hyperplane arrangement -/

/-- The reversed constraint `⟪a, p⟫ ≥ b`. -/
def Constraint.rev (c : Constraint ι) : Constraint ι :=
  ⟨-c.a, -c.b⟩

theorem Constraint.rev_le_iff (c : Constraint ι) (p : ι → ℝ) :
    c.rev.a ⬝ᵥ p ≤ c.rev.b ↔ c.b ≤ c.a ⬝ᵥ p := by
  simp [Constraint.rev, neg_dotProduct]

/-- The constraints of the cell of the arrangement `F` on the side `≤` of the constraints in `S`
and on the side `≥` of the constraints in `F \ S`. -/
def cellCons (F S : Finset (Constraint ι)) : Finset (Constraint ι) :=
  S ∪ (F \ S).image Constraint.rev

/-- The (closed) cell of the arrangement `F` on the side `≤` of the constraints in `S` and on the
side `≥` of the remaining constraints of `F`. -/
def cell (F S : Finset (Constraint ι)) : Set (ι → ℝ) :=
  {p | (∀ c ∈ S, c.a ⬝ᵥ p ≤ c.b) ∧ ∀ c ∈ F, c ∉ S → c.b ≤ c.a ⬝ᵥ p}

theorem hpoly_union_cellCons (cs F S : Finset (Constraint ι)) :
    hpoly (cs ∪ cellCons F S) = hpoly cs ∩ cell F S := by
  ext p
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, fun c hc ↦ h2 c (mem_union_left _ hc)⟩,
      fun c hc ↦ h2 c (mem_union_right _ (mem_union_left _ hc)), fun c hc hcS ↦ ?_⟩
    refine (c.rev_le_iff p).1 (h2 _ (mem_union_right _ (mem_union_right _ ?_)))
    exact mem_image_of_mem _ (mem_sdiff.2 ⟨hc, hcS⟩)
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, fun c hc ↦ ?_⟩
    rcases mem_union.1 hc with hc | hc
    · exact h2 c hc
    rcases mem_union.1 hc with hc | hc
    · exact h3 c hc
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hc
    exact (d.rev_le_iff p).2 (h4 d (mem_sdiff.1 hd).1 (mem_sdiff.1 hd).2)

theorem hpoly_union_pair_rev (cs : Finset (Constraint ι)) (g : Constraint ι) :
    hpoly (cs ∪ {g, g.rev}) = hpoly cs ∩ {p | g.a ⬝ᵥ p = g.b} := by
  ext p
  simp only [hpoly, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_union, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun c hc ↦ h2 c (Or.inl hc)⟩, le_antisymm (h2 g (Or.inr (Or.inl rfl)))
      ((g.rev_le_iff p).1 (h2 _ (Or.inr (Or.inr rfl))))⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_⟩
    rintro c (hc | rfl | rfl)
    exacts [h2 c hc, h3.le, (g.rev_le_iff p).2 h3.ge]

theorem convex_hpoly_inter_cell (cs F S : Finset (Constraint ι)) :
    Convex ℝ (hpoly cs ∩ cell F S) := by
  rw [← hpoly_union_cellCons]
  exact convex_hpoly _

theorem isCompact_hpoly_inter_cell {cs : Finset (Constraint ι)}
    (hb : Bornology.IsBounded (hpoly cs)) (F S : Finset (Constraint ι)) :
    IsCompact (hpoly cs ∩ cell F S) := by
  rw [← hpoly_union_cellCons]
  exact isCompact_hpoly (by rw [hpoly_union_cellCons]; exact hb.subset Set.inter_subset_left)

theorem supportFun_inter_cell_mem_maxSpan {cs : Finset (Constraint ι)}
    (hb : Bornology.IsBounded (hpoly cs)) {F S : Finset (Constraint ι)} {g : Constraint ι}
    (hg : g.IsNonconst) (hsub : hpoly cs ∩ cell F S ⊆ {p | g.a ⬝ᵥ p = g.b}) :
    supportFun (hpoly cs ∩ cell F S) ∈ maxSpan ι (Fintype.card ι - 1) := by
  rw [← hpoly_union_cellCons] at hsub ⊢
  exact supportFun_mem_maxSpan_of_subset
    (by rw [hpoly_union_cellCons]; exact hb.subset Set.inter_subset_left) hg hsub

theorem cell_empty_empty : cell (∅ : Finset (Constraint ι)) ∅ = Set.univ := by
  ext p
  simp [cell]

theorem cell_insert_of_notMem {F S : Finset (Constraint ι)} {g : Constraint ι} (hgS : g ∉ S) :
    cell (insert g F) S = cell F S ∩ {p | g.b ≤ g.a ⬝ᵥ p} := by
  ext p
  simp only [cell, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_mem_insert]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3⟩, h2 hgS⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    exact ⟨h1, fun _ ↦ h2, h3⟩

theorem cell_insert_insert {F S : Finset (Constraint ι)} {g : Constraint ι} (hgF : g ∉ F) :
    cell (insert g F) (insert g S) = cell F S ∩ {p | g.a ⬝ᵥ p ≤ g.b} := by
  ext p
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun c hc ↦ h1 c (mem_insert_of_mem hc), fun c hc hcS ↦ ?_⟩,
      h1 g (mem_insert_self g S)⟩
    refine h2 c (mem_insert_of_mem hc) ?_
    rw [mem_insert, not_or]
    exact ⟨fun h ↦ hgF (h ▸ hc), hcS⟩
  · rintro ⟨⟨h1, h2⟩, hg1⟩
    refine ⟨fun c hc ↦ ?_, fun c hc hcS ↦ ?_⟩
    · rcases mem_insert.1 hc with rfl | hc
      exacts [hg1, h1 c hc]
    · rw [mem_insert, not_or] at hcS
      rcases mem_insert.1 hc with rfl | hc
      exacts [(hcS.1 rfl).elim, h2 c hc hcS.2]

/-- Iterated cut: the support function of a bounded polytope agrees, modulo
`maxSpan ι (card ι - 1)`, with the sum of the support functions of its intersections with the
cells of an arrangement of nonconstant hyperplanes. -/
theorem supportFun_sub_sum_cell_mem_maxSpan {cs : Finset (Constraint ι)}
    (hb : Bornology.IsBounded (hpoly cs)) (F : Finset (Constraint ι))
    (hF : ∀ g ∈ F, g.IsNonconst) :
    supportFun (hpoly cs) - ∑ S ∈ F.powerset, supportFun (hpoly cs ∩ cell F S) ∈
      maxSpan ι (Fintype.card ι - 1) := by
  induction F using Finset.induction_on with
  | empty => simp [cell_empty_empty]
  | insert g F hgF ih =>
    have ih := ih fun g' hg' ↦ hF g' (mem_insert_of_mem hg')
    have hg := hF g (mem_insert_self g F)
    rw [sum_powerset_insert hgF]
    have key : ∀ S ∈ F.powerset, supportFun (hpoly cs ∩ cell (insert g F) S) +
        supportFun (hpoly cs ∩ cell (insert g F) (insert g S)) =
        supportFun (hpoly cs ∩ cell F S) +
          supportFun (hpoly cs ∩ cell F S ∩ {p | g.a ⬝ᵥ p = g.b}) := by
      intro S hS
      have hgS : g ∉ S := fun h ↦ hgF (mem_powerset.1 hS h)
      have hcut := supportFun_cut (isCompact_hpoly_inter_cell hb F S)
        (convex_hpoly_inter_cell cs F S) g.a g.b
      rw [cell_insert_of_notMem hgS, cell_insert_insert hgF, ← Set.inter_assoc,
        ← Set.inter_assoc, hcut]
      abel
    have hmem : ∑ S ∈ F.powerset, supportFun (hpoly cs ∩ cell F S ∩ {p | g.a ⬝ᵥ p = g.b}) ∈
        maxSpan ι (Fintype.card ι - 1) := by
      refine sum_mem fun S _ ↦ ?_
      rw [← hpoly_union_cellCons, ← hpoly_union_pair_rev]
      refine supportFun_mem_maxSpan_of_subset ?_ hg ?_
      · rw [hpoly_union_pair_rev, hpoly_union_cellCons]
        exact hb.subset (Set.inter_subset_left.trans Set.inter_subset_left)
      · rw [hpoly_union_pair_rev]
        exact Set.inter_subset_right
    rw [← sum_add_distrib, sum_congr rfl key, sum_add_distrib]
    convert sub_mem ih hmem using 1
    abel

/-- A convex set on which each of finitely many affine functions is not identically zero
contains a point at which none of them vanishes. -/
theorem exists_forall_ne_of_convex {C : Set (ι → ℝ)} (hC : Convex ℝ C) (hne : C.Nonempty)
    (G : Finset (Constraint ι)) (hG : ∀ g ∈ G, ∃ q ∈ C, g.a ⬝ᵥ q ≠ g.b) :
    ∃ p ∈ C, ∀ g ∈ G, g.a ⬝ᵥ p ≠ g.b := by
  classical
  induction G using Finset.induction_on with
  | empty =>
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, hp, by simp⟩
  | insert g G hgG ih =>
    obtain ⟨z, hzC, hz⟩ := ih fun g' hg' ↦ hG g' (mem_insert_of_mem hg')
    obtain ⟨q, hqC, hq⟩ := hG g (mem_insert_self g G)
    by_cases hgz : g.a ⬝ᵥ z = g.b
    · set φ : ℝ → ι → ℝ := fun t ↦ z + t • (q - z) with hφ
      have hcont : Continuous φ := by fun_prop
      have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ f ∈ G, f.a ⬝ᵥ φ t ≠ f.b := by
        rw [eventually_all_finset]
        intro f hf
        have : f.a ⬝ᵥ φ 0 ≠ f.b := by simpa [hφ] using hz f hf
        exact ((continuous_const.dotProduct hcont).tendsto 0).eventually_ne this
      have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := eventually_lt_nhds one_pos
      have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
      obtain ⟨t, ht1, ht2, ht3⟩ :=
        (h3.and ((h1.filter_mono nhdsWithin_le_nhds).and
          (h2.filter_mono nhdsWithin_le_nhds))).exists
      refine ⟨φ t, ?_, ?_⟩
      · have := hC hzC hqC (sub_nonneg.2 ht3.le) ht1.le (by ring)
        convert this using 1
        simp only [hφ]
        module
      · rw [forall_mem_insert]
        refine ⟨?_, ht2⟩
        simp only [hφ, dotProduct_add, dotProduct_smul, dotProduct_sub, hgz, smul_eq_mul]
        intro h
        have : t * (g.a ⬝ᵥ q - g.b) = 0 := by linarith
        rcases mul_eq_zero.1 this with h' | h'
        · exact ht1.ne' h'
        · exact hq (sub_eq_zero.1 h')
    · exact ⟨z, hzC, by rw [forall_mem_insert]; exact ⟨hgz, hz⟩⟩

/-- The transfer principle restricted to a single cell of the arrangement `G`. -/
theorem sum_smul_supportFun_inter_cell_mem_maxSpan {κ : Type*} (s : Finset κ) (c : κ → ℝ)
    (cs : κ → Finset (Constraint ι)) (G : Finset (Constraint ι)) (hG : ∀ g ∈ G, g.IsNonconst)
    (hcs : ∀ i ∈ s, cs i ⊆ G) (hbdd : ∀ i ∈ s, Bornology.IsBounded (hpoly (cs i)))
    (hgen : ∀ p : ι → ℝ, ∑ j, p j = 1 → (∀ g ∈ G, g.a ⬝ᵥ p ≠ g.b) →
      ∑ i ∈ s, c i * (hpoly (cs i)).indicator 1 p = 0) (S : Finset (Constraint ι)) :
    ∑ i ∈ s, c i • supportFun (hpoly (cs i) ∩ cell G S) ∈ maxSpan ι (Fintype.card ι - 1) := by
  by_cases hz : ∃ z ∈ hpoly ∅ ∩ cell G S, ∀ g ∈ G, g.a ⬝ᵥ z ≠ g.b
  · obtain ⟨z, ⟨hzH, hzc⟩, hzg⟩ := hz
    have hsum := hgen z hzH.1 hzg
    have key : ∀ i ∈ s, c i • supportFun (hpoly (cs i) ∩ cell G S) -
        (c i * (hpoly (cs i)).indicator 1 z) • supportFun (hpoly ∅ ∩ cell G S) ∈
          maxSpan ι (Fintype.card ι - 1) := by
      intro i hi
      by_cases hzi : z ∈ hpoly (cs i)
      · have heq : hpoly (cs i) ∩ cell G S = hpoly ∅ ∩ cell G S := by
          ext p
          constructor
          · rintro ⟨hp, hpc⟩
            exact ⟨⟨hp.1, by simp⟩, hpc⟩
          · rintro ⟨hp, hpc⟩
            refine ⟨⟨hp.1, fun d hd ↦ ?_⟩, hpc⟩
            have hdG := hcs i hi hd
            have hdS : d ∈ S := by
              by_contra hdS
              exact hzg d hdG (le_antisymm (hzi.2 d hd) (hzc.2 d hdG hdS))
            exact hpc.1 d hdS
        rw [heq, Set.indicator_of_mem hzi, Pi.one_apply, mul_one, sub_self]
        exact zero_mem _
      · rw [Set.indicator_of_notMem hzi, mul_zero, zero_smul, sub_zero]
        refine Submodule.smul_mem _ _ ?_
        have : ∃ d ∈ cs i, d.b < d.a ⬝ᵥ z := by
          by_contra! h
          exact hzi ⟨hzH.1, h⟩
        obtain ⟨d, hd, hdz⟩ := this
        have hdG := hcs i hi hd
        have hdS : d ∉ S := fun h ↦ (hzc.1 d h).not_gt hdz
        refine supportFun_inter_cell_mem_maxSpan (hbdd i hi) (hG d hdG) ?_
        rintro p ⟨hp, hpc⟩
        exact le_antisymm (hp.2 d hd) (hpc.2 d hdG hdS)
    have := sum_mem key
    rwa [sum_sub_distrib, ← sum_smul, hsum, zero_smul, sub_zero] at this
  · push Not at hz
    refine sum_mem fun i hi ↦ Submodule.smul_mem _ _ ?_
    rcases (hpoly (cs i) ∩ cell G S).eq_empty_or_nonempty with hemp | hne
    · rw [hemp, supportFun_empty]
      exact zero_mem _
    · have : ∃ g ∈ G, ∀ q ∈ hpoly (cs i) ∩ cell G S, g.a ⬝ᵥ q = g.b := by
        by_contra! h
        obtain ⟨p, ⟨hp, hpc⟩, hpg⟩ :=
          exists_forall_ne_of_convex (convex_hpoly_inter_cell _ _ _) hne G h
        obtain ⟨g, hg, hgp⟩ := hz p ⟨⟨hp.1, by simp⟩, hpc⟩
        exact hpg g hg hgp
      obtain ⟨g, hg, hgq⟩ := this
      exact supportFun_inter_cell_mem_maxSpan (hbdd i hi) (hG g hg) hgq

/-- **Transfer principle.** Let `G` be a finite set of hyperplanes, none parallel to
`∑ pᵢ = 1`, containing all constraints of the bounded polytopes `hpoly (cs i)`. If
`∑ i, c i * 1_{hpoly (cs i)}` vanishes at every point of `∑ pᵢ = 1` off the hyperplanes in `G`,
then `∑ i, c i • h_{hpoly (cs i)}` is a linear combination of maxima of `card ι - 1` linear forms.
-/
theorem transfer {κ : Type*} (s : Finset κ) (c : κ → ℝ) (cs : κ → Finset (Constraint ι))
    (G : Finset (Constraint ι)) (hG : ∀ g ∈ G, g.IsNonconst) (hcs : ∀ i ∈ s, cs i ⊆ G)
    (hbdd : ∀ i ∈ s, Bornology.IsBounded (hpoly (cs i)))
    (hgen : ∀ p : ι → ℝ, ∑ j, p j = 1 → (∀ g ∈ G, g.a ⬝ᵥ p ≠ g.b) →
      ∑ i ∈ s, c i * (hpoly (cs i)).indicator 1 p = 0) :
    ∑ i ∈ s, c i • supportFun (hpoly (cs i)) ∈ maxSpan ι (Fintype.card ι - 1) := by
  have h1 := sum_mem fun i hi ↦
    Submodule.smul_mem _ (c i) (supportFun_sub_sum_cell_mem_maxSpan (hbdd i hi) G hG)
  have h2 : ∑ S ∈ G.powerset, ∑ i ∈ s, c i • supportFun (hpoly (cs i) ∩ cell G S) ∈
      maxSpan ι (Fintype.card ι - 1) :=
    sum_mem fun S _ ↦ sum_smul_supportFun_inter_cell_mem_maxSpan s c cs G hG hcs hbdd hgen S
  convert add_mem h1 h2 using 1
  simp only [smul_sub, sum_sub_distrib, smul_sum]
  rw [sum_comm (s := s)]
  abel

end
