module

public import TwoHiddenLayers.Pyramid
public import TwoHiddenLayers.Subdivision

/-!
# Counting walks: the thermostat lemma

Fix a vertex `v` and write `V = ι \ {v}`, `m = |V|`. For a generic point `q` of the facet
`{∑ qᵢ = 1, q_v = 0}` with `s` positive coordinates we show

* `thermostat`: `∑_{π, M} (-1)^{|M|} 1_{B_{π,M}}(q) = 1_{E_v}(q) · (-1)^{s-1} s! (m-s)!`,
  where `π` runs over the orderings of `V` and `E_v = Q_{v,∅}`;
* `qcount`: `∑_{∅ ≠ R ⊆ V} c_{|R|} 1_{Q_{v,R}}(q) = 1_{E_v}(q) ∑_{r=1}^{m} c_r (s choose r)`.

We also record that all constraints involved are nonconstant off the apex `v`.
-/

open Finset

@[expose] public noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem mem_orderings {X : Finset ι} {l : List ι} : l ∈ orderings X ↔ l.Nodup ∧ l.toFinset = X := by
  rw [orderings, List.mem_toFinset, List.mem_permutations]
  refine ⟨fun h ↦ ⟨h.nodup_iff.2 X.nodup_toList, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rw [List.toFinset_eq_of_perm _ _ h, toList_toFinset]
  · exact List.perm_of_nodup_nodup_toFinset_eq h₁ X.nodup_toList (by rw [h₂, toList_toFinset])

omit [Fintype ι] in
/-- The empty set has exactly one ordering. -/
@[simp]
theorem orderings_empty : orderings (∅ : Finset ι) = {[]} := by
  simp [orderings]

omit [Fintype ι] in
/-- Decomposing the orderings of a nonempty set according to their first element. -/
theorem sum_orderings_eq {β : Type*} [AddCommMonoid β] {X : Finset ι} (hX : X.Nonempty)
    (F : List ι → β) :
    ∑ l ∈ orderings X, F l = ∑ x ∈ X, ∑ l ∈ orderings (X.erase x), F (x :: l) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun p _ ↦ p.1 :: p.2) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · rintro ⟨x, l⟩ hp
    simp only [mem_sigma, mem_orderings] at hp ⊢
    obtain ⟨hx, hl, hl'⟩ := hp
    refine ⟨List.nodup_cons.2 ⟨fun h ↦ ?_, hl⟩, ?_⟩
    · simpa [hl'] using (List.mem_toFinset.2 h)
    · rw [List.toFinset_cons, hl', insert_erase hx]
  · rintro ⟨x, l⟩ _ ⟨y, l'⟩ _ h
    simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · intro l hl
    rw [mem_orderings] at hl
    obtain ⟨hl, rfl⟩ := hl
    cases l with
    | nil => simp at hX
    | cons x t =>
      refine ⟨⟨x, t⟩, ?_, rfl⟩
      rw [List.nodup_cons] at hl
      simp only [mem_sigma, mem_orderings, List.toFinset_cons, mem_insert, true_or, true_and]
      refine ⟨hl.2, ?_⟩
      rw [erase_insert (by simpa using hl.1)]

/-! ### The walk weight -/

/-- The indicator `1_{[0, 1]}(u)`. -/
private def boxA (u : ℝ) : ℝ := if 0 ≤ u ∧ u ≤ 1 then 1 else 0

/-- The indicator `1_{[-1, 0]}(q_x)`. -/
private def boxD (q : ι → ℝ) (x : ι) : ℝ := if -1 ≤ q x ∧ q x ≤ 0 then 1 else 0

/-- The signed weight of the walks along the list `l`, starting at the level `u`. -/
private def walkW (q : ι → ℝ) : ℝ → List ι → ℝ
  | _, [] => 1
  | u, x :: l => (boxD q x - boxA u) * walkW q (u + q x) l

omit [Fintype ι] in
/-- `boxCons M pre l` only depends on `M ∩ l`. -/
theorem boxCons_congr {M M' : Finset ι} :
    ∀ (pre : Finset ι) (l : List ι), (∀ y ∈ l, y ∈ M ↔ y ∈ M') → boxCons M pre l = boxCons M' pre l
  | _, [], _ => rfl
  | pre, x :: l, h => by
    have hx := h x List.mem_cons_self
    simp only [boxCons, hx, boxCons_congr _ l fun y hy ↦ h y (List.mem_cons_of_mem _ hy)]

/-- Pairing with an indicator vector sums over the set. -/
theorem indVec_dotProduct (S : Finset ι) (q : ι → ℝ) : indVec S ⬝ᵥ q = ∑ i ∈ S, q i := by
  simp [indVec, dotProduct, ite_mul, Finset.sum_ite_mem]

/-- Unfolding one step of the feasibility condition of `boxCons`. -/
theorem forall_boxCons_cons (M pre : Finset ι) (x : ι) (l : List ι) (q : ι → ℝ) :
    (∀ c ∈ boxCons M pre (x :: l), c.a ⬝ᵥ q ≤ c.b) ↔
      (if x ∈ M then 0 ≤ ∑ i ∈ pre, q i ∧ ∑ i ∈ pre, q i ≤ 1 else -1 ≤ q x ∧ q x ≤ 0) ∧
      ∀ c ∈ boxCons M (insert x pre) l, c.a ⬝ᵥ q ≤ c.b := by
  rw [boxCons]
  simp only [mem_union, or_imp, forall_and]
  split_ifs <;>
  simp [indVec_dotProduct, neg_dotProduct, neg_le, and_comm]

private theorem ite_and_one_zero (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℝ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- Inclusion-exclusion over the markings of a list reproduces the walk weight. -/
private theorem sum_boxCons_eq_walkW (q : ι → ℝ) :
    ∀ (l : List ι) (pre : Finset ι), l.Nodup → (∀ x ∈ l, x ∉ pre) →
    ∑ M ∈ l.toFinset.powerset, (-1 : ℝ) ^ M.card *
      (if ∀ c ∈ boxCons M pre l, c.a ⬝ᵥ q ≤ c.b then 1 else 0) = walkW q (∑ i ∈ pre, q i) l
  | [], pre, _, _ => by simp [boxCons, walkW]
  | x :: l, pre, hnd, hpre => by
    rw [List.nodup_cons] at hnd
    have hxl : x ∉ l.toFinset := by simpa using hnd.1
    have hpre' : ∀ y ∈ l, y ∉ insert x pre := by
      intro y hy
      rw [mem_insert, not_or]
      exact ⟨fun h ↦ hnd.1 (h ▸ hy), hpre y (List.mem_cons_of_mem _ hy)⟩
    have hxpre : x ∉ pre := hpre x List.mem_cons_self
    rw [List.toFinset_cons, Finset.sum_powerset_insert hxl, walkW, add_comm _ (q x),
      ← sum_insert hxpre, ← sum_boxCons_eq_walkW q l _ hnd.2 hpre',
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun M hM ↦ ?_
    have hxM : x ∉ M := fun h ↦ hxl (mem_powerset.1 hM h)
    have hcong : boxCons (insert x M) (insert x pre) l = boxCons M (insert x pre) l := by
      refine boxCons_congr _ _ fun y hy ↦ ?_
      have : y ≠ x := fun h ↦ hnd.1 (h ▸ hy)
      simp [this]
    simp only [forall_boxCons_cons, hcong, card_insert_of_notMem hxM, mem_insert_self,
      ite_true, hxM, ite_false, ite_and_one_zero, boxA, boxD]
    ring

/-- The inner sum of the thermostat lemma over the markings of an ordering `h :: t`. -/
private theorem sum_markings_eq_walkW {v : ι} {q : ι → ℝ} (hq : ∑ i, q i = 1) (hqv : q v = 0)
    {h : ι} {t : List ι} (hnd : (h :: t).Nodup) :
    ∑ M ∈ markings (h :: t), (-1 : ℝ) ^ M.card * (facetPoly v (boxConsL M (h :: t))).indicator 1 q =
      walkW q (q h) t := by
  rw [List.nodup_cons] at hnd
  have := sum_boxCons_eq_walkW q t {h} hnd.2 fun x hx ↦ by
    rw [mem_singleton]
    rintro rfl
    exact hnd.1 hx
  rw [sum_singleton] at this
  rw [← this, markings, List.tail_cons]
  refine sum_congr rfl fun M _ ↦ ?_
  simp only [boxConsL, Set.indicator_apply, facetPoly, Set.mem_ofPred_eq, hq, hqv, true_and,
    Pi.one_apply]

/-! ### The closed form of the walk weights -/

/-- The starting level `∑_{V \ X} q` for the walks through `X`. -/
private def lev (v : ι) (q : ι → ℝ) (X : Finset ι) : ℝ := ∑ i ∈ univ.erase v \ X, q i

/-- The total signed weight of the walks through `X`. -/
private def gw (v : ι) (q : ι → ℝ) (X : Finset ι) : ℝ :=
  ∑ l ∈ orderings X, walkW q (lev v q X) l

/-- The indicator that all coordinates in `X` are `> -1`. -/
private def indGt (q : ι → ℝ) (X : Finset ι) : ℝ := if ∀ i ∈ X, -1 < q i then 1 else 0

private theorem lev_erase {v : ι} {q : ι → ℝ} {X : Finset ι} {x : ι} (hx : x ∈ X)
    (hXV : X ⊆ univ.erase v) : lev v q (X.erase x) = lev v q X + q x := by
  rw [lev, lev, sdiff_erase (hXV hx), sum_insert (fun h ↦ (mem_sdiff.1 h).2 hx), add_comm]

private theorem sum_add_lev {v : ι} (q : ι → ℝ) {X : Finset ι} (hXV : X ⊆ univ.erase v) :
    ∑ i ∈ X, q i + lev v q X = ∑ i ∈ univ.erase v, q i := by
  rw [lev, add_comm, sum_sdiff hXV]

private theorem indGt_erase {q : ι → ℝ} {X : Finset ι} {x : ι} (hx : -1 < q x) :
    indGt q (X.erase x) = indGt q X := by
  unfold indGt
  congr 1
  refine propext ⟨fun h i hi ↦ ?_, fun h i hi ↦ h i (mem_of_mem_erase hi)⟩
  by_cases hix : i = x
  · exact hix ▸ hx
  · exact h i (mem_erase.2 ⟨hix, hi⟩)

private theorem gw_eq_sum {v : ι} {q : ι → ℝ} {X : Finset ι} (hX : X.Nonempty)
    (hXV : X ⊆ univ.erase v) :
    gw v q X = ∑ x ∈ X, (boxD q x - boxA (lev v q X)) * gw v q (X.erase x) := by
  rw [gw, sum_orderings_eq hX]
  refine sum_congr rfl fun x hx ↦ ?_
  simp only [walkW, gw, mul_sum, lev_erase hx hXV]

/-- The closed form of the walk weights. -/
private theorem gw_eq {v : ι} {q : ι → ℝ} (hsum : ∑ i ∈ univ.erase v, q i = 1)
    (h0 : ∀ i ∈ univ.erase v, q i ≠ 0) (h1 : ∀ i ∈ univ.erase v, q i ≠ -1)
    (hlev : ∀ X ⊆ univ.erase v, X.Nonempty → X ≠ univ.erase v → lev v q X ≠ 0 ∧ lev v q X ≠ 1)
    (X : Finset ι) (hXV : X ⊆ univ.erase v) (hXne : X ≠ univ.erase v) :
    (0 < lev v q X → gw v q X = (-1) ^ (X.filter fun i ↦ 0 < q i).card *
      ((X.filter fun i ↦ 0 < q i).card.factorial : ℝ) *
      ((X.filter fun i ↦ q i < 0).card.factorial : ℝ) * indGt q X) ∧
    (lev v q X < 0 → X.Nonempty → gw v q X = 0) := by
  induction X using Finset.strongInduction with
  | H X ih =>
  have hsumX := sum_add_lev q hXV
  rw [hsum] at hsumX
  rcases X.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ ↦ ?_, fun _ h ↦ absurd h (by simp)⟩
    simp [gw, walkW, indGt]
  have hl := hlev X hXV hne hXne
  -- facts about the subsets `X.erase x`
  have hsub : ∀ x ∈ X, X.erase x ⊆ univ.erase v := fun x _ ↦ (erase_subset x X).trans hXV
  have hne' : ∀ x ∈ X, X.erase x ≠ univ.erase v := fun x _ h ↦
    hXne (subset_antisymm hXV (h ▸ erase_subset x X))
  have IH := fun x (hx : x ∈ X) ↦ ih (X.erase x) (erase_ssubset hx) (hsub x hx) (hne' x hx)
  have hlev1 : ∀ x ∈ X, lev v q X + q x ≠ 1 → (X.erase x).Nonempty := by
    intro x hx h
    rw [nonempty_iff_ne_empty]
    intro he
    apply h
    rw [← lev_erase hx hXV, he, lev, sdiff_empty, hsum]
  have hq0 : ∀ x ∈ X, q x ≠ 0 := fun x hx ↦ h0 x (hXV hx)
  have hq1 : ∀ x ∈ X, q x ≠ -1 := fun x hx ↦ h1 x (hXV hx)
  rw [gw_eq_sum hne hXV]
  refine ⟨fun hpos ↦ ?_, fun hneg _ ↦ ?_⟩
  swap
  · -- negative level: only steps with `q x < 0` contribute, and they stay negative
    refine sum_eq_zero fun x hx ↦ ?_
    have hA : boxA (lev v q X) = 0 := by
      rw [boxA, ite_eq_right_iff]
      exact fun h ↦ absurd h.1 (not_le.2 hneg)
    unfold boxD
    split_ifs with hD
    · have hx0 : q x < 0 := lt_of_le_of_ne hD.2 (hq0 x hx)
      have hlt : lev v q X + q x < 0 := by linarith
      rw [(IH x hx).2 (by rwa [lev_erase hx hXV]) (hlev1 x hx (by linarith))]
      ring
    · rw [hA]
      ring
  set P := X.filter fun i ↦ 0 < q i with hP
  set N := X.filter fun i ↦ q i < 0 with hN
  rcases lt_or_gt_of_ne hl.2 with hlt1 | hgt1
  · -- level in `(0, 1)`: only the steps with `q x > 0` contribute
    have hA : boxA (lev v q X) = 1 := ite_eq_left ⟨hpos.le, hlt1.le⟩
    have hterm : ∀ x ∈ X, (boxD q x - boxA (lev v q X)) * gw v q (X.erase x) =
        if 0 < q x then -((-1) ^ (P.card - 1) * ((P.card - 1).factorial : ℝ) *
          (N.card.factorial : ℝ) * indGt q X) else 0 := by
      intro x hx
      rw [hA]
      by_cases hx0 : 0 < q x
      · have hD : boxD q x = 0 := ite_eq_right fun h ↦ (h.2.trans_lt hx0).false
        have hxP : x ∈ P := mem_filter.2 ⟨hx, hx0⟩
        have hxN : x ∉ N := fun h ↦ ((mem_filter.1 h).2.trans hx0).false
        rw [ite_eq_left hx0, hD, (IH x hx).1 (by rw [lev_erase hx hXV]; linarith), filter_erase,
          filter_erase, ← hP, ← hN, erase_eq_of_notMem hxN, card_erase_of_mem hxP,
          indGt_erase (by linarith)]
        ring
      · have hx0' : q x < 0 := lt_of_le_of_ne (not_lt.1 hx0) (hq0 x hx)
        rw [ite_eq_right hx0]
        by_cases hx1 : -1 < q x
        · have hD : boxD q x = 1 := ite_eq_left ⟨hx1.le, hx0'.le⟩
          rw [hD]
          ring
        · have hx1' : q x < -1 := lt_of_le_of_ne (not_lt.1 hx1) (hq1 x hx)
          have hD : boxD q x = 0 := ite_eq_right fun h ↦ (h.1.trans_lt hx1').false
          rw [hD, (IH x hx).2 (by rw [lev_erase hx hXV]; linarith)
            (hlev1 x hx (by linarith))]
          ring
    rw [sum_congr rfl hterm, ← sum_filter, ← hP, sum_const, nsmul_eq_mul]
    have hPpos : 0 < P.card := by
      rw [card_pos]
      by_contra h
      rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
      have : ∑ i ∈ X, q i ≤ 0 := sum_nonpos fun i hi ↦ not_lt.1 (h hi)
      linarith
    obtain ⟨k, hk⟩ : ∃ k, P.card = k + 1 := ⟨P.card - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    ring
  · -- level `> 1`: only the steps with `-1 < q x < 0` contribute
    have hA : boxA (lev v q X) = 0 := ite_eq_right fun h ↦ (h.2.trans_lt hgt1).false
    have hterm : ∀ x ∈ X, (boxD q x - boxA (lev v q X)) * gw v q (X.erase x) =
        if -1 < q x ∧ q x < 0 then (-1) ^ P.card * (P.card.factorial : ℝ) *
          ((N.card - 1).factorial : ℝ) * indGt q X else 0 := by
      intro x hx
      rw [hA]
      by_cases hx' : -1 < q x ∧ q x < 0
      · have hD : boxD q x = 1 := ite_eq_left ⟨hx'.1.le, hx'.2.le⟩
        have hxN : x ∈ N := mem_filter.2 ⟨hx, hx'.2⟩
        have hxP : x ∉ P := fun h ↦ ((mem_filter.1 h).2.trans hx'.2).false
        rw [ite_eq_left hx', hD, (IH x hx).1 (by rw [lev_erase hx hXV]; linarith), filter_erase,
          filter_erase, ← hP, ← hN, erase_eq_of_notMem hxP, card_erase_of_mem hxN,
          indGt_erase hx'.1]
        ring
      · have hD : boxD q x = 0 := by
          refine ite_eq_right fun h ↦ hx' ⟨lt_of_le_of_ne h.1 (hq1 x hx).symm,
            lt_of_le_of_ne h.2 (hq0 x hx)⟩
        rw [ite_eq_right hx', hD]
        ring
    rw [sum_congr rfl hterm, ← sum_filter, sum_const, nsmul_eq_mul]
    by_cases hI : ∀ i ∈ X, -1 < q i
    · have hfN : (X.filter fun x ↦ -1 < q x ∧ q x < 0) = N := by
        refine filter_congr fun x hx ↦ ?_
        simp [hI x hx]
      have hNpos : 0 < N.card := by
        rw [card_pos]
        by_contra h
        rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
        have : 0 ≤ ∑ i ∈ X, q i := sum_nonneg fun i hi ↦ not_lt.1 (h hi)
        linarith
      obtain ⟨k, hk⟩ : ∃ k, N.card = k + 1 := ⟨N.card - 1, by omega⟩
      rw [hfN, hk, Nat.add_sub_cancel, Nat.factorial_succ]
      push_cast
      ring
    · simp [indGt, hI]

/-! ### Genericity -/

/-- Membership in the dilated facet `Q_{v,R}`. -/
theorem mem_facetPoly_qCons {v : ι} {R : Finset ι} {q : ι → ℝ} :
    q ∈ facetPoly v (qCons v R) ↔ ∑ i, q i = 1 ∧ q v = 0 ∧
      ∀ i ∈ univ.erase v, if i ∈ R then 0 ≤ q i else -1 ≤ q i := by
  simp only [facetPoly, qCons, Set.mem_ofPred_eq, forall_mem_image]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall₂_congr fun i _ ↦ ?_
  split_ifs <;> simp [neg_dotProduct, neg_le]

/-- Consequences of the genericity of `q`. -/
private theorem generic_facts {v : ι} {q : ι → ℝ} (hgen : ∀ g ∈ facetGen v, g.a ⬝ᵥ q ≠ g.b) :
    (∀ i ∈ univ.erase v, q i ≠ 0) ∧ (∀ i ∈ univ.erase v, q i ≠ -1) ∧
    ∀ X ⊆ univ.erase v, X.Nonempty → X ≠ univ.erase v → lev v q X ≠ 0 ∧ lev v q X ≠ 1 := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_, fun X hXV hX hXne ↦ ?_⟩
  · have := hgen ⟨Pi.single i 1, 0⟩ (by
      unfold facetGen
      exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_image_of_mem _ hi))))
    simpa [single_one_dotProduct] using this
  · have := hgen ⟨Pi.single i 1, -1⟩ (by
      unfold facetGen
      exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hi))))
    simpa [single_one_dotProduct] using this
  · have hS : (univ.erase v \ X) ∈ (univ.erase v).powerset.filter
        fun S ↦ S.Nonempty ∧ S ≠ univ.erase v := by
      refine mem_filter.2 ⟨mem_powerset.2 sdiff_subset, ?_, fun h ↦ ?_⟩
      · rw [sdiff_nonempty]
        exact fun h ↦ hXne (subset_antisymm hXV h)
      · obtain ⟨x, hx⟩ := hX
        have := h.symm ▸ hXV hx
        exact (mem_sdiff.1 this).2 hx
    have h₀ := hgen ⟨indVec (univ.erase v \ X), 0⟩ (by
      unfold facetGen
      exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hS)))
    have h₁ := hgen ⟨indVec (univ.erase v \ X), 1⟩ (by
      unfold facetGen
      exact mem_union_right _ (mem_image_of_mem _ hS))
    simp only [indVec_dotProduct] at h₀ h₁
    exact ⟨h₀, h₁⟩

private theorem indicator_qCons_empty {v : ι} {q : ι → ℝ} (hq : ∑ i, q i = 1) (hqv : q v = 0)
    (h1 : ∀ i ∈ univ.erase v, q i ≠ -1) :
    (facetPoly v (qCons v ∅)).indicator 1 q = indGt q (univ.erase v) := by
  have : q ∈ facetPoly v (qCons v ∅) ↔ ∀ i ∈ univ.erase v, -1 < q i := by
    simp only [mem_facetPoly_qCons, hq, hqv, notMem_empty, ite_false, true_and]
    exact forall₂_congr fun i hi ↦ ⟨fun h ↦ lt_of_le_of_ne h (h1 i hi).symm, le_of_lt⟩
  by_cases h : ∀ i ∈ univ.erase v, -1 < q i
  · rw [Set.indicator_of_mem (this.2 h), indGt, ite_eq_left h, Pi.one_apply]
  · rw [Set.indicator_of_notMem (mt this.1 h), indGt, ite_eq_right h]

theorem thermostat {v : ι} (hn : 3 ≤ Fintype.card ι) {q : ι → ℝ} (hq : ∑ i, q i = 1)
    (hqv : q v = 0) (hgen : ∀ g ∈ facetGen v, g.a ⬝ᵥ q ≠ g.b) :
    ∑ l ∈ orderings (univ.erase v), ∑ M ∈ markings l,
        (-1 : ℝ) ^ M.card * (facetPoly v (boxConsL M l)).indicator 1 q =
      (facetPoly v (qCons v ∅)).indicator 1 q *
        psi (Fintype.card ι - 1) ((univ.erase v).filter fun i ↦ 0 < q i).card := by
  obtain ⟨h0, h1, hlev⟩ := generic_facts hgen
  have hsum : ∑ i ∈ univ.erase v, q i = 1 := by rw [sum_erase _ hqv, hq]
  have hcardV : (univ.erase v).card = Fintype.card ι - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ]
  have hVne : (univ.erase v).Nonempty := by
    rw [← card_pos]
    omega
  set P := (univ.erase v).filter fun i ↦ 0 < q i with hP
  set N := (univ.erase v).filter fun i ↦ q i < 0 with hN
  have hPN : N.card = Fintype.card ι - 1 - P.card := by
    have hNeq : N = (univ.erase v).filter fun i ↦ ¬ 0 < q i :=
      filter_congr fun i hi ↦ ⟨fun h ↦ not_lt.2 h.le,
        fun h ↦ lt_of_le_of_ne (not_lt.1 h) (h0 i hi)⟩
    have := card_filter_add_card_filter_not (s := univ.erase v) (fun i ↦ 0 < q i)
    rw [hNeq, ← hcardV, ← this, ← hP]
    omega
  have hgw : ∀ h ∈ univ.erase v, ∑ t ∈ orderings ((univ.erase v).erase h), ∑ M ∈ markings (h :: t),
      (-1 : ℝ) ^ M.card * (facetPoly v (boxConsL M (h :: t))).indicator 1 q =
      if 0 < q h then (-1) ^ (P.card - 1) * ((P.card - 1).factorial : ℝ) *
        (N.card.factorial : ℝ) * indGt q (univ.erase v) else 0 := by
    intro h hh
    have hlevh : lev v q ((univ.erase v).erase h) = q h := by
      rw [lev, sdiff_erase_self hh, sum_singleton]
    have hne : (univ.erase v).erase h ≠ univ.erase v := fun H ↦
      notMem_erase h (univ.erase v) (by rw [H]; exact hh)
    have key := gw_eq hsum h0 h1 hlev _ (erase_subset _ _) hne
    have hsw : ∑ t ∈ orderings ((univ.erase v).erase h), ∑ M ∈ markings (h :: t),
        (-1 : ℝ) ^ M.card * (facetPoly v (boxConsL M (h :: t))).indicator 1 q =
        gw v q ((univ.erase v).erase h) := by
      rw [gw, hlevh]
      refine sum_congr rfl fun t ht ↦ ?_
      obtain ⟨hnd, hto⟩ := mem_orderings.1 ht
      refine sum_markings_eq_walkW hq hqv (List.nodup_cons.2 ⟨fun H ↦ ?_, hnd⟩)
      have := List.mem_toFinset.2 H
      rw [hto] at this
      exact notMem_erase h _ this
    rw [hsw]
    by_cases hpos : 0 < q h
    · have hhP : h ∈ P := mem_filter.2 ⟨hh, hpos⟩
      have hhN : h ∉ N := fun H ↦ ((mem_filter.1 H).2.trans hpos).false
      rw [ite_eq_left hpos, key.1 (hlevh ▸ hpos), filter_erase _ h (univ.erase v),
        filter_erase _ h (univ.erase v), ← hP, ← hN,
        erase_eq_of_notMem hhN, card_erase_of_mem hhP, indGt_erase (by linarith)]
    · have hneg : q h < 0 := lt_of_le_of_ne (not_lt.1 hpos) (h0 h hh)
      have hne' : ((univ.erase v).erase h).Nonempty := by
        rw [← card_pos, card_erase_of_mem hh]
        omega
      rw [ite_eq_right hpos, key.2 (hlevh ▸ hneg) hne']
  rw [sum_orderings_eq hVne, sum_congr rfl hgw, ← sum_filter, ← hP, sum_const, nsmul_eq_mul,
    indicator_qCons_empty hq hqv h1, psi, ← hPN]
  have hPpos : 0 < P.card := by
    rw [card_pos]
    by_contra h
    rw [not_nonempty_iff_eq_empty, filter_eq_empty_iff] at h
    have : ∑ i ∈ univ.erase v, q i ≤ 0 := sum_nonpos fun i hi ↦ not_lt.1 (h hi)
    linarith
  obtain ⟨k, hk⟩ : ∃ k, P.card = k + 1 := ⟨P.card - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- Counting the nonempty subsets of a finite set according to their cardinality. -/
theorem sum_powerset_nonempty_apply_card (c : ℕ → ℝ) (S : Finset ι) {m : ℕ} (hm : S.card ≤ m) :
    ∑ R ∈ S.powerset.filter (·.Nonempty), c R.card =
      ∑ r ∈ Icc 1 m, c r * (S.card.choose r : ℝ) := by
  set g : ℕ → ℝ := fun k ↦ if k = 0 then 0 else c k with hg
  have h₁ : ∀ R ∈ S.powerset, (if R.Nonempty then c R.card else 0) = g R.card := by
    intro R _
    simp only [hg, card_eq_zero, ← not_nonempty_iff_eq_empty]
    split_ifs <;> simp_all
  rw [sum_filter, sum_congr rfl h₁, sum_powerset_apply_card]
  calc ∑ k ∈ range (S.card + 1), S.card.choose k • g k
      = ∑ k ∈ range (m + 1), S.card.choose k • g k := by
        refine sum_subset (range_subset_range.2 (by omega)) fun k _ hk ↦ ?_
        rw [mem_range, not_lt] at hk
        rw [Nat.choose_eq_zero_of_lt (by omega), zero_smul]
    _ = ∑ k ∈ Icc 1 m, S.card.choose k • g k := by
        refine (sum_subset (fun k hk ↦ ?_) fun k hk hk' ↦ ?_).symm
        · rw [mem_Icc] at hk
          rw [mem_range]
          omega
        · have : k = 0 := by
            rw [mem_range] at hk
            rw [mem_Icc] at hk'
            omega
          simp [this, hg]
    _ = ∑ r ∈ Icc 1 m, c r * (S.card.choose r : ℝ) := by
        refine sum_congr rfl fun k hk ↦ ?_
        have : k ≠ 0 := by
          rw [mem_Icc] at hk
          omega
        simp [hg, this, nsmul_eq_mul, mul_comm]

theorem qcount {v : ι} (c : ℕ → ℝ) {q : ι → ℝ} (hgen : ∀ g ∈ facetGen v, g.a ⬝ᵥ q ≠ g.b) :
    ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
        c R.card * (facetPoly v (qCons v R)).indicator 1 q =
      (facetPoly v (qCons v ∅)).indicator 1 q *
        ∑ r ∈ Icc 1 (Fintype.card ι - 1),
          c r * (((univ.erase v).filter fun i ↦ 0 < q i).card.choose r : ℝ) := by
  obtain ⟨h0, -, -⟩ := generic_facts hgen
  set Pos := (univ.erase v).filter fun i ↦ 0 < q i with hPos
  have hmem : ∀ R ⊆ univ.erase v, (facetPoly v (qCons v R)).indicator (1 : (ι → ℝ) → ℝ) q =
      (facetPoly v (qCons v ∅)).indicator 1 q * if R ⊆ Pos then 1 else 0 := by
    intro R hR
    have key : q ∈ facetPoly v (qCons v R) ↔ q ∈ facetPoly v (qCons v ∅) ∧ R ⊆ Pos := by
      simp only [mem_facetPoly_qCons, notMem_empty, ite_false]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨h1, h2, fun i hi ↦ ?_⟩, fun i hiR ↦ ?_⟩
        · have := h3 i hi
          split_ifs at this
          · linarith
          · exact this
        · have := h3 i (hR hiR)
          rw [ite_eq_left hiR] at this
          exact mem_filter.2 ⟨hR hiR, lt_of_le_of_ne this (h0 i (hR hiR)).symm⟩
      · rintro ⟨⟨h1, h2, h3⟩, hRP⟩
        refine ⟨h1, h2, fun i hi ↦ ?_⟩
        split_ifs with hiR
        · exact (mem_filter.1 (hRP hiR)).2.le
        · exact h3 i hi
    by_cases ha : q ∈ facetPoly v (qCons v ∅) <;> by_cases hb : R ⊆ Pos <;>
      simp [key, ha, hb]
  have hsub : Pos ⊆ univ.erase v := filter_subset _ _
  have hcard : Pos.card ≤ Fintype.card ι - 1 := by
    have := card_le_card hsub
    rwa [card_erase_of_mem (mem_univ _), card_univ] at this
  rw [← sum_powerset_nonempty_apply_card c Pos hcard, mul_sum]
  calc _ = ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
          if R ⊆ Pos then (facetPoly v (qCons v ∅)).indicator 1 q * c R.card else 0 := by
        refine sum_congr rfl fun R hR ↦ ?_
        simp only [hmem R (mem_powerset.1 (mem_filter.1 hR).1)]
        split_ifs <;> ring
    _ = _ := by
        rw [← sum_filter]
        refine sum_congr ?_ fun _ _ ↦ rfl
        ext R
        simp only [mem_filter, mem_powerset]
        exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨h.1.trans hsub, h.2⟩, h.1⟩⟩

/-! ### Nonconstancy of the constraints -/

omit [DecidableEq ι] in
private theorem exists_ne_ne (hn : 3 ≤ Fintype.card ι) (i v : ι) : ∃ j, j ≠ i ∧ j ≠ v := by
  classical
  obtain ⟨j, -, hj⟩ := exists_mem_notMem_of_card_lt_card (s := {i, v}) (t := univ) (by
    rw [card_univ]
    exact card_le_two.trans_lt (by omega))
  simp only [mem_insert, mem_singleton, not_or] at hj
  exact ⟨j, hj.1, hj.2⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem nonconst_neg {v : ι} {a : ι → ℝ} (h : ∃ i j, i ≠ v ∧ j ≠ v ∧ a i ≠ a j) :
    ∃ i j, i ≠ v ∧ j ≠ v ∧ (-a) i ≠ (-a) j := by
  obtain ⟨i, j, hi, hj, h⟩ := h
  exact ⟨i, j, hi, hj, by simpa using h⟩

private theorem nonconst_single {v x : ι} (hx : x ≠ v) (hn : 3 ≤ Fintype.card ι) :
    ∃ i j, i ≠ v ∧ j ≠ v ∧ (Pi.single x 1 : ι → ℝ) i ≠ (Pi.single x 1 : ι → ℝ) j := by
  obtain ⟨j, hjx, hjv⟩ := exists_ne_ne hn x v
  exact ⟨x, j, hx, hjv, by simp [Pi.single_eq_of_ne hjx]⟩

omit [Fintype ι] in
private theorem nonconst_indVec {v i j : ι} {S : Finset ι} (hi : i ∈ S) (hj : j ∉ S) (hiv : i ≠ v)
    (hjv : j ≠ v) : ∃ i j, i ≠ v ∧ j ≠ v ∧ indVec S i ≠ indVec S j :=
  ⟨i, j, hiv, hjv, by simp [indVec, hi, hj]⟩

theorem nonconst_facetGen {v : ι} {g : Constraint ι} (hg : g ∈ facetGen v)
    (hn : 3 ≤ Fintype.card ι) : ∃ i j, i ≠ v ∧ j ≠ v ∧ g.a i ≠ g.a j := by
  unfold facetGen at hg
  simp only [mem_union, mem_image, mem_filter, mem_powerset] at hg
  rcases hg with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨S, ⟨hSV, hSne, hSV'⟩, rfl⟩) |
      ⟨S, ⟨hSV, hSne, hSV'⟩, rfl⟩
  · exact nonconst_single (mem_erase.1 hi).1 hn
  · exact nonconst_single (mem_erase.1 hi).1 hn
  all_goals
    obtain ⟨i, hi⟩ := hSne
    obtain ⟨j, hj, hjS⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hSV hSV')
    exact nonconst_indVec hi hjS (mem_erase.1 (hSV hi)).1 (mem_erase.1 hj).1

theorem nonconst_qCons {v : ι} {R : Finset ι} {g : Constraint ι} (hg : g ∈ qCons v R)
    (hn : 3 ≤ Fintype.card ι) : ∃ i j, i ≠ v ∧ j ≠ v ∧ g.a i ≠ g.a j := by
  unfold qCons at hg
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hg
  have := nonconst_neg (nonconst_single (mem_erase.1 hi).1 hn)
  by_cases hiR : i ∈ R <;> simp only [hiR, ite_true, ite_false] <;> exact this

private theorem nonconst_boxCons {v : ι} (hn : 3 ≤ Fintype.card ι) (M : Finset ι)
    {g : Constraint ι} : ∀ (pre : Finset ι) (t : List ι), pre.Nonempty → pre ⊆ univ.erase v →
    t.Nodup → (∀ x ∈ t, x ∈ univ.erase v ∧ x ∉ pre) → g ∈ boxCons M pre t →
    ∃ i j, i ≠ v ∧ j ≠ v ∧ g.a i ≠ g.a j
  | _, [], _, _, _, _, hg => by simp [boxCons] at hg
  | pre, x :: t, hne, hpre, hnd, ht, hg => by
    rw [boxCons, mem_union] at hg
    obtain ⟨hxV, hxpre⟩ := ht x List.mem_cons_self
    have hxv := (mem_erase.1 hxV).1
    rcases hg with hg | hg
    · split_ifs at hg
      · obtain ⟨i, hi⟩ := hne
        have h := nonconst_indVec hi hxpre (mem_erase.1 (hpre hi)).1 hxv
        rw [mem_insert, mem_singleton] at hg
        rcases hg with rfl | rfl
        · exact nonconst_neg h
        · exact h
      · rw [mem_insert, mem_singleton] at hg
        rcases hg with rfl | rfl
        · exact nonconst_neg (nonconst_single hxv hn)
        · exact nonconst_single hxv hn
    · rw [List.nodup_cons] at hnd
      refine nonconst_boxCons hn M (insert x pre) t (insert_nonempty _ _)
        (insert_subset hxV hpre) hnd.2 (fun y hy ↦ ?_) hg
      obtain ⟨hyV, hypre⟩ := ht y (List.mem_cons_of_mem _ hy)
      refine ⟨hyV, ?_⟩
      rw [mem_insert, not_or]
      exact ⟨fun h ↦ hnd.1 (h ▸ hy), hypre⟩

theorem nonconst_boxConsL {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v))
    (M : Finset ι) {g : Constraint ι} (hg : g ∈ boxConsL M l) (hn : 3 ≤ Fintype.card ι) :
    ∃ i j, i ≠ v ∧ j ≠ v ∧ g.a i ≠ g.a j := by
  obtain ⟨hnd, hl⟩ := mem_orderings.1 hl
  cases l with
  | nil => simp [boxConsL] at hg
  | cons h t =>
    rw [List.nodup_cons] at hnd
    have hmem : ∀ y ∈ h :: t, y ∈ univ.erase v := fun y hy ↦ hl ▸ List.mem_toFinset.2 hy
    refine nonconst_boxCons hn M {h} t (singleton_nonempty _)
      (singleton_subset_iff.2 (hmem h List.mem_cons_self)) hnd.2 (fun y hy ↦ ?_) hg
    refine ⟨hmem y (List.mem_cons_of_mem _ hy), ?_⟩
    rw [mem_singleton]
    rintro rfl
    exact hnd.1 hy

end
