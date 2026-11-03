module

public import TwoHiddenLayers.Box

/-!
# Two hidden ReLU layers compute the maximum

We assemble the proof that `max (x₁, …, xₙ)` lies in `reluNet (Fin n) 2`, i.e. can be computed by a
ReLU network with two hidden layers.

The proof is by induction on `n`. For `n ≥ 3`, the thermostat lemma, the count of the dilated
facets and coning show that for every vertex `v` the signed sum of the paramids
`pyr_{e_v}(B_{v,π,M})` agrees with a combination of the cones `pyr_{e_v}(Q_{v,R})` modulo maxima of
`n - 1` linear forms. Summing over `v` and using the subdivision lemma, the paramids sum to
`(-1)^n n! · max` modulo maxima of `n - 1` linear forms, which are handled by induction.

## Main results

* `max_mem_reluNet`: `max (x₁, …, xₙ)` lies in `reluNet (Fin n) 2`.
* `exists_twoLayerNet_eq_max`: there is an explicit ReLU network with two hidden layers computing
  `max (x₁, …, xₙ)`.
-/

open Finset

@[expose] public noncomputable section

/-- Coefficients expressing `psi m` in the basis `s ↦ (s choose r)`, defined by the triangular
recursion `a_r = psi m r - ∑_{k < r} a_k (r choose k)` (with `a_0 = 0`). -/
def coeffs (m : ℕ) (r : ℕ) : ℝ :=
  if r = 0 then 0 else psi m r - ∑ k : Fin r, coeffs m k * (r.choose k : ℝ)
decreasing_by exact k.isLt

theorem sum_range_coeffs_mul_choose (m : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    ∑ r ∈ range (s + 1), coeffs m r * (s.choose r : ℝ) = psi m s := by
  rw [sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one]
  conv_rhs => rw [show psi m s = coeffs m s + ∑ k : Fin s, coeffs m k * (s.choose k : ℝ) by
    rw [coeffs, ite_eq_right (by omega)]; ring]
  rw [add_comm, Fin.sum_univ_eq_sum_range (fun k ↦ coeffs m k * (s.choose k : ℝ))]

theorem sum_coeffs_mul_choose (m : ℕ) {s : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m) :
    ∑ r ∈ Icc 1 m, coeffs m r * (s.choose r : ℝ) = psi m s := by
  rw [← sum_range_coeffs_mul_choose m hs]
  have hsub : Icc 1 s ⊆ Icc 1 m := Icc_subset_Icc le_rfl hsm
  rw [← sum_subset hsub, ← sum_subset (s₁ := Icc 1 s) (s₂ := range (s + 1))]
  · intro r hr
    simp only [mem_Icc, mem_range] at hr ⊢
    omega
  · intro r hr hr'
    simp only [mem_Icc, mem_range, not_and_or, not_le] at hr hr'
    have : r = 0 := by omega
    subst this
    simp [coeffs]
  · intro r hr hr'
    simp only [mem_Icc, not_and_or, not_le] at hr hr'
    have : s < r := by omega
    simp [Nat.choose_eq_zero_of_lt this]

theorem psi_self_ne_zero (m : ℕ) : psi m m ≠ 0 := by
  simp [psi, Nat.factorial_ne_zero]

theorem sum_filter_nonempty_coeffs {ι : Type*} {X : Finset ι} {m : ℕ} (hX : X.card = m)
    (hm : 1 ≤ m) :
    ∑ R ∈ X.powerset.filter (·.Nonempty), coeffs m R.card = psi m m := by
  rw [sum_filter_of_ne fun R _ h ↦ ?_]
  · rw [sum_powerset_apply_card, hX, ← sum_range_coeffs_mul_choose m hm]
    simp [nsmul_eq_mul, mul_comm]
  · rw [nonempty_iff_ne_empty]
    rintro rfl
    simp [coeffs] at h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reindexing pairs `(v, R)` with `∅ ≠ R ⊆ ι \ {v}`. -/
theorem sum_sum_powerset_erase_comm {β : Type*} [AddCommMonoid β] (f : ι → Finset ι → β) :
    ∑ v, ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty), f v R =
      ∑ R ∈ univ.powerset.filter (fun R : Finset ι ↦ R.Nonempty ∧ R ≠ univ), ∑ v ∈ Rᶜ, f v R := by
  refine sum_comm' fun v R ↦ ?_
  simp only [mem_filter, mem_powerset, mem_univ, true_and, mem_compl]
  constructor
  · rintro ⟨hRv, hR⟩
    have hv : v ∉ R := fun h ↦ by simpa using hRv h
    exact ⟨hv, subset_univ _, hR, fun h ↦ hv (h ▸ mem_univ v)⟩
  · rintro ⟨hv, -, hR, -⟩
    exact ⟨fun x hx ↦ mem_erase.2 ⟨fun h ↦ hv (h ▸ hx), mem_univ _⟩, hR⟩

/-- The per-vertex identity: the signed paramids with apex `e_v` agree with a combination of the
coned dilated facets modulo maxima of `card ι - 1` linear forms. -/
theorem vertex_identity (hn : 3 ≤ Fintype.card ι) (v : ι) :
    (∑ lM ∈ (orderings (univ.erase v)).sigma markings,
        (-1 : ℝ) ^ lM.2.card • supportFun (pyr v (boxConsL lM.2 lM.1))) -
      ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
        coeffs (Fintype.card ι - 1) R.card • supportFun (pyr v (qCons v R)) ∈
      maxSpan ι (Fintype.card ι - 1) := by
  set m := Fintype.card ι - 1
  set S₁ := (orderings (univ.erase v)).sigma markings
  set S₂ := (univ.erase v).powerset.filter (·.Nonempty)
  set Gf := facetGen v ∪ S₁.biUnion (fun lM ↦ boxConsL lM.2 lM.1) ∪ S₂.biUnion (qCons v)
  set coef : (Σ _ : List ι, Finset ι) ⊕ Finset ι → ℝ :=
    Sum.elim (fun lM ↦ (-1 : ℝ) ^ lM.2.card) (fun R ↦ -coeffs m R.card)
  set csf : (Σ _ : List ι, Finset ι) ⊕ Finset ι → Finset (Constraint ι) :=
    Sum.elim (fun lM ↦ boxConsL lM.2 lM.1) (fun R ↦ qCons v R)
  have hS₁ : ∀ lM ∈ S₁, lM.1 ∈ orderings (univ.erase v) := fun lM h ↦ (mem_sigma.1 h).1
  have hcsf : ∀ i ∈ S₁.disjSum S₂, csf i ⊆ Gf := by
    rintro (lM | R) h
    · simp only [inl_mem_disjSum] at h
      exact (subset_biUnion_of_mem (fun lM : Σ _ : List ι, Finset ι ↦ boxConsL lM.2 lM.1) h).trans
        (subset_union_right.trans subset_union_left)
    · simp only [inr_mem_disjSum] at h
      exact (subset_biUnion_of_mem (qCons v) h).trans subset_union_right
  have hfacet : ∀ q : ι → ℝ, ∑ j, q j = 1 → q v = 0 → (∀ g ∈ Gf, g.a ⬝ᵥ q ≠ g.b) →
      ∑ i ∈ S₁.disjSum S₂, coef i * (facetPoly v (csf i)).indicator 1 q = 0 := by
    intro q hq hqv hqG
    have hgen : ∀ g ∈ facetGen v, g.a ⬝ᵥ q ≠ g.b := fun g hg ↦
      hqG g (mem_union_left _ (mem_union_left _ hg))
    rw [sum_disjSum]
    simp only [coef, csf, Sum.elim_inl, Sum.elim_inr, neg_mul, sum_neg_distrib]
    rw [sum_sigma, thermostat hn hq hqv hgen, qcount _ hgen, ← sub_eq_add_neg, ← mul_sub,
      sub_eq_zero.2, mul_zero]
    set s := ((univ.erase v).filter fun i ↦ 0 < q i).card
    refine (sum_coeffs_mul_choose m ?_ ?_).symm
    · rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, filter_eq_empty_iff]
      intro h
      have : ∑ j, q j ≤ 0 := by
        rw [← add_sum_erase _ _ (mem_univ v), hqv, zero_add]
        exact sum_nonpos fun i hi ↦ not_lt.1 (h hi)
      linarith
    · exact (card_filter_le _ _).trans (by rw [card_erase_of_mem (mem_univ v), card_univ])
  have hT := transfer (S₁.disjSum S₂) coef (fun i ↦ pyrCons v (csf i)) (pyrCons v Gf)
    (isNonconst_of_mem_pyrCons (fun g hg ↦ by
      simp only [Gf, mem_union, mem_biUnion] at hg
      rcases hg with (hg | ⟨lM, hlM, hg⟩) | ⟨R, -, hg⟩
      · exact nonconst_facetGen hg hn
      · exact nonconst_boxConsL (hS₁ lM hlM) _ hg hn
      · exact nonconst_qCons hg hn) (by omega))
    (fun i hi ↦ pyrCons_mono (hcsf i hi))
    (by
      rintro (lM | R) h
      · simp only [inl_mem_disjSum] at h
        exact isBounded_pyr (box_nonempty (hS₁ lM h) _ (by omega)) (isBounded_box (hS₁ lM h) _
          (by omega))
      · exact isBounded_pyr (facetPoly_qCons_nonempty (by omega) R)
          (isBounded_facetPoly_qCons v R))
    (fun p hp hpG ↦ pyr_generic v _ coef csf Gf hfacet p hp hpG)
  rw [sum_disjSum] at hT
  simpa [coef, csf, sub_eq_add_neg, neg_smul, pyr] using hT

/-- The main step: for `card ι ≥ 3`, if maxima of `card ι - 1` linear forms are computable with
two hidden layers, then so is `max (x_i)_i`. -/
theorem supportFun_simplex_mem_reluNet (hn : 3 ≤ Fintype.card ι)
    (hL : maxSpan ι (Fintype.card ι - 1) ≤ reluNet ι 2) :
    supportFun (simplex : Set (ι → ℝ)) ∈ reluNet ι 2 := by
  set m := Fintype.card ι - 1
  set T := univ.powerset.filter fun R : Finset ι ↦ R.Nonempty ∧ R ≠ univ
  -- the paramid sum
  set P : (ι → ℝ) → ℝ := ∑ v, ∑ lM ∈ (orderings (univ.erase v)).sigma markings,
    (-1 : ℝ) ^ lM.2.card • supportFun (pyr v (boxConsL lM.2 lM.1))
  have hP : P ∈ reluNet ι 2 := by
    refine Submodule.sum_mem _ fun v _ ↦ Submodule.sum_mem _ fun lM hlM ↦ ?_
    have hl := (mem_sigma.1 hlM).1
    refine Submodule.smul_mem _ _ ?_
    have : supportFun (pyr v (boxConsL lM.2 lM.1)) =
        fun x ↦ max ((Pi.single v 1 : ι → ℝ) ⬝ᵥ x)
          (supportFun (facetPoly v (boxConsL lM.2 lM.1)) x) := by
      ext x
      rw [supportFun_pyr (box_nonempty hl _ (by omega)) (isBounded_box hl _ (by omega)),
        single_dotProduct, one_mul]
    rw [this]
    exact reluNet.max_mem (reluNet.linear_mem 1 _) (supportFun_box_mem hl _ (by omega))
  -- swap the order of summation over pairs `(v, R)` with `v ∉ R`
  set K : ℝ := ∑ R ∈ T, coeffs m R.card * (Rᶜ.card : ℝ)
  have hK : K = Fintype.card ι * psi m m := by
    have := sum_sum_powerset_erase_comm fun (_ : ι) R ↦ coeffs m R.card
    simp only [sum_const, nsmul_eq_mul] at this
    rw [show K = ∑ R ∈ T, (Rᶜ.card : ℝ) * coeffs m R.card by simp [K, mul_comm], ← this]
    rw [sum_congr rfl fun v _ ↦ sum_filter_nonempty_coeffs (X := univ.erase v)
      (by rw [card_erase_of_mem (mem_univ v), card_univ]) (by omega)]
    simp
  have hKne : K ≠ 0 := by
    have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    rw [hK]
    exact mul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (psi_self_ne_zero m)
  -- the combined identity modulo `maxSpan`
  have hQ : ∑ v, ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
      coeffs m R.card • supportFun (pyr v (qCons v R)) - K • supportFun simplex ∈ maxSpan ι m := by
    rw [sum_sum_powerset_erase_comm fun v R ↦ coeffs m R.card • supportFun (pyr v (qCons v R))]
    simp_rw [← smul_sum]
    have : K • supportFun (simplex : Set (ι → ℝ)) =
        ∑ R ∈ T, coeffs m R.card • ((Rᶜ.card : ℝ) • supportFun simplex) := by
      simp only [smul_smul, ← sum_smul, K]
    rw [this, ← sum_sub_distrib]
    refine Submodule.sum_mem _ fun R hR ↦ ?_
    simp only [mem_filter] at hR
    rw [← smul_sub]
    exact Submodule.smul_mem _ _ (subdivision hR.2.1 hR.2.2)
  have hV : P - ∑ v, ∑ R ∈ (univ.erase v).powerset.filter (·.Nonempty),
      coeffs m R.card • supportFun (pyr v (qCons v R)) ∈ maxSpan ι m := by
    rw [← sum_sub_distrib]
    exact Submodule.sum_mem _ fun v _ ↦ vertex_identity hn v
  have hsum : P - K • supportFun simplex ∈ maxSpan ι m := by
    have := Submodule.add_mem _ hV hQ
    rwa [sub_add_sub_cancel] at this
  have : supportFun (simplex : Set (ι → ℝ)) = K⁻¹ • (P - (P - K • supportFun simplex)) := by
    rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hKne, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hP (hL hsum))

omit [DecidableEq ι] in
/-- Maxima of at most `n` linear forms are computable with two hidden layers once
`max (x₁, …, xₙ)` is. -/
theorem maxSpan_le_reluNet {n : ℕ} [NeZero n]
    (h : (fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x) ∈ reluNet (Fin n) 2) :
    maxSpan ι n ≤ reluNet ι 2 := by
  classical
  refine Submodule.span_le.2 ?_
  rintro f ⟨W, hW, hcard, rfl⟩
  obtain ⟨w₀, hw₀⟩ := hW
  -- enumerate `W` by `Fin n`, repeating `w₀`
  let e : Fin n → ι → ℝ := fun k ↦
    if hk : (k : ℕ) < W.card then (W.equivFin.symm ⟨k, hk⟩ : ι → ℝ) else w₀
  have he : ∀ k, e k ∈ W := by
    intro k
    simp only [e]
    split_ifs
    · exact Finset.coe_mem _
    · exact hw₀
  have hsurj : ∀ w ∈ W, ∃ k, e k = w := by
    intro w hw
    refine ⟨⟨W.equivFin ⟨w, hw⟩, (W.equivFin ⟨w, hw⟩).isLt.trans_le hcard⟩, ?_⟩
    simp [e]
  let A : (ι → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.mulVecLin (Matrix.of e)
  have hA : maxLin W = (fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x) ∘ A := by
    ext x
    have hWne : W.Nonempty := ⟨w₀, hw₀⟩
    simp only [maxLin, dite_eq_left hWne, Function.comp_apply, A, Matrix.mulVecLin_apply]
    have hmv : ∀ k, (Matrix.of e).mulVec x k = e k ⬝ᵥ x := fun k ↦ rfl
    simp only [hmv]
    apply le_antisymm
    · refine sup'_le _ _ fun w hw ↦ ?_
      obtain ⟨k, rfl⟩ := hsurj w hw
      exact le_sup'_of_le _ (mem_univ k) le_rfl
    · exact sup'_le _ _ fun k _ ↦ le_sup' (· ⬝ᵥ x) (he k)
  rw [hA]
  exact reluNet.comp_linearMap A h

theorem max_mem_reluNet_succ (n : ℕ) :
    (fun x : Fin (n + 1) → ℝ ↦ univ.sup' univ_nonempty x) ∈ reluNet (Fin (n + 1)) 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | _ | n
  · have : (fun x : Fin 1 → ℝ ↦ univ.sup' univ_nonempty x) =
        fun x ↦ (Pi.single 0 1 : Fin 1 → ℝ) ⬝ᵥ x := by
      ext x
      simp [single_dotProduct, univ_unique]
    rw [this]
    exact reluNet.linear_mem 2 _
  · have : (fun x : Fin 2 → ℝ ↦ univ.sup' univ_nonempty x) =
        fun x ↦ max ((Pi.single 0 1 : Fin 2 → ℝ) ⬝ᵥ x) ((Pi.single 1 1 : Fin 2 → ℝ) ⬝ᵥ x) := by
      ext x
      simp only [single_dotProduct, one_mul]
      apply le_antisymm
      · refine sup'_le _ _ fun k _ ↦ ?_
        fin_cases k
        exacts [le_max_left _ _, le_max_right _ _]
      · exact max_le (le_sup' x (mem_univ 0)) (le_sup' x (mem_univ 1))
    rw [this]
    exact reluNet.max_mem (reluNet.linear_mem 1 _) (reluNet.linear_mem 1 _)
  · have hL : maxSpan (Fin (n + 3)) (Fintype.card (Fin (n + 3)) - 1) ≤ reluNet (Fin (n + 3)) 2 := by
      rw [Fintype.card_fin]
      exact maxSpan_le_reluNet (n := n + 2) (ih (n + 1) (by omega))
    have := supportFun_simplex_mem_reluNet (by simp) hL
    rwa [show supportFun (simplex : Set (Fin (n + 3) → ℝ)) = fun x ↦ univ.sup' univ_nonempty x
      from funext supportFun_simplex] at this

/-- **Two hidden ReLU layers compute the maximum**: `MAXₙ ∈ ReLU_{n,2}`. -/
theorem max_mem_reluNet (n : ℕ) [NeZero n] :
    (fun x : Fin n → ℝ ↦ univ.sup' univ_nonempty x) ∈ reluNet (Fin n) 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact max_mem_reluNet_succ k

/-- **Two hidden ReLU layers compute the maximum**, with an explicit network:
there are widths `k₁, k₂` and weights such that for all `x : Fin n → ℝ`,
`max (x₁, …, xₙ) = w₃ ⬝ᵥ relu (W₂ *ᵥ relu (W₁ *ᵥ x + b₁) + b₂) + b₃`. -/
theorem exists_twoLayerNet_eq_max (n : ℕ) [NeZero n] :
    ∃ (k₁ k₂ : ℕ) (W₁ : Matrix (Fin k₁) (Fin n) ℝ) (b₁ : Fin k₁ → ℝ)
      (W₂ : Matrix (Fin k₂) (Fin k₁) ℝ) (b₂ : Fin k₂ → ℝ) (w₃ : Fin k₂ → ℝ) (b₃ : ℝ),
      ∀ x : Fin n → ℝ, univ.sup' univ_nonempty x = twoLayerNet W₁ b₁ W₂ b₂ w₃ b₃ x := by
  obtain ⟨k₁, k₂, W₁, b₁, W₂, b₂, w₃, b₃, h⟩ := reluNet.exists_twoLayerNet (max_mem_reluNet n)
  exact ⟨k₁, k₂, W₁, b₁, W₂, b₂, w₃, b₃, fun x ↦ congr_fun h x⟩

end
