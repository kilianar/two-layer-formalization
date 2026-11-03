module

public import TwoHiddenLayers.Network
public import TwoHiddenLayers.Support
public import TwoHiddenLayers.Thermostat

/-!
# The parallelepipeds `B_{π,M}`

For an ordering `l` of `ι \ {v}` and a marking `M`, the polytope `facetPoly v (boxConsL M l)` is
the preimage of a box under an affine isomorphism (the defining system is triangular). Hence it is
a nonempty bounded parallelepiped, and its support function is affine plus a sum of ReLUs of linear
forms, i.e. it lies in `reluNet ι 1`.
-/

open Finset

@[expose] public noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Parallelepipeds given by an invertible linear system -/

/-- The parallelepiped `{p | lo y ≤ ⟪a y, p⟫ ≤ hi y for all y}`. -/
def slabPoly (a : ι → ι → ℝ) (lo hi : ι → ℝ) : Set (ι → ℝ) :=
  {p | ∀ y, a y ⬝ᵥ p ∈ Set.Icc (lo y) (hi y)}

omit [DecidableEq ι] in
theorem mulVecLin_of_apply (a : ι → ι → ℝ) (p : ι → ℝ) (y : ι) :
    (Matrix.of a).mulVecLin p y = a y ⬝ᵥ p := rfl

omit [DecidableEq ι] in
theorem slabPoly_eq_preimage (a : ι → ι → ℝ) (lo hi : ι → ℝ) :
    slabPoly a lo hi = (Matrix.of a).mulVecLin ⁻¹' Set.Icc lo hi := by
  ext p
  simp only [slabPoly, Set.mem_Icc, Set.mem_ofPred_eq, Set.mem_preimage, Pi.le_def,
    mulVecLin_of_apply, ← forall_and]

/-- `max (lo * w) (hi * w)` written as a linear term plus a ReLU, bounding `z * w` for
`z ∈ [lo, hi]`. -/
theorem mul_le_of_mem_Icc {lo hi z : ℝ} (hz : z ∈ Set.Icc lo hi) (w : ℝ) :
    z * w ≤ lo * w + (hi - lo) * relu w := by
  rcases le_total 0 w with hw | hw
  · have : relu w = w := max_eq_left hw
    rw [this]
    nlinarith [hz.2]
  · have : relu w = 0 := max_eq_right hw
    rw [this]
    nlinarith [hz.1]

theorem mul_ite_eq {lo hi : ℝ} (w : ℝ) :
    (if 0 ≤ w then hi else lo) * w = lo * w + (hi - lo) * relu w := by
  split_ifs with hw
  · rw [show relu w = w from max_eq_left hw]; ring
  · rw [show relu w = 0 from max_eq_right (le_of_not_ge hw)]; ring

section slab

variable {a : ι → ι → ℝ} (ha : Function.Injective (Matrix.of a).mulVecLin) {lo hi : ι → ℝ}

/-- The linear automorphism `p ↦ (⟪a y, p⟫)_y`. -/
def slabEquiv : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.ofInjectiveEndo _ ha

omit [DecidableEq ι] in
include ha in
theorem slabPoly_eq_image :
    slabPoly a lo hi = (slabEquiv ha).symm '' Set.Icc lo hi := by
  rw [LinearEquiv.image_symm_eq_preimage, slabPoly_eq_preimage]
  rfl

omit [DecidableEq ι] in
include ha in
/-- A parallelepiped with `lo ≤ hi` is nonempty. -/
theorem slabPoly_nonempty (hlh : lo ≤ hi) : (slabPoly a lo hi).Nonempty := by
  rw [slabPoly_eq_image ha]
  exact ⟨_, lo, Set.left_mem_Icc.mpr hlh, rfl⟩

omit [DecidableEq ι] in
include ha in
/-- A parallelepiped is bounded. -/
theorem isBounded_slabPoly : Bornology.IsBounded (slabPoly a lo hi) := by
  rw [slabPoly_eq_image ha]
  exact (isCompact_Icc.image
    (LinearMap.continuous_of_finiteDimensional (slabEquiv ha).symm.toLinearMap)).isBounded

theorem dotProduct_symm_eq (z x : ι → ℝ) :
    (slabEquiv ha).symm z ⬝ᵥ x = ∑ y, z y * ((slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x) := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  simp only [map_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have : Pi.single y (z y) = z y • Pi.single y (1 : ℝ) := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [this, map_smul, smul_dotProduct, smul_eq_mul]

/-- The support function of a parallelepiped. -/
theorem supportFun_slabPoly (hlh : lo ≤ hi) (x : ι → ℝ) :
    supportFun (slabPoly a lo hi) x = ∑ y, (lo y * ((slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x) +
      (hi y - lo y) * relu ((slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x)) := by
  set w : ι → ℝ := fun y ↦ (slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x
  refine le_antisymm (supportFun_le (slabPoly_nonempty ha hlh) fun p hp ↦ ?_) ?_
  · rw [slabPoly_eq_image ha] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    rw [dotProduct_symm_eq]
    exact Finset.sum_le_sum fun y _ ↦ mul_le_of_mem_Icc ⟨hz.1 y, hz.2 y⟩ (w y)
  · let z : ι → ℝ := fun y ↦ if 0 ≤ w y then hi y else lo y
    have hz : z ∈ Set.Icc lo hi := by
      refine ⟨fun y ↦ ?_, fun y ↦ ?_⟩ <;> simp only [z] <;> split_ifs <;> simp [hlh y]
    have hp : (slabEquiv ha).symm z ∈ slabPoly a lo hi := by
      rw [slabPoly_eq_image ha]; exact ⟨z, hz, rfl⟩
    have := le_supportFun (isBounded_slabPoly ha) hp x
    rw [dotProduct_symm_eq] at this
    exact le_of_eq_of_le (Finset.sum_congr rfl fun y _ ↦ (mul_ite_eq (w y)).symm) this

omit [DecidableEq ι] in
include ha in
/-- The support function of a parallelepiped lies in `reluNet ι 1`. -/
theorem supportFun_slabPoly_mem (hlh : lo ≤ hi) : supportFun (slabPoly a lo hi) ∈ reluNet ι 1 := by
  classical
  have : supportFun (slabPoly a lo hi) = ∑ y, ((lo y) • (fun x ↦
      (slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x) + (hi y - lo y) • (fun x ↦
      relu ((slabEquiv ha).symm (Pi.single y 1) ⬝ᵥ x + 0))) := by
    funext x
    simp [supportFun_slabPoly ha hlh, Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun y _ ↦ add_mem (Submodule.smul_mem _ _ (reluNet.linear_mem 1 _))
    (Submodule.smul_mem _ _ (reluNet.relu_affine_mem _ _))

end slab

/-! ### The triangular system of `boxCons` -/

/-- The normal vector of the functional constrained at position `x` of the list `l` by
`boxCons M pre l`: `indVec` of the coordinates visited before `x` if `x ∈ M`, else `e_x`. -/
def boxCoef (M : Finset ι) : Finset ι → List ι → ι → ι → ℝ
  | _, [], _ => 0
  | pre, y :: l, x =>
    if x = y then (if y ∈ M then indVec pre else Pi.single y 1) else boxCoef M (insert y pre) l x

/-- The lower bound of the functional at position `x`. -/
def boxLo (M : Finset ι) (x : ι) : ℝ := if x ∈ M then 0 else -1

/-- The upper bound of the functional at position `x`. -/
def boxHi (M : Finset ι) (x : ι) : ℝ := if x ∈ M then 1 else 0

/-- The constraints `boxCons M pre l` as a triangular system of interval constraints. -/
theorem forall_boxCons_iff {M pre : Finset ι} {l : List ι} (hl : l.Nodup) (p : ι → ℝ) :
    (∀ c ∈ boxCons M pre l, c.a ⬝ᵥ p ≤ c.b) ↔
      ∀ x ∈ l, boxCoef M pre l x ⬝ᵥ p ∈ Set.Icc (boxLo M x) (boxHi M x) := by
  induction l generalizing pre with
  | nil => simp [boxCons]
  | cons y l ih =>
    obtain ⟨hy, hl⟩ := List.nodup_cons.mp hl
    have hrest : ∀ x ∈ l, boxCoef M pre (y :: l) x = boxCoef M (insert y pre) l x := by
      intro x hx
      have : x ≠ y := fun h ↦ hy (h ▸ hx)
      simp [boxCoef, this]
    rw [List.forall_mem_cons, boxCons, Finset.forall_mem_union, ih hl]
    refine and_congr ?_ ⟨fun h x hx ↦ hrest x hx ▸ h x hx, fun h x hx ↦ hrest x hx ▸ h x hx⟩
    by_cases hyM : y ∈ M <;>
      simp [hyM, boxCoef, boxLo, boxHi, neg_dotProduct, neg_le, and_comm]

/-- Triangularity of `boxCoef`: the homogeneous system has only the trivial solution. -/
theorem boxCoef_eq_zero {M pre : Finset ι} {l : List ι} (hl : l.Nodup)
    (hpre : Disjoint pre l.toFinset) {p : ι → ℝ} (hp : ∀ x ∈ l, boxCoef M pre l x ⬝ᵥ p = 0)
    (hsum : ∑ i ∈ pre ∪ l.toFinset, p i = 0) : (∀ x ∈ l, p x = 0) ∧ ∑ i ∈ pre, p i = 0 := by
  induction l generalizing pre with
  | nil => simpa using hsum
  | cons y l ih =>
    obtain ⟨hy, hl⟩ := List.nodup_cons.mp hl
    have hypre : y ∉ pre := fun h ↦ Finset.disjoint_left.mp hpre h (by simp)
    have hrest : ∀ x ∈ l, boxCoef M pre (y :: l) x = boxCoef M (insert y pre) l x := by
      intro x hx
      have : x ≠ y := fun h ↦ hy (h ▸ hx)
      simp [boxCoef, this]
    have hpre' : Disjoint (insert y pre) l.toFinset := by
      rw [Finset.disjoint_insert_left]
      exact ⟨by simpa using hy, (Finset.disjoint_of_subset_right (by simp) hpre)⟩
    obtain ⟨hl0, hs⟩ := ih hl hpre' (fun x hx ↦ hrest x hx ▸ hp x (by simp [hx]))
      (by rw [← hsum, List.toFinset_cons, Finset.insert_union, Finset.union_insert])
    rw [Finset.sum_insert hypre] at hs
    have hy0 := hp y (by simp)
    by_cases hyM : y ∈ M
    · simp only [boxCoef, ite_true, hyM, indVec_dotProduct] at hy0
      refine ⟨List.forall_mem_cons.mpr ⟨by linarith, hl0⟩, hy0⟩
    · simp only [boxCoef, ite_true, hyM, ite_false, single_one_dotProduct] at hy0
      refine ⟨List.forall_mem_cons.mpr ⟨hy0, hl0⟩, by linarith⟩

/-- The normal vectors of the full triangular system of `facetPoly v (boxConsL M (h :: t))`:
`e_v`, the all-ones vector at `h`, and `boxCoef` along `t`. -/
def boxA (v h : ι) (M : Finset ι) (t : List ι) (y : ι) : ι → ℝ :=
  if y = v then Pi.single v 1 else if y = h then 1 else boxCoef M {h} t y

/-- The lower bounds of the full triangular system. -/
def boxLoA (v h : ι) (M : Finset ι) (y : ι) : ℝ :=
  if y = v then 0 else if y = h then 1 else boxLo M y

/-- The upper bounds of the full triangular system. -/
def boxHiA (v h : ι) (M : Finset ι) (y : ι) : ℝ :=
  if y = v then 0 else if y = h then 1 else boxHi M y

omit [Fintype ι] in
theorem boxLoA_le_boxHiA (v h : ι) (M : Finset ι) : boxLoA v h M ≤ boxHiA v h M := by
  intro y
  simp only [boxLoA, boxHiA, boxLo, boxHi]
  split_ifs <;> norm_num

section full

variable {v h : ι} {t : List ι} (hnd : (h :: t).Nodup) (hX : insert h t.toFinset = univ.erase v)
  (M : Finset ι)

include hX

theorem ne_of_insert_eq_erase : h ≠ v := by
  have : h ∈ insert h t.toFinset := Finset.mem_insert_self _ _
  rw [hX] at this
  exact (Finset.mem_erase.mp this).1

theorem mem_tail_of_ne {i : ι} (hiv : i ≠ v) (hih : i ≠ h) : i ∈ t := by
  have : i ∈ insert h t.toFinset := hX ▸ Finset.mem_erase.mpr ⟨hiv, Finset.mem_univ i⟩
  simpa [hih] using this

include hnd

theorem ne_of_mem_tail {x : ι} (hx : x ∈ t) : x ≠ v ∧ x ≠ h := by
  refine ⟨fun hxv ↦ ?_, fun hxh ↦ (List.nodup_cons.mp hnd).1 (hxh ▸ hx)⟩
  have : x ∈ insert h t.toFinset := by simp [hx]
  rw [hX, hxv] at this
  simp at this

/-- The box written as a parallelepiped. -/
theorem facetPoly_boxCons_eq :
    facetPoly v (boxCons M {h} t) = slabPoly (boxA v h M t) (boxLoA v h M) (boxHiA v h M) := by
  have hhv : h ≠ v := ne_of_insert_eq_erase hX
  ext p
  simp only [facetPoly, slabPoly, Set.mem_ofPred_eq,
    forall_boxCons_iff (List.nodup_cons.mp hnd).2]
  constructor
  · rintro ⟨hs, hv0, ht⟩ y
    by_cases hyv : y = v
    · subst hyv; simp [boxA, boxLoA, boxHiA, hv0]
    by_cases hyh : y = h
    · subst hyh; simp [boxA, boxLoA, boxHiA, hyv, one_dotProduct, hs]
    simpa [boxA, boxLoA, boxHiA, hyv, hyh] using ht y (mem_tail_of_ne hX hyv hyh)
  · intro H
    refine ⟨by simpa [boxA, boxLoA, boxHiA, hhv, one_dotProduct] using H h,
      by simpa [boxA, boxLoA, boxHiA] using H v, fun x hx ↦ ?_⟩
    obtain ⟨hxv, hxh⟩ := ne_of_mem_tail hnd hX hx
    simpa [boxA, boxLoA, boxHiA, hxv, hxh] using H x

/-- The full triangular system is invertible. -/
theorem injective_boxA : Function.Injective (Matrix.of (boxA v h M t)).mulVecLin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  have hy : ∀ y, boxA v h M t y ⬝ᵥ p = 0 := fun y ↦ by
    simpa [mulVecLin_of_apply] using congrFun hp y
  have hhv : h ≠ v := ne_of_insert_eq_erase hX
  have hv0 : p v = 0 := by simpa [boxA] using hy v
  have hs : ∑ i, p i = 0 := by simpa [boxA, hhv, one_dotProduct] using hy h
  have hdis : Disjoint {h} t.toFinset := by
    simpa using (List.nodup_cons.mp hnd).1
  obtain ⟨ht0, hh0⟩ := boxCoef_eq_zero (M := M) (List.nodup_cons.mp hnd).2 hdis
    (p := p) (fun x hx ↦ by
      obtain ⟨hxv, hxh⟩ := ne_of_mem_tail hnd hX hx
      simpa [boxA, hxv, hxh] using hy x)
    (by
      rw [← Finset.insert_eq, hX]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)] at hs
      linarith)
  funext i
  by_cases hiv : i = v
  · subst hiv; exact hv0
  by_cases hih : i = h
  · subst hih; simpa using hh0
  exact ht0 i (mem_tail_of_ne hX hiv hih)

end full

/-- An ordering of `ι \ {v}` is nonempty if `ι` has at least two elements. -/
theorem exists_cons_of_mem_orderings {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v))
    (hn : 2 ≤ Fintype.card ι) :
    ∃ h t, l = h :: t ∧ (h :: t).Nodup ∧ insert h t.toFinset = univ.erase v := by
  obtain ⟨hnd, hX⟩ := mem_orderings.mp hl
  match l, hnd, hX with
  | [], _, hX =>
    have := congrArg Finset.card hX
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at this
    simp at this
    omega
  | h :: t, hnd, hX => exact ⟨h, t, rfl, hnd, by simpa using hX⟩

/-- The box as a parallelepiped `slabPoly` with an injective system. -/
theorem exists_box_eq_slabPoly {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v))
    (M : Finset ι) (hn : 2 ≤ Fintype.card ι) :
    ∃ (a : ι → ι → ℝ) (lo hi : ι → ℝ), Function.Injective (Matrix.of a).mulVecLin ∧ lo ≤ hi ∧
      facetPoly v (boxConsL M l) = slabPoly a lo hi := by
  obtain ⟨h, t, rfl, hnd, hX⟩ := exists_cons_of_mem_orderings hl hn
  exact ⟨_, _, _, injective_boxA hnd hX M, boxLoA_le_boxHiA v h M,
    facetPoly_boxCons_eq hnd hX M⟩

/-- The parallelepiped `B_{π,M}` is nonempty. -/
theorem box_nonempty {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v)) (M : Finset ι)
    (hn : 2 ≤ Fintype.card ι) : (facetPoly v (boxConsL M l)).Nonempty := by
  obtain ⟨a, lo, hi, ha, hlh, heq⟩ := exists_box_eq_slabPoly hl M hn
  exact heq ▸ slabPoly_nonempty ha hlh

/-- The parallelepiped `B_{π,M}` is bounded. -/
theorem isBounded_box {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v)) (M : Finset ι)
    (hn : 2 ≤ Fintype.card ι) : Bornology.IsBounded (facetPoly v (boxConsL M l)) := by
  obtain ⟨a, lo, hi, ha, -, heq⟩ := exists_box_eq_slabPoly hl M hn
  exact heq ▸ isBounded_slabPoly ha

/-- The support function of `B_{π,M}` is computed by a one-hidden-layer ReLU network. -/
theorem supportFun_box_mem {v : ι} {l : List ι} (hl : l ∈ orderings (univ.erase v))
    (M : Finset ι) (hn : 2 ≤ Fintype.card ι) :
    supportFun (facetPoly v (boxConsL M l)) ∈ reluNet ι 1 := by
  obtain ⟨a, lo, hi, ha, hlh, heq⟩ := exists_box_eq_slabPoly hl M hn
  exact heq ▸ supportFun_slabPoly_mem ha hlh

end
