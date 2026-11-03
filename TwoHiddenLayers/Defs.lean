module

public import Mathlib

/-!
# Basic definitions

This file collects the definitions shared by the formalization of the statement that
`max(x₁, …, xₙ)` can be computed by a ReLU network with two hidden layers.

* `relu`: the rectified linear unit.
* `reluNet ι k`: the space of functions `(ι → ℝ) → ℝ` computed by ReLU networks with `k` hidden
  layers.
* `supportFun K`: the support function `x ↦ sup_{p ∈ K} ⟪p, x⟫` of a set `K`.
* `maxLin W`, `maxSpan ι k`: maxima of finitely many linear forms, and the span of those maxima
  involving at most `k` linear forms.
* `Constraint ι`, `hpoly cs`: affine half-spaces and polytopes in the hyperplane `∑ pᵢ = 1`
  given by finitely many such half-spaces.
* `facetPoly v cs`, `pyr v cs`: polytopes in the facet hyperplane `{∑ pᵢ = 1, p_v = 0}` and the
  pyramids over them with apex `e_v`.
-/

open Finset

@[expose] public noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The rectified linear unit. -/
def relu (x : ℝ) : ℝ := max x 0

/-- The functions `(ι → ℝ) → ℝ` computable by ReLU networks with `k` hidden layers
(written `ReLU_{n,k}` in the paper).

* `reluNet ι 0` is the space of affine functions, spanned by the constant function `1` and the
  linear forms `x ↦ ⟪a, x⟫`;
* `reluNet ι (k + 1)` is spanned by the constant function `1` and the functions `relu ∘ g` with
  `g ∈ reluNet ι k`.

Taking spans at every level accounts for the affine maps between the layers and for the
affine output map; see `reluNet.exists_twoLayerNet` for the explicit form when `k = 2`. -/
def reluNet (ι : Type*) [Fintype ι] : ℕ → Submodule ℝ ((ι → ℝ) → ℝ)
  | 0 => Submodule.span ℝ (insert (fun _ ↦ 1) (Set.range fun (a : ι → ℝ) (x : ι → ℝ) ↦ a ⬝ᵥ x))
  | k + 1 =>
    Submodule.span ℝ (insert (fun _ ↦ 1) {f | ∃ g ∈ reluNet ι k, f = fun x ↦ relu (g x)})

/-- The support function `x ↦ sup_{p ∈ K} ⟪p, x⟫` of a set `K`.
It is only meaningful for bounded nonempty `K`; for `K = ∅` it is `0`. -/
def supportFun (K : Set (ι → ℝ)) (x : ι → ℝ) : ℝ :=
  sSup ((fun p ↦ p ⬝ᵥ x) '' K)

/-- The maximum of the linear forms `x ↦ ⟪w, x⟫` for `w ∈ W` (and `0` if `W = ∅`). -/
def maxLin (W : Finset (ι → ℝ)) (x : ι → ℝ) : ℝ :=
  if h : W.Nonempty then W.sup' h (· ⬝ᵥ x) else 0

/-- The span of all maxima of at most `k` linear forms. -/
def maxSpan (ι : Type*) [Fintype ι] (k : ℕ) : Submodule ℝ ((ι → ℝ) → ℝ) :=
  Submodule.span ℝ {f | ∃ W : Finset (ι → ℝ), W.Nonempty ∧ W.card ≤ k ∧ f = maxLin W}

/-- An affine half-space `{p | ⟪a, p⟫ ≤ b}`. -/
@[ext]
structure Constraint (ι : Type*) where
  /-- The normal vector. -/
  a : ι → ℝ
  /-- The right hand side. -/
  b : ℝ

instance : DecidableEq (Constraint ι) := Classical.decEq _

/-- A constraint is nonconstant on the hyperplane `∑ pᵢ = 1` iff its normal vector is not
a multiple of the all-ones vector. -/
def Constraint.IsNonconst (c : Constraint ι) : Prop :=
  ∃ i j, c.a i ≠ c.a j

/-- The polytope `{p | ∑ pᵢ = 1, ⟪c.a, p⟫ ≤ c.b for all c ∈ cs}`. -/
def hpoly (cs : Finset (Constraint ι)) : Set (ι → ℝ) :=
  {p | ∑ i, p i = 1 ∧ ∀ c ∈ cs, c.a ⬝ᵥ p ≤ c.b}

/-- The polytope `{p | ∑ pᵢ = 1, p_v = 0, ⟪c.a, p⟫ ≤ c.b for all c ∈ cs}` in a facet hyperplane. -/
def facetPoly (v : ι) (cs : Finset (Constraint ι)) : Set (ι → ℝ) :=
  {p | ∑ i, p i = 1 ∧ p v = 0 ∧ ∀ c ∈ cs, c.a ⬝ᵥ p ≤ c.b}

variable [DecidableEq ι]

/-- Homogenization of a facet constraint with respect to the apex `e_v`:
`⟪a, p⟫ ≤ b` on `{p_v = 0}` becomes `∑_{i ≠ v} aᵢ pᵢ ≤ b (1 - p_v)`. -/
def Constraint.homog (v : ι) (c : Constraint ι) : Constraint ι :=
  ⟨Function.update c.a v c.b, c.b⟩

/-- The constraints of the pyramid with apex `e_v` over `facetPoly v cs`. -/
def pyrCons (v : ι) (cs : Finset (Constraint ι)) : Finset (Constraint ι) :=
  insert ⟨-Pi.single v 1, 0⟩ (insert ⟨Pi.single v 1, 1⟩ (cs.image (Constraint.homog v)))

/-- The pyramid with apex `e_v` over `facetPoly v cs`. -/
def pyr (v : ι) (cs : Finset (Constraint ι)) : Set (ι → ℝ) :=
  hpoly (pyrCons v cs)

/-! ### The concrete polytopes of the proof -/

/-- The constraints `pᵢ ≥ 0` of the standard simplex. -/
def simplexCons : Finset (Constraint ι) :=
  univ.image fun i ↦ ⟨-Pi.single i 1, 0⟩

/-- The standard simplex `Δ = conv {e_i}`. -/
def simplex : Set (ι → ℝ) :=
  hpoly (simplexCons : Finset (Constraint ι))

/-- The constraints of `T_v = pyr_{q_C}(Δ_{-v})`, i.e. `p ∈ Δ` and `p_v ≤ p_w` for `w ∈ C`. -/
def tCons (C : Finset ι) (v : ι) : Finset (Constraint ι) :=
  simplexCons ∪ (C.erase v).image fun w ↦ ⟨Pi.single v 1 - Pi.single w 1, 0⟩

/-- The constraints of the dilated facet `Q_{v,R}`: `pᵢ ≥ 0` for `i ∈ R` and `pᵢ ≥ -1` for the
remaining `i ≠ v`. -/
def qCons (v : ι) (R : Finset ι) : Finset (Constraint ι) :=
  (univ.erase v).image fun i ↦ if i ∈ R then ⟨-Pi.single i 1, 0⟩ else ⟨-Pi.single i 1, 1⟩

/-- The indicator vector of a finite set. -/
def indVec (S : Finset ι) : ι → ℝ :=
  fun i ↦ if i ∈ S then 1 else 0

/-- The orderings of a finite set, as lists. -/
def orderings (X : Finset ι) : Finset (List ι) :=
  X.toList.permutations.toFinset

/-- The constraints of the parallelepiped `B_{π,M}` read along the list `x :: l`, where `pre` is
the set of coordinates already visited: if `x ∈ M` we require `0 ≤ ∑_{pre} p ≤ 1`, otherwise
`-1 ≤ p_x ≤ 0`. -/
def boxCons (M : Finset ι) : Finset ι → List ι → Finset (Constraint ι)
  | _, [] => ∅
  | pre, x :: l =>
    (if x ∈ M then {⟨-indVec pre, 0⟩, ⟨indVec pre, 1⟩}
      else {⟨-Pi.single x 1, 1⟩, ⟨Pi.single x 1, 0⟩}) ∪ boxCons M (insert x pre) l

/-- The constraints of the parallelepiped `B_{π,M}` for the ordering `π = l`. -/
def boxConsL (M : Finset ι) : List ι → Finset (Constraint ι)
  | [] => ∅
  | h :: t => boxCons M {h} t

/-- The admissible markings `M` for the ordering `l`: subsets of the positions after the first. -/
def markings (l : List ι) : Finset (Finset ι) :=
  l.tail.toFinset.powerset

/-- The hyperplanes in the facet `{p_v = 0}` that a point has to avoid in order to be generic for
the thermostat lemma: `pᵢ = 0`, `pᵢ = -1` and `∑_{S} p = 0`, `∑_{S} p = 1` for nonempty proper
subsets `S` of the coordinates `≠ v`. -/
def facetGen (v : ι) : Finset (Constraint ι) :=
  ((univ.erase v).image fun i ↦ (⟨Pi.single i 1, 0⟩ : Constraint ι)) ∪
  ((univ.erase v).image fun i ↦ (⟨Pi.single i 1, -1⟩ : Constraint ι)) ∪
  (((univ.erase v).powerset.filter fun S ↦ S.Nonempty ∧ S ≠ univ.erase v).image
    fun S ↦ (⟨indVec S, 0⟩ : Constraint ι)) ∪
  (((univ.erase v).powerset.filter fun S ↦ S.Nonempty ∧ S ≠ univ.erase v).image
    fun S ↦ (⟨indVec S, 1⟩ : Constraint ι))

/-- The signed number `(-1)^(s-1) s! (m-s)!` of thermostat walks. -/
def psi (m s : ℕ) : ℝ :=
  (-1) ^ (s - 1) * (s.factorial : ℝ) * ((m - s).factorial : ℝ)

end
