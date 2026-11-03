module

public import TwoHiddenLayers.Defs

/-!
# ReLU networks with `k` hidden layers

We prove closure properties of the hierarchy `reluNet ι k` of functions computable by ReLU
networks with `k` hidden layers:

* `reluNet.mono`: `reluNet ι k ≤ reluNet ι l` for `k ≤ l`;
* `reluNet.relu_mem`, `reluNet.max_mem`: applying `relu`, or taking the maximum of two functions,
  costs one hidden layer;
* `reluNet.comp_linearMap`: the hierarchy is closed under precomposition with linear maps.

Finally, `reluNet.exists_twoLayerNet` shows that every function in `reluNet ι 2` is computed by an
explicit network `x ↦ w₃ ⬝ᵥ relu (W₂ *ᵥ relu (W₁ *ᵥ x + b₁) + b₂) + b₃`.
-/

open Finset Matrix

@[expose] public noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

namespace reluNet

theorem one_mem (k : ℕ) : (fun _ ↦ (1 : ℝ)) ∈ reluNet ι k := by
  cases k <;> exact Submodule.subset_span (Set.mem_insert _ _)

/-- Constant functions are computed by ReLU networks of any depth. -/
theorem const_mem (k : ℕ) (c : ℝ) : (fun _ ↦ c) ∈ reluNet ι k := by
  convert Submodule.smul_mem _ c (one_mem (ι := ι) k) using 1
  funext x
  simp

/-- Applying `relu` costs one hidden layer. -/
theorem relu_mem {k : ℕ} {g : (ι → ℝ) → ℝ} (hg : g ∈ reluNet ι k) :
    (fun x ↦ relu (g x)) ∈ reluNet ι (k + 1) :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨g, hg, rfl⟩)

/-- Linear forms are computed without hidden layers. -/
theorem linear_mem_zero (a : ι → ℝ) : (fun x ↦ a ⬝ᵥ x) ∈ reluNet ι 0 :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨a, rfl⟩)

/-- Affine functions are computed without hidden layers. -/
theorem affine_mem_zero (a : ι → ℝ) (b : ℝ) : (fun x ↦ a ⬝ᵥ x + b) ∈ reluNet ι 0 :=
  add_mem (linear_mem_zero a) (const_mem 0 b)

theorem relu_sub_relu_neg (y : ℝ) : relu y - relu (-y) = y := by
  simp only [relu]
  rcases le_total y 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

/-- A function computed with `k` hidden layers is also computed with `k + 1` hidden layers. -/
theorem le_succ (k : ℕ) : reluNet ι k ≤ reluNet ι (k + 1) := by
  induction k with
  | zero =>
    refine Submodule.span_le.2 ?_
    rintro f (rfl | ⟨a, rfl⟩)
    · exact one_mem 1
    · have h := sub_mem (relu_mem (linear_mem_zero a)) (relu_mem (linear_mem_zero (-a)))
      have he : ((fun x ↦ relu (a ⬝ᵥ x)) - fun x ↦ relu (-a ⬝ᵥ x)) = fun x ↦ a ⬝ᵥ x := by
        funext x
        simp only [Pi.sub_apply, neg_dotProduct, relu_sub_relu_neg]
      rw [he] at h
      exact h
  | succ k ih =>
    refine Submodule.span_le.2 ?_
    rintro f (rfl | ⟨g, hg, rfl⟩)
    · exact one_mem _
    · exact relu_mem (ih hg)

/-- The hierarchy `reluNet ι k` is monotone in the number `k` of hidden layers. -/
theorem mono : Monotone (reluNet ι) :=
  monotone_nat_of_le_succ le_succ

/-- Affine functions are computed by ReLU networks of any depth. -/
theorem affine_mem (k : ℕ) (a : ι → ℝ) (b : ℝ) : (fun x ↦ a ⬝ᵥ x + b) ∈ reluNet ι k :=
  mono (Nat.zero_le k) (affine_mem_zero a b)

/-- Linear forms are computed by ReLU networks of any depth. -/
theorem linear_mem (k : ℕ) (a : ι → ℝ) : (fun x ↦ a ⬝ᵥ x) ∈ reluNet ι k :=
  mono (Nat.zero_le k) (linear_mem_zero a)

/-- A single ReLU neuron is computed with one hidden layer. -/
theorem relu_affine_mem (a : ι → ℝ) (b : ℝ) : (fun x ↦ relu (a ⬝ᵥ x + b)) ∈ reluNet ι 1 :=
  relu_mem (affine_mem_zero a b)

/-- The maximum of two functions computed with `k` hidden layers is computed with `k + 1`
hidden layers, via `max g h = h + relu (g - h)`. -/
theorem max_mem {k : ℕ} {g h : (ι → ℝ) → ℝ} (hg : g ∈ reluNet ι k) (hh : h ∈ reluNet ι k) :
    (fun x ↦ max (g x) (h x)) ∈ reluNet ι (k + 1) := by
  convert add_mem (le_succ k hh) (relu_mem (sub_mem hg hh)) using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, relu]
  rw [← max_add_add_left, add_zero, add_sub_cancel]

/-- Precomposition with a linear map preserves the number of hidden layers. -/
theorem comp_linearMap (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) {k : ℕ} {f : (κ → ℝ) → ℝ}
    (hf : f ∈ reluNet κ k) : f ∘ A ∈ reluNet ι k := by
  classical
  induction k generalizing f with
  | zero =>
    induction hf using Submodule.span_induction with
    | mem f hf =>
      rcases hf with rfl | ⟨a, rfl⟩
      · exact one_mem 0
      · convert linear_mem_zero (a ᵥ* LinearMap.toMatrix' A) using 1
        funext x
        simp [← dotProduct_mulVec, LinearMap.toMatrix'_mulVec]
    | zero => exact zero_mem _
    | add f g _ _ hf hg => exact add_mem hf hg
    | smul r f _ hf => exact Submodule.smul_mem _ r hf
  | succ k ih =>
    induction hf using Submodule.span_induction with
    | mem f hf =>
      rcases hf with rfl | ⟨g, hg, rfl⟩
      · exact one_mem _
      · exact relu_mem (ih hg)
    | zero => exact zero_mem _
    | add f g _ _ hf hg => exact add_mem hf hg
    | smul r f _ hf => exact Submodule.smul_mem _ r hf

/-- Every function computed without hidden layers is affine. -/
theorem exists_affine {g : (ι → ℝ) → ℝ} (hg : g ∈ reluNet ι 0) :
    ∃ (a : ι → ℝ) (c : ℝ), g = fun x ↦ a ⬝ᵥ x + c := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
    rcases hf with rfl | ⟨a, rfl⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨a, 0, by simp⟩
  | zero => exact ⟨0, 0, by funext x; simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨a, c, rfl⟩ := hf
    obtain ⟨a', c', rfl⟩ := hg
    refine ⟨a + a', c + c', ?_⟩
    funext x
    simp only [Pi.add_apply, add_dotProduct]
    ring
  | smul r f _ hf =>
    obtain ⟨a, c, rfl⟩ := hf
    refine ⟨r • a, r * c, ?_⟩
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, smul_dotProduct, mul_add]

/-- Every function computed with one hidden layer is an explicit finite linear combination of
ReLU neurons plus a constant. -/
theorem exists_sum {g : (ι → ℝ) → ℝ} (hg : g ∈ reluNet ι 1) :
    ∃ (k : ℕ) (a : Fin k → ι → ℝ) (b d : Fin k → ℝ) (c : ℝ),
      g = fun x ↦ ∑ j, d j * relu (a j ⬝ᵥ x + b j) + c := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
    rcases hf with rfl | ⟨g, hg, rfl⟩
    · exact ⟨0, ![], ![], ![], 1, by simp⟩
    · obtain ⟨a, b, rfl⟩ := exists_affine hg
      exact ⟨1, ![a], ![b], ![1], 0, by simp⟩
  | zero => exact ⟨0, ![], ![], ![], 0, by funext x; simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨k, a, b, d, c, rfl⟩ := hf
    obtain ⟨k', a', b', d', c', rfl⟩ := hg
    refine ⟨k + k', Fin.append a a', Fin.append b b', Fin.append d d', c + c', ?_⟩
    funext x
    simp only [Pi.add_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
    ring
  | smul r f _ hf =>
    obtain ⟨k, a, b, d, c, rfl⟩ := hf
    refine ⟨k, a, b, r • d, r * c, ?_⟩
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, mul_add, mul_sum, mul_assoc]

end reluNet

/-- The function computed by a ReLU network with two hidden layers of widths `k₁` and `k₂`. -/
def twoLayerNet {k₁ k₂ : ℕ} (W₁ : Matrix (Fin k₁) ι ℝ) (b₁ : Fin k₁ → ℝ)
    (W₂ : Matrix (Fin k₂) (Fin k₁) ℝ) (b₂ : Fin k₂ → ℝ) (w₃ : Fin k₂ → ℝ) (b₃ : ℝ)
    (x : ι → ℝ) : ℝ :=
  w₃ ⬝ᵥ (fun j ↦ relu ((W₂ *ᵥ fun i ↦ relu ((W₁ *ᵥ x) i + b₁ i)) j + b₂ j)) + b₃


/-- Running two networks in parallel and adding their outputs. -/
theorem twoLayerNet_add {k₁ k₂ k₁' k₂' : ℕ} (W₁ : Matrix (Fin k₁) ι ℝ) (b₁ : Fin k₁ → ℝ)
    (W₂ : Matrix (Fin k₂) (Fin k₁) ℝ) (b₂ : Fin k₂ → ℝ) (w₃ : Fin k₂ → ℝ) (b₃ : ℝ)
    (W₁' : Matrix (Fin k₁') ι ℝ) (b₁' : Fin k₁' → ℝ)
    (W₂' : Matrix (Fin k₂') (Fin k₁') ℝ) (b₂' : Fin k₂' → ℝ) (w₃' : Fin k₂' → ℝ) (b₃' : ℝ) :
    twoLayerNet W₁ b₁ W₂ b₂ w₃ b₃ + twoLayerNet W₁' b₁' W₂' b₂' w₃' b₃' =
      twoLayerNet (Matrix.of (Fin.append W₁ W₁')) (Fin.append b₁ b₁')
        (Matrix.of (Fin.append (fun j ↦ Fin.append (W₂ j) 0) (fun j ↦ Fin.append 0 (W₂' j))))
        (Fin.append b₂ b₂') (Fin.append w₃ w₃') (b₃ + b₃') := by
  funext x
  simp only [twoLayerNet, dotProduct, mulVec, Pi.add_apply, Fin.sum_univ_add, Matrix.of_apply,
    Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, sum_const_zero, add_zero,
    zero_add]
  have h₁ (i : Fin k₁) : Fin.append W₁ W₁' (Fin.castAdd k₁' i) = W₁ i := Fin.append_left _ _ _
  have h₂ (i : Fin k₁') : Fin.append W₁ W₁' (Fin.natAdd k₁ i) = W₁' i := Fin.append_right _ _ _
  simp only [h₁, h₂]
  ring

/-- Every function computed with two hidden layers is computed by an explicit network
`twoLayerNet`. -/
theorem reluNet.exists_twoLayerNet {f : (ι → ℝ) → ℝ} (hf : f ∈ reluNet ι 2) :
    ∃ (k₁ k₂ : ℕ) (W₁ : Matrix (Fin k₁) ι ℝ) (b₁ : Fin k₁ → ℝ) (W₂ : Matrix (Fin k₂) (Fin k₁) ℝ)
      (b₂ : Fin k₂ → ℝ) (w₃ : Fin k₂ → ℝ) (b₃ : ℝ), f = twoLayerNet W₁ b₁ W₂ b₂ w₃ b₃ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with rfl | ⟨g, hg, rfl⟩
    · exact ⟨0, 0, 0, 0, 0, 0, 0, 1, by funext x; simp [twoLayerNet]⟩
    · obtain ⟨k, a, b, d, c, rfl⟩ := reluNet.exists_sum hg
      refine ⟨k, 1, Matrix.of a, b, Matrix.of fun _ ↦ d, fun _ ↦ c, fun _ ↦ 1, 0, ?_⟩
      funext x
      simp [twoLayerNet, dotProduct, mulVec]
  | zero => exact ⟨0, 0, 0, 0, 0, 0, 0, 0, by funext x; simp [twoLayerNet]⟩
  | add f g _ _ hf hg =>
    obtain ⟨k₁, k₂, W₁, b₁, W₂, b₂, w₃, b₃, rfl⟩ := hf
    obtain ⟨k₁', k₂', W₁', b₁', W₂', b₂', w₃', b₃', rfl⟩ := hg
    exact ⟨_, _, _, _, _, _, _, _, twoLayerNet_add W₁ b₁ W₂ b₂ w₃ b₃ W₁' b₁' W₂' b₂' w₃' b₃'⟩
  | smul r f _ hf =>
    obtain ⟨k₁, k₂, W₁, b₁, W₂, b₂, w₃, b₃, rfl⟩ := hf
    refine ⟨k₁, k₂, W₁, b₁, W₂, b₂, r • w₃, r * b₃, ?_⟩
    funext x
    simp only [twoLayerNet, Pi.smul_apply, smul_eq_mul, smul_dotProduct, mul_add]

end
