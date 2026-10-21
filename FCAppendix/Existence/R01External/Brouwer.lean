/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
Modified for publication: explanatory comments removed;
namespace and Lean/Mathlib compatibility adapted where needed.
-/
module

public import FCAppendix.Existence.R01External.CubicalSperner
public import FCAppendix.Existence.R01External.ConvexHomeomorph

@[expose] public section

open KuhnSimplex

variable {n : ℕ}

namespace KuhnSimplex

noncomputable def rlPoint
    (f : Set.Icc (0 : Fin n → ℝ) 1 → Set.Icc (0 : Fin n → ℝ) 1)
    (x : Set.Icc (0 : Fin n → ℝ) 1) : ℕ :=
  match (Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1}) with
    | some k => k.1
    | none => n

lemma rlPoint_le_n (f : Set.Icc (0 : Fin n → ℝ) 1 → Set.Icc (0 : Fin n → ℝ) 1)
    (x : Set.Icc (0 : Fin n → ℝ) 1) :
    rlPoint f x ≤ n := by
  unfold rlPoint
  cases hm : Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1 } with
  | top => exact le_rfl
  | coe m => exact le_of_lt m.isLt

lemma rlPoint_props (f : Set.Icc (0 : Fin n → ℝ) 1 → Set.Icc (0 : Fin n → ℝ) 1)
    (x : Set.Icc (0 : Fin n → ℝ) 1) :
    rlPoint f x ≤ n ∧
    ∀ k : Fin n, (rlPoint f x = k.1 → (f x).1 k < x.1 k ∨ x.1 k = 1) ∧
                 ((f x).1 k < x.1 k ∨ x.1 k = 1 → rlPoint f x ≤ k.1) := by
  unfold rlPoint
  cases hm : Finset.min { i | (f x).1 i < x.1 i ∨ x.1 i = 1 } with
  | top =>
    refine ⟨le_rfl, fun k => ⟨fun h => ?_, fun hk => ?_⟩⟩
    · exact absurd h.symm (ne_of_lt k.isLt)
    · have he := Finset.min_eq_top.mp hm
      have hin : k ∈ ({ i | (f x).1 i < x.1 i ∨ x.1 i = 1 } : Finset (Fin n)) := by
        simpa using hk
      exact absurd (he ▸ hin) (Finset.notMem_empty k)
  | coe m =>
    refine ⟨le_of_lt m.isLt, fun k => ⟨fun h => ?_, fun hk => ?_⟩⟩
    · have heq : m = k := Fin.ext h
      have hmem := Finset.mem_of_min hm
      rw [heq] at hmem
      exact (Finset.mem_filter.mp hmem).2
    · have hin : k ∈ ({ i | (f x).1 i < x.1 i ∨ x.1 i = 1 } : Finset (Fin n)) := by
        simpa using hk
      have hle := Finset.min_le hin
      rw [hm] at hle; exact_mod_cast hle

lemma rlPoint_sperner (f : Set.Icc (0 : Fin n → ℝ) 1 → Set.Icc (0 : Fin n → ℝ) 1)
    (x : Set.Icc (0 : Fin n → ℝ) 1) :
    rlPoint f x ≤ n ∧
    ∀ k : Fin n,
      (x.1 k = 0 → rlPoint f x ≠ k.1) ∧
      (x.1 k = 1 → rlPoint f x ≤ k.1) := by
  obtain ⟨h_le_n, h_props⟩ := rlPoint_props f x
  refine ⟨h_le_n, fun k => ⟨fun hx0 heq => ?_, fun hx1 => (h_props k).2 (Or.inr hx1)⟩⟩
  have h_cond := (h_props k).1 heq
  rw [hx0] at h_cond
  rcases h_cond with h_lt | h_eq
  · exact not_lt_of_ge ((f x).2.1 k) h_lt
  · exact zero_ne_one h_eq

lemma rlPoint_ineq (f : Set.Icc (0 : Fin n → ℝ) 1 → Set.Icc (0 : Fin n → ℝ) 1)
    (x : Set.Icc (0 : Fin n → ℝ) 1) (k : Fin n) :
    (rlPoint f x = k → (f x).1 k ≤ x.1 k) ∧
    (rlPoint f x > k → (f x).1 k ≥ x.1 k) := by
  have h1 := (rlPoint_props f x).2 k
  refine ⟨fun h_eq => ?_, ?_⟩
  · rcases h1.1 h_eq with h_lt | h_eq_one
    · exact le_of_lt h_lt
    · rw [h_eq_one]; exact (f x).2.2 k
  · contrapose!
    exact fun h_lt => h1.2 (Or.inl h_lt)

noncomputable def discreteMap (p : ℕ) (v : Fin n → Fin (p + 1)) :
    Set.Icc (0 : Fin n → ℝ) 1 :=
  ⟨fun i ↦ ((v i).1 : ℝ) / p, by
    refine ⟨fun i ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), fun i ↦ ?_⟩
    exact div_le_one_of_le₀ (Nat.cast_le.mpr (v i).is_le) (Nat.cast_nonneg _)⟩

lemma dist_discreteMap (p : ℕ) (ppos : 0 < p) (v1 v2 : Fin n → Fin (p + 1))
    (h1 : ∀ k, (v1 k).1 ≤ (v2 k).1 + 1 ∧ (v2 k).1 ≤ (v1 k).1 + 1) :
    dist (discreteMap p v1) (discreteMap p v2) ≤ 1 / p := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr ppos
  rw [Subtype.dist_eq, dist_pi_le_iff (by positivity)]
  intro k
  dsimp [discreteMap]
  rw [Real.dist_eq, abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · rw [sub_le_iff_le_add', ← add_div, div_le_div_iff_of_pos_right hp]
    exact_mod_cast (h1 k).1
  · rw [sub_le_iff_le_add', ← add_div, div_le_div_iff_of_pos_right hp]
    exact_mod_cast (h1 k).2

noncomputable def spernerColoringOfFunction
    (f : Set.Icc (0 : Fin n → ℝ) 1 → Set.Icc (0 : Fin n → ℝ) 1)
    (p : ℕ) (ppos : 0 < p) : SpernerColoring n p where
  color v := ⟨rlPoint f (discreteMap p v), Nat.lt_add_one_iff.mpr (rlPoint_le_n f _)⟩
  proper v k := by
    obtain ⟨_, h_props⟩ := rlPoint_sperner f (discreteMap p v)
    refine ⟨fun h0 => ?_, fun hp1 => ?_⟩
    · intro heq
      exact (h_props k).1 (by simp [discreteMap, h0]) (Fin.ext_iff.mp heq)
    · exact (h_props k).2 (by
        dsimp [discreteMap]
        rw [hp1, Fin.val_last, div_self (Nat.cast_ne_zero.mpr (ne_of_gt ppos))])

lemma nearbyPoints (f : Set.Icc (0 : Fin n → ℝ) 1 → Set.Icc (0 : Fin n → ℝ) 1)
    (p0 : ℕ) :
    ∃ x0 : Set.Icc (0 : Fin n → ℝ) 1, ∀ k : Fin n,
      (f x0).1 k ≥ x0.1 k ∧
      ∃ xk : Set.Icc (0 : Fin n → ℝ) 1,
        dist x0 xk ≤ 1 / ↑(p0 + 1) ∧ (f xk).1 k ≤ xk.1 k := by
  have ppos : 0 < p0 + 1 := Nat.succ_pos p0
  let SC := spernerColoringOfFunction f (p0 + 1) ppos

  obtain ⟨S, hv, hfc⟩ := weakerCubicalSperner n (p0 + 1) SC ppos

  obtain ⟨i0, hi0⟩ := hfc (Fin.last n)
  refine ⟨discreteMap (p0 + 1) (S.vertex hv i0), fun k => ⟨?_, ?_⟩⟩
  ·
    refine (rlPoint_ineq f _ k).2 ?_

    have h_rl : rlPoint f (discreteMap (p0 + 1) (S.vertex hv i0)) = n :=
      Fin.val_eq_of_eq (by simpa only [SC, spernerColoringOfFunction] using hi0)
    rw [h_rl]; exact k.isLt
  ·
    obtain ⟨ik, hik⟩ := hfc k.castSucc
    refine ⟨discreteMap (p0 + 1) (S.vertex hv ik), ?_,
            (rlPoint_ineq f _ k).1 ?_⟩
    ·
      exact dist_discreteMap (p0 + 1) ppos _ _ fun j =>
        ⟨vertex_close S hv i0 ik j, vertex_close S hv ik i0 j⟩
    ·
      exact Fin.val_eq_of_eq (by simpa only [SC, spernerColoringOfFunction] using hik)

end KuhnSimplex

theorem fixedPointUnitCube
    (f : C(Set.Icc (0 : Fin n → ℝ) 1, Set.Icc (0 : Fin n → ℝ) 1)) :
    ∃ x, f x = x := by
  choose x0 hx0 using nearbyPoints f
  choose xk hxk using fun p k ↦ (hx0 p k).2
  let u : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hu_atTop : ↑u ≤ (Filter.atTop : Filter ℕ) := Ultrafilter.of_le Filter.atTop
  haveI : CompactSpace (Set.Icc (0 : Fin n → ℝ) 1) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨x_star, -, h_tendsto_x0⟩ :=
    isCompact_univ.ultrafilter_le_nhds (u.map x0) (by simp)
  use x_star
  ext k
  have hc_proj : Continuous (fun x : Set.Icc (0 : Fin n → ℝ) 1 ↦ x.1 k) :=
    (continuous_apply k).comp continuous_subtype_val
  have hc_f_proj : Continuous (fun x : Set.Icc (0 : Fin n → ℝ) 1 ↦ (f x).1 k) :=
    hc_proj.comp f.continuous
  apply le_antisymm
  ·
    have h_dist : Filter.Tendsto (fun i => dist (x0 i) (xk i k)) u (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      · exact tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hu_atTop
      · exact Filter.Eventually.of_forall fun i => dist_nonneg
      · exact Filter.Eventually.of_forall fun i => by exact_mod_cast (hxk i k).1
    have h_tendsto_xk : Filter.Tendsto (fun i => xk i k) u (nhds x_star) :=
      tendsto_of_tendsto_of_dist h_tendsto_x0 h_dist
    exact le_of_tendsto_of_tendsto' (hc_f_proj.tendsto x_star |>.comp h_tendsto_xk)
      (hc_proj.tendsto x_star |>.comp h_tendsto_xk) (fun i ↦ (hxk i k).2)
  ·
    exact le_of_tendsto_of_tendsto' (hc_proj.tendsto x_star |>.comp h_tendsto_x0)
      (hc_f_proj.tendsto x_star |>.comp h_tendsto_x0) (fun i ↦ (hx0 i k).1)

theorem brouwerFixedPoint {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) : ∃ x, f x = x := by
  obtain ⟨k, ⟨e⟩⟩ := homeoUnitCubeOfConvexCompact s hcvx hcmpct hne
  let g := (toContinuousMap e).comp (f.comp (toContinuousMap e.symm))
  obtain ⟨y, hy⟩ := @fixedPointUnitCube k g
  use (toContinuousMap e.symm) y
  let e' := EquivLike.toEquiv e
  exact (e'.apply_eq_iff_eq_symm_apply).1 hy
