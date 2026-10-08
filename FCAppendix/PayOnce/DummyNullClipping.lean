import FCAppendix.PayOnce.NullClipping
import FCAppendix.PayOnce.DummyJointKernel

namespace FCAppendix.PayOnce.DummyNullClipping
open MeasureTheory Filter Topology Set CommonList DummyKernel
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ae_positive_coord_ne_erased_function (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0)
    (j : ι) (f : (ι → ℝ) → ℝ) (hf : Measurable f) :
    ∀ᵐ d ∂Measure.pi (fun _ : ι => G), 0 < d j → d j ≠ f (Function.update d j 1) := by
  let P : ℝ → (ι → ℝ) → Prop := fun u d => 0 < u → u ≠ f (Function.update d j 1)
  have hm : Measurable (fun d : ι → ℝ => Function.update d j (1:ℝ)) :=
    measurable_pi_lambda _ fun i => by
      by_cases hi : i = j
      · subst i; simp
      · simpa [Function.update_of_ne hi] using measurable_pi_apply i
  have hP : MeasurableSet {p : ℝ × (ι → ℝ) | P p.1 p.2} := by
    have hh := (measurableSet_lt (measurable_const (a := (0:ℝ))) measurable_fst).compl.union
      (measurableSet_eq_fun measurable_fst ((hf.comp hm).comp measurable_snd)).compl
    convert hh using 1
    ext p
    simp only [P,mem_union,mem_compl_iff,mem_setOf_eq,imp_iff_not_or,Function.comp_def]
  apply FCAppendix.Resample.ae_resample G j P hP
  · intro u d u'
    simp only [P,Function.update_idem]
  · apply (Measure.ae_ae_comm hP).mpr
    apply Filter.Eventually.of_forall
    intro d
    by_cases hfpos : 0 < f (Function.update d j 1)
    · have hz := measure_eq_zero_iff_ae_notMem.mp (hatom _ hfpos)
      filter_upwards [hz] with u hu _ he
      exact hu he
    · exact Filter.Eventually.of_forall fun u hu he => hfpos (he ▸ hu)

noncomputable def boundaryBid (n c : ℕ) (hn : 2 ≤ n) (i j : ι) (q : ℝ)
    (d : ι → ℝ) : ℝ :=
  (d i/q) / H n ((c:ℝ) - ∑ k ∈ Finset.univ.erase j,
    measurableKernel n hn (d k) (d i/q))

theorem measurable_boundaryBid (n c : ℕ) (hn : 2 ≤ n) (i j : ι) (q : ℝ) :
    Measurable (boundaryBid n c hn i j q) := by
  have hcoord (k : ι) : Measurable (fun d : ι → ℝ => d k) := measurable_pi_apply k
  have hsum : Measurable (fun d : ι → ℝ => ∑ k ∈ Finset.univ.erase j,
      measurableKernel n hn (d k) (d i/q)) := by
    apply Finset.measurable_sum
    intro k _
    exact (measurable_measurableKernel hn).comp ((hcoord k).prodMk ((hcoord i).div_const q))
  exact ((hcoord i).div_const q).div
    ((continuous_H n).measurable.comp (measurable_const.sub hsum))

theorem boundaryBid_eq_of_clearing {n c : ℕ} (hn : 2 ≤ n) (d : ι → ℝ)
    {i j : ι} (hij : i ≠ j) {q L : ℝ} (hL : 0 < L) (he : d i/q = L)
    (hcap : ∑ k, kernel n (d k) L = (c:ℝ))
    (hint : kernel n (d j) L ∈ Ioo (0:ℝ) 1) :
    d j = boundaryBid n c hn i j q (Function.update d j 1) := by
  have hdj : 0 < d j := by
    by_contra hnpos
    have hz := kernel_of_le n ((le_of_not_gt hnpos).trans hL.le)
    linarith [hint.1]
  have hsum : (∑ k ∈ Finset.univ.erase j,
      measurableKernel n hn (Function.update d j 1 k) (Function.update d j 1 i/q)) =
      ∑ k ∈ Finset.univ.erase j, kernel n (d k) L := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk),Function.update_of_ne hij,he]
    exact measurableKernel_eq hn _ hL
  unfold boundaryBid
  rw [hsum,Function.update_of_ne hij,he]
  have hp := (scalarThreshold_kernel n hn hdj hL).2.2.2.2 hint.1 hint.2
  have hh : (c:ℝ) - ∑ k ∈ Finset.univ.erase j, kernel n (d k) L = kernel n (d j) L := by
    rw [← hcap,← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
    ring
  rw [hh]
  exact (eq_div_iff (H_pos n (by omega) _ hint.1.le hint.2.le).ne').mpr hp

theorem ae_no_interior_clipping (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) {n : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ d ∂Measure.pi (fun _ : ι => G), ∀ c : ℕ, ∀ L, 0 < L →
      (∑ k, kernel n (d k) L = (c:ℝ)) → ∀ i j,
      kernel n (d j) L ∈ Ioo (0:ℝ) 1 → d i ≠ L ∧ d i ≠ (n:ℝ)*L := by
  have hgraph (q : ℝ) : ∀ᵐ d ∂Measure.pi (fun _ : ι => G), ∀ c : ℕ, ∀ i j,
      0 < d j → d j ≠ boundaryBid n c hn i j q (Function.update d j 1) :=
    ae_all_iff.mpr fun c => ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
      ae_positive_coord_ne_erased_function G hatom j _ (measurable_boundaryBid n c hn i j q)
  filter_upwards [hgraph 1,hgraph n] with d hg0 hg1
  intro c L hL hcap i j hj
  have hdj : 0 < d j := by
    by_contra hnpos
    have hz := kernel_of_le n ((le_of_not_gt hnpos).trans hL.le)
    linarith [hj.1]
  constructor
  · intro he
    have hij : i ≠ j := by
      intro hij
      subst j
      have hz := kernel_of_le n he.le
      linarith [hj.1]
    exact hg0 c i j hdj (boundaryBid_eq_of_clearing hn d hij hL (by simpa using he) hcap hj)
  · intro he
    have hij : i ≠ j := by
      intro hij
      subst j
      have hz := kernel_of_ge n hn hL he.ge
      linarith [hj.2]
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact hg1 c i j hdj (boundaryBid_eq_of_clearing hn d hij hL
      ((div_eq_iff hn0).mpr (by simpa [mul_comm] using he)) hcap hj)

theorem ae_no_positive_ratio_pairs (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) (n : ℕ) :
    ∀ᵐ d ∂Measure.pi (fun _ : ι => G), ∀ i j, i ≠ j → 0 < d j → d j ≠ (n:ℝ)*d i := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
  · have hm : Measurable (fun d : ι → ℝ => (n:ℝ)*d i) :=
      measurable_const.mul (measurable_pi_apply i)
    filter_upwards [ae_positive_coord_ne_erased_function G hatom j _ hm] with d hd _
    simpa only [Function.update_of_ne hij] using hd

theorem ae_regularRoot (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ b : ℝ, 0 < b → G {b} = 0) {n c : ℕ} (hn : 2 ≤ n) :
    ∀ᵐ d ∂Measure.pi (fun _ : ι => G),
      NullClipping.RegularRoot n (min c (Fintype.card (Active d))) d := by
  filter_upwards [ae_no_interior_clipping G hatom hn,ae_no_positive_ratio_pairs G hatom n]
    with d hclip hratio
  let C := min c (Fintype.card (Active d))
  obtain ⟨μ,hμ,_⟩ := exists_equilibrium n hn (fun j : Active d => d j.val)
    (fun j => j.property) C (min_le_right _ _)
  obtain ⟨L,hL,_,hcap⟩ := equilibrium_kernel n hn (fun j : Active d => d j.val)
    (fun j => j.property) C (min_le_right _ _) μ hμ
  have hfull : ∑ j, kernel n (d j) L = (C:ℝ) := by
    rw [← sum_active d hL]
    exact hcap
  by_cases hi : ∃ j, kernel n (d j) L ∈ Ioo (0:ℝ) 1
  · obtain ⟨j,hj⟩ := hi
    exact ⟨L,hL,hfull,fun i => (hclip C L hL hfull i j hj).1,
      fun i => (hclip C L hL hfull i j hj).2⟩
  · have hend : ∀ j : Active d, kernel n (d j.val) L = 0 ∨ kernel n (d j.val) L = 1 := by
      intro j
      have hk := scalarThreshold_kernel n hn j.property hL
      by_cases hz : kernel n (d j.val) L = 0
      · exact Or.inl hz
      · right
        by_contra ho
        exact hi ⟨j.val,lt_of_le_of_ne hk.1 (Ne.symm hz),lt_of_le_of_ne hk.2.1 ho⟩
    have hr : ∀ i j : Active d, i ≠ j → d j.val ≠ (n:ℝ)*d i.val := by
      intro i j hij
      exact hratio i.val j.val (fun he => hij (Subtype.ext he)) j.property
    obtain ⟨T,hT,hTcap,hz,ho⟩ := NullClipping.regularRoot_of_endpoints hn
      (fun j : Active d => d j.val) (fun j => j.property) hL hcap hend hr
    refine ⟨T,hT,?_,?_,?_⟩
    · rw [← sum_active d hT]
      exact hTcap
    · intro j
      by_cases hj : 0 < d j
      · exact hz ⟨j,hj⟩
      · exact (lt_of_le_of_lt (le_of_not_gt hj) hT).ne
    · intro j
      by_cases hj : 0 < d j
      · exact ho ⟨j,hj⟩
      · exact (lt_of_le_of_lt (le_of_not_gt hj)
          (mul_pos (by exact_mod_cast (show 0 < n by omega)) hT)).ne

end FCAppendix.PayOnce.DummyNullClipping
