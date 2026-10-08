import FCAppendix.PayOnce.DummyCoverageDerivative

namespace FCAppendix.PayOnce.DummyFixedFocalRegularity
open MeasureTheory Filter Set CommonList DummyKernel OwnImpact
open scoped BigOperators
variable {ι : Type*}

def focalList (b : ℝ) (r : ι → ℝ) (i : Option ι) : ℝ := i.elim b r

@[simp] theorem focalList_none (b : ℝ) (r : ι → ℝ) : focalList b r none = b := rfl
@[simp] theorem focalList_some (b : ℝ) (r : ι → ℝ) (i : ι) : focalList b r (some i) = r i := rfl

theorem measurable_focalList (b : ℝ) : Measurable (focalList b : (ι → ℝ) → Option ι → ℝ) := by
  apply measurable_pi_lambda
  intro i
  cases i with
  | none => exact measurable_const
  | some i => exact measurable_pi_apply i

theorem focalList_update [DecidableEq ι] (b : ℝ) (r : ι → ℝ) (j : ι) (v : ℝ) :
    focalList b (Function.update r j v) = Function.update (focalList b r) (some j) v := by
  funext i
  cases i <;> simp [focalList,Function.update_apply]

variable [Fintype ι]

theorem ae_no_interior_clipping_fixed (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ x : ℝ, 0 < x → G {x} = 0) {n : ℕ} (hn : 2 ≤ n) (b : ℝ) :
    ∀ᵐ r ∂Measure.pi (fun _ : ι => G), ∀ C : ℕ, ∀ L, 0 < L →
      (∑ i, kernel n (focalList b r i) L = (C:ℝ)) → ∀ i j,
      kernel n (r j) L ∈ Ioo (0:ℝ) 1 →
        focalList b r i ≠ L ∧ focalList b r i ≠ (n:ℝ)*L := by
  classical
  have hgraph (q : ℝ) : ∀ᵐ r ∂Measure.pi (fun _ : ι => G), ∀ C : ℕ,
      ∀ i : Option ι, ∀ j : ι, 0 < r j →
        r j ≠ DummyNullClipping.boundaryBid n C hn i (some j) q
          (Function.update (focalList b r) (some j) 1) := by
    apply ae_all_iff.mpr
    intro C
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    have hh := DummyNullClipping.ae_positive_coord_ne_erased_function G hatom j
      (fun r => DummyNullClipping.boundaryBid n C hn i (some j) q (focalList b r))
      ((DummyNullClipping.measurable_boundaryBid n C hn i (some j) q).comp (measurable_focalList b))
    simpa only [focalList_update] using hh
  filter_upwards [hgraph 1,hgraph n] with r hg0 hg1
  intro C L hL hcap i j hj
  have hdj : 0 < r j := by
    by_contra hnpos
    have hz := kernel_of_le n ((le_of_not_gt hnpos).trans hL.le)
    linarith [hj.1]
  constructor
  · intro he
    have hij : i ≠ some j := by
      intro hij
      rw [hij] at he
      have hz := kernel_of_le n (show r j ≤ L from he.le)
      linarith [hj.1]
    exact hg0 C i j hdj (DummyNullClipping.boundaryBid_eq_of_clearing hn (focalList b r)
      hij hL (by simpa only [div_one] using he) hcap hj)
  · intro he
    have hij : i ≠ some j := by
      intro hij
      rw [hij] at he
      have hz := kernel_of_ge n hn hL (show (n:ℝ)*L ≤ r j from he.ge)
      linarith [hj.2]
    have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact hg1 C i j hdj (DummyNullClipping.boundaryBid_eq_of_clearing hn (focalList b r)
      hij hL ((div_eq_iff hn0).mpr (by simpa only [mul_comm] using he)) hcap hj)

theorem ae_rivals_ne_fixed (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ x : ℝ, 0 < x → G {x} = 0) {x : ℝ} (hx : 0 < x) :
    ∀ᵐ r ∂Measure.pi (fun _ : ι => G), ∀ j, r j ≠ x := by
  have hxne : ∀ᵐ y ∂G, y ≠ x := by
    simpa only [mem_singleton_iff] using measure_eq_zero_iff_ae_notMem.mp (hatom x hx)
  apply ae_all_iff.mpr
  intro j
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => G) (i := j)).eventually hxne

theorem ae_no_positive_ratio_pairs_fixed (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ x : ℝ, 0 < x → G {x} = 0) {n : ℕ} (hn : 2 ≤ n)
    {b : ℝ} (hb : 0 < b) :
    ∀ᵐ r ∂Measure.pi (fun _ : ι => G), ∀ i j : Option ι, i ≠ j →
      0 < focalList b r j → focalList b r j ≠ (n:ℝ)*focalList b r i := by
  classical
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  filter_upwards [DummyNullClipping.ae_no_positive_ratio_pairs G hatom n,
    ae_rivals_ne_fixed (ι := ι) G hatom (mul_pos hnR hb),
    ae_rivals_ne_fixed (ι := ι) G hatom (div_pos hb hnR)] with r hratio hnb hbn
  intro i j hij hj
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j => exact hnb j
  | some i =>
    cases j with
    | none =>
      intro he
      apply hbn i
      apply (eq_div_iff hnR.ne').mpr
      change b = (n:ℝ)*r i at he
      nlinarith
    | some j => exact hratio i j (fun h => hij (congrArg some h)) hj

theorem exists_interior_rival {n C : ℕ} (hn : 2 ≤ n) (b : ℝ) (r : ι → ℝ)
    {L : ℝ} (hL : 0 < L)
    (hcap : ∑ i, kernel n (focalList b r i) L = (C:ℝ))
    (hi : ∃ i, kernel n (focalList b r i) L ∈ Ioo (0:ℝ) 1) :
    ∃ j, kernel n (r j) L ∈ Ioo (0:ℝ) 1 := by
  classical
  obtain ⟨i,hi⟩ := hi
  cases i with
  | some i => exact ⟨i,hi⟩
  | none =>
    obtain ⟨j,hj,hji⟩ := exists_other_interior (fun i => kernel n (focalList b r i) L) C
      (fun i => KernelTailEvent.kernel_bounds hn hL (focalList b r i)) hcap none hi
    cases j with
    | none => exact (hj rfl).elim
    | some j => exact ⟨j,hji⟩

theorem ae_regularRoot_fixed_bid (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ x : ℝ, 0 < x → G {x} = 0) {n c : ℕ} (hn : 2 ≤ n)
    {b : ℝ} (hb : 0 < b) :
    ∀ᵐ r ∂Measure.pi (fun _ : ι => G),
      NullClipping.RegularRoot n (min c (Fintype.card (Active r)+1)) (focalList b r) := by
  classical
  filter_upwards [ae_no_interior_clipping_fixed (ι := ι) G hatom hn b,
    ae_no_positive_ratio_pairs_fixed (ι := ι) G hatom hn hb] with r hclip hratio
  let C := min c (Fintype.card (Active r)+1)
  let d := focalList b r
  obtain ⟨L,hL,_,hcap⟩ := allocation_root (c := c) hn r hb
  have hfull : ∑ i, kernel n (d i) L = (C:ℝ) := by
    simpa only [d,focalList,Fintype.sum_option,Option.elim_none,Option.elim_some] using hcap
  by_cases hi : ∃ i, kernel n (d i) L ∈ Ioo (0:ℝ) 1
  · obtain ⟨j,hj⟩ := exists_interior_rival hn b r hL hfull hi
    exact ⟨L,hL,hfull,fun i => (hclip C L hL hfull i j hj).1,
      fun i => (hclip C L hL hfull i j hj).2⟩
  · have hend : ∀ j : Active d, kernel n (d j.val) L = 0 ∨ kernel n (d j.val) L = 1 := by
      intro j
      have hk := KernelTailEvent.kernel_bounds hn hL (d j.val)
      by_cases hz : kernel n (d j.val) L = 0
      · exact Or.inl hz
      · right
        by_contra ho
        exact hi ⟨j.val,lt_of_le_of_ne hk.1 (Ne.symm hz),lt_of_le_of_ne hk.2 ho⟩
    have hcapA : (∑ j : Active d, kernel n (d j.val) L) = (C:ℝ) := by
      rw [sum_active d hL]
      exact hfull
    have hr : ∀ i j : Active d, i ≠ j → d j.val ≠ (n:ℝ)*d i.val := by
      intro i j hij
      exact hratio i.val j.val (fun he => hij (Subtype.ext he)) j.property
    obtain ⟨T,hT,hTcap,hz,ho⟩ := NullClipping.regularRoot_of_endpoints hn
      (fun j : Active d => d j.val) (fun j => j.property) hL hcapA hend hr
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
          (mul_pos (Nat.cast_pos.mpr (by omega : 0 < n)) hT)).ne

end FCAppendix.PayOnce.DummyFixedFocalRegularity

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList DummyFixedFocalRegularity
variable {ι : Type*} [Fintype ι]

theorem ae_regularClearing_fixed_bid (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ x : ℝ, 0 < x → G {x} = 0) {n c : ℕ} (hn : 2 ≤ n)
    {b : ℝ} (hb : 0 < b) :
    ∀ᵐ r ∂Measure.pi (fun _ : ι => G), RegularClearing n c r b := by
  filter_upwards [ae_regularRoot_fixed_bid (ι := ι) (c := c) G hatom hn hb] with r hr
  obtain ⟨L,hL,hcap,hzero,hone⟩ := hr
  refine ⟨fun j => j.property,L,hL,?_,hzero none,hone none,
    fun j => hzero (some j.val),fun j => hone (some j.val)⟩
  rw [sum_active r hL]
  simpa only [focalList,Fintype.sum_option,Option.elim_none,Option.elim_some] using hcap

theorem hasDerivAt_coverage_fixed_bid (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : ∀ x : ℝ, 0 < x → G {x} = 0) {n c : ℕ} (hn : 2 ≤ n)
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun r : ι → ℝ => deriv (fun x => success n (allocation n c hn r x)) b)
      (Measure.pi (fun _ : ι => G)) ∧
    HasDerivAt (coverage n c hn (Measure.pi (fun _ : ι => G)))
      (∫ r, deriv (fun x => success n (allocation n c hn r x)) b
        ∂Measure.pi (fun _ : ι => G)) b :=
  hasDerivAt_coverage_of_regular hn _ hb (ae_regularClearing_fixed_bid G hatom hn hb)

end FCAppendix.PayOnce.DummyKernel
