import FCAppendix.PayOnce.CoverageDerivative
import FCAppendix.Probability.Resample

namespace FCAppendix.PayOnce.NullClipping
open MeasureTheory Filter Topology Set CommonList
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ae_coord_ne_erased_function (G : Measure ℝ) [IsProbabilityMeasure G]
    [NullSingletonClass G] (j : ι) (f : (ι → ℝ) → ℝ) (hf : Measurable f) :
    ∀ᵐ d ∂Measure.pi (fun _ : ι => G), d j ≠ f (Function.update d j 1) := by
  let P : ℝ → (ι → ℝ) → Prop := fun u d => u ≠ f (Function.update d j 1)
  have hm : Measurable (fun d : ι → ℝ => Function.update d j (1 : ℝ)) :=
    measurable_pi_lambda _ fun i => by
      by_cases hi : i = j
      · subst i; simp
      · simpa [Function.update_of_ne hi] using measurable_pi_apply i
  have hP : MeasurableSet {p : ℝ × (ι → ℝ) | P p.1 p.2} :=
    (measurableSet_eq_fun measurable_fst ((hf.comp hm).comp measurable_snd)).compl
  apply FCAppendix.Resample.ae_resample G j P hP
  · intro u d u'
    simp only [P, Function.update_idem]
  · apply (Measure.ae_ae_comm hP).mpr
    exact Filter.Eventually.of_forall fun d => G.ae_ne (f (Function.update d j 1))

noncomputable def positiveKernel (n : ℕ) (hn : 2 ≤ n) (b L : ℝ) : ℝ :=
  scalarDemand n hn 1 (by norm_num) (L / b)

theorem positiveKernel_eq {n : ℕ} (hn : 2 ≤ n) {b L : ℝ} (hb : 0 < b) (hL : 0 < L) :
    positiveKernel n hn b L = kernel n b L :=
  (KernelTailEvent.kernel_eq_scalarDemand_ratio hn hb hL).symm

noncomputable def boundaryBid (n c : ℕ) (hn : 2 ≤ n) (i j : ι) (q : ℝ)
    (d : ι → ℝ) : ℝ :=
  (d i / q) / H n ((c : ℝ) - ∑ k ∈ Finset.univ.erase j,
    positiveKernel n hn (d k) (d i / q))

theorem measurable_boundaryBid (n c : ℕ) (hn : 2 ≤ n) (i j : ι) (q : ℝ) :
    Measurable (boundaryBid n c hn i j q) := by
  have hcoord (k : ι) : Measurable (fun d : ι → ℝ => d k) := measurable_pi_apply k
  have hsum : Measurable (fun d : ι → ℝ => ∑ k ∈ Finset.univ.erase j,
      positiveKernel n hn (d k) (d i / q)) := by
    apply Finset.measurable_sum
    intro k _
    exact (scalarDemand_continuous n hn 1 (by norm_num)).measurable.comp
      (((hcoord i).div_const q).div (hcoord k))
  exact ((hcoord i).div_const q).div
    ((continuous_H n).measurable.comp (measurable_const.sub hsum))

theorem boundaryBid_eq_of_clearing {n c : ℕ} (hn : 2 ≤ n) (d : ι → ℝ)
    (hd : ∀ k, 0 < d k) {i j : ι} (hij : i ≠ j) {q L : ℝ}
    (hL : 0 < L) (he : d i / q = L)
    (hcap : ∑ k, kernel n (d k) L = (c : ℝ))
    (hint : kernel n (d j) L ∈ Ioo (0 : ℝ) 1) :
    d j = boundaryBid n c hn i j q (Function.update d j 1) := by
  have hsum : (∑ k ∈ Finset.univ.erase j,
      positiveKernel n hn (Function.update d j 1 k) (Function.update d j 1 i / q)) =
      ∑ k ∈ Finset.univ.erase j, kernel n (d k) L := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk), Function.update_of_ne hij, he]
    exact positiveKernel_eq hn (hd k) hL
  unfold boundaryBid
  rw [hsum, Function.update_of_ne hij, he]
  have hp := (scalarThreshold_kernel n hn (hd j) hL).2.2.2.2 hint.1 hint.2
  have hh : (c : ℝ) - ∑ k ∈ Finset.univ.erase j, kernel n (d k) L = kernel n (d j) L := by
    rw [← hcap, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
    ring
  rw [hh]
  exact (eq_div_iff (H_pos n (by omega) _ hint.1.le hint.2.le).ne').mpr hp

theorem ae_no_interior_clipping (G : Measure ℝ) [IsProbabilityMeasure G]
    [NullSingletonClass G] {n c : ℕ} (hn : 2 ≤ n)
    (hpos : ∀ᵐ b ∂G, 0 < b) :
    ∀ᵐ d ∂Measure.pi (fun _ : ι => G), ∀ L, 0 < L →
      (∑ k, kernel n (d k) L = (c : ℝ)) → ∀ i j,
      kernel n (d j) L ∈ Ioo (0 : ℝ) 1 → d i ≠ L ∧ d i ≠ (n : ℝ) * L := by
  have hpositive : ∀ᵐ d ∂Measure.pi (fun _ : ι => G), ∀ k, 0 < d k :=
    Filter.eventually_all.mpr fun _ => Measure.tendsto_eval_ae_ae.eventually hpos
  have hgraph (q : ℝ) : ∀ᵐ d ∂Measure.pi (fun _ : ι => G), ∀ i j,
      d j ≠ boundaryBid n c hn i j q (Function.update d j 1) :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      ae_coord_ne_erased_function G j _ (measurable_boundaryBid n c hn i j q)
  filter_upwards [hpositive, hgraph 1, hgraph n] with d hd hg0 hg1
  intro L hL hcap i j hj
  constructor
  · intro he
    have hij : i ≠ j := by
      intro hij
      subst j
      have hz := kernel_of_le n he.le
      linarith [hj.1]
    exact hg0 i j (boundaryBid_eq_of_clearing hn d hd hij hL (by simpa using he) hcap hj)
  · intro he
    have hij : i ≠ j := by
      intro hij
      subst j
      have hz := kernel_of_ge n hn hL he.ge
      linarith [hj.2]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact hg1 i j (boundaryBid_eq_of_clearing hn d hd hij hL
      ((div_eq_iff hn0).mpr (by simpa [mul_comm] using he)) hcap hj)

theorem ae_no_ratio_pairs (G : Measure ℝ) [IsProbabilityMeasure G]
    [NullSingletonClass G] (n : ℕ) :
    ∀ᵐ d ∂Measure.pi (fun _ : ι => G), ∀ i j, i ≠ j → d j ≠ (n : ℝ) * d i := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
  · have hm : Measurable (fun d : ι → ℝ => (n : ℝ) * d i) :=
      measurable_const.mul (measurable_pi_apply i)
    filter_upwards [ae_coord_ne_erased_function G j _ hm] with d hd _
    simpa only [Function.update_of_ne hij] using hd

def RegularRoot (n c : ℕ) (d : ι → ℝ) : Prop :=
  ∃ L, 0 < L ∧ (∑ k, kernel n (d k) L = (c : ℝ)) ∧
    (∀ k, d k ≠ L) ∧ (∀ k, d k ≠ (n : ℝ) * L)

omit [DecidableEq ι] in
theorem regularRoot_of_strict_endpoints {n c : ℕ} (hn : 2 ≤ n)
    (d : ι → ℝ) {L T : ℝ} (hT : 0 < T)
    (hcap : ∑ k, kernel n (d k) L = (c : ℝ))
    (hend : ∀ k, kernel n (d k) L = 0 ∨ kernel n (d k) L = 1)
    (hz : ∀ k, kernel n (d k) L = 0 → d k < T)
    (ho : ∀ k, kernel n (d k) L = 1 → (n : ℝ) * T < d k) : RegularRoot n c d := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hTn : T < (n : ℝ) * T := by nlinarith
  have he (k : ι) : kernel n (d k) T = kernel n (d k) L := by
    rcases hend k with hk | hk
    · rw [kernel_of_le n (hz k hk).le, hk]
    · rw [kernel_of_ge n hn hT (ho k hk).le, hk]
  refine ⟨T, hT, (Finset.sum_congr rfl fun k _ => he k).trans hcap, ?_, ?_⟩
  · intro k
    rcases hend k with hk | hk
    · exact (hz k hk).ne
    · exact (hTn.trans (ho k hk)).ne'
  · intro k
    rcases hend k with hk | hk
    · exact ((hz k hk).trans hTn).ne
    · exact (ho k hk).ne'

omit [DecidableEq ι] in

theorem regularRoot_of_endpoints {n c : ℕ} (hn : 2 ≤ n) (d : ι → ℝ)
    (hd : ∀ k, 0 < d k) {L : ℝ} (hL : 0 < L)
    (hcap : ∑ k, kernel n (d k) L = (c : ℝ))
    (hend : ∀ k, kernel n (d k) L = 0 ∨ kernel n (d k) L = 1)
    (hratio : ∀ i j, i ≠ j → d j ≠ (n : ℝ) * d i) : RegularRoot n c d := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hzero : ∀ k, d k ≠ L
  · have hev : ∀ᶠ T in 𝓝 L, ∀ k, kernel n (d k) L = 0 → d k < T := by
      apply Filter.eventually_all.mpr
      intro k
      by_cases hk : kernel n (d k) L = 0
      · have hdk : d k < L := lt_of_le_of_ne ((kernel_eq_zero_iff n hn (hd k) hL).mp hk) (hzero k)
        filter_upwards [eventually_gt_nhds hdk] with T hT _
        exact hT
      · exact Filter.Eventually.of_forall fun _ he => (hk he).elim
    have hchoice : ∀ᶠ T in 𝓝[<] L, 0 < T ∧ T < L ∧
        ∀ k, kernel n (d k) L = 0 → d k < T := by
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds,
        (eventually_gt_nhds hL).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with T he hp ht
      exact ⟨hp, ht, he⟩
    obtain ⟨T, hT, hTL, hz⟩ := hchoice.exists
    apply regularRoot_of_strict_endpoints hn d hT hcap hend hz
    intro k hk
    have hh := (le_div_iff₀ hnR).mp ((kernel_eq_one_iff n hn (hd k) hL).mp hk)
    nlinarith
  · push Not at hzero
    obtain ⟨i, hi⟩ := hzero
    have hstrict (k : ι) (hk : kernel n (d k) L = 1) : (n : ℝ) * L < d k := by
      have hh := (le_div_iff₀ hnR).mp ((kernel_eq_one_iff n hn (hd k) hL).mp hk)
      have hne : d k ≠ (n : ℝ) * L := by
        intro he
        by_cases hik : i = k
        · subst k
          nlinarith
        · exact hratio i k hik (by simpa only [hi] using he)
      exact lt_of_le_of_ne (by nlinarith) hne.symm
    have hev : ∀ᶠ T in 𝓝 L, ∀ k, kernel n (d k) L = 1 → (n : ℝ) * T < d k := by
      apply Filter.eventually_all.mpr
      intro k
      by_cases hk : kernel n (d k) L = 1
      · have ht := (tendsto_const_nhds.mul tendsto_id).eventually_lt_const (hstrict k hk)
        filter_upwards [ht] with T hT _
        exact hT
      · exact Filter.Eventually.of_forall fun _ he => (hk he).elim
    have hchoice : ∀ᶠ T in 𝓝[>] L, L < T ∧
        ∀ k, kernel n (d k) L = 1 → (n : ℝ) * T < d k := by
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with T he ht
      exact ⟨ht, he⟩
    obtain ⟨T, hLT, ho⟩ := hchoice.exists
    apply regularRoot_of_strict_endpoints hn d (hL.trans hLT) hcap hend ?_ ho
    intro k hk
    exact ((kernel_eq_zero_iff n hn (hd k) hL).mp hk).trans_lt hLT

theorem ae_positive_regularRoot (G : Measure ℝ) [IsProbabilityMeasure G]
    [NullSingletonClass G] {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι)
    (hpos : ∀ᵐ b ∂G, 0 < b) :
    ∀ᵐ d ∂Measure.pi (fun _ : ι => G), (∀ k, 0 < d k) ∧ RegularRoot n c d := by
  have hpositive : ∀ᵐ d ∂Measure.pi (fun _ : ι => G), ∀ k, 0 < d k :=
    Filter.eventually_all.mpr fun _ => Measure.tendsto_eval_ae_ae.eventually hpos
  filter_upwards [hpositive, ae_no_interior_clipping G hn hpos, ae_no_ratio_pairs G n]
    with d hd hclip hratio
  refine ⟨hd, ?_⟩
  obtain ⟨μ, hμ, _⟩ := exists_equilibrium n hn d hd c hc
  obtain ⟨L, hL, _, hcap⟩ := equilibrium_kernel n hn d hd c hc μ hμ
  by_cases hi : ∃ j, kernel n (d j) L ∈ Ioo (0 : ℝ) 1
  · obtain ⟨j, hj⟩ := hi
    exact ⟨L, hL, hcap, fun i => (hclip L hL hcap i j hj).1,
      fun i => (hclip L hL hcap i j hj).2⟩
  · apply regularRoot_of_endpoints hn d hd hL hcap ?_ hratio
    intro k
    have hk := scalarThreshold_kernel n hn (hd k) hL
    by_cases hz : kernel n (d k) L = 0
    · exact Or.inl hz
    · right
      by_contra ho
      exact hi ⟨k, lt_of_le_of_ne hk.1 (Ne.symm hz), lt_of_le_of_ne hk.2.1 ho⟩

theorem ae_regularClearing (G : Measure ℝ) [IsProbabilityMeasure G]
    [NullSingletonClass G] {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (hpos : ∀ᵐ b ∂G, 0 < b) :
    ∀ᵐ b ∂G, ∀ᵐ rivals ∂Measure.pi (fun _ : ι => G),
      AnalyticalKernel.RegularClearing n c rivals b := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)
  have hfull := ae_positive_regularRoot (ι := Option ι) G hn (by simpa using hc) hpos
  rw [← Measure.pi_map_piOptionEquivProd (fun _ : Option ι => G)] at hfull
  have hp := ae_of_ae_map e.symm.measurable.aemeasurable hfull
  have hreg : ∀ᵐ z ∂(Measure.pi (fun _ : ι => G)).prod G,
      AnalyticalKernel.RegularClearing n c z.1 z.2 := by
    filter_upwards [hp] with z hz
    obtain ⟨hpositive, L, hL, hcap, hz0, hz1⟩ := hz
    refine ⟨fun j => hpositive (some j), L, hL, ?_, hz0 none, hz1 none,
      fun j => hz0 (some j), fun j => hz1 (some j)⟩
    change kernel n (e.symm z none) L + ∑ j, kernel n (e.symm z (some j)) L = (c : ℝ)
    simpa only [Fintype.sum_option, add_comm] using hcap
  have hswap : ∀ᵐ z ∂G.prod (Measure.pi (fun _ : ι => G)),
      AnalyticalKernel.RegularClearing n c z.2 z.1 := by
    have hh := hreg
    rw [← Measure.prod_swap] at hh
    exact ae_of_ae_map measurable_swap.aemeasurable hh
  exact Measure.ae_ae_of_ae_prod hswap

theorem ae_hasDerivAt_coverage (G : Measure ℝ) [IsProbabilityMeasure G]
    [NullSingletonClass G] {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (hpos : ∀ᵐ b ∂G, 0 < b) :
    ∀ᵐ b ∂G,
      Integrable (fun rivals => deriv (fun x => success n
        (AnalyticalKernel.allocation n c hn hc rivals x)) b) (Measure.pi (fun _ : ι => G)) ∧
      HasDerivAt (AnalyticalKernel.coverage n c hn hc (Measure.pi (fun _ : ι => G)))
        (∫ rivals, deriv (fun x => success n
          (AnalyticalKernel.allocation n c hn hc rivals x)) b ∂Measure.pi (fun _ : ι => G)) b := by
  filter_upwards [hpos, ae_regularClearing (ι := ι) G hn hc hpos] with b hb hreg
  exact AnalyticalKernel.hasDerivAt_coverage_of_regular hn hc _ hb hreg

end FCAppendix.PayOnce.NullClipping
