import FCAppendix.Affine.Tail04.JoinedHighPolicy

set_option maxHeartbeats 500000

noncomputable section
namespace FCAppendix.Affine.Tail04.AllCountHighPolicy
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon JoinedHighPolicy

local instance (ι : Type*) : TopologicalSpace (Finset ι) := ⊥
local instance (ι : Type*) : DiscreteTopology (Finset ι) := ⟨rfl⟩
local instance (ι : Type*) : MeasurableSpace (Finset ι) := ⊤
local instance (ι : Type*) : BorelSpace (Finset ι) := ⟨borel_eq_top_of_discrete.symm⟩

def equalBase (N H c : ℕ) (ξ B R Rp Rm : ℝ)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hR : 0 ≤ R) (hRpB : Rp ≤ B) (hBRm : B < Rm) (hRm : 0 < Rm) :
    (PolicyParameters N H R Rp 1 B × Row H R Rp Rm) → unitInterval → Finset (Target N H) :=
  Classical.choose (exists_equal_upper_sampler N H c R Rp Rm ξ 1 B
    hξ (by norm_num) hR hRpB hBRm hRm)

def equalSample (N H c : ℕ) (ξ B R Rp Rm : ℝ)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hR : 0 ≤ R) (hRpB : Rp ≤ B) (hBRm : B < Rm) (hRm : 0 < Rm) :
    (Parameters N H R Rp B × Row H R Rp Rm) → unitInterval → Finset (Target N H) :=
  fun z u => equalBase N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm (equalParameter z.1,z.2) u

lemma equal_measurable (N H c : ℕ) (ξ B R Rp Rm : ℝ)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hR : 0 ≤ R) (hRpB : Rp ≤ B) (hBRm : B < Rm) (hRm : 0 < Rm) :
    Measurable (Function.uncurry (equalSample N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm)) := by
  have h := (Classical.choose_spec (exists_equal_upper_sampler N H c R Rp Rm ξ 1 B
    hξ (by norm_num) hR hRpB hBRm hRm)).1
  have he : Measurable (equalParameter : Parameters N H R Rp B → PolicyParameters N H R Rp 1 B) :=
    (measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  exact h.comp (((he.comp (measurable_fst.comp measurable_fst)).prodMk
    (measurable_snd.comp measurable_fst)).prodMk measurable_snd)

lemma equal_capacity (N H c : ℕ) (ξ B R Rp Rm : ℝ)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hR : 0 ≤ R) (hRpB : Rp ≤ B) (hBRm : B < Rm) (hRm : 0 < Rm)
    (p : Parameters N H R Rp B) (row : Row H R Rp Rm) (u : unitInterval) :
    (equalSample N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm (p,row) u).card ≤ c :=
  (Classical.choose_spec (exists_equal_upper_sampler N H c R Rp Rm ξ 1 B
    hξ (by norm_num) hR hRpB hBRm hRm)).2.2.1 (equalParameter p) row u

lemma equal_law (N H c : ℕ) (ξ B R Rp Rm : ℝ)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hR : 0 ≤ R) (hRpB : Rp ≤ B) (hBRm : B < Rm) (hRm : 0 < Rm)
    (p : Parameters N H R Rp B) (row : Row H R Rp Rm) :
    volume.map (equalSample N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm (p,row)) =
      (rowKernel (c := c) (ξ := ξ) (equalParameter p) row).map
        (fun a => restore (publicBids p) (policyMean N H c R Rp ξ 1 B (equalParameter p)) ξ row a) := by
  have hbids : EqualPrivateMeasurable.bids (equalParameter p) = publicBids p := rfl
  rw [←hbids]
  exact (Classical.choose_spec (exists_equal_upper_sampler N H c R Rp Rm ξ 1 B
    hξ (by norm_num) hR hRpB hBRm hRm)).2.1 (equalParameter p) row

theorem equal_mean (N H c : ℕ) (ξ B R Rp Rm : ℝ)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hR : 0 ≤ R) (hRpB : Rp ≤ B) (hBRm : B < Rm) (hRm : 0 < Rm)
    (p : Parameters N H R Rp B) (θ : Measure (Row H R Rp Rm)) [IsProbabilityMeasure θ]
    (hθ : θ.map signal=WeakProbability.toMeasure p.2.1) (i : Fin N) :
    LocalSamplerMean.mean (equalSample N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm) p θ (Sum.inl i) =
      policyMean N H c R Rp ξ 1 B (equalParameter p) i := by
  let r : Row H R Rp Rm × Action N H c → Finset (Target N H) := fun z =>
    restore (publicBids p) (policyMean N H c R Rp ξ 1 B (equalParameter p)) ξ z.1 z.2
  have hr : Measurable r := by
    simpa only [Function.comp_def, r] using (measurable_restore ξ).comp
      ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  rw [LocalSamplerMean.of_kernel_map _
    (equal_measurable N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm) p θ
    (rowKernel (c := c) (ξ := ξ) (equalParameter p)) r hr
    (equal_law N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm p)]
  exact original_row_active_mean (equalParameter p) θ hθ i

theorem equal_original_optimal (N H c : ℕ) (ξ B R Rp Rm : ℝ)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hR : 0 ≤ R) (hRpB : Rp ≤ B) (hBRm : B < Rm) (hRm : 0 < Rm)
    (p : Parameters N H R Rp B) (θ : Measure (Row H R Rp Rm)) [IsProbabilityMeasure θ]
    (hθ : θ.map signal=WeakProbability.toMeasure p.2.1)
    (row : Row H R Rp Rm) (u : unitInterval) :
    Finite.Optimal c
      (receipt (publicBids p)
        (fun i => LocalSamplerMean.mean (equalSample N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm)
          p θ (Sum.inl i)) ξ row)
      (equalSample N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm (p,row) u) := by
  have hq : (fun i => LocalSamplerMean.mean (equalSample N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm)
      p θ (Sum.inl i)) = policyMean N H c R Rp ξ 1 B (equalParameter p) :=
    funext (equal_mean N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm p θ hθ)
  rw [hq]
  exact (Classical.choose_spec (exists_equal_upper_sampler N H c R Rp Rm ξ 1 B
    hξ (by norm_num) hR hRpB hBRm hRm)).2.2.2.1 (equalParameter p) row u

def castRow {H K : ℕ} {R Rp Rm : ℝ} (h : H=K) (row : Row K R Rp Rm) : Row H R Rp Rm :=
  fun k => row (Fin.cast h k)

lemma continuous_castRow {H K : ℕ} {R Rp Rm : ℝ} (h : H=K) :
    Continuous (castRow (R := R) (Rp := Rp) (Rm := Rm) h) :=
  continuous_pi fun k => continuous_apply (Fin.cast h k)

def OriginalRowCompatibility (N H0 H1 : ℕ) (R Rp Rm B : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B)
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm)) : Prop :=
  if h : H0=H1 then
    θ0.map signal=WeakProbability.toMeasure p.2.1 ∧
      θ1.map (fun row => signal (castRow h row))=WeakProbability.toMeasure p.2.1
  else
    θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0 ∧
      θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1

theorem exists_all_count_high (N H0 H1 c : ℕ) (ξ B R Rp Rm width π : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hB : 1 ≤ B) (hw : 0 < width) (hπ : 0 ≤ π)
    (hR : 0 < R) (hRRp : R ≤ Rp) (hRp : Rp < 1) (hBRm : B < Rm)
    (hrare0 : (1-ξ)*B+ξ*B*((H0:ℝ)*π) ≤ R)
    (hrare1 : (1-ξ)*B+ξ*B*((H1:ℝ)*π) ≤ R) (hfirst : (1-ξ)*B < 1)
    (hany0 : ν0.prob AtypicalOriginalPosterior.anyUpper ≤ (H0:ℝ)*π)
    (hany1 : ν1.prob AtypicalOriginalPosterior.anyUpper ≤ (H1:ℝ)*π) :
    ∃ (f0 : (Parameters N H0 R Rp B × Row H0 R Rp Rm) → unitInterval → Finset (Target N H0))
      (f1 : (Parameters N H0 R Rp B × Row H1 R Rp Rm) → unitInterval → Finset (Target N H1)),
      Measurable (Function.uncurry f0) ∧ Measurable (Function.uncurry f1) ∧
      (∀ p row u, (f0 (p,row) u).card ≤ c) ∧
      (∀ p row u, (f1 (p,row) u).card ≤ c) ∧
      (∀ (p : Parameters N H0 R Rp B)
        (θ0 : ProbabilityMeasure (Row H0 R Rp Rm)) (θ1 : ProbabilityMeasure (Row H1 R Rp Rm)),
        OriginalRowCompatibility N H0 H1 R Rp Rm B ν0 ν1 p θ0 θ1 →
        (∀ row u, Finite.Optimal c
          (receipt (publicBids p) (fun i => LocalSamplerMean.mean f1 p (θ1 : Measure (Row H1 R Rp Rm)) (Sum.inl i)) ξ row)
          (f0 (p,row) u)) ∧
        (∀ row u, Finite.Optimal c
          (receipt (publicBids p) (fun i => LocalSamplerMean.mean f0 p (θ0 : Measure (Row H0 R Rp Rm)) (Sum.inl i)) ξ row)
          (f1 (p,row) u))) := by
  by_cases heq : H0=H1
  · subst H1
    let f := equalSample N H0 c ξ B R Rp Rm ⟨hξ.le,hξ1⟩ hR.le
      (hRp.le.trans hB) hBRm (((by norm_num : (0:ℝ)<1).trans_le hB).trans hBRm)
    have hf := equal_measurable N H0 c ξ B R Rp Rm ⟨hξ.le,hξ1⟩ hR.le
      (hRp.le.trans hB) hBRm (((by norm_num : (0:ℝ)<1).trans_le hB).trans hBRm)
    have hc := equal_capacity N H0 c ξ B R Rp Rm ⟨hξ.le,hξ1⟩ hR.le
      (hRp.le.trans hB) hBRm (((by norm_num : (0:ℝ)<1).trans_le hB).trans hBRm)
    refine ⟨f,f,hf,hf,hc,hc,?_⟩
    intro p θ0 θ1 hcomp
    have hcast : (fun row : Row H0 R Rp Rm => signal (castRow (rfl : H0=H0) row)) = signal := by
      funext row
      apply congrArg signal
      funext i
      apply congrArg row
      apply Fin.ext
      rfl
    have hh : (θ0 : Measure (Row H0 R Rp Rm)).map signal=WeakProbability.toMeasure p.2.1 ∧
        (θ1 : Measure (Row H0 R Rp Rm)).map signal=WeakProbability.toMeasure p.2.1 := by
      simpa [OriginalRowCompatibility, hcast] using hcomp
    constructor
    · exact equal_original_optimal N H0 c ξ B R Rp Rm ⟨hξ.le,hξ1⟩ hR.le
        (hRp.le.trans hB) hBRm (((by norm_num : (0:ℝ)<1).trans_le hB).trans hBRm) p (θ1 : Measure (Row H0 R Rp Rm)) hh.2
    · exact equal_original_optimal N H0 c ξ B R Rp Rm ⟨hξ.le,hξ1⟩ hR.le
        (hRp.le.trans hB) hBRm (((by norm_num : (0:ℝ)<1).trans_le hB).trans hBRm) p (θ0 : Measure (Row H0 R Rp Rm)) hh.1
  · let f0 := unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1
    let f1 := unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1
    refine ⟨f0,f1,measurable_unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1,
      measurable_unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1,
      unequal0_capacity N H0 H1 c ξ B R Rp Rm width ν0 ν1 hξ hξ1 hw,
      unequal1_capacity N H0 H1 c ξ B R Rp Rm width ν0 ν1 hξ hξ1 hw,?_⟩
    intro p θ0 θ1 hcomp
    have hh : (θ0 : Measure (Row H0 R Rp Rm)).map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0 ∧
        (θ1 : Measure (Row H1 R Rp Rm)).map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1 := by
      simpa [OriginalRowCompatibility,heq] using hcomp
    exact ⟨unequal0_optimal N H0 H1 c ξ B R Rp Rm width π ν0 ν1 hξ hξ1 hB hw hπ
        hR hRRp hRp hBRm hrare1 hfirst hany1 p (θ1 : Measure (Row H1 R Rp Rm)) hh.2,
      unequal1_optimal N H0 H1 c ξ B R Rp Rm width π ν0 ν1 hξ hξ1 hB hw hπ
        hR hRRp hRp hBRm hrare0 hfirst hany0 p (θ0 : Measure (Row H0 R Rp Rm)) hh.1⟩

theorem optimal_upper_rank {N H c : ℕ} {R Rp Rm B ξ : ℝ}
    (b q : Fin N → ℝ) (row : Row H R Rp Rm) (S : Finset (Target N H))
    (hopt : Finite.Optimal c (receipt b q ξ row) S)
    (hξ : 0 ≤ ξ) (hb : ∀ i, b i ∈ Icc (0:ℝ) B) (hq : ∀ i, 0 ≤ q i)
    (hRp : Rp ≤ B) (hBRm : B < Rm) (hRm : 0 < Rm)
    (j : Fin H) (hj : Sum.inr j ∈ upperPool N row)
    (hno : ∀ i ∈ upperPool N row, i ≠ Sum.inr j →
      receipt b q ξ row i ≠ numericalEntry (row j)) :
    Sum.inr j ∈ S ↔
      ((upperPool N row).filter fun i => numericalEntry (row j) < receipt b q ξ row i).card < c := by
  let r := receipt b q ξ row
  have hrj : r (Sum.inr j)=numericalEntry (row j) := rfl
  have hjpos : 0 < r (Sum.inr j) := hRm.trans_le (receipt_upper_ge b q ξ row _ hj)
  have houtside (i : Target N H) (hi : i ∉ upperPool N row) : r i < r (Sum.inr j) :=
    (receipt_nonupper_le b q ξ row hξ hb hq hRp i hi).trans_lt
      (hBRm.trans_le (receipt_upper_ge b q ξ row _ hj))
  have hbetter : (Finset.univ.filter fun i => r (Sum.inr j) < r i)=
      (upperPool N row).filter fun i => numericalEntry (row j) < r i := by
    ext i
    by_cases hi : i ∈ upperPool N row
    · simp [hi,hrj]
    · have hh : r i < numericalEntry (row j) := by simpa only [hrj] using houtside i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi, false_and, iff_false]
      exact not_lt.mpr hh.le
  have hcompetitors : (Finset.univ.filter fun i => i ≠ Sum.inr j ∧ r (Sum.inr j) ≤ r i)=
      (upperPool N row).filter fun i => numericalEntry (row j) < r i := by
    ext i
    by_cases hi : i ∈ upperPool N row
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,hi,hrj]
      constructor
      · intro hh
        exact lt_of_le_of_ne hh.2 (hno i hi hh.1).symm
      · intro hh
        exact ⟨fun he => by subst i; exact (lt_irrefl _ hh),hh.le⟩
    · have hh : r i < numericalEntry (row j) := by simpa only [hrj] using houtside i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi, false_and, iff_false]
      exact fun h => (not_le.mpr hh) h.2
  constructor
  · intro hs
    by_contra hn
    have he := Finite.excluded_of_many_better c r S hopt (Sum.inr j)
      (by rw [hbetter]; exact le_of_not_gt hn)
    exact he hs
  · intro hrank
    exact Finite.included_of_few_competitors c r S hopt (Sum.inr j) hjpos
      (by simpa only [hcompetitors] using hrank)

end FCAppendix.Affine.Tail04.AllCountHighPolicy
