import FCAppendix.Affine.Uniform06.PrefixMonotonicity
import FCAppendix.Affine.LowBody.PatternFiniteEnvelope
import FCAppendix.Affine.LowBody.ClusterLossBound
import FCAppendix.Affine.LowBody.LiteralCarrierBounds

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.Uniform06.PureDuplicateIntervals

open MeasureTheory Set Filter LowBody
open scoped BigOperators

variable {N : ℕ}

def rowPureSelection (κ : ℝ) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) :
    Finset (Fin (N+1)) × Finset (Fin (N+1)) :=
  (patternTemplate c (fun j => (ω j).1)).selection κ (rowBids b ω)

def rowPureDuplicate (κ : ℝ) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  pureDuplicate (rowPureSelection κ c b ω) 0

theorem measurable_rowPureSelection (κ : ℝ) (c : ℕ) (b : ℝ) :
    Measurable (rowPureSelection (N := N) κ c b) := by
  have hk : Measurable (fun ω : Fin N → RowRival => fun j => (ω j).1) :=
    measurable_pi_lambda _ (fun j => (measurable_pi_apply j).fst)
  have hb : Measurable (fun ω : Fin N → RowRival => rowBids b ω) :=
    measurable_rowBids.comp (measurable_const.prodMk measurable_id)
  have hs : Measurable (fun q : (Fin N → Fin 4) × (Fin (N+1) → ℝ) =>
      (patternTemplate c q.1).selection κ q.2) :=
    measurable_from_prod_countable_right (fun k => (patternTemplate c k).measurable_selection κ)
  convert! hs.comp (hk.prodMk hb) using 1

theorem measurable_rowPureDuplicate (κ : ℝ) (c : ℕ) (b : ℝ) :
    Measurable (rowPureDuplicate (N := N) κ c b) :=
  (measurable_of_countable (fun P : Finset (Fin (N+1)) × Finset (Fin (N+1)) =>
    pureDuplicate P 0)).comp (measurable_rowPureSelection κ c b)

theorem rowPureDuplicate_bounds (κ : ℝ) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) :
    rowPureDuplicate κ c b ω ∈ Icc (0:ℝ) 1 := by
  unfold rowPureDuplicate pureDuplicate
  split_ifs <;> norm_num

theorem integrable_rowPureDuplicate (κ : ℝ) (c : ℕ) (b : ℝ)
    (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P] :
    Integrable (rowPureDuplicate κ c b) P := by
  apply Integrable.of_bound (C := 1) (measurable_rowPureDuplicate κ c b).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (rowPureDuplicate_bounds κ c b ω).1]
    exact (rowPureDuplicate_bounds κ c b ω).2

theorem pureDuplicate_eq_indicator_copy {ι : Type*} [DecidableEq ι]
    (P : Finset ι × Finset ι) (i : ι) :
    pureDuplicate P i = if focalCopy P i=2 then 1 else 0 := by
  simp only [pureDuplicate,focalCopy_eq_two_iff,Finset.mem_inter]

theorem row_duplicate_acquisition_in_harmfulCluster
    (c : ℕ) {κ x y : ℝ} (hκ : 0 < κ) (hx : 0 < x) (hxy : x < y)
    (ω : Fin (N+1) → RowRival)
    (hω : ∀ j, (ω j).1=0 → 0 ≤ (ω j).2)
    (hxdup : rowPureDuplicate κ c x ω=0)
    (hydup : rowPureDuplicate κ c y ω=1) :
    ω ∈ harmfulCluster c (Icc x y ∪ Icc (κ*x) (κ*y)) := by
  classical
  let T := patternTemplate c (fun j => (ω j).1)
  have hnot : focalCopy (T.selection κ (rowBids x ω)) 0 ≠ 2 := by
    intro he
    rw [rowPureDuplicate,rowPureSelection,pureDuplicate_eq_indicator_copy,if_pos he] at hxdup
    norm_num at hxdup
  have hdup : focalCopy (T.selection κ (rowBids y ω)) 0 = 2 := by
    by_contra he
    rw [rowPureDuplicate,rowPureSelection,pureDuplicate_eq_indicator_copy,if_neg he] at hydup
    norm_num at hydup
  have he : T.harmfulInterval κ (rowBids x ω) 0 y := by
    apply T.duplicate_acquisition_interval hκ (rowBids x ω)
      (rowBids_nonneg x ω hx.le hω) (rowBids_outside c x ω)
      0 (focal_mem_patternTemplate c _)
      (by simpa only [rowBids,Fin.cons_zero] using hx) y
      (by simpa only [rowBids,Fin.cons_zero] using hxy) hnot
    rwa [rowBids_update]
  have hr := pattern_harmfulInterval_to_row c κ x y ω he
  obtain ⟨j,hj,hjI⟩ := hr.2
  exact ⟨hr.1,⟨j,hj,hjI⟩⟩

theorem row_duplicate_increment_le_harmfulCluster
    (c : ℕ) {κ x y : ℝ} (hκ : 0 < κ) (hx : 0 < x) (hxy : x < y)
    (ω : Fin (N+1) → RowRival)
    (hω : ∀ j, (ω j).1=0 → 0 ≤ (ω j).2) :
    rowPureDuplicate κ c y ω-rowPureDuplicate κ c x ω ≤
      (harmfulCluster c (Icc x y ∪ Icc (κ*x) (κ*y))).indicator (fun _ => (1:ℝ)) ω := by
  classical
  by_cases he : ω ∈ harmfulCluster c (Icc x y ∪ Icc (κ*x) (κ*y))
  · rw [Set.indicator_of_mem he]
    linarith [(rowPureDuplicate_bounds κ c y ω).2,(rowPureDuplicate_bounds κ c x ω).1]
  · rw [Set.indicator_of_notMem he]
    by_cases hxdup : rowPureDuplicate κ c x ω=0
    · have hydup : rowPureDuplicate κ c y ω=0 := by
        unfold rowPureDuplicate pureDuplicate
        split_ifs with hy
        · exfalso
          apply he
          exact row_duplicate_acquisition_in_harmfulCluster c hκ hx hxy ω hω hxdup
            (by simp only [rowPureDuplicate,pureDuplicate,if_pos hy])
        · rfl
      simp only [hxdup,hydup,sub_self,le_refl]
    · have hxeq : rowPureDuplicate κ c x ω=1 := by
        unfold rowPureDuplicate pureDuplicate at hxdup ⊢
        split_ifs at * <;> simp_all
      rw [hxeq]
      linarith [(rowPureDuplicate_bounds κ c y ω).2]

def expectedPureDuplicate (s a h κ : ℝ) (G : Measure ℝ) (c : ℕ) (b : ℝ) : ℝ :=
  ∫ ω : Fin N → RowRival, rowPureDuplicate κ c b ω
    ∂Measure.pi (fun _ : Fin N => rivalLaw s a h G)

theorem actual_pure_duplicate_interval_bound
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ᵐ b ∂G, 0 ≤ b) (c : ℕ)
    {κ x y : ℝ} (hκ : 0 < κ) (hx : 0 < x) (hxy : x < y) :
    expectedPureDuplicate (N := N+1) s a h κ G c y-
      expectedPureDuplicate (N := N+1) s a h κ G c x ≤
      (N+1:ℕ)*s*(G.real (Icc x y)+G.real (Icc (κ*x) (κ*y)))*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) := by
  let μ := rivalLaw s a h G
  letI : IsProbabilityMeasure μ := rivalLaw_isProbability s a h hs ha hh hsum G
  let P := Measure.pi fun _ : Fin (N+1) => μ
  have hrows : ∀ᵐ ω ∂P, ∀ j, 0 ≤ (ω j).2 :=
    iid_rows_ae_bid_nonnegative μ (rivalLaw_ae_bid_nonnegative s a h G hG)
  have hpoint : ∀ᵐ ω ∂P,
      rowPureDuplicate κ c y ω-rowPureDuplicate κ c x ω ≤
      (harmfulCluster c (Icc x y ∪ Icc (κ*x) (κ*y))).indicator (fun _ => (1:ℝ)) ω := by
    filter_upwards [hrows] with ω hω
    exact row_duplicate_increment_le_harmfulCluster c hκ hx hxy ω (fun j _ => hω j)
  have hi := integral_mono_ae
    ((integrable_rowPureDuplicate κ c y P).sub (integrable_rowPureDuplicate κ c x P))
    ((integrable_const (1:ℝ)).indicator
      (measurableSet_harmfulCluster_set c _ (measurableSet_Icc.union measurableSet_Icc))) hpoint
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_rowPureDuplicate κ c y P)
    (integrable_rowPureDuplicate κ c x P)] at hi
  have hbound := expected_two_cluster_loss (N := N) s a h hs ha hh hsum G c
    (Icc x y) (Icc (κ*x) (κ*y)) measurableSet_Icc measurableSet_Icc (1:ℝ) (by norm_num)
  have hcand := hi.trans hbound
  simpa only [expectedPureDuplicate,one_mul] using hcand

theorem real_Icc_eq_Ioc_of_atomless (G : Measure ℝ) [IsFiniteMeasure G]
    (hatom : ∀ x : ℝ, G {x}=0) (a b : ℝ) :
    G.real (Icc a b) = G.real (Ioc a b) := by
  apply measureReal_congr
  have hn : ∀ᵐ x ∂G, x ≠ a := by
    rw [ae_iff]
    simpa using hatom a
  filter_upwards [hn] with x hx
  apply propext
  constructor
  · intro h
    exact ⟨lt_of_le_of_ne h.1 (Ne.symm hx),h.2⟩
  · intro h
    exact ⟨h.1.le,h.2⟩

theorem actual_pure_duplicate_rank_increment
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : ∀ᵐ b ∂G, 0 ≤ b) (hatom : ∀ b : ℝ, G {b}=0) (c : ℕ)
    {κ x y : ℝ} (hκ : 0 < κ) (hx : 0 < x) (hxy : x < y) :
    expectedPureDuplicate (N := N+1) s a h κ G c y-
      expectedPureDuplicate (N := N+1) s a h κ G c x ≤
      (N+1:ℕ)*(s*G.real (Ioc x y)+s*G.real (Ioc (κ*x) (κ*y)))*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) := by
  have hbound := actual_pure_duplicate_interval_bound (N := N) s a h hs ha hh hsum G hG c hκ hx hxy
  rw [real_Icc_eq_Ioc_of_atomless G hatom,real_Icc_eq_Ioc_of_atomless G hatom] at hbound
  convert! hbound using 1
  ring

end FCAppendix.Affine.Uniform06.PureDuplicateIntervals
