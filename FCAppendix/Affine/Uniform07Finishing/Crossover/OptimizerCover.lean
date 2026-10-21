import FCAppendix.Affine.Uniform07Finishing.Crossover.RateAndError
import Mathlib.Topology.Sequences

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open Set Filter Topology

structure SingletonOptimizerSequence (q : ℕ→ℝ→ℝ) (t : ℝ) where
  market : ℕ→ℕ
  market_tendsto : Tendsto market atTop atTop
  value : ℕ→ℝ
  bid : ℕ→ℝ
  value_mem : ∀ k, value k∈Ioc (0:ℝ) t
  bid_mem : ∀ k, bid k∈Icc (0:ℝ) (value k)
  optimal : ∀ k, ∀ z∈Icc (0:ℝ) (value k),
    utilityOne (value k) z (q (market k) z)≤
      utilityOne (value k) (bid k) (q (market k) (bid k))

theorem exists_positive_singleton_optimizer
    {q : ℝ→ℝ} {v : ℝ} (hv : 0< v)
    (hq : ContinuousOn q (Icc (0:ℝ) v))
    (hqNonneg : ∀ z∈Icc (0:ℝ) v, 0≤ q z)
    (hhalf : 0< q (v/2)) :
    ∃ b∈Ico (0:ℝ) v, 0< utilityOne v b (q b) ∧
      ∀ z∈Icc (0:ℝ) v, utilityOne v z (q z)≤ utilityOne v b (q b) := by
  have hc : ContinuousOn (fun z => utilityOne v z (q z)) (Icc (0:ℝ) v) := by
    unfold utilityOne
    exact (continuousOn_const.sub continuousOn_id).mul hq
  obtain ⟨b,hb,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) v).Nonempty from ⟨0,⟨le_rfl,hv.le⟩⟩) hc
  have hhalfmem : v/2∈Icc (0:ℝ) v := by constructor <;> linarith
  have huHalf : 0< utilityOne v (v/2) (q (v/2)) := by
    unfold utilityOne
    exact mul_pos (by linarith) hhalf
  have hu : 0< utilityOne v b (q b) := huHalf.trans_le (hmax hhalfmem)
  have hbv : b< v := positive_singleton_utility_implies_underbid (hqNonneg b hb) hu
  exact ⟨b,⟨hb.1,hbv⟩,hu,fun z hz => hmax hz⟩

theorem underbid_optimizer_is_global
    {q : ℝ→ℝ} {v b : ℝ} (_hv : 0≤ v)
    (hq : ∀ z≥ 0, 0≤ q z) (hu : 0< utilityOne v b (q b))
    (hopt : ∀ z∈Icc (0:ℝ) v, utilityOne v z (q z)≤ utilityOne v b (q b)) :
    ∀ z≥ 0, utilityOne v z (q z)≤ utilityOne v b (q b) := by
  intro z hz
  by_cases hzv : z≤ v
  · exact hopt z ⟨hz,hzv⟩
  · have hzv' : v≤ z := (lt_of_not_ge hzv).le
    have hnonpos : utilityOne v z (q z)≤ 0 := by
      unfold utilityOne
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hzv') (hq z hz)
    exact hnonpos.trans hu.le

theorem optimizer_limit_regimes
    {v b entry lowStart lowTop crossoverEnd : ℝ}
    (hbv : b≤ v) (hoverlap : lowStart< lowTop) :
    v=entry ∨ entry< v ∨
      (v< entry ∧ (b< lowTop ∨ b∈Ioo lowStart crossoverEnd ∨
        (crossoverEnd≤ b ∧ b< entry))) := by
  rcases lt_trichotomy v entry with hv | hv | hv
  · refine Or.inr (Or.inr ⟨hv,?_⟩)
    by_cases hb : b< lowTop
    · exact Or.inl hb
    · have hlo : lowStart< b := hoverlap.trans_le (le_of_not_gt hb)
      by_cases hhi : b< crossoverEnd
      · exact Or.inr (Or.inl ⟨hlo,hhi⟩)
      · exact Or.inr (Or.inr ⟨le_of_not_gt hhi,hbv.trans_lt hv⟩)
  · exact Or.inl hv
  · exact Or.inr (Or.inl hv)

theorem eventually_every_lower_singleton_optimizer_loses
    {q d : ℕ→ℝ→ℝ} {eta t entry lowStart lowTop crossoverEnd : ℝ}
    (_ht : 0< t) (hoverlap : lowStart< lowTop)
    (hlow : ∀ᶠ m in atTop, ∀ v∈Ioc (0:ℝ) t,
      ∀ b∈Icc (0:ℝ) v, b≤ lowTop →
      (∀ z∈Icc (0:ℝ) v,
        utilityOne v z (q m z)≤ utilityOne v b (q m b)) →
      utilityOne v b (q m b)< utilityTwo eta v b (q m b) (d m b))
    (hcross : ∀ s : SingletonOptimizerSequence q t, ∀ v0 b0,
      Tendsto s.value atTop (𝓝 v0) → Tendsto s.bid atTop (𝓝 b0) →
      v0< entry → b0∈Ioo lowStart crossoverEnd →
      ∀ᶠ k in atTop, ∃ z∈Icc (0:ℝ) (s.value k),
        utilityOne (s.value k) (s.bid k) (q (s.market k) (s.bid k))<
          utilityTwo eta (s.value k) z (q (s.market k) z) (d (s.market k) z))
    (hcanonical : ∀ s : SingletonOptimizerSequence q t, ∀ v0 b0,
      Tendsto s.value atTop (𝓝 v0) → Tendsto s.bid atTop (𝓝 b0) →
      v0< entry → crossoverEnd≤ b0 → b0< entry →
      ∀ᶠ k in atTop, ∃ z∈Icc (0:ℝ) (s.value k),
        utilityOne (s.value k) (s.bid k) (q (s.market k) (s.bid k))<
          utilityTwo eta (s.value k) z (q (s.market k) z) (d (s.market k) z))
    (hentry : ∀ s : SingletonOptimizerSequence q t,
      Tendsto s.value atTop (𝓝 entry) →
      ∀ᶠ k in atTop, ∃ z∈Icc (0:ℝ) (s.value k),
        utilityOne (s.value k) (s.bid k) (q (s.market k) (s.bid k))<
          utilityTwo eta (s.value k) z (q (s.market k) z) (d (s.market k) z))
    (hactive : ∀ s : SingletonOptimizerSequence q t, ∀ v0,
      Tendsto s.value atTop (𝓝 v0) → entry< v0 → v0≤ t →
      ∀ᶠ k in atTop, ∃ z∈Icc (0:ℝ) (s.value k),
        utilityOne (s.value k) (s.bid k) (q (s.market k) (s.bid k))<
          utilityTwo eta (s.value k) z (q (s.market k) z) (d (s.market k) z)) :
    ∀ᶠ m in atTop, ∀ v∈Ioc (0:ℝ) t, ∀ b∈Icc (0:ℝ) v,
      (∀ z∈Icc (0:ℝ) v,
        utilityOne v z (q m z)≤ utilityOne v b (q m b)) →
      ∃ z∈Icc (0:ℝ) v,
        utilityOne v b (q m b)< utilityTwo eta v z (q m z) (d m z) := by
  classical
  by_contra hn
  have hfreq : ∃ᶠ m in atTop, ∃ v∈Ioc (0:ℝ) t,
      ∃ b∈Icc (0:ℝ) v,
        (∀ z∈Icc (0:ℝ) v,
          utilityOne v z (q m z)≤ utilityOne v b (q m b)) ∧
        ¬∃ z∈Icc (0:ℝ) v,
          utilityOne v b (q m b)< utilityTwo eta v z (q m z) (d m z) := by
    simpa only [not_eventually,not_forall,Classical.not_imp,exists_prop] using hn
  obtain ⟨phi,hphi,hbad⟩ := extraction_of_frequently_atTop hfreq
  choose v hv b hb hopt hlose using hbad
  have hcompact : IsCompact (Icc (0:ℝ) t ×ˢ Icc (0:ℝ) t) :=
    isCompact_Icc.prod isCompact_Icc
  have hmem (j : ℕ) : (v j,b j)∈Icc (0:ℝ) t ×ˢ Icc (0:ℝ) t :=
    ⟨⟨(hv j).1.le,(hv j).2⟩,⟨(hb j).1,(hb j).2.trans (hv j).2⟩⟩
  obtain ⟨z,hz,chi,hchi,hconv⟩ := hcompact.isSeqCompact hmem
  let s : SingletonOptimizerSequence q t := {
    market := phi ∘ chi
    market_tendsto := hphi.tendsto_atTop.comp hchi.tendsto_atTop
    value := v ∘ chi
    bid := b ∘ chi
    value_mem := fun k => hv (chi k)
    bid_mem := fun k => hb (chi k)
    optimal := fun k => hopt (chi k) }
  have hvconv : Tendsto s.value atTop (𝓝 z.1) :=
    continuous_fst.tendsto z |>.comp hconv
  have hbconv : Tendsto s.bid atTop (𝓝 z.2) :=
    continuous_snd.tendsto z |>.comp hconv
  have hbv : z.2≤ z.1 := le_of_tendsto_of_tendsto hbconv hvconv
    (.of_forall fun k => (s.bid_mem k).2)
  have hwin : ∀ᶠ k in atTop, ∃ y∈Icc (0:ℝ) (s.value k),
      utilityOne (s.value k) (s.bid k) (q (s.market k) (s.bid k))<
        utilityTwo eta (s.value k) y (q (s.market k) y) (d (s.market k) y) := by
    rcases optimizer_limit_regimes hbv hoverlap with he | ha | ⟨hvlt,hcases⟩
    · apply hentry s
      simpa only [he] using hvconv
    · exact hactive s z.1 hvconv ha hz.1.2
    · rcases hcases with hlo | hcr | hca
      · have hsmall : ∀ᶠ k in atTop, s.bid k< lowTop :=
          hbconv.eventually (Iio_mem_nhds hlo)
        have hlow' := s.market_tendsto.eventually hlow
        filter_upwards [hsmall,hlow'] with k hk hm
        refine ⟨s.bid k,s.bid_mem k,?_⟩
        exact hm (s.value k) (s.value_mem k) (s.bid k) (s.bid_mem k)
          hk.le (s.optimal k)
      · exact hcross s z.1 z.2 hvconv hbconv hvlt hcr
      · exact hcanonical s z.1 z.2 hvconv hbconv hvlt hca.1 hca.2
  obtain ⟨k,hk⟩ := hwin.exists
  exact hlose (chi k) hk

end FCAppendix.Affine.Uniform07Finishing.Crossover
