import FCAppendix.Affine.ClippedResidualKernel

noncomputable section
namespace FCAppendix.Affine.ClippedResidual
open MeasureTheory Set Filter Topology
open scoped BigOperators
section AbstractRoot
variable {α : Type*}

lemma root_distance_bound (F : α → ℝ → ℝ) (root : α → ℝ)
    {lo hi k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hroot : ∀ a, root a ∈ Icc lo hi ∧ F a (root a) = r)
    (hdrop : ∀ a z₁ z₂, z₁ ∈ Icc lo hi → z₂ ∈ Icc lo hi → z₁ ≤ z₂ →
      k*(z₂-z₁)*F a z₂ ≤ F a z₁-F a z₂)
    (a a₀ : α) (hnear : r/2 ≤ F a (root a₀)) :
    |root a-root a₀| ≤ 2*|F a (root a₀)-r|/(k*r) := by
  have hd : 0 < k*r := mul_pos hk hr
  by_cases h : root a₀ ≤ root a
  · have hh := hdrop a (root a₀) (root a) (hroot a₀).1 (hroot a).1 h
    rw [(hroot a).2] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    apply (le_div_iff₀ hd).2
    have ha := le_abs_self (F a (root a₀)-r)
    have hn := abs_nonneg (F a (root a₀)-r)
    nlinarith
  · have h' : root a ≤ root a₀ := le_of_not_ge h
    have hh := hdrop a (root a) (root a₀) (hroot a).1 (hroot a₀).1 h'
    rw [(hroot a).2] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr h')]
    apply (le_div_iff₀ hd).2
    have ha := neg_le_abs (F a (root a₀)-r)
    have hp := mul_nonneg (mul_nonneg hk.le (sub_nonneg.mpr h'))
      (sub_nonneg.mpr hnear)
    nlinarith

theorem root_continuous [TopologicalSpace α] (F : α → ℝ → ℝ) (root : α → ℝ)
    {lo hi k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hroot : ∀ a, root a ∈ Icc lo hi ∧ F a (root a) = r)
    (hdrop : ∀ a z₁ z₂, z₁ ∈ Icc lo hi → z₂ ∈ Icc lo hi → z₁ ≤ z₂ →
      k*(z₂-z₁)*F a z₂ ≤ F a z₁-F a z₂)
    (hcont : ∀ z ∈ Icc lo hi, Continuous (fun a => F a z)) : Continuous root := by
  apply continuous_iff_continuousAt.mpr
  intro a₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  let δ : ℝ := min (r/2) (ε*(k*r)/2)
  have hδ : 0 < δ := lt_min (half_pos hr) (by positivity)
  have hc : ContinuousAt (fun a => F a (root a₀)) a₀ :=
    (hcont (root a₀) (hroot a₀).1).continuousAt
  have he : ∀ᶠ a in 𝓝 a₀, |F a (root a₀)-r| < δ := by
    have ht := (Metric.continuousAt_iff'.mp hc) δ hδ
    simpa [Real.dist_eq, (hroot a₀).2] using ht
  filter_upwards [he] with a ha
  have hnear : r/2 ≤ F a (root a₀) := by
    have hsmall := lt_of_lt_of_le ha (min_le_left (r/2) (ε*(k*r)/2))
    have hside := (abs_lt.mp hsmall).1
    linarith
  have hb := root_distance_bound F root hk hr hroot hdrop a a₀ hnear
  have hs : |F a (root a₀)-r| < ε*(k*r)/2 :=
    lt_of_lt_of_le ha (min_le_right _ _)
  have hquot : 2*|F a (root a₀)-r|/(k*r) < ε := by
    apply (div_lt_iff₀ (mul_pos hk hr)).2
    linarith
  simpa [Real.dist_eq] using hb.trans_lt hquot

end AbstractRoot

section Guarded
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ξ U lo hi slack : ℝ} {d : ℕ} (E : Finset ι)

abbrev GuardedBids (ξ U lo hi slack : ℝ) (d : ℕ) (E : Finset ι) :=
  {b : ι→ℝ // (∀i,b i≤U) ∧
    (d:ℝ)+(E.card:ℝ)+slack<∑i,exposure ξ lo (b i) ∧
    (∑i,exposure ξ hi (b i))<(d:ℝ)-slack}

variable (hξ : 0<ξ) (hξ1 : ξ<1) (hU : 0<U) (hlo : 0<lo) (hlh : lo<hi)
    (hguard : (1-ξ)*U≤lo) (hd : 0<d) (hslack : 0<slack)

def clearing (b : GuardedBids ξ U lo hi slack d E) : ℝ :=
  (exists_unique_balanced_root b.1 E hξ hξ1 hU hlo hlh hguard b.2.1
    (by exact_mod_cast hd) hslack b.2.2.1 b.2.2.2).exists.choose

lemma clearing_spec (b : GuardedBids ξ U lo hi slack d E) :
    clearing E hξ hξ1 hU hlo hlh hguard hd hslack b∈Icc lo hi ∧
      remainingDemand ξ b.1 E (clearing E hξ hξ1 hU hlo hlh hguard hd hslack b)=(d:ℝ) :=
  (exists_unique_balanced_root b.1 E hξ hξ1 hU hlo hlh hguard b.2.1
    (by exact_mod_cast hd) hslack b.2.2.1 b.2.2.2).exists.choose_spec

theorem continuous_clearing :
    Continuous (clearing E hξ hξ1 hU hlo hlh hguard hd hslack) := by
  apply root_continuous (fun b z => remainingDemand ξ b.1 E z)
    (clearing E hξ hξ1 hU hlo hlh hguard hd hslack)
    (show 0<1/(ξ*U) by positivity) (show (0:ℝ)<d by exact_mod_cast hd)
    (clearing_spec E hξ hξ1 hU hlo hlh hguard hd hslack)
  · intro b z₁ z₂ hz₁ hz₂ h12
    have hh := remainingDemand_drop b.1 E hξ hξ1 hU hlo hguard hz₁.1 h12 b.2.1
    convert hh using 1
    ring
  · intro z hz
    unfold remainingDemand
    apply continuous_finsetSum
    intro i _
    by_cases hiE : i∈E
    · simp only [hiE,if_true]
      exact continuous_const
    · simp only [hiE,if_false]
      exact (continuous_exposure hξ (hlo.trans_le hz.1)).comp
        ((continuous_apply i).comp continuous_subtype_val)

theorem continuous_pairMarginal :
    Continuous (fun b : GuardedBids ξ U lo hi slack d E =>
      smallMarginal ξ (clearing E hξ hξ1 hU hlo hlh hguard hd hslack b) b.1 E) ∧
    Continuous (fun b : GuardedBids ξ U lo hi slack d E =>
      largeMarginal ξ (clearing E hξ hξ1 hU hlo hlh hguard hd hslack b) b.1 E) := by
  have hc := continuous_clearing E hξ hξ1 hU hlo hlh hguard hd hslack
  have he (i : ι) : Continuous (fun b : GuardedBids ξ U lo hi slack d E =>
      exposure ξ (clearing E hξ hξ1 hU hlo hlh hguard hd hslack b) (b.1 i)) := by
    have hb : Continuous (fun b : GuardedBids ξ U lo hi slack d E => b.1 i) :=
      (continuous_apply i).comp continuous_subtype_val
    unfold exposure
    apply continuous_const.min
    exact (continuous_const.max (hb.sub hc)).div (continuous_const.mul (hb.max hc))
      (fun b => ne_of_gt (mul_pos hξ ((hlo.trans_le
        (clearing_spec E hξ hξ1 hU hlo hlh hguard hd hslack b).1.1).trans_le (le_max_right _ _))))
  constructor
  · apply continuous_pi
    intro i
    unfold smallMarginal
    split
    · exact continuous_const
    · exact he i
  · apply continuous_pi
    intro i
    unfold largeMarginal
    split
    · exact continuous_const
    · exact he i

def guardedSmallLottery (b : GuardedBids ξ U lo hi slack d E) : FiniteLaw (Finset ι) :=
  ExactCapacity.symmetricLottery
    (smallMarginal ξ (clearing E hξ hξ1 hU hlo hlh hguard hd hslack b) b.1 E)

def guardedLargeLottery (b : GuardedBids ξ U lo hi slack d E) : FiniteLaw (Finset ι) :=
  ExactCapacity.symmetricLottery
    (largeMarginal ξ (clearing E hξ hξ1 hU hlo hlh hguard hd hslack b) b.1 E)

theorem measurable_guardedSmallLottery_mass (S : Finset ι) :
    Measurable (fun b => (guardedSmallLottery E hξ hξ1 hU hlo hlh hguard hd hslack b).mass S) :=
  (ExactCapacity.measurable_symmetricLottery_mass S).comp
    (continuous_pairMarginal E hξ hξ1 hU hlo hlh hguard hd hslack).1.measurable

theorem measurable_guardedLargeLottery_mass (S : Finset ι) :
    Measurable (fun b => (guardedLargeLottery E hξ hξ1 hU hlo hlh hguard hd hslack b).mass S) :=
  (ExactCapacity.measurable_symmetricLottery_mass S).comp
    (continuous_pairMarginal E hξ hξ1 hU hlo hlh hguard hd hslack).2.measurable

theorem exists_guarded_private_samplers :
    ∃ (small large : GuardedBids ξ U lo hi slack d E→unitInterval→Finset ι),
      Measurable (Function.uncurry small) ∧ Measurable (Function.uncurry large) ∧
      (∀b,volume.map (small b)=FiniteLaw.probabilityMeasure
        (guardedSmallLottery E hξ hξ1 hU hlo hlh hguard hd hslack b)) ∧
      (∀b,volume.map (large b)=FiniteLaw.probabilityMeasure
        (guardedLargeLottery E hξ hξ1 hU hlo hlh hguard hd hslack b)) := by
  obtain ⟨f,hf,hflaw⟩ := FiniteLaw.exists_measurable_sampler
    (guardedSmallLottery E hξ hξ1 hU hlo hlh hguard hd hslack)
    (measurable_guardedSmallLottery_mass E hξ hξ1 hU hlo hlh hguard hd hslack)
  obtain ⟨f',hf',hf'law⟩ := FiniteLaw.exists_measurable_sampler
    (guardedLargeLottery E hξ hξ1 hU hlo hlh hguard hd hslack)
    (measurable_guardedLargeLottery_mass E hξ hξ1 hU hlo hlh hguard hd hslack)
  exact ⟨f,f',hf,hf',hflaw,hf'law⟩

end Guarded
end FCAppendix.Affine.ClippedResidual
