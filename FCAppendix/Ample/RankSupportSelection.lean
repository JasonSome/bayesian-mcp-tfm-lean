import FCAppendix.Ample.RankRateAlgebra
import FCAppendix.Ample.SlackSelection

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.RankMeasureTools

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem rank_allIdentities_bestReply_compProd (Γ : FiniteGame m n c Seed)
    (hu : UsersOptimal Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ∀ i : Fin m, (problem Γ i).BestResponse x.1 x.2 := by
  exact ae_all_iff.mpr (fun i => ae_bestResponse_compProd Γ hu i)

theorem rank_actualBestReply_compProd (Γ : FiniteGame m n c Seed)
    (hu : UsersOptimal Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), actualBestReply Γ (x.1-Γ.g) x.2 := by
  by_cases hm : 0 < m
  · filter_upwards [rank_allIdentities_bestReply_compProd Γ hu] with x hx
    intro hm'
    simpa only [sub_add_cancel] using hx ⟨0, hm'⟩
  · exact ae_of_all _ (fun _ hm' => (hm hm').elim)

namespace RankLimit
variable {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
    {pi : ℕ → ℝ} {h : ℝ} {nu : ℕ → Measure ℝ}
    (hr : RankLimit Γ pi h nu)

include hr

theorem interval_tendsto {k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    {a b : ℝ} (ha : a ∈ Icc 0 h) (hb : b ∈ Icc 0 h) (hab : a ≤ b) :
    Tendsto (fun t => (rankClassLaw (Γ t) k).real (Ioc a b)) atTop
      (𝓝 ((nu k).real (Ioc a b))) := by
  letI := hr.finite hk
  have hl := hr.moving_tail (Eventually.of_forall (fun _ => ha)) tendsto_const_nhds hk
  have hu := hr.moving_tail (Eventually.of_forall (fun _ => hb)) tendsto_const_nhds hk
  have he := hl.sub hu
  simp only [hr.tail_eq_strict hk, strict_tail_sub hab] at he
  exact he

theorem eventually_supported_in_band
    (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    (hu : ∀ t, UsersOptimal (Γ t)) (hact : ∀ t, NonpositiveAbstention (Γ t))
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) {a b : ℝ}
    (ha : a ∈ Icc 0 h) (hb : b ∈ Icc 0 h) (hab : a ≤ b)
    (hmass : 0 < (nu k).real (Ioc a b)) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧ ∀ᶠ t in atTop,
      ∃ x : ℝ × JointAction n,
        actualBestReply (Γ t) (x.1-g) x.2 ∧
        x.1-g ∈ Icc lo hi ∧ 0 < x.2.bid ∧ x.2.routeCount = k ∧
        ascendingBidRank (Γ t) x.2.bid ∈ Ioc a b := by
  classical
  obtain ⟨lo, hi, hlo, hlh, htight⟩ :=
    exists_compact_positive_band F g (div_pos hmass (by norm_num : (0:ℝ)<4))
  refine ⟨lo, hi, hlo, hlh, ?_⟩
  have hband := (hr.interval_tendsto hk ha hb hab).eventually_const_lt
    (show (nu k).real (Ioc a b)/2 < (nu k).real (Ioc a b) by linarith)
  filter_upwards [hband] with t ht
  let E : Set (ℝ × JointAction n) := {x | 0 < x.2.bid ∧ x.2.routeCount = k ∧
    ascendingBidRank (Γ t) x.2.bid ∈ Ioc a b}
  let Bad : Set (ℝ × JointAction n) := {x | g < x.1 ∧ x.1-g ∉ Icc lo hi}
  have hE : ((Γ t).F ⊗ₘ (Γ t).σ).real E =
      (rankClassLaw (Γ t) k).real (Ioc a b) := by
    rw [rankClassLaw_real_apply _ _ _ measurableSet_Ioc]
  have hBad : ((Γ t).F ⊗ₘ (Γ t).σ).real Bad < (nu k).real (Ioc a b)/4 := by
    have hBmeas : MeasurableSet {v : ℝ | g < v ∧ v-g ∉ Icc lo hi} :=
      (measurableSet_lt measurable_const measurable_id).inter
        (((measurable_id.sub_const g) measurableSet_Icc).compl)
    change ((Γ t).F ⊗ₘ (Γ t).σ).real
      {x | x.1 ∈ {v : ℝ | g < v ∧ v-g ∉ Icc lo hi}} < _
    rw [joint_value_probability _ _ hBmeas, hF t]
    exact htight
  by_contra hno
  have hsub : E ≤ᵐ[((Γ t).F ⊗ₘ (Γ t).σ)] Bad := by
    filter_upwards [rank_actualBestReply_compProd (Γ t) (hu t), hact t]
      with x hxBR hxact hxE
    have hxv : g < x.1 := by
      by_contra hnot
      have he := hxact (by simpa only [hg t] using le_of_not_gt hnot)
      have hk0 := (Finset.mem_Icc.mp hk).1
      have hxk := hxE.2.1
      omega
    by_contra hxBad
    have hxval : x.1-g ∈ Icc lo hi := by
      by_contra hxnot
      exact hxBad ⟨hxv, hxnot⟩
    apply hno
    refine ⟨x, ?_, hxval, hxE.1, hxE.2.1, hxE.2.2⟩
    simpa only [hg t] using hxBR
  have hle : ((Γ t).F ⊗ₘ (Γ t).σ).real E ≤
      ((Γ t).F ⊗ₘ (Γ t).σ).real Bad :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  rw [hE] at hle
  linarith

theorem supported_approximation
    (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    (hu : ∀ t, UsersOptimal (Γ t)) (hact : ∀ t, NonpositiveAbstention (Γ t))
    (Q : ℕ → Prop) (hQ : ∀ᶠ t in atTop, Q t)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) {u : ℝ}
    (hu0 : 0 < u) (huh : u < h) (hus : u ∈ (nu k).support) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ x : ℕ → ℝ × JointAction n,
      (∀ q, Q (phi q) ∧ actualBestReply (Γ (phi q)) ((x q).1-g) (x q).2 ∧
        g < (x q).1 ∧ 0 < (x q).2.bid ∧ (x q).2.routeCount = k) ∧
      Tendsto (fun q => ascendingBidRank (Γ (phi q)) (x q).2.bid) atTop (𝓝 u) := by
  classical
  letI := hr.finite hk
  let δ : ℕ → ℝ := fun q => min (min (u/2) ((h-u)/2)) (1/((q:ℝ)+1))
  have hδ (q : ℕ) : 0 < δ q := by
    exact lt_min (lt_min (by linarith) (by linarith))
      (one_div_pos.mpr (by positivity))
  have hδu (q : ℕ) : δ q ≤ u/2 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hδh (q : ℕ) : δ q ≤ (h-u)/2 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hδq (q : ℕ) : δ q ≤ 1/((q:ℝ)+1) := min_le_right _ _
  have hev (q : ℕ) : ∀ᶠ t in atTop,
      ∃ x : ℝ × JointAction n, Q t ∧ actualBestReply (Γ t) (x.1-g) x.2 ∧
        g < x.1 ∧ 0 < x.2.bid ∧ x.2.routeCount = k ∧
        |ascendingBidRank (Γ t) x.2.bid-u| ≤ 1/((q:ℝ)+1) := by
    have ha : u-δ q ∈ Icc 0 h := ⟨by linarith [hδu q], by linarith [hδ q]⟩
    have hb : u+δ q ∈ Icc 0 h := ⟨by linarith [hδ q], by linarith [hδh q]⟩
    have hab : u-δ q ≤ u+δ q := by linarith [hδ q]
    have hn : Ioo (u-δ q) (u+δ q) ∈ 𝓝 u :=
      isOpen_Ioo.mem_nhds ⟨by linarith [hδ q], by linarith [hδ q]⟩
    have hpos : 0 < nu k (Ioc (u-δ q) (u+δ q)) :=
      (Measure.mem_support_iff_forall u |>.mp hus _ hn).trans_le
        (measure_mono Ioo_subset_Ioc_self)
    have hm : 0 < (nu k).real (Ioc (u-δ q) (u+δ q)) :=
      ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top _ _)
    obtain ⟨lo, hi, hlo, _hlh, hsel⟩ :=
      hr.eventually_supported_in_band F g hF hg hu hact hk ha hb hab hm
    filter_upwards [hsel, hQ] with t ht htQ
    obtain ⟨x, hBR, hval, hbid, hroute, hrank⟩ := ht
    refine ⟨x, htQ, hBR, by linarith [hval.1], hbid, hroute, ?_⟩
    exact (abs_le.mpr ⟨by linarith [hrank.1], by linarith [hrank.2]⟩).trans (hδq q)
  choose N hN using fun q => Filter.eventually_atTop.mp (hev q)
  let phi : ℕ → ℕ := fun q => Nat.rec (N 0)
    (fun q prev => max (prev+1) (N (q+1))) q
  have hphi : StrictMono phi := by
    apply strictMono_nat_of_lt_succ
    intro q
    exact lt_of_lt_of_le (Nat.lt_succ_self (phi q)) (le_max_left _ _)
  have hNphi (q : ℕ) : N q ≤ phi q := by
    cases q with
    | zero => exact le_rfl
    | succ q => exact le_max_right _ _
  choose x hx using fun q => hN q (phi q) (hNphi q)
  refine ⟨phi, hphi, x, fun q => ⟨(hx q).1, (hx q).2.1,
    (hx q).2.2.1, (hx q).2.2.2.1, (hx q).2.2.2.2.1⟩, ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hε
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp he
  refine ⟨N₀, fun q hq => ?_⟩
  simpa only [Real.dist_eq] using ((hx q).2.2.2.2.2).trans_lt (hN₀ q hq)

end RankLimit
end FCAppendix.Bayes
