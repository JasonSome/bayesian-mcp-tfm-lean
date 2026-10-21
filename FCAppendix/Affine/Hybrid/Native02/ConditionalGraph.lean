import FCAppendix.Affine.Hybrid.Native02.CountsFromPayoff
import FCAppendix.Affine.Hybrid.UniformFiniteMenu

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes

theorem original_joint_graph_to_conditional_graph {M C : ℕ→ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) (F : Measure ℝ)
    (hF : ∀ k,(G k).F=F) (K : Set ℝ) (beta : ℝ→ℝ)
    (hgraph : ∀ eps>0,∀ᶠk in atTop,∀ᵐx ∂(G k).F⊗ₘ(G k).σ,
      x.1∈ K→|x.2.bid-beta x.1|< eps) :
    ∀ᵐv ∂F,v∈ K→∀ eps>0,∀ᶠk in atTop,
      ∀ᵐa ∂(G k).σ v,|a.bid-beta v|< eps := by
  classical
  have hn (n : ℕ) : ∃N,∀ k≥ N,∀ᵐv ∂F,∀ᵐa ∂(G k).σ v,
      v∈ K→|a.bid-beta v|<1/((n:ℝ)+1) := by
    obtain ⟨N,hN⟩ := eventually_atTop.mp
      (hgraph (1/((n:ℝ)+1)) (by positivity))
    refine ⟨N,fun k hk=>?_⟩
    simpa only [hF k] using Measure.ae_ae_of_ae_compProd (hN k hk)
  choose cutoff hcutoff using hn
  have hcommon : ∀ᵐv ∂F,∀ n k,cutoff n≤ k→∀ᵐa ∂(G k).σ v,
      v∈ K→|a.bid-beta v|<1/((n:ℝ)+1) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    by_cases hk : cutoff n≤ k
    · exact (hcutoff n k hk).mono (fun v hv _=> hv)
    · exact ae_of_all _ (fun v h=> False.elim (hk h))
  filter_upwards [hcommon] with v hv
  intro hvK eps heps
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt heps
  filter_upwards [eventually_ge_atTop (cutoff n)] with k hk
  exact (hv n k hk).mono (fun a ha=>(ha hvK).trans hn)

theorem original_joint_graph_common_set {M C : ℕ→ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) (F : Measure ℝ)
    (hF : ∀ k,(G k).F=F) (K : Set ℝ) (beta : ℝ→ℝ)
    (P : ℝ→ Prop) (hP : ∀ᵐv ∂F,P v)
    (hgraph : ∀ eps>0,∀ᶠk in atTop,∀ᵐx ∂(G k).F⊗ₘ(G k).σ,
      x.1∈ K→|x.2.bid-beta x.1|< eps) :
    ∃S : Set ℝ,MeasurableSet S ∧ (∀ᵐv ∂F,v∈ S) ∧
      ∀ v∈ S,P v ∧ (v∈ K→∀ eps>0,∀ᶠk in atTop,
        ∀ᵐa ∂(G k).σ v,|a.bid-beta v|< eps) := by
  apply exists_measurable_common_conull F
  exact hP.and (original_joint_graph_to_conditional_graph G F hF K beta hgraph)

theorem typeOutcome_mass_sub_le_of_ae {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m 2 c Seed) (i : Fin m)
    (v a eps : ℝ) (r : Fin 3)
    (h : ∀ᵐact ∂G.σ v,|((problem G i).outcome act).mass r-a|≤ eps) :
    |(typeOutcome G i v).mass r-a|≤ eps := by
  have ht := integral_abs_sub_le_of_ae_bound (G.σ v)
    (fun act=>((problem G i).outcome act).mass r) (fun _=>0) a 0 eps
    (measurable_outcome_mass G i r).aestronglyMeasurable (integrable_const 0)
    (by simpa only [zero_mul,zero_add] using h)
  simpa only [integral_zero,mul_zero,zero_add,typeOutcome,FiniteLaw.average] using ht

theorem conditional_mass_limit_of_graph_and_uniform_raw {M C : ℕ→ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) (v bstar : ℝ)
    (B : Set ℝ) (_hstar : bstar∈ B)
    (support : ∀ k,∀ᵐa ∂(G k).σ v,a.bid∈ B ∧ a.routeCount=2)
    (graph : ∀ delta>0,∀ᶠk in atTop,∀ᵐa ∂(G k).σ v,|a.bid-bstar|< delta)
    (limitMass : ℝ→ Fin 3→ℝ)
    (hcont : ∀ r,ContinuousWithinAt (fun b=> limitMass b r) B bstar)
    (hraw : ∀ eps>0,∀ᶠk in atTop,∀ i : Fin (M k),∀ a : JointAction 2,
      a.bid∈ B→ a.routeCount=2→∀ r,
        |((problem (G k) i).outcome a).mass r-limitMass a.bid r|< eps) :
    ∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G k) (i k) v).mass r)
        atTop (𝓝 (limitMass bstar r)) := by
  intro i r
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  obtain ⟨delta,hdelta,hnear⟩ := Metric.continuousWithinAt_iff.mp (hcont r)
    (eps/4) (by positivity)
  filter_upwards [hraw (eps/4) (by positivity),graph delta hdelta] with k hk hg
  rw [Real.dist_eq]
  have hbound : |(typeOutcome (G k) (i k) v).mass r-limitMass bstar r|≤ eps/2 := by
    apply typeOutcome_mass_sub_le_of_ae
    filter_upwards [support k,hg] with a ha hga
    have hnear' : |limitMass a.bid r-limitMass bstar r|< eps/4 := by
      simpa only [Real.dist_eq] using hnear ha.1 (by simpa only [Real.dist_eq] using hga)
    have hraw' := hk (i k) a ha.1 ha.2 r
    calc
      _≤|((problem (G k) (i k)).outcome a).mass r-limitMass a.bid r|+
        |limitMass a.bid r-limitMass bstar r| := abs_sub_le _ _ _
      _≤ eps/2 := by linarith
  exact hbound.trans_lt (by linarith)

theorem raw_mass_limit_of_uniform_raw {M C : ℕ→ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed)
    (a : JointAction 2) (B : Set ℝ) (ha : a.bid∈ B) (hk : a.routeCount=2)
    (limitMass : ℝ→ Fin 3→ℝ)
    (hraw : ∀ eps>0,∀ᶠk in atTop,∀ i : Fin (M k),∀ a : JointAction 2,
      a.bid∈ B→ a.routeCount=2→∀ r,
        |((problem (G k) i).outcome a).mass r-limitMass a.bid r|< eps) :
    ∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>((problem (G k) (i k)).outcome a).mass r)
        atTop (𝓝 (limitMass a.bid r)) := by
  intro i r
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  filter_upwards [hraw eps heps] with k h
  simpa only [Real.dist_eq] using h (i k) a ha hk r

end FCAppendix.Affine.Hybrid.Native02
