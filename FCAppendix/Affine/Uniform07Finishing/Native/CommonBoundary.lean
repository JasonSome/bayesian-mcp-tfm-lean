import FCAppendix.Affine.Uniform07Finishing.Native.SourcePopulation
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Sequences

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology

theorem continuous_finite_bid_cdf (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hatom : ∀ b : ℝ, μ {b} = 0) :
    Continuous (fun b : ℝ => μ.real (Iic b)) := by
  have he : (fun b : ℝ => μ.real (Iic b)) =
      (fun b => μ.real univ - μ.real (Ioi b)) := by
    funext b
    rw [← compl_Ioi, measureReal_compl measurableSet_Ioi]
  rw [he]
  exact continuous_const.sub
    (Ample.RankMeasureTools.continuous_strict_tail μ hatom)

theorem closed_contains_measure_support {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) {C : Set X} (hC : IsClosed C)
    (hae : ∀ᵐ x ∂μ, x ∈ C) : μ.support ⊆ C := by
  intro x hx
  by_contra hnot
  have hpos : 0 < μ Cᶜ :=
    (Measure.mem_support_iff_forall x).mp hx _ (hC.isOpen_compl.mem_nhds hnot)
  have hz : μ Cᶜ = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    simpa only [mem_compl_iff, not_not] using hae
  exact hpos.ne' hz

theorem bid_support_of_scaled_subtype_map (U : ℝ)
    (π : Measure (ℝ × Icc (0 : ℝ) U)) (μ : Measure ℝ) (k : ENNReal)
    (hμ : μ = k • ((π.map Prod.snd).map (fun b : Icc (0 : ℝ) U => (b : ℝ))))
    {b : Icc (0 : ℝ) U} (hb : (b : ℝ) ∈ μ.support) :
    b ∈ (π.map Prod.snd).support := by
  let ν := π.map Prod.snd
  let D : Set ℝ := (fun b : Icc (0 : ℝ) U => (b : ℝ)) '' ν.support
  have hD : IsClosed D :=
    (Measure.isClosed_support.isCompact.image continuous_subtype_val).isClosed
  have hae : ∀ᵐ x ∂ν.map (fun b : Icc (0 : ℝ) U => (b : ℝ)), x ∈ D := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable hD.measurableSet).mpr
    filter_upwards [Measure.support_mem_ae (μ := ν)] with a ha
    exact ⟨a, ha, rfl⟩
  have hμae : ∀ᵐ x ∂μ, x ∈ D := by
    rw [hμ]
    exact Measure.ae_smul_measure hae k
  rcases closed_contains_measure_support μ hD hμae hb with ⟨a, ha, hab⟩
  have he : a = b := Subtype.ext hab
  simpa only [he] using ha

theorem joint_rank_graph_support {B : Type*} [TopologicalSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (π : Measure (ℝ × B)) (M : B → ℝ) (hM : Continuous M)
    (hrank : ∀ᵐ z ∂π, z.1 = M z.2) {b : B}
    (hb : b ∈ (π.map Prod.snd).support) : (M b, b) ∈ π.support := by
  let C : Set B := {b | (M b, b) ∈ π.support}
  have hC : IsClosed C :=
    Measure.isClosed_support.preimage (hM.prodMk continuous_id)
  have hae : ∀ᵐ b ∂π.map Prod.snd, b ∈ C := by
    apply (ae_map_iff measurable_snd.aemeasurable hC.measurableSet).mpr
    filter_upwards [hrank, Measure.support_mem_ae (μ := π)] with z hz hs
    simpa only [← hz] using hs
  exact closed_contains_measure_support (π.map Prod.snd) hC hae hb

theorem joint_rank_graph_support_local {B : Type*} [TopologicalSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    (π : Measure (ℝ × B)) (M : B → ℝ) (hM : Continuous M)
    (J : Set B) (hJ : IsOpen J)
    (hrank : ∀ᵐ z ∂π, z.2 ∈ J → z.1 = M z.2) {b : B}
    (hb : b ∈ (π.map Prod.snd).support) (hbJ : b ∈ J) :
    (M b, b) ∈ π.support := by
  let C : Set B := {b | (M b, b) ∈ π.support}
  let D : Set B := C ∪ Jᶜ
  have hC : IsClosed C :=
    Measure.isClosed_support.preimage (hM.prodMk continuous_id)
  have hD : IsClosed D := hC.union hJ.isClosed_compl
  have hae : ∀ᵐ b ∂π.map Prod.snd, b ∈ D := by
    apply (ae_map_iff measurable_snd.aemeasurable hD.measurableSet).mpr
    filter_upwards [hrank, Measure.support_mem_ae (μ := π)] with z hz hs
    by_cases hzJ : z.2 ∈ J
    · apply Or.inl
      change (M z.2, z.2) ∈ π.support
      simpa only [← hz hzJ] using hs
    · exact Or.inr hzJ
  have hbD := closed_contains_measure_support (π.map Prod.snd) hD hae hb
  exact hbD.resolve_right (not_not.mpr hbJ)

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actual_payoff_continuous_value (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (a : JointAction 2) :
    Continuous (fun v : ℝ => (problem Γ i).payoff v a) := by
  change Continuous (fun v : ℝ => ((problem Γ i).outcome a).utility v a.bid Γ.g Γ.A Γ.G)
  simp only [CountLaw.utility_eq]
  fun_prop

theorem actual_support_broadcast_IC_at (Γ : FiniteGame m 2 c Seed) (U : ℝ)
    (π : Measure (ℝ × Icc (0 : ℝ) U))
    (hIC : ∀ᵐ z ∂π, ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U b') ≤
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2))
    {v : ℝ} {b : Icc (0 : ℝ) U} (hs : (v, b) ∈ π.support)
    (hpay : ∀ i : Fin m, ContinuousAt (fun z : ℝ × Icc (0 : ℝ) U =>
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)) (v, b)) :
    ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
      (problem Γ i).payoff v (sourceLowerBroadcastAction U b') ≤
        (problem Γ i).payoff v (sourceLowerBroadcastAction U b) := by
  let E : Set (ℝ × Icc (0 : ℝ) U) := {z | ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
    (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U b') ≤
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)}
  have hcl : (v, b) ∈ closure E := closed_contains_measure_support π isClosed_closure
    (hIC.mono (fun _ hz => subset_closure hz)) hs
  obtain ⟨z, hz, hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  intro i b'
  have hl := ((actual_payoff_continuous_value Γ i (sourceLowerBroadcastAction U b')).comp
    continuous_fst).tendsto (v, b)
  exact le_of_tendsto_of_tendsto (hl.comp hlim) ((hpay i).tendsto.comp hlim)
    (Eventually.of_forall (fun n => hz n i b'))

theorem actual_common_boundary_broadcast_IC_local_at (Γ : FiniteGame m 2 c Seed)
    (U : ℝ) (π : Measure (ℝ × Icc (0 : ℝ) U))
    (M : Icc (0 : ℝ) U → ℝ) (hM : Continuous M)
    (J : Set (Icc (0 : ℝ) U)) (hJ : IsOpen J)
    (hrank : ∀ᵐ z ∂π, z.2 ∈ J → z.1 = M z.2)
    (hIC : ∀ᵐ z ∂π, ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U b') ≤
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2))
    {b : Icc (0 : ℝ) U} (hb : b ∈ (π.map Prod.snd).support) (hbJ : b ∈ J)
    (hpay : ∀ i : Fin m, ContinuousAt (fun z : ℝ × Icc (0 : ℝ) U =>
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)) (M b, b)) :
    ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
      (problem Γ i).payoff (M b) (sourceLowerBroadcastAction U b') ≤
        (problem Γ i).payoff (M b) (sourceLowerBroadcastAction U b) :=
  actual_support_broadcast_IC_at Γ U π hIC
    (joint_rank_graph_support_local π M hM J hJ hrank hb hbJ) hpay

theorem actual_common_boundary_best_response (Γ : FiniteGame m 2 c Seed) (U : ℝ)
    (hpay : ∀ i : Fin m, Continuous (fun z : ℝ × Icc (0 : ℝ) U =>
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)))
    (π : Measure (ℝ × Icc (0 : ℝ) U))
    (M : Icc (0 : ℝ) U → ℝ) (hM : Continuous M)
    (hrank : ∀ᵐ z ∂π, z.1 = M z.2)
    (hIC : ∀ᵐ z ∂π, ∀ i : Fin m, ∀ a' : JointAction 2,
      (problem Γ i).payoff z.1 a' ≤
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2))
    {b : Icc (0 : ℝ) U} (hb : b ∈ (π.map Prod.snd).support) :
    ∀ i : Fin m, ∀ a' : JointAction 2,
      (problem Γ i).payoff (M b) a' ≤
        (problem Γ i).payoff (M b) (sourceLowerBroadcastAction U b) := by
  let C : Set (ℝ × Icc (0 : ℝ) U) :=
    {z | ∀ i : Fin m, ∀ a' : JointAction 2,
      (problem Γ i).payoff z.1 a' ≤
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)}
  have hC : IsClosed C := by
    have he : C = ⋂ i : Fin m, ⋂ a' : JointAction 2,
        {z | (problem Γ i).payoff z.1 a' ≤
          (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)} := by
      ext z
      simp only [C, mem_setOf_eq, mem_iInter]
    rw [he]
    exact isClosed_iInter (fun i => isClosed_iInter (fun a' =>
      isClosed_le ((actual_payoff_continuous_value Γ i a').comp continuous_fst) (hpay i)))
  exact closed_contains_measure_support π hC hIC (joint_rank_graph_support π M hM hrank hb)

theorem actual_common_boundary_broadcast_IC (Γ : FiniteGame m 2 c Seed) (U : ℝ)
    (hpay : ∀ i : Fin m, Continuous (fun z : ℝ × Icc (0 : ℝ) U =>
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)))
    (π : Measure (ℝ × Icc (0 : ℝ) U))
    (M : Icc (0 : ℝ) U → ℝ) (hM : Continuous M)
    (hrank : ∀ᵐ z ∂π, z.1 = M z.2)
    (hIC : ∀ᵐ z ∂π, ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U b') ≤
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2))
    {b : Icc (0 : ℝ) U} (hb : b ∈ (π.map Prod.snd).support) :
    ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
      (problem Γ i).payoff (M b) (sourceLowerBroadcastAction U b') ≤
        (problem Γ i).payoff (M b) (sourceLowerBroadcastAction U b) := by
  let C : Set (ℝ × Icc (0 : ℝ) U) :=
    {z | ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U b') ≤
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)}
  have hC : IsClosed C := by
    have he : C = ⋂ i : Fin m, ⋂ b' : Icc (0 : ℝ) U,
        {z | (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U b') ≤
          (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)} := by
      ext z
      simp only [C, mem_setOf_eq, mem_iInter]
    rw [he]
    exact isClosed_iInter (fun i => isClosed_iInter (fun b' =>
      isClosed_le ((actual_payoff_continuous_value Γ i
        (sourceLowerBroadcastAction U b')).comp continuous_fst) (hpay i)))
  exact closed_contains_measure_support π hC hIC (joint_rank_graph_support π M hM hrank hb)

theorem actual_common_boundary_broadcast_IC_local (Γ : FiniteGame m 2 c Seed) (U : ℝ)
    (hpay : ∀ i : Fin m, Continuous (fun z : ℝ × Icc (0 : ℝ) U =>
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)))
    (π : Measure (ℝ × Icc (0 : ℝ) U))
    (M : Icc (0 : ℝ) U → ℝ) (hM : Continuous M)
    (J : Set (Icc (0 : ℝ) U)) (hJ : IsOpen J)
    (hrank : ∀ᵐ z ∂π, z.2 ∈ J → z.1 = M z.2)
    (hIC : ∀ᵐ z ∂π, ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U b') ≤
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2))
    {b : Icc (0 : ℝ) U} (hb : b ∈ (π.map Prod.snd).support) (hbJ : b ∈ J) :
    ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
      (problem Γ i).payoff (M b) (sourceLowerBroadcastAction U b') ≤
        (problem Γ i).payoff (M b) (sourceLowerBroadcastAction U b) := by
  let C : Set (ℝ × Icc (0 : ℝ) U) :=
    {z | ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U b') ≤
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)}
  have hC : IsClosed C := by
    have he : C = ⋂ i : Fin m, ⋂ b' : Icc (0 : ℝ) U,
        {z | (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U b') ≤
          (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)} := by
      ext z
      simp only [C, mem_setOf_eq, mem_iInter]
    rw [he]
    exact isClosed_iInter (fun i => isClosed_iInter (fun b' =>
      isClosed_le ((actual_payoff_continuous_value Γ i
        (sourceLowerBroadcastAction U b')).comp continuous_fst) (hpay i)))
  exact closed_contains_measure_support π hC hIC
    (joint_rank_graph_support_local π M hM J hJ hrank hb hbJ)

theorem actual_common_boundary_gap_comparison (Γ : FiniteGame m 2 c Seed) (U : ℝ)
    (hpay : ∀ i : Fin m, Continuous (fun z : ℝ × Icc (0 : ℝ) U =>
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)))
    (π : Measure (ℝ × Icc (0 : ℝ) U))
    (M : Icc (0 : ℝ) U → ℝ) (hM : Continuous M)
    (hrank : ∀ᵐ z ∂π, z.1 = M z.2)
    (hIC : ∀ᵐ z ∂π, ∀ i : Fin m, ∀ b' : Icc (0 : ℝ) U,
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U b') ≤
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2))
    {y : Icc (0 : ℝ) U} (hy : y ∈ (π.map Prod.snd).support)
    (x : Icc (0 : ℝ) U) (_hxy : x ≤ y) :
    ∀ z : Icc (0 : ℝ) U, x ≤ z → z ≤ y → ∀ i : Fin m,
      (problem Γ i).payoff (M y) (sourceLowerBroadcastAction U z) ≤
        (problem Γ i).payoff (M y) (sourceLowerBroadcastAction U y) := by
  intro z _ _ i
  exact actual_common_boundary_broadcast_IC Γ U hpay π M hM hrank hIC hy i z

end FCAppendix.Affine.Uniform07Finishing
