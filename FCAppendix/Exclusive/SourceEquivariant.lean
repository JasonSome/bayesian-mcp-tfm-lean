import FCAppendix.Exclusive.SourceProposer
import FCAppendix.Exclusive.MarkerConstructionEquivariant

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem constructed_source_policy_equivariant (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ L, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback L s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids L))
    (hpolicy : ∀ j L s, (Γ.policy j L s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback L s).val) :
    PolicyLawEquivariant Γ := by
  classical
  intro e j L _
  by_cases helig : Marker.SourceEligible hm cutoff L n c
  · apply Measure.map_congr
    exact Eventually.of_forall fun s => by
      change (Γ.policy j (L ∘ e.symm) s).val = (Γ.policy j L s).val.map e.toEmbedding
      rw [hpolicy,hpolicy]
      exact Marker.sourceContinuation_relabel_of_eligible hm hn hc cutoff fallback e L helig s s
  · have helig' : ¬ Marker.SourceEligible hm cutoff (L ∘ e.symm) n c :=
      fun h => helig ((Marker.sourceEligible_relabel_iff hm e cutoff L).mp h)
    let f := fun s => (Γ.policy j L s).val
    let f' := fun s => (Γ.policy j (L ∘ e.symm) s).val
    let T := fun S : Finset (Fin m) => S.map e.toEmbedding
    have hf : Measurable f := measurable_policy_at_list Γ j L
    have hf' : Measurable f' := measurable_policy_at_list Γ j (L ∘ e.symm)
    have hT : Measurable T := measurable_of_countable _
    have he : FiniteLaw.ofMeasure Γ.seedLaw f' hf' =
        FiniteLaw.ofMeasure Γ.seedLaw (T ∘ f) (hT.comp hf) := by
      rw [← FiniteLaw.ofMeasure_map Γ.seedLaw f hf T hT]
      change seedLottery Γ j (L ∘ e.symm) = (seedLottery Γ j L).map T
      rw [source_seedLottery_of_not_eligible Γ hm hn hc cutoff fallback hfallback hcanonical
        hpolicy j (L ∘ e.symm) helig',
        source_seedLottery_of_not_eligible Γ hm hn hc cutoff fallback hfallback hcanonical
        hpolicy j L helig]
      exact canonicalLottery_relabel n hn c hc (listBids L) e
    have hx := congrArg FiniteLaw.probabilityMeasure he
    simpa only [FiniteLaw.probabilityMeasure_ofMeasure,f,f',T,Function.comp_def] using hx

end FCAppendix.Bayes.ExclusiveConstruction
