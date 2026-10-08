import FCAppendix.Finite.ConditionalCountLaw
import FCAppendix.Finite.InterimUtilityBounds
import FCAppendix.Finite.SingletonError
import FCAppendix.Finite.NearPPISubsequence
import FCAppendix.Finite.CapacityFill

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_typeUtility_le_price_error (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hΓ : UsersOptimal Γ) (a p : ℝ) (ha : 0 ≤ a) (hp : 0 ≤ p)
    (hA : ∀ r, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) :
    ∀ᵐ v ∂Γ.F, typeUtility Γ v ≤
      (v - Γ.g - p) * (conditionalTypeCountLaw Γ hm v).success -
      p * (conditionalTypeCountLaw Γ hm v).duplicates + typePaymentError Γ a p v := by
  have hbr := ae_all_iff.mpr hΓ
  filter_upwards [hbr] with v hv
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ =>
    envelope_le_strategy_price_error Γ i a p v ha hp hA (hv i))
  have hd := div_le_div_of_nonneg_right hh (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  simpa only [typeUtility, conditionalTypeCountLaw_success, conditionalTypeCountLaw_duplicates,
    typePaymentError, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    add_div, sub_div, mul_div_assoc] using hd

theorem aggregate_limits_of_positive_quantiles
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (hm : ∀ k, 0 < M k)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (g : ℝ) (hg : ∀ k, (Γ k).g = g)
    (a : ℕ → ℝ) (ρ p : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1) (hp0 : 0 < p)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1)) (ha0 : ∀ k, 0 ≤ a k)
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hquant : ∀ q : ℝ, 0 < q → q < ρ →
      Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 p))
    (hcut : F {g + p} = 0) :
    Tendsto (fun k => (finiteCoverage (Γ k),
      (finiteLoad (Γ k) - finiteCoverage (Γ k), finiteLoad (Γ k)))) atTop
      (𝓝 (F.real (Ioi (g + p)), (0, F.real (Ioi (g + p))))) := by
  obtain ⟨δ, hδ, hδmeas, hδ0, hlower⟩ := exists_vanishing_singleton_error M C Γ j g hg
    a ρ (ρ / 2) p hρ (by positivity) (by linarith) hM hcap ha hΓ hp hatom hA
    (hquant (ρ / 2) (by positivity) (by linarith))
  have he0 := tendsto_mean_typePaymentError_of_visible_tail M C Γ j a p ρ hp0.le hρ0.le
    hM ha hcap (fun k => (hΓ k).proposers) hA
    (visible_tail_below_common_quantile_limit M C Γ j ρ p hp0 hquant)
  simp_rw [hF] at he0
  have hupper (k : ℕ) : ∀ᵐ v ∂F, typeUtility (Γ k) v ≤
      (v - (g + p)) * (conditionalTypeCountLaw (Γ k) (hm k) v).success -
      p * (conditionalTypeCountLaw (Γ k) (hm k) v).duplicates + typePaymentError (Γ k) (a k) p v := by
    have hh := ae_typeUtility_le_price_error (Γ k) (hm k) (hΓ k).users (a k) p (ha0 k) hp0.le (hA k)
    simpa only [hF, hg, sub_add_eq_sub_sub] using hh
  have hlow (k : ℕ) : ∀ᵐ v ∂F,
      max (v - (g + p)) 0 - δ k v ≤ typeUtility (Γ k) v := by
    apply Eventually.of_forall
    intro v
    simpa only [sub_add_eq_sub_sub] using typeUtility_lower (Γ k) (hm k) v _ (fun i => hlower k i v)
  have hIe (k : ℕ) : Integrable (typePaymentError (Γ k) (a k) p) F := by
    rw [← hF k]
    exact integrable_typePaymentError (Γ k) (a k) p (ha0 k) hp0.le
  have hh := NearPPI.aggregate_limits F (fun k v => conditionalTypeCountLaw (Γ k) (hm k) v)
    (fun k => typeUtility (Γ k)) (fun k => typePaymentError (Γ k) (a k) p) δ (g + p) p hp0 hcut
    (fun k => (measurable_conditionalTypeCountLaw_success (Γ k) (hm k)).aestronglyMeasurable)
    (fun k => (measurable_conditionalTypeCountLaw_duplicates (Γ k) (hm k)).aestronglyMeasurable)
    (fun k => Eventually.of_forall (typeUtility_nonneg (Γ k)))
    (fun k => Eventually.of_forall (typePaymentError_nonneg (Γ k) (a k) p))
    (fun k => Eventually.of_forall (hδ k)) hupper hlow hIe he0 (Eventually.of_forall hδ0)
  have hS (k : ℕ) : (∫ v, (conditionalTypeCountLaw (Γ k) (hm k) v).success ∂F) = finiteCoverage (Γ k) := by
    rw [← hF k, integral_conditionalTypeCountLaw_success]
  have hD (k : ℕ) : (∫ v, (conditionalTypeCountLaw (Γ k) (hm k) v).duplicates ∂F) =
      finiteLoad (Γ k) - finiteCoverage (Γ k) := by
    rw [← hF k, integral_conditionalTypeCountLaw_duplicates]
  have hL (k : ℕ) : (∫ v, (conditionalTypeCountLaw (Γ k) (hm k) v).load ∂F) = finiteLoad (Γ k) := by
    rw [← hF k, integral_conditionalTypeCountLaw_load]
  simpa only [hS, hD, hL, NearPPI.integral_cutoffSuccess, measureReal_def] using hh

theorem aggregate_limits_of_positive_quantiles_eventually
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (g : ℝ) (hg : ∀ k, (Γ k).g = g)
    (a : ℕ → ℝ) (ρ p : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1) (hp0 : 0 < p)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hquant : ∀ q : ℝ, 0 < q → q < ρ →
      Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 p))
    (hcut : F {g + p} = 0) :
    Tendsto (fun k => (finiteCoverage (Γ k),
      (finiteLoad (Γ k) - finiteCoverage (Γ k), finiteLoad (Γ k)))) atTop
      (𝓝 (F.real (Ioi (g + p)), (0, F.real (Ioi (g + p))))) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hM.eventually_gt_atTop 0).and
    ((tendsto_order.mp ha).1 0 zero_lt_one))
  have hs : Tendsto (fun k : ℕ => k + N) atTop atTop := tendsto_add_atTop_nat N
  apply (tendsto_add_atTop_iff_nat N).mp
  exact aggregate_limits_of_positive_quantiles (fun k => M (k + N)) (fun k => C (k + N))
    (fun k => Γ (k + N)) j (fun k => (hN (k + N) (by omega)).1)
    F (fun k => hF (k + N)) g (fun k => hg (k + N)) (fun k => a (k + N)) ρ p hρ0 hρ hp0
    (hM.comp hs) (hcap.comp hs) (ha.comp hs) (fun k => (hN (k + N) (by omega)).2.le)
    (fun k => hΓ (k + N)) (fun k => hp (k + N)) (fun k => hatom (k + N))
    (fun k => hA (k + N)) (fun q hq hqr => (hquant q hq hqr).comp hs) hcut

theorem tail_eq_capacity_of_positive_quantiles
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (g : ℝ) (hg : ∀ k, (Γ k).g = g)
    (a : ℕ → ℝ) (ρ p : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1) (hp0 : 0 < p)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hquant : ∀ q : ℝ, 0 < q → q < ρ →
      Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 p))
    (hcut : F {g + p} = 0) : F.real (Ioi (g + p)) = (n : ℝ) * ρ := by
  have hagg := aggregate_limits_of_positive_quantiles_eventually M C Γ j F hF g hg a ρ p
    hρ0 hρ hp0 hM hcap ha hΓ hp hatom hA hquant hcut
  have htail := visible_tail_below_common_quantile_limit M C Γ j ρ p hp0 hquant
  have hload := tendsto_finiteLoad_of_visible_tail M C Γ j a (p / 2) ρ (by positivity) hM
    ((tendsto_order.mp ha).1 0 zero_lt_one) hcap (fun k => (hΓ k).proposers) hA
    (htail (p / 2) (by linarith))
  have htailLoad : Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 (F.real (Ioi (g + p)))) := by
    have hc : Continuous (fun z : ℝ × (ℝ × ℝ) => z.2.2) := by fun_prop
    exact (hc.tendsto _).comp hagg
  exact tendsto_nhds_unique htailLoad hload

theorem nearPPI_aggregate_limits
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ k, (Γ k).F = F) (g : ℝ) (hg : ∀ k, (Γ k).g = g)
    (a : ℕ → ℝ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hscarce : (n : ℝ) * ρ < F.real (Ioi g)) :
    Tendsto (fun k => (finiteCoverage (Γ k),
      (finiteLoad (Γ k) - finiteCoverage (Γ k), finiteLoad (Γ k)))) atTop
      (𝓝 ((n : ℝ) * ρ, (0, (n : ℝ) * ρ))) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨p, hp0, φ, hφ, hquant, _, _⟩ := exists_positive_price_subsequence
    (M ∘ ns) (C ∘ ns) (fun k => Γ (ns k)) j F (fun k => hF (ns k)) g (fun k => hg (ns k))
    (a ∘ ns) ρ hρ0 hρ (hM.comp hns) (hcap.comp hns) (ha.comp hns)
    (fun k => hΓ (ns k)) (fun k => hp (ns k)) (fun k => hatom (ns k)) (fun k => hA (ns k)) hscarce
  have hs := hns.comp hφ.tendsto_atTop
  have hagg := aggregate_limits_of_positive_quantiles_eventually
    (fun k => M (ns (φ k))) (fun k => C (ns (φ k))) (fun k => Γ (ns (φ k))) j
    F (fun k => hF (ns (φ k))) g (fun k => hg (ns (φ k))) (fun k => a (ns (φ k)))
    ρ p hρ0 hρ hp0 (hM.comp hs) (hcap.comp hs) (ha.comp hs)
    (fun k => hΓ (ns (φ k))) (fun k => hp (ns (φ k))) (fun k => hatom (ns (φ k)))
    (fun k => hA (ns (φ k))) hquant (measure_singleton _)
  have hprice := tail_eq_capacity_of_positive_quantiles
    (fun k => M (ns (φ k))) (fun k => C (ns (φ k))) (fun k => Γ (ns (φ k))) j
    F (fun k => hF (ns (φ k))) g (fun k => hg (ns (φ k))) (fun k => a (ns (φ k)))
    ρ p hρ0 hρ hp0 (hM.comp hs) (hcap.comp hs) (ha.comp hs)
    (fun k => hΓ (ns (φ k))) (fun k => hp (ns (φ k))) (fun k => hatom (ns (φ k)))
    (fun k => hA (ns (φ k))) hquant (measure_singleton _)
  exact ⟨φ, by simpa only [hprice] using hagg⟩

end FCAppendix.Bayes
