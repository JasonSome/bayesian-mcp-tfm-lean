import FCAppendix.Affine.Tail04.NativeVersionedSource

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeVersionedSource
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne NativeVersionedRows

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)
  (V : NativeImplementation (NativeSource.input s hs))

lemma lower_band (k : ℕ) (v : ℝ) (hv : v ∈ lowerValues P) :
    ∀ᵐ a ∂(V.toNativeFamilyData.game k).σ v,a.bid < s.scalar.R := by
  by_cases hV : v ∈ V.valueSet
  · filter_upwards [V.common_bands v hV k] with a ha
    rcases hv with hv | hv
    · exact (ha.1 hv.2).1.trans_lt
        ((NativeSource.input s hs).d_lt_L.trans
          ((NativeSource.input s hs).L_lt_U.trans s.scalar.cap_below_floor))
    · exact (ha.2.1 hv).1.2.trans_lt s.scalar.cap_below_floor
  · have hk : (V.toNativeFamilyData.game k).σ v =
        Measure.dirac (V.toNativeFamilyData.nullAction k v) := by
      simp only [NativeFamilyData.game,nullTypeGame,Kernel.piecewise_apply,if_neg hV,
        Kernel.deterministic_apply]
    rw [hk]
    rw [ae_dirac_eq]
    change (V.toNativeFamilyData.nullAction k v).bid < s.scalar.R
    rcases hv with hv | hv
    · change (sourceNullAction _ _ P.d0 _ _ _ v).bid < s.scalar.R
      simp only [sourceNullAction,if_pos hv.2,lowNullAction,max_eq_left hv.1]
      have hd := (NativeSource.input s hs).d_lt_L.trans
        ((NativeSource.input s hs).L_lt_U.trans s.scalar.cap_below_floor)
      change P.d0 < s.scalar.R at hd
      change v/2 < s.scalar.R
      linarith [hv.2, hv.1, P.d0_pos]

    · change (sourceNullAction _ _ P.d0 _ _ _ v).bid < s.scalar.R
      rw [sourceNullAction_active (NativeSource.input s hs).value_order
        (NativeSource.input s hs).L_pos.le P.d0 V.source.t P.low_partial_gap (P.partial_active_gap.trans_le V.source.t_mem.1)
        V.active.targetBid (V.source.upperBid (V.toNativeFamilyData.index k)) ⟨v,hv⟩]
      exact (V.active.targetBid ⟨v,hv⟩).2.2.trans_lt s.scalar.cap_below_floor

lemma lower_count_eq (k : ℕ) (hk : 200 ≤ V.toNativeFamilyData.M k)
    (v : ℝ) (hv : v ∈ lowerValues P) :
    conditionalTypeCountLaw (data s hs V k hk).original (by omega) v =
      conditionalTypeCountLaw (V.toNativeFamilyData.game k) (by omega) v := by
  have hbelow : v < P.vA-P.w := by
    rcases hv with hv | hv
    · linarith [hv.2,P.low_partial_gap,P.partial_active_gap,P.w_pos]
    · exact hv.2.trans_lt P.partial_active_gap
  apply FiniteLaw.ext
  intro r
  have hband : ∀ᵐ a ∂(data s hs V k hk).reference.σ v,a.bid < (data s hs V k hk).R := by
    rw [reference_eq s hs V k hk]
    exact lower_band s hs V k v hv
  have he := (data s hs V k hk).lower_expect v hbelow hband
    (fun q => if q=r then 1 else 0)
  simp only [FiniteLaw.expect_singleton] at he
  rw [reference_eq s hs V k hk] at he
  exact he

lemma large (k : ℕ) : 200 ≤ V.toNativeFamilyData.M (k+200) := by
  rw [V.toNativeFamilyData.M_eq]
  omega

def originalGame (k : ℕ) : FiniteGame (V.toNativeFamilyData.M (k+200)) 2
    (marketCapacity (V.toNativeFamilyData.M (k+200))) unitInterval :=
  (data s hs V (k+200) (large s hs V k)).original

lemma low_count_limit (v : ℝ) (hv : v ∈ Icc (0:ℝ) P.d0) (r : Fin 3) :
    Tendsto (fun k => (conditionalTypeCountLaw (originalGame s hs V k)
      (by have := large s hs V k;omega) v).mass r) atTop
      (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r)) := by
  have hm (k : ℕ) : 0 < V.toNativeFamilyData.M k :=
    lt_of_lt_of_le (by norm_num) (V.toNativeFamilyData.market_valid k).1
  have h := conditional_average_mass_tendsto V.toNativeFamilyData.game hm v
    (FiniteLaw.dirac (0:Fin 3)) (V.low_count_limit v hv) r
  have hshift := h.comp (tendsto_add_atTop_nat 200)
  convert! hshift using 1
  funext k
  rw [originalGame,lower_count_eq s hs V (k+200) (large s hs V k) v (Or.inl hv)]
  rfl

lemma partial_count_limit (v : {v : ℝ // v ∈ P.partialValues}) (r : Fin 3) :
    Tendsto (fun k => (conditionalTypeCountLaw (originalGame s hs V k)
      (by have := large s hs V k;omega) v.1).mass r) atTop
      (𝓝 ((s.partialLimit hs v.1 v.2).mass r)) := by
  have hm (k : ℕ) : 0 < V.toNativeFamilyData.M k :=
    lt_of_lt_of_le (by norm_num) (V.toNativeFamilyData.market_valid k).1
  have h := conditional_average_mass_tendsto V.toNativeFamilyData.game hm v.1
    ((NativeSource.input s hs).activeCount v) (V.active_count_limit v) r
  rw [NativeSource.input_active_count s hs v] at h
  have hshift := h.comp (tendsto_add_atTop_nat 200)
  convert! hshift using 1
  funext k
  rw [originalGame,lower_count_eq s hs V (k+200) (large s hs V k) v.1 (Or.inr v.2)]
  rfl

end FCAppendix.Affine.Tail04.NativeVersionedSource
