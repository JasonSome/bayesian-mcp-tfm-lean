import FCAppendix.Affine.Tail04.DownstreamHigherBridge
import FCAppendix.Affine.Hybrid.Tail03.OriginalLawIdentity

noncomputable section
namespace FCAppendix.Affine.TailFinish04
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Hybrid.Tail03 Tail04

variable {eta1 eta2 : ℝ} (p : Hybrid.Tail03.Parameters eta1 eta2)

private abbrev P := Hybrid.Tail03.EarlySourceAdapter.values p

private lemma source_support_lower (v : ℝ)
    (hv : v∈Icc (0:ℝ) (P p).d0∪(P p).partialValues∪(P p).bulkValues∪Ici (P p).M) :
    v∈Icc (0:ℝ) p.d0∪Icc (2-p.valueWidth) (2+p.valueWidth)∪
      Ici (bulkValue p.center-p.valueWidth) := by
  rcases hv with ((hl|hp)|ha)|ht
  · exact Or.inl (Or.inl hl)
  · exact Or.inl (Or.inr hp)
  · exact Or.inr ha.1
  · apply Or.inr
    change bulkValue p.center-p.valueWidth≤v
    change p.tailFloor≤v at ht
    linarith [p.tail_separation,p.valueWidth_pos]

private lemma original_support : ∀ᵐv ∂(commonLaw p : Measure ℝ),
    v∈Icc (0:ℝ) (P p).d0∪(P p).partialValues∪(P p).bulkValues∪Ici (P p).M := by
  rw [←OriginalLawIdentity.valueLaw_eq_commonLaw p]
  exact (P p).fine_support

private def pairFamilies (Y : DownstreamLowerBridge.Family p)
    (Z : DownstreamHigherBridge.Family p) :
    ActualTwoCoefficientFamilies (commonLaw p) eta1 eta2 where
  firstMarket:=max Y.offset Z.offset
  firstMarket_pos:=by
    have hz : 0<Z.offset := by
      dsimp [DownstreamHigherBridge.Family.offset]
      omega
    exact hz.trans_le (le_max_right _ _)
  lower:=fun m hm=>Y.native m ((le_max_left _ _).trans hm)
  upper:=fun m hm=>Z.native m ((le_max_right _ _).trans hm)

private theorem assemble_limits (Y : DownstreamLowerBridge.Family p)
    (Z : DownstreamHigherBridge.Family p) :
    Nonempty (OneCommonSubsequenceLimits p (pairFamilies p Y Z)) := by
  let f:=pairFamilies p Y Z
  have hcofinal : Tendsto (fun j=>Z.population (Z.subsequence j)) atTop atTop :=
    Z.family.population_tendsto.comp Z.subsequence_strict.tendsto_atTop
  obtain ⟨K,hK⟩:=eventually_atTop.1
    (hcofinal.eventually (eventually_ge_atTop f.firstMarket))
  let index : ℕ→f.Market:=fun j=>
    ⟨Z.population (Z.subsequence (K+j)),hK (K+j) (by omega)⟩
  have hincreasing : StrictMono (fun j=>(index j).1) := by
    intro a b hab
    change Z.population (Z.subsequence (K+a))<Z.population (Z.subsequence (K+b))
    rw [Z.exact_index,Z.exact_index]
    exact Nat.add_lt_add_left (Z.subsequence_strict (by omega)) _
  have hindex : Tendsto (fun j=>(index j).1) atTop atTop :=
    hincreasing.tendsto_atTop
  have hshift : Tendsto (fun j : ℕ=>K+j) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat K
  have hlargeY (j : ℕ) : Y.offset≤(index j).1 :=
    (le_max_left _ _).trans (index j).2
  have hlargeZ (j : ℕ) : Z.offset≤(index j).1 :=
    (le_max_right _ _).trans (index j).2
  have hindexZ (j : ℕ) : (index j).1-Z.offset=Z.subsequence (K+j) := by
    change Z.population (Z.subsequence (K+j))-Z.offset=Z.subsequence (K+j)
    rw [Z.exact_index]
    omega
  have hupper_count (j : ℕ) (v : ℝ) :
      ((f.upperAt (index j)).conditionalCount v)=
        (Z.nativeAt (Z.subsequence (K+j))).conditionalCount v := by
    change (Z.native (index j).1 (hlargeZ j)).conditionalCount v=_
    rw [Z.native_count,hindexZ]
  have hupper_load (j : ℕ) :
      finiteLoad (f.upperAt (index j)).game=
        finiteLoad (Z.nativeAt (Z.subsequence (K+j))).game := by
    change finiteLoad (Z.native (index j).1 (hlargeZ j)).game=_
    rw [Z.native_load,hindexZ]
  have hlower_load (j : ℕ) :
      finiteLoad (f.lowerAt (index j)).game=
        finiteLoad (Y.nativeAt ((index j).1-Y.offset)).game := by
    change finiteLoad (Y.native (index j).1 (hlargeY j)).game=_
    exact Y.native_load _ _
  have lower_limits (v : ℝ)
      (hv : v∈Icc (0:ℝ) p.d0∪Icc (2-p.valueWidth) (2+p.valueWidth)∪
        Ici (bulkValue p.center-p.valueWidth)) (r : Fin 3) :
      Tendsto (fun j=>((f.lowerAt (index j)).conditionalCount v).mass r) atTop
        (𝓝 ((Y.limitLaw v).mass r)) := by
    exact Y.original_fixed_counts_on (fun j=>(index j).1) hindex hlargeY v hv r
  have upper_limits (v : ℝ)
      (hv : v∈Icc (0:ℝ) (P p).d0∪(P p).partialValues∪(P p).bulkValues∪Ici (P p).M)
      (r : Fin 3) :
      Tendsto (fun j=>((f.upperAt (index j)).conditionalCount v).mass r) atTop
        (𝓝 ((Z.limitLaw v).mass r)) := by
    have h:= (DownstreamHigherBridge.Family.fixed_counts Z v hv r).comp hshift
    simpa only [Function.comp_def,hupper_count] using h
  refine ⟨{
    index:=index
    increasing:=hincreasing
    multiplier:=Z.multiplier
    multiplier_mem:=Z.multiplier_mem
    lowerLaw:=Y.limitLaw
    upperLaw:=Z.limitLaw
    measurable_lower:=Y.measurable_limitLaw
    measurable_upper:=Z.measurable_limitLaw
    ae_count_limits:=?_
    fixed_tail_count_limits:=?_
    lower_tail:=Y.limit_tail
    upper_tail_failure:=Z.limit_tail_failure
    upper_tail_duplicates:=Z.limit_tail_duplicates
    low_lower:=Y.limit_low_ae
    low_upper:=Z.limit_low_ae
    partial_lower:=Y.limit_partial_ae
    partial_upper:=Z.limit_partial_ae
    fixed_upper_lower:=Y.limit_fixed_upper_ae
    underfill_lower:=?_
    underfill_upper:=?_ }⟩
  · filter_upwards [original_support p] with v hv
    intro r
    exact ⟨lower_limits v (source_support_lower p v hv) r,upper_limits v hv r⟩
  · intro v hv r
    have hs : v∈Icc (0:ℝ) (P p).d0∪(P p).partialValues∪(P p).bulkValues∪Ici (P p).M :=
      Or.inr hv
    exact ⟨lower_limits v (source_support_lower p v hs) r,upper_limits v hs r⟩
  · have hsub : Tendsto (fun j=>(index j).1-Y.offset) atTop atTop :=
      (tendsto_sub_atTop_nat Y.offset).comp hindex
    have h:=Y.underfill_tendsto.comp hsub
    have he (j : ℕ) : Y.population ((index j).1-Y.offset)=(index j).1 :=
      Y.population_reindex _ (hlargeY j)
    convert! h using 1
    funext j
    dsimp only [Function.comp_apply]
    have hcap := congrArg (fun m : ℕ => 2*(sourceCapacity m:ℝ)/(m:ℝ)) (he j)
    exact congrArg₂ (fun x y : ℝ => x-y) hcap.symm (hlower_load j)
  · have h:=Z.underfill_tendsto.comp (Z.subsequence_strict.tendsto_atTop.comp hshift)
    convert! h using 1
    funext j
    dsimp only [Function.comp_apply]
    rw [hupper_load j]
    rfl

theorem exists_original_tail_families
    (p : Hybrid.Tail03.Parameters eta1 eta2) :
    Nonempty (Hybrid.Tail03.BothOriginalFiniteFamiliesAndLimits p) := by
  obtain ⟨Y⟩:=DownstreamLowerBridge.exists_family p
  obtain ⟨Z⟩:=DownstreamHigherBridge.exists_family p
  obtain ⟨limits⟩:=assemble_limits p Y Z
  exact ⟨{families:=pairFamilies p Y Z,limits:=limits}⟩

end FCAppendix.Affine.TailFinish04
