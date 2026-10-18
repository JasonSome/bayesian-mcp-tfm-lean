import FCAppendix.Exclusive.NarrowGlobalGuardsRawReference

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open Set

lemma pricedPayoff_full_route_strict_global (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (ha : a.Allowed) (lam p0 b : ℝ)
    (hlam : 0 < lam) (hp0 : 0 < p0) (hp1 : p0 < 1)
    (hFOC : 1=lam*fTariff d a p0) (hne : b ≠ referenceBid d lam p0) :
    pricedPayoff (d+1) (d+1) a b lam < referenceUtility d a lam 1 p0 := by
  let p := menuMarginal (d+1) b lam
  have hpr := menuMarginal_bounds (d+1) b lam hlam
  have hplt : p < 1 := demand_lt_one _ (hlam.trans_le (le_max_right _ _)) hlam
  have hpactive : p=activeDemand (d+1) b lam := menuMarginal_eq_activeDemand _ (by omega) b lam hlam
  by_cases hz : p=0
  · have hpos := referenceUtility_pos d hd a ha lam 1 p0 hlam hp0 hp1 hFOC
    change PayOnce.success (d+1) p-b*binomialPolynomial (d+1) a.charge p < _
    simpa only [hz,PayOnce.success,sub_zero,one_pow,sub_self,
      binomialPolynomial_at_zero,UserTariff.charge_zero,mul_zero] using hpos
  · have hpp : 0 < p := lt_of_le_of_ne hpr.1 (Ne.symm hz)
    have hb : 0 < b := by
      by_contra hn
      have hh : activeDemand (d+1) b lam=0 := by simp [activeDemand,hn]
      exact hz (hpactive.trans hh)
    have hbl : lam < b := (demand_pos_iff (d+1) (by omega) hb hlam.le).mp (by
      simpa only [p,hpactive,activeDemand,if_pos hb] using hpp)
    have hprice : b*(1-p)^d=lam := by
      simpa only [Nat.add_sub_cancel] using
        (show b*(1-p)^((d+1)-1)=lam from by
          rw [hpactive,activeDemand,if_pos hb,demand_receipt (d+1) (by omega) hb hlam,
            min_eq_right hbl.le])
    have hbid : referenceBid d lam p=b :=
      (div_eq_iff (pow_pos (sub_pos.mpr hplt) _).ne').mpr hprice.symm
    have hnep : p ≠ p0 := fun he => hne (hbid.symm.trans (congrArg (referenceBid d lam) he))
    have hr := referenceUtility_strict_global d hd a ha lam 1 p0 hlam hp0 hp1 hFOC p
      ⟨hpr.1,hplt⟩ hnep
    have he : pricedPayoff (d+1) (d+1) a b lam=referenceUtility d a lam 1 p := by
      unfold pricedPayoff referenceUtility
      rw [referenceBidCost_eq_actual d a lam p hpr.1 hplt,hbid,
        binomialPolynomial_eq_expect _ _ _ hpr.1 hplt.le]
      simp only [one_mul]
      rfl
    exact he.trans_lt hr

def referenceCentralBid (d : ℕ) (a : UserTariff) (p0 : ℝ) : ℝ :=
  referenceBid d (normalizedPrice d a p0) p0

lemma referenceRawFullGap_pos (d : ℕ) (hd : 1 ≤ d) (a : UserTariff) (ha : a.Allowed)
    (p0 b : ℝ) (hp0 : 0 < p0) (hp1 : p0 < 1)
    (hne : b ≠ referenceCentralBid d a p0) :
    0 < referenceRawGap d (d+1) a p0 b := by
  have hf := (fTariff_pos_and_derivative_pos d hd a ha hp0.le hp1).1
  apply sub_pos.mpr
  exact pricedPayoff_full_route_strict_global d hd a ha _ p0 b
    (one_div_pos.mpr hf) hp0 hp1 (one_div_mul_cancel hf.ne').symm hne

lemma continuousOn_referenceCentralBid_affine (d : ℕ) (hd : 1 ≤ d)
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1) :
    ContinuousOn (fun eta => referenceCentralBid d (.affine eta) p0) (Icc (0:ℝ) 1) :=
  (continuousOn_normalizedPrice_affine d hd p0 hp0 hp1).div_const ((1-p0)^d)

lemma compact_positive_margin {α : Type*} [TopologicalSpace α] (K : Set α)
    (hK : IsCompact K) (f : α → ℝ) (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ x ∈ K, gap ≤ f x := by
  by_cases hn : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hn hf
    exact ⟨f x,hpos x hx,fun y hy => hmin hy⟩
  · exact ⟨1,zero_lt_one,fun x hx => (hn ⟨x,hx⟩).elim⟩

theorem referenceRawFullGap_uniform_compact (d : ℕ) (hd : 1 ≤ d)
    (p0 B radius : ℝ) (hp0 : 0 < p0) (hp1 : p0 < 1) (hradius : 0 < radius) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ a : UserTariff, a.Allowed → ∀ b ∈ Icc (0:ℝ) B,
      radius ≤ |b-referenceCentralBid d a p0| →
      gap ≤ referenceRawGap d (d+1) a p0 b := by
  let K0 : Set (ℝ×ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) B
  let K := {x ∈ K0 | radius ≤ |x.2-referenceCentralBid d (.affine x.1) p0|}
  have hK0 : IsCompact K0 := isCompact_Icc.prod isCompact_Icc
  have hbc : ContinuousOn (fun x : ℝ×ℝ => referenceCentralBid d (.affine x.1) p0) K0 :=
    (continuousOn_referenceCentralBid_affine d hd p0 hp0.le hp1).comp'
      continuous_fst.continuousOn (fun _ hx => hx.1)
  have hdist : ContinuousOn (fun x : ℝ×ℝ => |x.2-referenceCentralBid d (.affine x.1) p0|) K0 :=
    (continuous_snd.continuousOn.sub hbc).abs
  have hKclosed : IsClosed K := hK0.isClosed.isClosed_le continuousOn_const hdist
  have hK : IsCompact K := hK0.of_isClosed_subset hKclosed (fun _ hx => hx.1)
  have hgc := (continuousOn_referenceRawGap_affine d (d+1) hd p0 hp0.le hp1).mono
    (show K ⊆ Icc (0:ℝ) 1 ×ˢ univ from fun _ hx => ⟨hx.1.1,mem_univ _⟩)
  obtain ⟨ga,hga,hgaBound⟩ := compact_positive_margin K hK
    (fun x => referenceRawGap d (d+1) (.affine x.1) p0 x.2) hgc (by
      intro x hx
      apply referenceRawFullGap_pos d hd (.affine x.1) hx.1.1 p0 x.2 hp0 hp1
      intro he
      have hh := hx.2
      rw [he,sub_self,abs_zero] at hh
      exact (not_le_of_gt hradius) hh)
  let Ku := {b ∈ Icc (0:ℝ) B | radius ≤ |b-referenceCentralBid d .unique p0|}
  have hKu : IsCompact Ku := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  have hf := (fTariff_pos_and_derivative_pos d hd .unique trivial hp0.le hp1).1
  have huc : ContinuousOn (referenceRawGap d (d+1) .unique p0) Ku := by
    apply continuousOn_const.sub
    exact (continuous_pricedPayoff_fixedPrice (d+1) (d+1) (by omega) .unique
      (normalizedPrice d .unique p0) (one_div_pos.mpr hf)).continuousOn
  obtain ⟨gu,hgu,hguBound⟩ := compact_positive_margin Ku hKu _ huc (by
    intro b hb
    apply referenceRawFullGap_pos d hd .unique trivial p0 b hp0 hp1
    intro he
    have hh := hb.2
    rw [he,sub_self,abs_zero] at hh
    exact (not_le_of_gt hradius) hh)
  refine ⟨min gu ga,lt_min hgu hga,?_⟩
  intro a ha b hb hdist
  cases a with
  | unique => exact (min_le_left _ _).trans (hguBound b ⟨hb,hdist⟩)
  | affine eta =>
    exact (min_le_right _ _).trans (hgaBound (eta,b) ⟨⟨ha,hb⟩,hdist⟩)

end FCAppendix.Exclusive.Narrow.Global
