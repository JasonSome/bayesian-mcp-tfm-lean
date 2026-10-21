import FCAppendix.Affine.Uniform07Finishing.Native.WeightedContinuation
import FCAppendix.Affine.WeightedSampler

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine
open Existence.PayOnceBounded (listBids positiveSupport mem_positiveSupport)
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem canonical_eq_clipped_at_root {ξ U z : ℝ} (b : ι→ℝ) (d : ℕ)
    (hξ:0<ξ) (hξ1:ξ<1) (hz:0< z) (hguard:(1-ξ)*U≤ z)
    (hbU:∀i,b i≤ U) (hroot:(∑i,ClippedResidual.exposure ξ z (b i))=(d:ℝ)) :
    EqualCapacity.positiveMarginal ξ d b=fun i=>ClippedResidual.exposure ξ z (b i) := by
  let S:=positiveSupport b
  let q:=fun i : ι=>ClippedResidual.exposure ξ z (b i)
  have hzero (i : ι) (hi:i∉S) : q i=0 := by
    have hb:b i≤ 0:=le_of_not_gt (fun h=>hi ((mem_positiveSupport b i).mpr h))
    exact ClippedResidual.exposure_zero (hb.trans hz.le)
  have hsumS:(∑i:S,q i.1)=(d:ℝ) := by
    calc
      _ = ∑i∈S,q i := Finset.sum_attach S q
      _ = ∑i:ι,q i := Finset.sum_subset (Finset.subset_univ S) (fun i _ hi=>hzero i hi)
      _ = _ := hroot
  have hd:d≤ S.card := by
    have hh:(d:ℝ)≤(S.card:ℝ) := by
      rw [←hsumS]
      calc
        (∑i:S,q i.1)≤∑_i:S,(1:ℝ) :=
          Finset.sum_le_sum (fun i _=>ClippedResidual.exposure_le_one ξ z (b i.1))
        _ = _ := by simp
    exact_mod_cast hh
  have ht:=ClippedResidual.exposure_threshold hξ hξ1 hz hguard b hbU
  have hk:EqualCapacity.IsKernel ξ d (fun i:S=>b i.1) (fun i:S=>q i.1) := by
    refine ⟨fun i=>ClippedResidual.exposure_nonneg hξ hz,
      fun i=>ClippedResidual.exposure_le_one ξ z _,?_,z,hz.le,?_,?_,?_⟩
    · simpa only [Fintype.card_coe,min_eq_left hd] using hsumS
    · intro i hi; exact ht.1 i.1 hi
    · intro i hi; exact ht.2.1 i.1 hi
    · intro i hi hj; exact ht.2.2 i.1 hi hj
  have hb (i:S) : 0< b i.1 := (mem_positiveSupport b i.1).mp i.2
  have he:=EqualCapacity.isKernel_unique hξ d (fun i:S=>b i.1) hb
    (EqualCapacity.kernelMarginal ξ d (fun i:S=>b i.1)) (fun i:S=>q i.1)
    (EqualCapacity.kernelMarginal_spec hξ hξ1 d _ hb) hk
  funext i
  by_cases hi:i∈S
  · change EqualCapacity.onSupport ξ d S b i=q i
    rw [EqualCapacity.onSupport,dif_pos hi,he]
  · change EqualCapacity.onSupport ξ d S b i=q i
    rw [EqualCapacity.onSupport_outside ξ d S b i hi,hzero i hi]

lemma clipped_lt_one {ξ z b : ℝ} (hξ:0<ξ) (hz:0< z) (hguard:(1-ξ)*b< z) :
    ClippedResidual.exposure ξ z b<1 := by
  by_cases hb:b≤ z
  · rw [ClippedResidual.exposure_zero hb]
    norm_num
  · have hzb:z< b:=lt_of_not_ge hb
    have hb0:0< b:=hz.trans hzb
    rw [ClippedResidual.exposure,max_eq_left hzb.le,max_eq_right (sub_pos.mpr hzb).le]
    apply (min_le_right _ _).trans_lt
    apply (div_lt_one (mul_pos hξ hb0)).mpr
    nlinarith

theorem threshold_eq_guarded_root {ξ U z : ℝ} [Nonempty ι]
    (b : ι→ℝ) (d : ℕ) (hξ:0<ξ) (hξ1:ξ<1) (hz:0< z)
    (hguard:(1-ξ)*U< z) (hbU:∀i,b i≤ U) (hd:0< d)
    (hroot:(∑i,ClippedResidual.exposure ξ z (b i))=(d:ℝ)) :
    threshold ξ d b=z := by
  have he:=canonical_eq_clipped_at_root b d hξ hξ1 hz hguard.le hbU hroot
  obtain ⟨i,hi⟩ : ∃i,0< ClippedResidual.exposure ξ z (b i) := by
    by_contra hn
    push Not at hn
    have hzq:∀i,ClippedResidual.exposure ξ z (b i)=0 :=
      fun i=>le_antisymm (hn i) (ClippedResidual.exposure_nonneg hξ hz)
    simp only [hzq,Finset.sum_const_zero] at hroot
    have hdR:(0:ℝ)< d:=by exact_mod_cast hd
    linarith
  have hbi:z< b i := by
    by_contra hn
    rw [ClippedResidual.exposure_zero (le_of_not_gt hn)] at hi
    exact (lt_irrefl 0) hi
  have hguard_i:(1-ξ)*b i< z :=
    (mul_le_mul_of_nonneg_left (hbU i) (by linarith)).trans_lt hguard
  have hip:EqualCapacity.positiveMarginal ξ d b i=ClippedResidual.exposure ξ z (b i):=
    congrFun he i
  have ht:=(threshold_spec ξ hξ hξ1 d b).1.2.2 i (by rw [hip];exact hi)
    (by rw [hip];exact clipped_lt_one hξ hz hguard_i)
  dsimp only at ht
  rw [hip,ClippedResidual.exposure_receipt hξ hz hbi hguard_i.le] at ht
  exact ht.symm

theorem source_U4_passes_native_test {m : ℕ} [Nonempty (Fin m)]
    {ξ U lo hi slack : ℝ} (L : LocalList m) (_hL:NonnegativeList L)
    (d₀ d₁ : ℕ) (E : Finset (Fin m))
    (hξ:0<ξ) (hξ1:ξ<1) (hU:0< U) (hlo:0< lo) (hlh:lo< hi)
    (hguard:(1-ξ)*U< lo) (hbU:∀i,entryBid (L i)≤ U)
    (hd:0< min d₀ d₁) (heps:0< slack)
    (hcard:E.card=max d₀ d₁-min d₀ d₁)
    (hlow:((min d₀ d₁:ℕ):ℝ)+(E.card:ℝ)+slack<
      ∑i,ClippedResidual.exposure ξ lo (entryBid (L i)))
    (hhigh:(∑i,ClippedResidual.exposure ξ hi (entryBid (L i)))<
      ((min d₀ d₁:ℕ):ℝ)-slack)
    (hE:∀i∈E,hi≤ entryBid (L i)) :
    ValidExclusive ξ L d₀ d₁ E ∧
    ∃z∈Icc lo hi,
      ClippedResidual.remainingDemand ξ (fun i=>entryBid (L i)) E z=(min d₀ d₁:ℕ) ∧
      EqualCapacity.positiveMarginal ξ (min d₀ d₁) (listBids (remainder L E))=
        ClippedResidual.smallMarginal ξ z (fun i=>entryBid (L i)) E := by
  obtain ⟨z,⟨hz,hr⟩,hunique⟩ := ClippedResidual.exists_unique_balanced_root
    (fun i=>entryBid (L i)) E hξ hξ1 hU hlo hlh hguard.le hbU
    (by exact_mod_cast hd) heps hlow hhigh
  have hz0:0< z:=hlo.trans_le hz.1
  have hroot:(∑i,ClippedResidual.exposure ξ z (listBids (remainder L E) i))=
      ((min d₀ d₁:ℕ):ℝ) := by
    calc
      _ = ClippedResidual.remainingDemand ξ (fun i=>entryBid (L i)) E z := by
        unfold ClippedResidual.remainingDemand
        apply Finset.sum_congr rfl
        intro i _
        by_cases hiE:i∈E
        · simp [remainder_bid,hiE,ClippedResidual.exposure_zero hz0.le]
        · simp only [listBids_eq_entry,remainder_entry,if_neg hiE]
      _ = _ := hr
  have hBU:∀i,listBids (remainder L E) i≤ U := by
    intro i
    rw [listBids_eq_entry,remainder_entry]
    split_ifs
    · exact hU.le
    · exact hbU i
  have hth:threshold ξ (min d₀ d₁) (listBids (remainder L E))=z :=
    threshold_eq_guarded_root _ _ hξ hξ1 hz0 (hguard.trans_le hz.1) hBU hd hroot
  have hpc:=canonical_eq_clipped_at_root _ _ hξ hξ1 hz0 (hguard.le.trans hz.1) hBU hroot
  have hfill:min d₀ d₁≤(positiveSupport (listBids (remainder L E))).card := by
    have hp:=EqualCapacity.positiveMarginal_spec ξ (min d₀ d₁) hξ hξ1
      (listBids (remainder L E))
    rw [hpc,hroot] at hp
    have hh:((min d₀ d₁:ℕ):ℝ)≤(positiveSupport (listBids (remainder L E))).card := by
      rw [hp.2.2]
      exact_mod_cast min_le_right (min d₀ d₁) (positiveSupport (listBids (remainder L E))).card
    exact_mod_cast hh
  have hvalid:ValidExclusive ξ L d₀ d₁ E := by
    refine ⟨hcard,?_,hfill,?_⟩
    · intro i hiE hn
      have hh:=hE i hiE
      rw [hn] at hh
      simp only [entryBid] at hh
      linarith
    · intro i hiE
      rw [hth]
      exact ⟨(mul_le_mul_of_nonneg_left (hbU i) (by linarith)).trans
        (hguard.le.trans hz.1),hz.2.trans (hE i hiE)⟩
  refine ⟨hvalid,z,hz,hr,?_⟩
  rw [hpc]
  funext i
  by_cases hiE:i∈E
  · simp [ClippedResidual.smallMarginal,remainder_bid,hiE,
      ClippedResidual.exposure_zero hz0.le]
  · simp only [ClippedResidual.smallMarginal,listBids_eq_entry,remainder_entry,if_neg hiE]

theorem weighted_path_exclusive_properties {m : ℕ} [Nonempty (Fin m)]
    (L : LocalList m) (w : WeightedSampling.Weights (Fin m)) (Δ : ℕ)
    (hW:(Δ:ℝ)< WeightedSampling.totalWeight w)
    (hpositive:∀i,0< w.1 i→ L i≠none)
    (path : WeightedSampling.Path (Fin m) Δ)
    (hpath:0<(WeightedSampling.pathLaw w Δ ∅).mass path) :
    (WeightedSampling.finalSet Δ ∅ path).card=Δ ∧
    (∀i∈WeightedSampling.finalSet Δ ∅ path,L i≠none) ∧
    ∀i,w.1 i=0→ i∉WeightedSampling.finalSet Δ ∅ path := by
  have hW':((∅:Finset (Fin m)).card:ℝ)+Δ< WeightedSampling.totalWeight w := by simpa using hW
  have hc:=WeightedSampling.finalSet_card w Δ ∅ hW' path hpath
  have hp:=WeightedSampling.finalSet_weight_pos w Δ ∅ hW' (by simp) path hpath
  refine ⟨by simpa using hc,fun i hi=>hpositive i (hp i hi),?_⟩
  intro i hz hi
  have hh:=hp i hi
  rw [hz] at hh
  exact (lt_irrefl 0) hh

end FCAppendix.Affine.Uniform07Finishing.Weighted
