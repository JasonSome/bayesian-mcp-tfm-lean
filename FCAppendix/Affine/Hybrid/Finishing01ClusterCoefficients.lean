import FCAppendix.Affine.Hybrid.Finishing01ClusterPointwise

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01.Primitives
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
variable (P : Primitives)

def sourceCrossingGamma : ℝ := (1-P.z)*P.clusterRankGain/16

theorem sourceCrossingGamma_pos : 0< P.sourceCrossingGamma := by
  unfold sourceCrossingGamma
  exact div_pos (mul_pos (sub_pos.mpr P.z_lt_one) P.clusterRankGain_pos) (by norm_num)

theorem uniform_good_count_coefficient (c : ℕ→ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho)) :
    ∃delta : ℝ,0< delta ∧ ∀ᶠN : ℕ in atTop,∀ kind : Fin N→ Fin 4,
      ¬activePatternCountException P.categories delta kind →
      activePatternGuarded P.xi P.L P.U (c (N+1)) P.z kind →
      let K := activePatternOwner (c (N+1)) P.z kind 0+
        activePatternOwner (c (N+1)) P.z kind 1
      (K:ℝ)/(Fintype.card (ActivePatternIndex kind):ℝ)≤(1+P.z)/2 ∧
      P.sourceCrossingGamma/((N+1:ℕ):ℝ)^2≤
        ((1-fillFraction (ι:=ActivePatternIndex kind) K)*(P.clusterRankGain/2))/
          (4*rankDenominator (ActivePatternIndex kind)) := by
  have htol : 0<(1-P.z)/2 := half_pos (sub_pos.mpr P.z_lt_one)
  have hS : {p : Fin 4→ℝ | |normalizedOwnerShare p-P.z|<(1-P.z)/2}∈
      𝓝 (sourceCountPoint P.a P.h P.rho P.z) := by
    filter_upwards [source_menu_neighborhood P.a P.h P.rho P.z P.xi P.L P.U
      ((1-P.z)/2) P.a_pos P.z_lt_one P.xi_pos P.xi_lt_one
      P.qbar_pos P.qbar_lt_one P.box_lower P.box_upper htol] with p hp
    exact hp.2.2.2.1
  obtain ⟨delta,hd,hcounts⟩ := eventually_typical_count_point_mem
    P.a P.h P.rho P.z P.z_nonneg P.z_lt_one.le P.rho_lower P.rho_upper c hc
    {p : Fin 4→ℝ | |normalizedOwnerShare p-P.z|<(1-P.z)/2} hS
  refine ⟨delta,hd,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hcounts] with N hN
  intro kind hgood hg
  have hclose (k : Fin 4) :
      |(fullCategoryCount activeFocalPrefix kind k:ℝ)-(N+1:ℕ)*P.categories.mass k|≤
        (N+1:ℕ)*delta := by
    have h := (lt_of_not_ge (fun h => hgood ⟨k,h⟩)).le
    simpa only [fullCategoryCount,Nat.cast_add] using h
  have hA : |(Fintype.card (ActivePatternIndex kind):ℝ)-(N+1:ℕ)*P.a|≤(N+1:ℕ)*delta := by
    simpa [activePattern_count_active,Primitives.categories,LowBody.categoryLaw_mass] using hclose 1
  have hH0 : |(activePatternUpper kind 0:ℝ)-(N+1:ℕ)*(P.h/2)|≤(N+1:ℕ)*delta := by
    have hh := hclose 2
    rw [show fullCategoryCount activeFocalPrefix kind 2=activePatternUpper kind 0 from
      activePattern_count_upper kind 0] at hh
    simpa [Primitives.categories,LowBody.categoryLaw_mass] using hh
  have hH1 : |(activePatternUpper kind 1:ℝ)-(N+1:ℕ)*(P.h/2)|≤(N+1:ℕ)*delta := by
    have hh := hclose 3
    rw [show fullCategoryCount activeFocalPrefix kind 3=activePatternUpper kind 1 from
      activePattern_count_upper kind 1] at hh
    simpa [Primitives.categories,LowBody.categoryLaw_mass] using hh
  have howner := hN (Fintype.card (ActivePatternIndex kind))
    (activePatternUpper kind 0) (activePatternUpper kind 1) hA hH0 hH1
  change |normalizedOwnerShare (finiteCountPoint (N+1)
    (Fintype.card (ActivePatternIndex kind)) (activePatternSmall (c (N+1)) kind)
      (activePatternQuota P.z kind) (activePatternGap (c (N+1)) kind))-P.z|<(1-P.z)/2 at howner
  rw [normalizedOwnerShare_count_eq (N+1) (Fintype.card (ActivePatternIndex kind))
    (activePatternSmall (c (N+1)) kind) (activePatternQuota P.z kind)
    (activePatternGap (c (N+1)) kind) (by omega)
      (lt_of_lt_of_le (by norm_num : (0:ℕ)<2) hg.1)] at howner
  have hshare : ((activePatternOwner (c (N+1)) P.z kind 0+
      activePatternOwner (c (N+1)) P.z kind 1:ℕ):ℝ)/
      (Fintype.card (ActivePatternIndex kind):ℝ)≤(1+P.z)/2 := by
    rw [activePatternOwner_sum_of_ne (c (N+1)) P.z kind hg.2.1]
    linarith [(abs_lt.mp howner).2]
  refine ⟨hshare,?_⟩
  have hcard : Fintype.card (ActivePatternIndex kind)≤ N+1 := by
    simpa only [Fintype.card_fin] using
      (Fintype.card_le_of_injective (Subtype.val : ActivePatternIndex kind→ Fin (N+1))
        Subtype.val_injective)
  have hcoef := favored_crossing_coefficient_lower (ι:=ActivePatternIndex kind)
    hg.1 hg.2.2.2.1.le hcard P.z_lt_one P.clusterRankGain_pos.le hshare
  have he : P.sourceCrossingGamma/((N+1:ℕ):ℝ)^2=
      (1-P.z)*P.clusterRankGain/(16*((N+1:ℕ):ℝ)^2) := by
    unfold sourceCrossingGamma
    ring
  rw [he]
  exact hcoef

end FCAppendix.Affine.Hybrid.Finish01.Primitives
