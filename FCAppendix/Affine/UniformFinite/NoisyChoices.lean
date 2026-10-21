import FCAppendix.Affine.UniformFinite.PhysicalLaw

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology
open Existence.Distributional

def choiceForBid (i : Row) (v : Value i) (b : ℝ) : unitInterval :=
  ⟨Uniform05.clip01 ((b-Uniform05.floorBid i v)/width i v),
    Uniform05.clip01_nonneg _,Uniform05.clip01_le_one _⟩

lemma measurable_choiceForBid (i : Row) :
    Measurable (fun p : Value i×ℝ=> choiceForBid i p.1 p.2) := by
  apply Measurable.subtype_mk
  have hf := (Uniform05.continuous_floor i).measurable
  unfold width hiBid
  exact Uniform05.continuous_clip01.measurable.comp (by fun_prop)

lemma choiceForBid_exact (i : Row) (v : Value i) (hv : 0<(v:ℝ))
    (b : ℝ) (hb : b∈Icc (Uniform05.floorBid i v) (hiBid i v)) :
    (baseBid i (v,choiceForBid i v b):ℝ)=b := by
  have hw := width_positive i v hv
  have hq : (b-Uniform05.floorBid i v)/width i v∈Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hb.1) hw.le
    · apply (div_le_one hw).mpr
      unfold width
      linarith [hb.2]
  rw [baseBid_val]
  change Uniform05.floorBid i v+width i v*
    Uniform05.clip01 ((b-Uniform05.floorBid i v)/width i v)=b
  rw [Uniform05.clip01_eq_self hq]
  field_simp [hw.ne']
  ring

lemma noisy_bid_from_base (i : Row) (eps : unitInterval)
    (p : Value i×unitInterval) (z : unitInterval) :
    (noisyBid i (eps,(p,z)):ℝ)=
      (1-(eps:ℝ))*(baseBid i p:ℝ)+
        (eps:ℝ)*(Uniform05.floorBid i p.1+width i p.1*(z:ℝ)) := by
  rw [baseBid_val]
  change noisyRealBid i eps p.1 p.2 z=_
  unfold noisyRealBid
  ring

lemma same_noise_difference (i : Row) (eps : unitInterval) (v : Value i)
    (q q' z : unitInterval) :
    (noisyBid i (eps,((v,q'),z)):ℝ)-(noisyBid i (eps,((v,q),z)):ℝ)=
      (1-(eps:ℝ))*((baseBid i (v,q'):ℝ)-(baseBid i (v,q):ℝ)) := by
  rw [noisy_bid_from_base,noisy_bid_from_base]
  ring

lemma width_le_value (i : Row) (v : Value i) : width i v≤(v:ℝ) := by
  have hf := Uniform05.floor_nonneg i v
  have hh : hiBid i v≤(v:ℝ) := min_le_left _ _
  unfold width
  linarith

lemma width_le_cap (i : Row) (v : Value i) : width i v≤ Uniform05.cap i := by
  have hf := Uniform05.floor_nonneg i v
  have hh : hiBid i v≤ Uniform05.cap i := min_le_right _ _
  unfold width
  linarith

theorem physical_base_error (i : Row) (eps : unitInterval)
    (p : Value i×unitInterval) (z : unitInterval) :
    |(noisyBid i (eps,(p,z)):ℝ)-(baseBid i p:ℝ)|≤(eps:ℝ)*(p.1:ℝ) := by
  have he : (noisyBid i (eps,(p,z)):ℝ)-(baseBid i p:ℝ)=
      (eps:ℝ)*width i p.1*((z:ℝ)-(p.2:ℝ)) := by
    rw [baseBid_val]
    change noisyRealBid i eps p.1 p.2 z-_= _
    unfold noisyRealBid
    ring
  have hz : |(z:ℝ)-(p.2:ℝ)|≤1 := abs_le.mpr
    ⟨by linarith [z.property.1,p.2.property.2],
      by linarith [z.property.2,p.2.property.1]⟩
  rw [he,abs_mul,abs_mul,abs_of_nonneg eps.property.1,
    abs_of_nonneg (width_nonneg i p.1)]
  calc
    _≤(eps:ℝ)*width i p.1*1 :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg eps.property.1 (width_nonneg i p.1))
    _≤(eps:ℝ)*(p.1:ℝ) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left (width_le_value i p.1) eps.property.1

theorem feasible_target_noise_error (i : Row) (eps : unitInterval) (v : Value i)
    (hv : 0<(v:ℝ)) (b : ℝ)
    (hb : b∈Icc (Uniform05.floorBid i v) (hiBid i v)) (z : unitInterval) :
    |(noisyBid i (eps,((v,choiceForBid i v b),z)):ℝ)-b|≤(eps:ℝ)*(v:ℝ) := by
  simpa only [choiceForBid_exact i v hv b hb] using
    physical_base_error i eps (v,choiceForBid i v b) z

theorem crossing_target (i : Row) (v : Value i) (hv : 0<(v:ℝ))
    (B center radius surplus capSlack : ℝ)
    (hB : B∈Icc (Uniform05.floorBid i v) (hiBid i v))
    (hcluster : |B-center|≤ radius) (hr : 0≤ radius)
    (hsurplus : B+surplus≤(v:ℝ)) (hcap : B+capSlack≤ Uniform05.cap i)
    (hsmallV : 3*radius≤ surplus) (hsmallU : 3*radius≤ capSlack) :
    center+2*radius∈Icc (Uniform05.floorBid i v) (hiBid i v) ∧
    (baseBid i (v,choiceForBid i v (center+2*radius)):ℝ)=center+2*radius := by
  have hc := abs_le.mp hcluster
  have hh : center+2*radius∈Icc (Uniform05.floorBid i v) (hiBid i v) := by
    constructor
    · linarith [hB.1]
    · apply le_min <;> linarith
  exact ⟨hh,choiceForBid_exact i v hv _ hh⟩

theorem compact_physical_subsequence (i : Row) (eps : ℕ→ unitInterval)
    (pi : ℕ→ Joint i) (heps : Tendsto eps atTop (𝓝 0)) :
    ∃ (pi0 : Joint i) (phi : ℕ→ℕ), StrictMono phi ∧
      Tendsto (pi∘phi) atTop (𝓝 pi0) ∧
      Tendsto (fun j=> physicalLaw i (eps (phi j),pi (phi j))) atTop
        (𝓝 (pushLaw (lowerMeasure i) (baseBid i) (continuous_baseBid i) pi0)) := by
  obtain ⟨pi0,phi,hphi,hlim⟩ := CompactSpace.tendsto_subseq pi
  refine ⟨pi0,phi,hphi,hlim,?_⟩
  rw [← physicalLaw_zero]
  exact (continuous_physicalLaw i).continuousAt.tendsto.comp
    ((heps.comp hphi.tendsto_atTop).prodMk_nhds hlim)

end FCAppendix.Affine.UniformFinite
