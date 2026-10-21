import FCAppendix.Affine.UniformFinite.ZeroQuadratic
import FCAppendix.Affine.UniformFinite.PositiveAtomLimit

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional
namespace ZeroAtoms
open OriginalGain

theorem no_zero_atom_of_noisy_cluster (i : Row) (N L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (hH : 0< PositiveClusters.sourceH i (N+2))
    (eps : ℕ→ unitInterval) (pi : ℕ→ Joint i) (pi0 : Joint i)
    (hepspos : ∀j,0<(eps j:ℝ)) (heps0 : Tendsto eps atTop (𝓝 0))
    (hIC : ∀j,NoisyIC i (N+1) (eps j) (pi j))
    (hpi : Tendsto pi atTop (𝓝 pi0)) :
    (realBidLaw i 0 pi0 : Measure ℝ) {0}=0 := by
  have hfinite:=finite_zero_cluster_estimates i N L hN hroom eps pi hepspos heps0 hIC
  have hjoint : Tendsto (fun j=>(pi j).1) atTop (𝓝 pi0.1):=
    continuous_subtype_val.continuousAt.tendsto.comp hpi
  have hcut (tau : ℝ) (htau : 0< tau) :
      (pi0.1 : Measure (Value i×unitInterval))
        {p | tau<(p.1:ℝ) ∧ (baseBid i p:ℝ)=0}=0 := by
    let Z : Set (Value i×unitInterval):={p | tau<(p.1:ℝ) ∧ (baseBid i p:ℝ)=0}
    let mass:=(pi0.1 : Measure (Value i×unitInterval)).real Z
    let A:=Uniform05.t i*PositiveClusters.sourceH i (N+2)*tau/4
    have hA : 0< A:=by have ht:=Uniform05.t_pos i; dsimp only [A]; positivity
    let r : ℕ→ℝ:=fun k=>1/((k:ℝ)+1)
    have hr (k : ℕ) : 0< r k:=by dsimp [r]; positivity
    have hrt : Tendsto r atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
    have hbound (k : ℕ) : mass*A≤11*r k := by
      obtain ⟨dmax,hdmax,hf⟩:=hfinite tau htau (r k) (hr k)
      let δ:=min (r k) (dmax/2)
      have hδ : 0<δ:=lt_min (hr k) (half_pos hdmax)
      have hδmax : δ< dmax:=(min_le_right _ _).trans_lt (half_lt_self hdmax)
      have hδr : δ≤ r k:=min_le_left _ _
      have hp:=LowBody.open_mass_bound_of_finite_quadratic
        (fun j=>(pi j).1) pi0.1 hjoint (cluster i tau δ) (isOpen_cluster i tau δ)
        A (10*δ+r k) hA (by positivity)
        (fun _=> A) (fun _=>10*δ+r k) tendsto_const_nhds tendsto_const_nhds
        (hf δ hδ hδmax)
      have hz : mass≤(pi0.1 : Measure (Value i×unitInterval)).real (cluster i tau δ) := by
        apply measureReal_mono ?_ (measure_ne_top _ _)
        intro p hp
        exact ⟨hp.1,by simpa only [hp.2] using hδ⟩
      exact (mul_le_mul_of_nonneg_right hz hA.le).trans (hp.trans (by linarith))
    have hz : mass*A≤0:=ge_of_tendsto (by simpa using hrt.const_mul 11)
      (Eventually.of_forall hbound)
    have hm : mass=0:=le_antisymm (by nlinarith) measureReal_nonneg
    exact (ENNReal.toReal_eq_zero_iff _).mp hm |>.resolve_right (measure_ne_top _ _)
  have hall : ∀ᵐp∂(pi0.1 : Measure (Value i×unitInterval)),∀n : ℕ,
      ¬((1:ℝ)/((n:ℝ)+1)<(p.1:ℝ) ∧ (baseBid i p:ℝ)=0) := by
    apply ae_all_iff.mpr
    intro n
    exact measure_eq_zero_iff_ae_notMem.mp (hcut (1/((n:ℝ)+1)) (by positivity))
  have hbase : ∀ᵐp∂(pi0.1 : Measure (Value i×unitInterval)),(baseBid i p:ℝ)≠0 := by
    filter_upwards [original_value_positive i pi0,hall] with p hp hn
    intro hz
    obtain ⟨n,hnt⟩:=exists_nat_one_div_lt hp
    exact hn n ⟨by simpa only [Nat.cast_add,Nat.cast_one] using hnt,hz⟩
  rw [← PositiveClusters.baseRealLaw_zero,PositiveClusters.baseRealLaw,
    ProbabilityMeasure.toMeasure_map,Measure.map_apply
      (continuous_baseBid i).subtype_val.measurable (measurableSet_singleton 0)]
  exact measure_eq_zero_iff_ae_notMem.mpr hbase

end ZeroAtoms

namespace FiniteAtoms
open OriginalGain PositiveClusters

theorem real_atomless_of_noisy_cluster (i : Row) (N L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (hL : 0< sourceL i (N+2)) (hH : 0< sourceH i (N+2))
    (hsmall : lossCoefficient i (N+2)/gainCoefficient i (N+2)<1/2)
    (eps : ℕ→ unitInterval) (pi : ℕ→ Joint i) (pi0 : Joint i)
    (hepspos : ∀j,0<(eps j:ℝ)) (heps0 : Tendsto eps atTop (𝓝 0))
    (heps : ∀j,(eps j:ℝ)≤ noiseBound i (N+2))
    (hIC : ∀j,NoisyIC i (N+1) (eps j) (pi j))
    (hpi : Tendsto pi atTop (𝓝 pi0))
    (hcap : ∀j,∀ᵐp∂((pi j).1 : Measure (Value i×unitInterval)),
      (baseBid i p:ℝ)≤ Uniform05.cap i-capSlack i) :
    NullSingletonClass (realBidLaw i 0 pi0 : Measure ℝ) := by
  have hpos:=no_positive_atoms_of_noisy_cluster i N L hN hroom hL hH hsmall
    eps pi pi0 hepspos heps0 heps hIC hpi hcap
  have hz:=ZeroAtoms.no_zero_atom_of_noisy_cluster i N L hN hroom hH
    eps pi pi0 hepspos heps0 hIC hpi
  constructor
  intro b
  rcases lt_trichotomy b 0 with hb|rfl|hb
  · rw [← baseRealLaw_zero,baseRealLaw,ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (continuous_baseBid i).subtype_val.measurable (measurableSet_singleton b)]
    have hempty : ((fun p : Value i×unitInterval=>(baseBid i p:ℝ)) ⁻¹' {b})=∅ := by
      ext p
      simp only [mem_preimage,mem_singleton_iff,mem_empty_iff_false,iff_false]
      intro he
      have hn:=(baseBid i p).property.1
      linarith
    rw [hempty,measure_empty]
  · exact hz
  · exact hpos b hb

theorem bid_atomless_of_real (i : Row) (pi0 : Joint i)
    (h : NullSingletonClass (realBidLaw i 0 pi0 : Measure ℝ)) :
    NullSingletonClass (bidLaw i (0,pi0) : Measure (Bid i)) := by
  letI:=h
  constructor
  intro b
  have hz : (realBidLaw i 0 pi0 : Measure ℝ) {(b:ℝ)}=0:=measure_singleton _
  rw [realBidLaw,ProbabilityMeasure.toMeasure_map,
    Measure.map_apply measurable_subtype_coe (measurableSet_singleton (b:ℝ))] at hz
  have he : ((Subtype.val : Bid i→ℝ) ⁻¹' {(b:ℝ)})={b}:=by
    ext x
    simp only [mem_preimage,mem_singleton_iff]
    constructor
    · exact Subtype.ext
    · exact congrArg Subtype.val
  rw [he] at hz
  exact hz

theorem seed_atom_zero (i : Row) (pi0 : Joint i)
    (h : NullSingletonClass (realBidLaw i 0 pi0 : Measure ℝ)) :
    (realBidLaw i 0 pi0 : Measure ℝ) {Uniform05.t i/2}=0 := by
  letI:=h
  exact measure_singleton _

end FiniteAtoms
end FCAppendix.Affine.UniformFinite
