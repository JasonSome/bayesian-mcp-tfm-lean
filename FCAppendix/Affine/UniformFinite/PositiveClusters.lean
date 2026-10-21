import FCAppendix.Affine.UniformFinite.OriginalQuadratic
import FCAppendix.Affine.UniformFinite.CapLocalization
import FCAppendix.Affine.LowBody.PositiveClusterLimit

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional
open scoped BigOperators
namespace PositiveClusters
open OriginalGain ActualAtoms

def sourceL (i : Row) (M : ℕ) : ℝ :=
  AtomEvents.lowerEvent (Uniform05.t i) (Uniform05.t_pos i).le (Uniform05.t_lt_one i).le M

def sourceH (i : Row) (M : ℕ) : ℝ := AtomEvents.boundaryEvent (Uniform05.t i) M

def sourceE (i : Row) (M : ℕ) : ℝ :=
  AtomEvents.duplicateEvent (Uniform05.zc i) (Uniform05.zc_probability_bounds i).1
    (Uniform05.zc_probability_bounds i).2 M

def gainCoefficient (i : Row) (M : ℕ) : ℝ :=
  Uniform05.t i*(1-Uniform05.chi)*sourceL i M*sourceH i M/4

def lossCoefficient (i : Row) (M : ℕ) : ℝ :=
  Uniform05.eta i*((M-1:ℕ):ℝ)*Uniform05.t i*sourceE i M

def noiseBound (i : Row) (M : ℕ) : ℝ :=
  min (1/100) ((1-Uniform05.chi)*sourceL i M/4)

lemma noiseBound_pos (i : Row) (M : ℕ) (hL : 0< sourceL i M) : 0< noiseBound i M := by
  apply lt_min (by norm_num)
  dsimp [Uniform05.chi]
  positivity

lemma noiseBound_cost (i : Row) {M : ℕ} (eps : unitInterval)
    (heps : (eps:ℝ)≤ noiseBound i M) :
    (1+Uniform05.eta i)*(Uniform05.chi+(eps:ℝ))≤1 := by
  have h : (eps:ℝ)≤1/100:=heps.trans (min_le_left _ _)
  cases i <;> norm_num [Uniform05.eta,Uniform05.chi] at * <;> nlinarith

lemma gainCoefficient_pos (i : Row) (M : ℕ)
    (hL : 0< sourceL i M) (hH : 0< sourceH i M) : 0< gainCoefficient i M := by
  unfold gainCoefficient
  have ht:=Uniform05.t_pos i
  have hc : 0<1-Uniform05.chi:=by norm_num [Uniform05.chi]
  positivity

lemma lossCoefficient_nonneg (i : Row) (M : ℕ) : 0≤ lossCoefficient i M := by
  unfold lossCoefficient sourceE
  exact mul_nonneg (mul_nonneg (mul_nonneg (Uniform05.eta_range i).1.le
    (Nat.cast_nonneg _)) (Uniform05.t_pos i).le) (FiniteLaw.prob_nonneg _ _)

lemma coefficient_ratio (i : Row) (M : ℕ)
    (_hL : 0< sourceL i M) (_hH : 0< sourceH i M) :
    lossCoefficient i M/gainCoefficient i M =
      AtomEvents.sourceCoefficient (Uniform05.eta i) Uniform05.chi
        (Uniform05.t i) (Uniform05.zc i) (Uniform05.t_pos i).le (Uniform05.t_lt_one i).le
        (Uniform05.zc_probability_bounds i).1 (Uniform05.zc_probability_bounds i).2 M := by
  unfold lossCoefficient gainCoefficient AtomEvents.sourceCoefficient sourceL sourceH sourceE
  field_simp [(Uniform05.t_pos i).ne',
    show 1-Uniform05.chi≠0 by norm_num [Uniform05.chi]]

def baseRealLaw (i : Row) (pi : Joint i) : ProbabilityMeasure ℝ :=
  pi.1.map ((continuous_baseBid i).subtype_val.measurable.aemeasurable)

lemma continuous_baseRealLaw (i : Row) : Continuous (baseRealLaw i) :=
  (ProbabilityMeasure.continuous_map (continuous_baseBid i).subtype_val).comp continuous_subtype_val

lemma baseRealLaw_zero (i : Row) (pi : Joint i) :
    baseRealLaw i pi=realBidLaw i 0 pi := by
  apply ProbabilityMeasure.toMeasure_injective
  change (pi.1 : Measure (Value i×unitInterval)).map (fun p=>(baseBid i p:ℝ))=
    (realBidLaw i 0 pi : Measure ℝ)
  rw [realBidLaw_original]
  simp only [drawBid,noisyBid_zero]
  rw [show (fun p : LowerDraw i=>(baseBid i p.1:ℝ))=
      (fun p : Value i×unitInterval=>(baseBid i p:ℝ))∘Prod.fst from rfl,
    ← Measure.map_map (continuous_baseBid i).subtype_val.measurable measurable_fst,
    lowerDraw_original_pair_law]

lemma continuous_realBidLaw (i : Row) : Continuous (fun p : unitInterval×Joint i=> realBidLaw i p.1 p.2) :=
  (ProbabilityMeasure.continuous_map continuous_subtype_val).comp
    ((ProbabilityMeasure.continuous_map continuous_snd).comp
      ((continuous_subtype_val).comp (continuous_physicalLaw i)))

def cluster (i : Row) (b δ : ℝ) : Set (Value i×unitInterval) :=
  {p | (baseBid i p:ℝ)∈Ioo (b-δ) (b+δ)}

lemma measurableSet_cluster (i : Row) (b δ : ℝ) : MeasurableSet (cluster i b δ) :=
  (continuous_baseBid i).subtype_val.measurable measurableSet_Ioo

lemma cluster_mass (i : Row) (pi : Joint i) (b δ : ℝ) :
    (carrier i pi (cluster i b δ)).real univ=
      (baseRealLaw i pi : Measure ℝ).real (Ioo (b-δ) (b+δ)) := by
  rw [carrier_mass,baseRealLaw,ProbabilityMeasure.toMeasure_map]
  simp only [Measure.real,Measure.map_apply (continuous_baseBid i).subtype_val.measurable measurableSet_Ioo]
  rfl

def deviation (i : Row) (b δ : ℝ) (p : Value i×unitInterval) : unitInterval :=
  choiceForBid i p.1 (b+3*δ)

lemma measurable_deviation (i : Row) (b δ : ℝ) : Measurable (deviation i b δ) :=
  (measurable_choiceForBid i).comp (measurable_fst.prodMk measurable_const)

lemma noise_eq_base_at_choice (i : Row) (eps : unitInterval) (p : Value i×unitInterval) :
    (drawBid i eps (p,p.2):ℝ)=(baseBid i p:ℝ) := by
  change noisyRealBid i eps p.1 p.2 p.2=(baseBid i p:ℝ)
  rw [baseBid_val]
  unfold noisyRealBid
  ring

theorem physical_cluster_geometry (i : Row) (N : ℕ)
    (hM : 2*Uniform07.capacity (N+2)< N+2) (hc : 0< Uniform07.capacity (N+2))
    (hL : 0< sourceL i (N+2)) (eps : unitInterval)
    (heps : (eps:ℝ)≤ noiseBound i (N+2)) (pi : Joint i)
    (hIC : NoisyIC i (N+1) eps pi)
    (hcap : ∀ᵐp∂(pi.1 : Measure (Value i×unitInterval)),
      (baseBid i p:ℝ)≤ Uniform05.cap i-capSlack i)
    (b δ : ℝ) (_hb : 0< b) (hδ : 0<δ) (hδb : δ< b/4)
    (hδS : 4*δ≤(1-Uniform05.chi)*(b/2)*sourceL i (N+2)/2)
    (hδU : 4*δ≤ capSlack i) (henoise : (eps:ℝ)*Uniform05.t i<δ/2) :
    ∀ᵐp∂carrier i pi (cluster i b δ),
      b-2*δ≤(drawBid i eps p:ℝ) ∧ (drawBid i eps p:ℝ)≤ b+2*δ ∧
      b+2*δ<(drawBid i eps ((p.1.1,deviation i b δ p.1),p.2):ℝ) ∧
      (1-Uniform05.chi)*(b-2*δ)*sourceL i (N+2)/2≤
        (p.1.1:ℝ)-(drawBid i eps p:ℝ) ∧
      (drawBid i eps ((p.1.1,deviation i b δ p.1),p.2):ℝ)-(b-2*δ)≤6*δ ∧
      Icc (drawBid i eps p:ℝ) (drawBid i eps ((p.1.1,deviation i b δ p.1),p.2):ℝ)⊆
        Icc (b-2*δ) (b+4*δ) ∪
          Icc (Uniform05.kappa i*(b-2*δ)) (Uniform05.kappa i*(b+4*δ)) ∧
      Icc (Uniform05.kappa i*(drawBid i eps p:ℝ))
          (Uniform05.kappa i*(drawBid i eps ((p.1.1,deviation i b δ p.1),p.2):ℝ))⊆
        Icc (b-2*δ) (b+4*δ) ∪
          Icc (Uniform05.kappa i*(b-2*δ)) (Uniform05.kappa i*(b+4*δ)) := by
  have hsur:=ActualSurplus.noisyIC_common_conull_surplus i (N+1) hM hc eps
    (heps.trans (min_le_right _ _)) (noiseBound_cost i eps heps) pi hIC
  have hpre : ∀ᵐp∂(pi.1 : Measure (Value i×unitInterval)).restrict (cluster i b δ),
      p∈cluster i b δ ∧ (baseBid i p:ℝ)≤ Uniform05.cap i-capSlack i ∧
      ∀z : unitInterval,(1-Uniform05.chi)*(drawBid i eps (p,z):ℝ)*sourceL i (N+2)/2≤
        (p.1:ℝ)-(drawBid i eps (p,z):ℝ) := by
    filter_upwards [ae_restrict_mem (measurableSet_cluster i b δ),
      ae_restrict_of_ae hcap,ae_restrict_of_ae hsur] with p hp hU hS
    exact ⟨hp,hU,hS⟩
  have hpull:= (Measure.quasiMeasurePreserving_fst
    (μ:=(pi.1 : Measure (Value i×unitInterval)).restrict (cluster i b δ))
    (ν:=(volume : Measure unitInterval))).ae hpre
  filter_upwards [hpull] with p hp
  obtain ⟨hcB,hcapB,hS⟩:=hp
  have hbase:=baseBid_feasible i p.1
  have hB0 : b-δ<(baseBid i p.1:ℝ):=hcB.1
  have hB1 : (baseBid i p.1:ℝ)< b+δ:=hcB.2
  have hv : 0<(p.1.1:ℝ):=by
    have hh:=hbase.2.trans (min_le_left _ _)
    linarith
  have hsB:=hS p.1.2
  rw [noise_eq_base_at_choice] at hsB
  have hsf : 4*δ≤(p.1.1:ℝ)-(baseBid i p.1:ℝ) := by
    have hm:=mul_le_mul_of_nonneg_right (show b/2≤(baseBid i p.1:ℝ) by linarith)
      (mul_nonneg (show 0≤1-Uniform05.chi by norm_num [Uniform05.chi]) hL.le)
    nlinarith
  have htarget : b+3*δ∈Icc (Uniform05.floorBid i p.1.1) (hiBid i p.1.1) := by
    refine ⟨?_,le_min ?_ ?_⟩ <;> linarith [hbase.1]
  have hnewbase:=choiceForBid_exact i p.1.1 hv (b+3*δ) htarget
  have herrx:=physical_base_error i eps p.1 p.2
  have herry:=feasible_target_noise_error i eps p.1.1 hv (b+3*δ) htarget p.2
  have hepsv : (eps:ℝ)*(p.1.1:ℝ)<δ/2 :=
    (mul_le_mul_of_nonneg_left p.1.1.property.2 eps.property.1).trans_lt henoise
  have hxe:=abs_le.mp herrx
  have hye:=abs_le.mp herry
  have hxl : b-2*δ≤(drawBid i eps p:ℝ):=by change _≤(noisyBid i (eps,p):ℝ); linarith
  have hxu : (drawBid i eps p:ℝ)≤ b+2*δ:=by change (noisyBid i (eps,p):ℝ)≤ _; linarith
  have hyl : b+2*δ<(drawBid i eps ((p.1.1,deviation i b δ p.1),p.2):ℝ):=by
    dsimp only [drawBid,deviation]
    linarith
  have hyu : (drawBid i eps ((p.1.1,deviation i b δ p.1),p.2):ℝ)≤ b+4*δ:=by
    dsimp only [drawBid,deviation]
    linarith
  refine ⟨hxl,hxu,hyl,?_,by linarith,?_,?_⟩
  · have hs:=hS p.2
    have hm:=mul_le_mul_of_nonneg_right hxl
      (mul_nonneg (show 0≤1-Uniform05.chi by norm_num [Uniform05.chi]) hL.le)
    nlinarith
  · intro y hy
    exact Or.inl ⟨hxl.trans hy.1,hy.2.trans hyu⟩
  · intro y hy
    exact Or.inr ⟨(mul_le_mul_of_nonneg_left hxl (Uniform05.kappa_range i).1.le).trans hy.1,
      hy.2.trans (mul_le_mul_of_nonneg_left hyu (Uniform05.kappa_range i).1.le)⟩

theorem finite_cluster_estimates (i : Row) (N L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (hL : 0< sourceL i (N+2))
    (eps : ℕ→ unitInterval) (pi : ℕ→ Joint i)
    (hepspos : ∀j,0<(eps j:ℝ)) (heps0 : Tendsto eps atTop (𝓝 0))
    (heps : ∀j,(eps j:ℝ)≤ noiseBound i (N+2))
    (hIC : ∀j,NoisyIC i (N+1) (eps j) (pi j))
    (hcap : ∀j,∀ᵐp∂((pi j).1 : Measure (Value i×unitInterval)),
      (baseBid i p:ℝ)≤ Uniform05.cap i-capSlack i) :
    ∀b : ℝ,0< b→∀err : ℝ,0< err→∃δmax>0,
      ∀δ : ℝ,0<δ→δ< b/4→δ<δmax→∀ᶠj in atTop,
        (baseRealLaw i (pi j) : Measure ℝ).real (Ioo (b-δ) (b+δ))^2*
            ((b-2*δ)*gainCoefficient i (N+2)) ≤
          (baseRealLaw i (pi j) : Measure ℝ).real (Ioo (b-δ) (b+δ))*
            ((b+4*δ)*lossCoefficient i (N+2)*
              ((realBidLaw i (eps j) (pi j) : Measure ℝ).real (Icc (b-2*δ) (b+4*δ))+
                (realBidLaw i (eps j) (pi j) : Measure ℝ).real
                  (Icc (Uniform05.kappa i*(b-2*δ)) (Uniform05.kappa i*(b+4*δ))))+
              (6*(1+Uniform05.eta i))*δ+err) := by
  intro b hb err herr
  obtain ⟨r,hr,hq⟩:=exists_actual_cluster_quadratic i N L hN hroom (b/2) err (by linarith) herr
  let dmax:=min (r/7) (min ((1-Uniform05.chi)*b*sourceL i (N+2)/32) (capSlack i/4))
  have hdmax : 0< dmax:=by
    have hc : 0<1-Uniform05.chi:=by norm_num [Uniform05.chi]
    exact lt_min (by positivity) (lt_min (by positivity) (by have hs:=capSlack_pos i; positivity))
  refine ⟨dmax,hdmax,?_⟩
  intro δ hδ hδb hδmax
  have hsmallr : 6*δ< r:=by have h:=hδmax.trans_le (min_le_left _ _); linarith
  have hsmallS : 4*δ≤(1-Uniform05.chi)*(b/2)*sourceL i (N+2)/2 := by
    have h:=hδmax.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    nlinarith
  have hsmallU : 4*δ≤ capSlack i := by
    have h:=hδmax.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have henoise : ∀ᶠj in atTop,(eps j:ℝ)*Uniform05.t i<δ/2 :=
    (((continuous_subtype_val.tendsto 0).comp heps0).mul_const (Uniform05.t i)).eventually_lt_const
      (by simpa using half_pos hδ)
  filter_upwards [henoise] with j hj
  have hgeo:=physical_cluster_geometry i N (by omega) (by omega) hL (eps j) (heps j)
    (pi j) (hIC j) (hcap j) b δ hb hδ hδb hsmallS hsmallU hj
  let B:=Icc (b-2*δ) (b+4*δ)
  let C:=Icc (Uniform05.kappa i*(b-2*δ)) (Uniform05.kappa i*(b+4*δ))
  have hq':=hq (eps j) (hepspos j) (pi j) (hIC j) (cluster i b δ)
    (measurableSet_cluster i b δ) (deviation i b δ) (measurable_deviation i b δ)
    (b-2*δ) (b+2*δ) ((1-Uniform05.chi)*(b-2*δ)*sourceL i (N+2)/2) (6*δ)
    (by linarith) (by
      have hc : 0≤1-Uniform05.chi:=by norm_num [Uniform05.chi]
      have hbδ : 0≤b-2*δ:=by linarith
      exact div_nonneg (mul_nonneg (mul_nonneg hc hbδ) hL.le) (by norm_num))
    (by positivity) hsmallr (B∪C) (measurableSet_Icc.union measurableSet_Icc) hgeo
  rw [cluster_mass] at hq'
  have hH : (PiBinomial.pmf N (Uniform05.t i) L *
      PiBinomial.pmf (2*Uniform07.capacity (N+2)) (1/2)
        (Uniform07.capacity (N+2)-L-1))=sourceH i (N+2) := by
    have he : AtomEvents.otherLower (N+2)=L:=by dsimp [AtomEvents.otherLower]; omega
    simp only [sourceH,AtomEvents.boundaryEvent,Nat.add_sub_cancel,he]
  rw [hH] at hq'
  have hmass:=measureReal_union_le (μ:=(realBidLaw i (eps j) (pi j) : Measure ℝ)) B C
  have hnon:=lossCoefficient_nonneg i (N+2)
  have hdu : (b+2*δ)*lossCoefficient i (N+2)≤(b+4*δ)*lossCoefficient i (N+2):=
    mul_le_mul_of_nonneg_right (by linarith) hnon
  have hmnon : 0≤(realBidLaw i (eps j) (pi j) : Measure ℝ).real (B∪C):=measureReal_nonneg
  have hBnon : 0≤(b+4*δ)*lossCoefficient i (N+2):=by positivity
  have hh:=mul_le_mul hdu hmass hmnon hBnon
  have hpnon : 0≤(baseRealLaw i (pi j) : Measure ℝ).real (Ioo (b-δ) (b+δ)):=measureReal_nonneg
  have hm:=mul_le_mul_of_nonneg_left hh hpnon
  unfold gainCoefficient lossCoefficient at *
  simp only [show N+2-1=N+1 by omega] at *
  dsimp only [B,C,sourceE] at *
  nlinarith only [hq',hm]

end PositiveClusters
end FCAppendix.Affine.UniformFinite
