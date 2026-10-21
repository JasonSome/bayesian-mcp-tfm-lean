import FCAppendix.Affine.UniformFinite.PositiveClusters

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional
namespace PositiveClusters
open OriginalGain

theorem atom_contraction_of_additive_clusters
    (H G : ℕ→ ProbabilityMeasure ℝ) (G0 : ProbabilityMeasure ℝ)
    (hH : Tendsto H atTop (𝓝 G0)) (hG : Tendsto G atTop (𝓝 G0))
    {κ A D C : ℝ} (hκ : 0≤κ) (hA : 0< A) (hD : 0≤ D) (hC : 0≤ C)
    (hfinite : ∀b : ℝ,0< b→∀err : ℝ,0< err→∃δmax>0,
      ∀δ : ℝ,0<δ→δ< b/4→δ<δmax→∀ᶠj in atTop,
        (H j : Measure ℝ).real (Ioo (b-δ) (b+δ))^2*((b-2*δ)*A)≤
          (H j : Measure ℝ).real (Ioo (b-δ) (b+δ))*
            ((b+4*δ)*D*((G j : Measure ℝ).real (Icc (b-2*δ) (b+4*δ))+
              (G j : Measure ℝ).real (Icc (κ*(b-2*δ)) (κ*(b+4*δ))))+C*δ+err)) :
    ∀b : ℝ,0< b→(G0 : Measure ℝ).real {b}≤
      (D/A)*((G0 : Measure ℝ).real {b}+(G0 : Measure ℝ).real {κ*b}) := by
  intro b hb
  let r : ℕ→ℝ:=fun k=>1/((k:ℝ)+1)
  have hr (k : ℕ) : 0< r k:=by dsimp [r]; positivity
  have ha : Antitone r:=by
    intro j k hjk
    dsimp [r]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have ht : Tendsto r atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  apply LowBody.atom_bound_of_shrinking_envelopes (G0 : Measure ℝ) hb hA r
    (fun k=>(hr k).le) ha ht hκ
  apply Eventually.of_forall
  intro k
  obtain ⟨δmax,hδmax,hf⟩:=hfinite b hb (r k) (hr k)
  let δ:=min (r k/2) (min (b/8) (δmax/2))
  have hδ : 0<δ:=lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδr : 2*δ≤ r k:=by have h:=min_le_left (r k/2) (min (b/8) (δmax/2)); linarith
  have hδb : δ< b/4:=by
    have h:δ≤ b/8:=(min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hδmax' : δ<δmax:=by
    have h:δ≤δmax/2:=(min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hAδ : 0<(b-2*δ)*A:=mul_pos (by linarith) hA
  have hDδ : 0≤(b+4*δ)*D:=mul_nonneg (by linarith) hD
  have herr : 0≤ C*δ+r k:=by positivity
  have hm:=LowBody.atom_bound_of_varying_finite_cluster_estimates H G G0 hH hG
    (Ioo (b-δ) (b+δ)) (Icc (b-2*δ) (b+4*δ))
    (Icc (κ*(b-2*δ)) (κ*(b+4*δ)))
    isOpen_Ioo isClosed_Icc isClosed_Icc b ((b-2*δ)*A) ((b+4*δ)*D) (C*δ+r k)
    ⟨by linarith,by linarith⟩ hAδ hDδ herr
    (fun _=>(b-2*δ)*A) (fun _=>(b+4*δ)*D) (fun _=> C*δ+r k)
    tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds
    (by simpa only [add_assoc] using hf δ hδ hδb hδmax')
  have hB : (G0 : Measure ℝ).real (Icc (b-2*δ) (b+4*δ))≤
      (G0 : Measure ℝ).real (Icc (b-3*r k) (b+3*r k)) := by
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    constructor <;> linarith [hx.1,hx.2,hr k]
  have hK : (G0 : Measure ℝ).real (Icc (κ*(b-2*δ)) (κ*(b+4*δ)))≤
      (G0 : Measure ℝ).real (Icc (κ*b-3*κ*r k) (κ*b+3*κ*r k)) := by
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    have hm:=mul_le_mul_of_nonneg_left hδr hκ
    have hp:=mul_nonneg hκ (hr k).le
    constructor <;> nlinarith [hx.1,hx.2]
  have hl : (G0 : Measure ℝ).real {b}*((b-r k)*A)≤
      (G0 : Measure ℝ).real {b}*((b-2*δ)*A) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by linarith) hA.le) measureReal_nonneg
  have hcoef : (b+4*δ)*D≤(b+3*r k)*D:=
    mul_le_mul_of_nonneg_right (by linarith [hr k]) hD
  have hright:=mul_le_mul hcoef (add_le_add hB hK)
    (add_nonneg measureReal_nonneg measureReal_nonneg) (by positivity : 0≤(b+3*r k)*D)
  have herr' : C*δ+r k≤(C+1)*r k:=by
    have hh:=mul_le_mul_of_nonneg_left (show δ≤ r k by linarith [hr k]) hC
    nlinarith
  exact hl.trans (hm.trans (add_le_add hright herr'))

theorem no_positive_atoms_of_noisy_cluster (i : Row) (N L : ℕ)
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
    ∀b : ℝ,0< b→(realBidLaw i 0 pi0 : Measure ℝ) {b}=0 := by
  have hbase : Tendsto (fun j=> baseRealLaw i (pi j)) atTop (𝓝 (realBidLaw i 0 pi0)) := by
    rw [← baseRealLaw_zero]
    exact ((continuous_baseRealLaw i).tendsto pi0).comp hpi
  have hphys : Tendsto (fun j=> realBidLaw i (eps j) (pi j)) atTop (𝓝 (realBidLaw i 0 pi0)) := by
    convert! ((continuous_realBidLaw i).tendsto (0,pi0)).comp (heps0.prodMk_nhds hpi) using 1
  have hA:=gainCoefficient_pos i (N+2) hL hH
  have hD:=lossCoefficient_nonneg i (N+2)
  have hC : 0≤6*(1+Uniform05.eta i):=by linarith [(Uniform05.eta_range i).1]
  have hrec:=atom_contraction_of_additive_clusters
    (fun j=> baseRealLaw i (pi j)) (fun j=> realBidLaw i (eps j) (pi j))
    (realBidLaw i 0 pi0) hbase hphys (Uniform05.kappa_range i).1.le hA hD hC
    (finite_cluster_estimates i N L hN hroom hL eps pi hepspos heps0 heps hIC hcap)
  exact LowBody.no_positive_atoms_of_cluster_bound (realBidLaw i 0 pi0 : Measure ℝ)
    (Uniform05.kappa_range i).1 (div_nonneg hD hA.le) hsmall hrec

end PositiveClusters
end FCAppendix.Affine.UniformFinite
