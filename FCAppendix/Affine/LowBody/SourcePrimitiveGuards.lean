import FCAppendix.Affine.LowBody.ArrivalUnderflow
import FCAppendix.Affine.LowBody.FirstCopyBoundary

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology Classical

theorem eventually_primitive_source_guards (s a h : ℝ) (hs : 0<s) (ha : 0≤a) (hh : 0<h)
    (hsum : s+a+h=1) (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (c : ℕ→ℕ) (ρ η : ℝ) (hρ : 0<ρ) (hrank : ρ<a+h/2) (hη : 0≤η)
    (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ))
    (hgap : 2*Ample.binaryKL ρ (1-h/2)<jointRate s a h ρ) :
    let Cref:=categoryLaw s a h hs.le ha hh.le hsum Gref
    ∀ᶠm : ℕ in atTop,
      let L:=(CommonList.iid Cref (m-1)).prob (LocalUnderflow (c m) 0)
      let H:=boundary c (1-h/2) m
      let D:=(CommonList.iid Cref (m-1)).prob (BothUnderflow (c m))
      let E:=(CommonList.iid Cref (m-2)).prob (BothUnderflow (c m))
      2 < m ∧ 0 < c m ∧ 0<L ∧ E<H ∧ D≤L/4 ∧
        8*η*((m-1:ℕ):ℝ)*E/(L*(H-E))<1/2 ∧
        ∀(G : Measure ℝ)(_hG : IsProbabilityMeasure G)(u : ℝ),
          H≤PiBinomial.pmf (m-2) (higherBidProbability s a h G u) (c m-1) ∧
          H-E≤(Measure.pi (fun _ : Fin (m-2)=>rivalLaw s a h G)).real
            (firstCopyBoundary (c m) u) := by
  have hh1 : h≤1:=by linarith [hs.le]
  have hp0 : 0<1-h/2:=by linarith
  have hp1 : 1-h/2<1:=by linarith
  have hq : a+h/2≤1-h/2:=by linarith [hs.le]
  have hρp : ρ<1-h/2:=hrank.trans_le hq
  have hrates:=eventually_source_guards s a h hs.le ha hh.le hsum Gref c ρ η hη
    hp0 hp1 hρ hρp hc hgap
  have hboundary:=eventually_boundary_uniform c ρ (a+h/2) (1-h/2) hρ hrank hq hp1 hc
  have hcap : ∀ᶠm : ℕ in atTop,0 < c m:=by
    filter_upwards [hc.eventually_const_lt hρ,eventually_gt_atTop (0:ℕ)] with m hm hm0
    have hmR : (0:ℝ) < m:=Nat.cast_pos.mpr hm0
    exact Nat.cast_pos.mp ((div_pos_iff_of_pos_right hmR).mp hm)
  filter_upwards [hrates,hboundary,hcap,eventually_gt_atTop (2:ℕ)] with m hmR hmB hcm hm2
  have hL : (CommonList.iid (categoryLaw s a h hs.le ha hh.le hsum Gref) (m-1)).prob
      (LocalUnderflow (c m) 0)=ell c (1-h/2) hp0.le hp1.le m:=by
    exact localUnderflow_probability s a h hs.le ha hh.le hsum Gref (m-1) (c m) hcm
  rw [←hL] at hmR
  refine ⟨hm2,hcm,hmR.1,hmR.2.1,hmR.2.2.1,hmR.2.2.2,?_⟩
  intro G hG u
  letI:=hG
  have hp:=hmB (higherBidProbability s a h G u)
    (higherBidProbability_bounds s a h hs.le hsum G u)
  refine ⟨hp,?_⟩
  have hactual:=firstCopyBoundary_probability_lower s a h hs.le ha hh.le hsum G (m-2) (c m) u
  have hcat : categoryLaw s a h hs.le ha hh.le hsum G=
      categoryLaw s a h hs.le ha hh.le hsum Gref:=by
    apply FiniteLaw.ext
    intro k
    rw [categoryLaw_mass,categoryLaw_mass]
  rw [hcat] at hactual
  exact (sub_le_sub_right hp _).trans hactual

end FCAppendix.Affine.LowBody
