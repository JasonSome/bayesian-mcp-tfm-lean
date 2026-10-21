import FCAppendix.Affine.LowBody.NoisyDeviations
import FCAppendix.Affine.LowBody.NoisyBaseLaw

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set Classical

def crossingChoice (ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/4) (b δ : ℝ)
    {d : ℝ} (w : LowValue d) : unitInterval:=
  choiceAtRatio ε hε hsmall ((b+2*δ)/w.1)

theorem measurable_crossingChoice (ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/4) (b δ d : ℝ) :
    Measurable (crossingChoice ε hε hsmall b δ (d:=d)) :=
  (continuous_choiceAtRatio ε hε hsmall).measurable.comp
    (measurable_const.div measurable_subtype_coe)

theorem crossing_target_bounds {d ε ell b δ w beta : ℝ}
    (hε : 0≤ε) (hell : 0≤ell) (hδ : 0<δ) (hδb : δ<b)
    (hw : w∈Icc (0:ℝ) d) (hbeta : beta∈Ioo (b-δ) (b+δ))
    (hbetaw : beta≤w) (hgap : w*ell/4≤w-beta)
    (hnoise : ε*d<δ) (hroom : 3*δ+ε*d≤(b-δ)*ell/4) :
    0<w ∧ ε*w≤b+2*δ ∧ b+2*δ≤w/(1+ε) := by
  have hwpos : 0<w:=lt_of_lt_of_le (by linarith [hbeta.1]) hbetaw
  have hd : 0≤d:=hw.1.trans hw.2
  have hlow : b-δ≤w:=hbeta.1.le.trans hbetaw
  have hmul:=mul_le_mul_of_nonneg_right hlow hell
  have hmargin : ε*d≤w-(b+2*δ) := by nlinarith [hbeta.1]
  have htarget : b+2*δ≤d := by
    have hnd : 0≤ε*d:=mul_nonneg hε hd
    linarith [hw.2]
  refine ⟨hwpos,?_,?_⟩
  · have hcost:=mul_le_mul_of_nonneg_left hw.2 hε
    linarith
  · apply (le_div_iff₀ (by linarith : 0<1+ε)).mpr
    have hcost:=mul_le_mul_of_nonneg_left htarget hε
    nlinarith

theorem crossing_implemented_geometry {d ε ell b δ w beta z : ℝ}
    (hε : 0≤ε) (hell : 0≤ell) (hδ : 0<δ) (hδb : δ<b)
    (hw : w∈Icc (0:ℝ) d) (hbeta : beta∈Ioo (b-δ) (b+δ))
    (hbetaw : beta≤w) (hgap : w*ell/4≤w-beta)
    (hnoise : ε*d<δ) (hroom : 3*δ+ε*d≤(b-δ)*ell/4)
    (hz : z∈Icc (0:ℝ) 1) :
    let old:=beta*(1+ε*z)
    let raised:=(b+2*δ)*(1+ε*z)
    old∈Icc (b-δ) (b+δ+ε*d) ∧
    raised∈Icc (b+2*δ) (b+3*δ) ∧
    old<raised ∧ raised≤w ∧ raised-old<4*δ ∧
    (b-δ)*ell/4-ε*d≤w-old := by
  dsimp only
  have ht:=crossing_target_bounds hε hell hδ hδb hw hbeta hbetaw hgap hnoise hroom
  have hbeta0 : 0≤beta:=by linarith [hbeta.1]
  have hbetaD : beta≤d:=hbetaw.trans hw.2
  have hx0 : 0≤b+2*δ:=by linarith
  have hxD : b+2*δ≤d:=by
    have hxw : b+2*δ≤w := by
      have hh:=(le_div_iff₀ (by linarith : 0<1+ε)).mp ht.2.2
      nlinarith [mul_nonneg hε hx0]
    exact hxw.trans hw.2
  have hcost (v : ℝ) (hv0 : 0≤v) (hvD : v≤d) : 0≤v*ε*z ∧ v*ε*z≤ε*d := by
    refine ⟨mul_nonneg (mul_nonneg hv0 hε) hz.1,?_⟩
    calc
      _≤v*ε*1:=mul_le_mul_of_nonneg_left hz.2 (mul_nonneg hv0 hε)
      _=ε*v:=by ring
      _≤ε*d:=mul_le_mul_of_nonneg_left hvD hε
  have hcOld:=hcost beta hbeta0 hbetaD
  have hcNew:=hcost (b+2*δ) hx0 hxD
  have hmax : (b+2*δ)*(1+ε*z)≤w := by
    have hh:=(le_div_iff₀ (by linarith : 0<1+ε)).mp ht.2.2
    have hprod:=mul_le_mul_of_nonneg_left hz.2 (mul_nonneg hx0 hε)
    nlinarith
  have hlow : b-δ≤w:=hbeta.1.le.trans hbetaw
  have hmul:=mul_le_mul_of_nonneg_right hlow hell
  refine ⟨⟨by nlinarith [hbeta.1,hcOld.1],by nlinarith [hbeta.2,hcOld.2]⟩,
    ⟨by nlinarith [hcNew.1],by nlinarith [hcNew.2]⟩,?_,hmax,?_,?_⟩ <;>
    nlinarith [hbeta.1,hbeta.2,hcOld.1,hcOld.2,hcNew.1,hcNew.2]

theorem crossingChoice_exact {d ε ell b δ : ℝ} (hε : 0<ε) (hsmall : ε≤1/4)
    (hell : 0≤ell) (hδ : 0<δ) (hδb : δ<b)
    (w : LowValue d) (q : unitInterval)
    (hcluster : w.1*bidRatio ε q∈Ioo (b-δ) (b+δ))
    (hgap : w.1*ell/4≤w.1-w.1*bidRatio ε q)
    (hnoise : ε*d<δ) (hroom : 3*δ+ε*d≤(b-δ)*ell/4) :
    w.1*bidRatio ε (crossingChoice ε hε hsmall b δ w)=b+2*δ := by
  have hbase:=noisyBid_bounds hε (by linarith) w q (0:unitInterval)
  have hbasew : w.1*bidRatio ε q≤w.1:=by simpa using hbase.2
  have ht:=crossing_target_bounds hε.le hell hδ hδb w.property hcluster hbasew hgap hnoise hroom
  exact target_bid_exact hε hsmall ht.1 ht.2.1 ht.2.2

theorem zero_cluster_target_bounds {d ε δ tau w : ℝ}
    (hε : 0≤ε) (hsmall : ε≤1/4) (hδ : 0<δ) (htau : 4*δ≤tau)
    (hw : w∈Icc tau d) (hnoise : ε*d≤δ) :
    0<w ∧ ε*w≤3*δ ∧ 3*δ≤w/(1+ε) := by
  have hw0 : 0<w:=by linarith [hw.1]
  refine ⟨hw0,?_,?_⟩
  · have hm:=mul_le_mul_of_nonneg_left hw.2 hε
    linarith
  · apply (le_div_iff₀ (by linarith : 0<1+ε)).mpr
    have hm:=mul_le_mul_of_nonneg_left hsmall hδ.le
    nlinarith [hw.1]

theorem zero_cluster_implemented_geometry {d ε δ tau w beta z : ℝ}
    (hε : 0≤ε) (hsmall : ε≤1/4) (hδ : 0<δ) (htau : 4*δ≤tau)
    (hw : w∈Icc tau d) (hbeta : beta∈Icc (0:ℝ) δ)
    (hbetaw : beta≤w) (hnoise : ε*d≤δ) (hz : z∈Icc (0:ℝ) 1) :
    let old:=beta*(1+ε*z)
    let raised:=3*δ*(1+ε*z)
    old∈Icc (0:ℝ) (2*δ) ∧ raised∈Icc (3*δ) (4*δ) ∧
    old<raised ∧ raised≤w ∧ raised-old≤4*δ ∧ tau-2*δ≤w-old := by
  dsimp only
  have ht:=zero_cluster_target_bounds hε hsmall hδ htau hw hnoise
  have hwD:=hw.2
  have hbetaD : beta≤d:=hbetaw.trans hwD
  have hxD : 3*δ≤d:=by linarith [hw.1]
  have hcost (v : ℝ) (hv0 : 0≤v) (hvD : v≤d) : 0≤v*ε*z ∧ v*ε*z≤δ := by
    refine ⟨mul_nonneg (mul_nonneg hv0 hε) hz.1,?_⟩
    calc
      _≤v*ε*1:=mul_le_mul_of_nonneg_left hz.2 (mul_nonneg hv0 hε)
      _=ε*v:=by ring
      _≤ε*d:=mul_le_mul_of_nonneg_left hvD hε
      _≤δ:=hnoise
  have hcOld:=hcost beta hbeta.1 hbetaD
  have hcNew:=hcost (3*δ) (by linarith) hxD
  have hmax : 3*δ*(1+ε*z)≤w := by
    have hm:=mul_le_mul_of_nonneg_left hz.2 (mul_nonneg (show 0≤3*δ by linarith) hε)
    have hh:=(le_div_iff₀ (by linarith : 0<1+ε)).mp ht.2.2
    nlinarith
  refine ⟨⟨by nlinarith [hbeta.1,hcOld.1],by nlinarith [hbeta.2,hcOld.2]⟩,
    ⟨by nlinarith [hcNew.1],by nlinarith [hcNew.2]⟩,?_,hmax,?_,?_⟩ <;>
    nlinarith [hw.1,hbeta.1,hbeta.2,hcOld.1,hcOld.2,hcNew.1,hcNew.2]

theorem zero_cluster_choice_exact {d ε δ tau : ℝ} (hε : 0<ε) (hsmall : ε≤1/4)
    (hδ : 0<δ) (htau : 4*δ≤tau) (w : LowValue d) (hw : tau≤w.1) (hnoise : ε*d≤δ) :
    w.1*bidRatio ε (crossingChoice ε hε hsmall δ δ w)=3*δ := by
  have ht:=zero_cluster_target_bounds hε.le hsmall hδ htau ⟨hw,w.property.2⟩ hnoise
  have hh:=target_bid_exact hε hsmall ht.1 ht.2.1 ht.2.2
  simpa only [crossingChoice,show δ+2*δ=3*δ by ring] using hh

end FCAppendix.Affine.LowBody
