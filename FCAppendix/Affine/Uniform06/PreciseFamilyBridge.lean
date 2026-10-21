import FCAppendix.Affine.Uniform06.PreciseFamilyFields
import FCAppendix.Affine.Uniform06.PreciseSourceSequence
import FCAppendix.Affine.Uniform06.SourceEarlyLate
import FCAppendix.Affine.Uniform06.FullBidGeometry
import FCAppendix.Affine.Uniform06.RawCenteredArray
import FCAppendix.Affine.Uniform06.ActualArrayTail
import FCAppendix.Affine.Uniform06.CompactUniformSequence

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourcePreciseFamily

open PreciseSourceSequence.Data
open MeasureTheory Set Filter Topology LowBody
open Uniform07 LiteralExperiment SourceEarlyFamily SourcePrefixConstructor
open PreciseSourceSequence MixedIntervalLLT RawTiltedSource RawMixedSource

def marginOfData {i : Row} (S : Data i) (n : ℕ) :
    (Fin (S.m n-1) → Fin 4) → ℝ :=
  fun kinds => S.cm n (fun j => kinds (Fin.cast (S.rivals n) j))

section Family
variable {C : ℕ → Type*}
    (G : ∀ m,C m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,C m → GuardData)
    (cm : ∀ m,C m → (Fin (m-1) → Fin 4) → ℝ)

theorem eventually_test_of_derived_data (i : Row)
    (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (E : C m) a,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {a}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2
        ∂(G m E:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    (hK : KernelFields G g cm i) {d : ℝ} (hd : 0< d) (hdmax : d≤ x i-1/2)
    (Test : (m : ℕ) → ProbabilityMeasure (ℝ × ℝ) → GuardData →
      ((Fin (m-1) → Fin 4) → ℝ) → ℝ → Prop)
    (hdata : ∀ S : Data i,S.ReceiptBand →
      (∀ n a,((S.G n:Measure (ℝ × ℝ)).map Prod.snd) {a}=0) →
      (∀ n,PointGeometry i (S.g n) (S.b n)) →
      ∀ᶠ n in atTop,Test (S.m n) (S.G n) (S.g n) (marginOfData S n) (S.b n)) :
    ∀ᶠ m in atTop,∀ E : C m,∀ b∈Icc (cutoff i/2) ((x i-d)*cutoff i),
      Test m (G m E) (g m E) (cm m E) b := by
  classical
  let hi := (x i-d)*cutoff i
  have hhi : hi< entry i := by
    dsimp [hi]
    unfold entry
    nlinarith [mul_pos hd (cutoff_pos i)]
  obtain ⟨θ,t0,Θ,ht0,hΘ,hθ⟩ := exists_uniform_matching_parameters G g cm i h05 hd hdmax
  have hgeom := eventually_point_geometry G g cm i h05 hfields hpsi hK hhi
  have hused := source_common_used G g cm i h05 hatom
  have hbox : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p∈EarlyJointCompactness.box (cutoff i) (ReceiptGap.cap i) := by
    intro m E
    exact (hused m E).mono fun p hp =>
      ⟨hp.1,hp.2.1.le,hp.2.2.1.2.trans (min_le_right _ _)⟩
  have hbelow : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.2≤ p.1 :=
    fun m E => (h05.permitted m E).mono fun _ hp => hp.2.trans (min_le_left _ _)
  apply CompactUniformSequence.eventually_all_of_good_subsequence
    (Icc (cutoff i/2) hi) (fun m E b => Test m (G m E) (g m E) (cm m E) b)
  intro m hm E b hb
  obtain ⟨b0,hb0,φ,hφ,hblim⟩ := isCompact_Icc.isSeqCompact hb
  let mm := fun n => m (φ n)
  let EE := fun n => E (φ n)
  let GG := fun n => G (mm n) (EE n)
  let bb := fun n => b (φ n)
  have hbb : Tendsto bb atTop (𝓝 b0) := by simpa only [bb,Function.comp_def] using hblim
  let tt := fun n => θ (mm n) (EE n) (bb n)
  let gg := fun n => g (mm n) (EE n)
  have hm' : Tendsto mm atTop atTop := hm.comp hφ.tendsto_atTop
  have hG' : Tendsto GG atTop (𝓝 (FullJointLaw.law i)) :=
    SourceEarlyLate.every_triangular_source_selection G g cm i h05 hatom hfields hpsi mm hm' EE
  have hbp (n : ℕ) : 0< bb n := (half_pos (cutoff_pos i)).trans_le (hb (φ n)).1
  have hband (n : ℕ) : bb n∈Icc (cutoff i/2) hi := hb (φ n)
  have hθ' : ∀ᶠ n in atTop,
      tt n∈Icc t0 Θ ∧
      SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (bb n)
        (GG n:Measure (ℝ × ℝ)))) Prod.fst (tt n)=
          (capacity (mm n):ℝ)/((mm n-1:ℕ):ℝ) := by
    filter_upwards [hm'.eventually hθ] with n hn
    exact hn (EE n) (bb n) (hband n)
  have hgeom' : ∀ᶠ n in atTop,PointGeometry i (gg n) (bb n) := by
    filter_upwards [hm'.eventually hgeom] with n hn
    exact hn (EE n) (bb n) (hband n)
  have hL : Tendsto (fun n => (gg n).multiplier) atTop (𝓝 (entry i)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hm'.eventually (h05.root_limit ε hε)] with n hn
    simpa only [Real.dist_eq] using hn (EE n)
  have hz : b0/cutoff i∈Ico (1/2:ℝ) (x i) := by
    constructor
    · exact (le_div_iff₀ (cutoff_pos i)).mpr (by nlinarith [hb0.1])
    · exact (div_lt_iff₀ (cutoff_pos i)).mpr (hb0.2.trans_lt hhi)
  have hblim' : Tendsto bb atTop (𝓝 ((b0/cutoff i)*cutoff i)) := by
    simpa only [div_mul_cancel₀ b0 (cutoff_pos i).ne'] using hbb
  obtain ⟨θ0,hθ0,hθlim,n0,A,hAN,hAlaw,hAX,hAY,hgap⟩ :=
    RawCenteredArray.exists_raw_array_from_early_joint_limit i GG (FullJointLaw.law i) hG'
      (FullBidGeometry.full_value_marginal i)
      (FullBidGeometry.full_below_value i) (FullBidGeometry.full_active_graph i)
      bb tt hbp hz hblim' mm hm' (hθ'.mono fun _ hn => hn.2)
  have hradius (n : ℕ) : (gg n).radius=cutoff i/10000 :=
    (hfields (mm n) (EE n)).radius_eq

  let split := entry i-cutoff i/1000
  have hreceipt : ReceiptGap.threshold i+cutoff i/1000< split := by
    have hh := ReceiptGap.receipt_entry_margin i
    dsimp [split]
    have ht := cutoff_pos i
    linarith
  have hbranch :
      (∀ᶠ n in atTop,bb n≤(gg n).multiplier-(gg n).radius) ∨
      (∃ e>0,∀ᶠ n in atTop,ReceiptGap.threshold i+e≤ bb n) := by
    by_cases hl : b0≤ split
    · left
      have hlim : Tendsto (fun n => (gg n).multiplier-(gg n).radius-bb n)
          atTop (𝓝 (entry i-cutoff i/10000-b0)) := by
        simpa only [hradius] using (hL.sub_const (cutoff i/10000)).sub hbb
      have hp : 0< entry i-cutoff i/10000-b0 := by
        dsimp [split] at hl
        have ht := cutoff_pos i
        linarith
      exact (hlim.eventually (Ioi_mem_nhds hp)).mono fun n hn => by linarith
    · right
      have hp : ReceiptGap.threshold i+cutoff i/1000< b0 :=
        hreceipt.trans (lt_of_not_ge hl)
      exact ⟨cutoff i/1000,div_pos (cutoff_pos i) (by norm_num),
        (hbb.eventually (Ioi_mem_nhds hp)).mono fun _ hn => hn.le⟩
  have ha : 0< EarlyRankCeiling.ceilingValue i-entry i :=
    sub_pos.mpr (EarlyRankCeiling.ceilingValue_bounds i).1.1
  have hactive : ∀ᶠ n in atTop,∀ᵐ p ∂(GG n:Measure (ℝ × ℝ)),
      p.1∈Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1|≤ cutoff i/10000 := by
    have hh := hm'.eventually (source_early_active G g cm i h05
      (EarlyRankCeiling.ceilingValue i-entry i) ha (cutoff i/10000)
        (div_pos (cutoff_pos i) (by norm_num)))
    have he : entry i+(EarlyRankCeiling.ceilingValue i-entry i)=
        EarlyRankCeiling.ceilingValue i := by ring
    filter_upwards [hh] with n hn
    simpa only [he] using hn (EE n)
  have hstep (Branch : ℕ → Prop) (hBr : ∀ᶠ n in atTop,Branch n)
      (hB : ∀ (S : Data i),
        (∀ n,∃ q, S.b n=bb q ∧ S.g n=gg q ∧ Branch q) → S.ReceiptBand) :
      ∃ ψ : ℕ → ℕ,StrictMono ψ ∧
        ∀ᶠ n in atTop,Test (m (ψ n)) (G (m (ψ n)) (E (ψ n)))
          (g (m (ψ n)) (E (ψ n))) (cm (m (ψ n)) (E (ψ n))) (b (ψ n)) := by
    obtain ⟨k,hk⟩ := eventually_atTop.mp
      ((tendsto_add_atTop_nat n0).eventually (hθ'.and (hgeom'.and hBr)))
    let j := fun n : ℕ => n+k+n0
    have hj : Tendsto j atTop atTop :=
      (tendsto_add_atTop_nat n0).comp (tendsto_add_atTop_nat k)
    have hjmono : StrictMono j := by intro a b hab; dsimp [j]; omega
    have htail (n : ℕ) : tt (j n)∈Icc t0 Θ ∧
        PointGeometry i (gg (j n)) (bb (j n)) ∧ Branch (j n) := by
      have hh := hk (n+k) (by omega)
      exact ⟨hh.1.1,hh.2.1,hh.2.2⟩
    let ma := fun n => mm (n+n0)
    have hma : Tendsto ma atTop atTop := hm'.comp (tendsto_add_atTop_nat n0)
    have hNa : ∀ n,A.N n=ma n-1 := fun n => congrFun hAN n
    let AA := ActualArrayTail.physicalTail A ma hNa hma k
    have hAA : ∀ n,AA.N n=mm (j n)-1 := fun _ => rfl
    have hAAraw (n : ℕ) : AA.law n=tiltedSource i (GG (j n):Measure (ℝ × ℝ))
        (bb (j n)) (tt (j n)) := by
      change A.law (n+k)=_
      rw [hAlaw]
    let rr := fun n => LiteralCenteredArray.mean i
      (PhysicalExposureLimit.lowerProbability i (GG (j n)) (bb (j n)) (hbp (j n)))
        (-tt (j n))
    have hAAX (n : ℕ) : ∀ᵐ x ∂AA.law n,AA.X n x=demand (xi i) (bb (j n)) x-rr n := by
      apply ae_of_all
      intro x
      change A.X (n+k) x=_
      rw [hAX]
    have hAAY (n : ℕ) : AA.Y n=integerSign := by
      change A.Y (n+k)=_
      rw [hAY]
    have hmatch : ∀ᶠ n in atTop,(∫ x,demand (xi i) (bb (j n)) x
        ∂tiltedSource i (GG (j n):Measure (ℝ × ℝ)) (bb (j n)) (tt (j n)))=
          (capacity (mm (j n)):ℝ)/(AA.N n:ℝ) := by
      filter_upwards [hj.eventually hθ'] with n hn
      have hp : (∫ x,demand (xi i) (bb (j n)) x
        ∂tiltedSource i (GG (j n):Measure (ℝ × ℝ)) (bb (j n)) (tt (j n)))=
          SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (bb (j n))
            (GG (j n):Measure (ℝ × ℝ)))) Prod.fst (tt (j n)) := by
        have hpres := tilted_point_preserving i (GG (j n):Measure (ℝ × ℝ))
          (hbp (j n)) (tt (j n))
        change (∫ x,Prod.fst (point (xi i) (bb (j n)) x) ∂_)=∫ y,Prod.fst y ∂_
        have hmap := hpres.map_eq
        dsimp only [MixedLaw.tiltedLaw] at hmap
        rw [← hmap]
        exact (integral_map hpres.measurable.aemeasurable measurable_fst.aestronglyMeasurable).symm
      rw [hp,hn.2,hAA]
    let S : Data i := {
      G := fun n => GG (j n)
      joint_limit := hG'.comp hj
      A := AA
      gap := ActualArrayTail.physicalTail_gap A hgap ma hNa hma k
      m := fun n => mm (j n)
      market := hm'.comp hj
      rivals := hAA
      b := fun n => bb (j n)
      θ := fun n => tt (j n)
      r := rr
      g := fun n => gg (j n)
      cm := fun n => cm (mm (j n)) (EE (j n))
      cmbar := fun n => hK.cmbar (mm (j n)) (EE (j n)) (bb (j n)) (tt (j n))
      raw_law := hAAraw
      raw_sign := hAAY
      raw_center := hAAX
      hi := hi
      Θ := Θ
      t0 := t0
      b0 := b0
      θ0 := θ0
      subentry := hhi
      theta_lower_pos := ht0
      bid_band := fun n => hband (j n)
      theta_band := fun n => (htail n).1
      bid_limit := hbb.comp hj
      theta_limit := hθlim.comp hj
      value_marginal := fun n => h05.value_marginal (mm (j n)) (EE (j n))
      below_value := fun n => hbelow (mm (j n)) (EE (j n))
      box := fun n => hbox (mm (j n)) (EE (j n))
      early_active := hj.eventually hactive
      matching := hmatch
      multiplier_limit := hL.comp hj
      literal_fields := fun n => hfields (mm (j n)) (EE (j n))
      population_eq := fun n => hK.population_eq (mm (j n)) (EE (j n))
      bid_multiplier := fun n => (htail n).2.1.bid_multiplier.le
      guard_lower_pos := fun n => (htail n).2.1.prefix.lower_pos
      bid_rejection := fun n => (htail n).2.1.bid_rejection.le
      ε := hK.ε
      Kcount := hK.Kcount
      margin_pos := hK.margin_pos
      margin_lower := fun n => hK.margin_lower (mm (j n)) (EE (j n))
      count_constant_nonneg := hK.count_constant_nonneg
      count_receipt := by
        intro n
        rw [hAAraw]
        exact hK.count_receipt (mm (j n)) (EE (j n)) (bb (j n)) (tt (j n))
          (hbp (j n)) (htail n).2.1.bid_multiplier.le }
    have hSband : S.ReceiptBand := hB S (fun n => ⟨j n,rfl,rfl,(htail n).2.2⟩)
    have hout := hdata S hSband
      (fun n a => hatom (mm (j n)) (EE (j n)) a)
      (fun n => (htail n).2.1)
    refine ⟨φ ∘ j,hφ.comp hjmono,?_⟩
    exact hout
  rcases hbranch with hlow | ⟨e,he,hhigh⟩
  · exact hstep (fun n => bb n≤(gg n).multiplier-(gg n).radius) hlow
      (fun S hs => Or.inl (fun n => by
        obtain ⟨q,hb,hg,hq⟩ := hs n
        rw [hb,hg]
        exact hq))
  · exact hstep (fun n => ReceiptGap.threshold i+e≤ bb n) hhigh
      (fun S hs => Or.inr ⟨e,he,fun n => by
        obtain ⟨q,hb,_hg,hq⟩ := hs n
        rw [hb]
        exact hq⟩)

end Family
end FCAppendix.Affine.Uniform06.SourcePreciseFamily
