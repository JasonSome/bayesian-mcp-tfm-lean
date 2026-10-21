import FCAppendix.Affine.Tail04.OrderedSourcePartialConstruction
import FCAppendix.Affine.Tail04.SourceMovingScalarGuards
import FCAppendix.Affine.Tail04.SourceLowConstructor
import FCAppendix.Affine.Tail04.OrderedNativeZeroNoiseSource

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceFiniteStartingPoint
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional OriginalValues OriginalPopulation MenuError LowBody
open SourceMovingScalarGuards SourceTailNoisyFixedPoint OrderedOriginalNoisySequence
open SourceMomentRectangle

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)

def data (N : ℕ) (r : Range P ξ Up u k N) : FiniteTailNoisyGame.Data :=
  SourceNoisyData.data P ξ u Up (cap ξ k N) width (iidCapacity (99/200) N)
    hξ hξh hu r.base_contains_bulk hRUp.le hUp r.base_below_nominal hw

structure StartingPoint (N : ℕ) where
  range : Range P ξ Up u k N
  low : ActualAtomlessLowLimit N P.d0 ξ (iidCapacity (99/200) N)
    (NativeLowSourceIC.categories P (cutoff N) range.cutoff_gt_M.le) P.originalLowLaw
  underflow_pos : 0<(CommonList.iid
    (NativeLowSourceIC.categories P (cutoff N) range.cutoff_gt_M.le) N).prob
      (LocalUnderflow (iidCapacity (99/200) N) 0)
  double_underflow : (CommonList.iid
    (NativeLowSourceIC.categories P (cutoff N) range.cutoff_gt_M.le) N).prob
      (BothUnderflow (iidCapacity (99/200) N))≤
    (CommonList.iid (NativeLowSourceIC.categories P (cutoff N) range.cutoff_gt_M.le) N).prob
      (LocalUnderflow (iidCapacity (99/200) N) 0)/4
  sequence : Sequence (data P ξ Up u k width hξ hξh hu hRUp hUp hw N range)
    P (cutoff N) range.cutoff_gt_M N
  partial_atomless : NullSingletonClass (Sequence.realBaseLaw 2 sequence.limit : Measure ℝ)

theorem construct (N : ℕ) (r : Range P ξ Up u k N)
    (L : SourceLowConstructor.AtMarket P ξ Markets.capacity (N+1))
    (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)
    (hmargin : 4*(SourcePartialNoisyError.valueBound P+1)*SourcePartialPublicGuard.badBound P ξ N<
      ((Up-Central.R ξ)/2)*(1-P.theta)) :
    Nonempty (StartingPoint P ξ Up u k width hξ hξh hu hRUp hUp hw N) := by
  let D := data P ξ Up u k width hξ hξh hu hRUp hUp hw N r
  let cats := NativeLowSourceIC.categories P (cutoff N) r.cutoff_gt_M.le
  have hL : ActualAtomlessLowLimit N P.d0 ξ (iidCapacity (99/200) N) cats P.originalLowLaw := by
    simpa only [cats,cutoff,Nat.add_sub_cancel,Markets.capacity,iidCapacity,
      Nat.cast_add,Nat.cast_one] using L.low
  have hell : 0<(CommonList.iid cats N).prob (LocalUnderflow (iidCapacity (99/200) N) 0) := by
    simpa only [cats,cutoff,Nat.add_sub_cancel,Markets.capacity,iidCapacity,
      Nat.cast_add,Nat.cast_one] using! L.underflow_pos
  have hsmall : (CommonList.iid cats N).prob (BothUnderflow (iidCapacity (99/200) N))≤
      (CommonList.iid cats N).prob (LocalUnderflow (iidCapacity (99/200) N) 0)/4 := by
    simpa only [cats,cutoff,Nat.add_sub_cancel,Markets.capacity,iidCapacity,
      Nat.cast_add,Nat.cast_one] using! L.double_underflow
  have hdR : P.d0< D.R := by
    change P.d0< Central.R ξ
    unfold Central.R
    linarith
  have hBH : D.B< Central.B ξ+1 :=
    D.hUF.trans_lt (lt_add_of_pos_right _ (by norm_num))
  have hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
      (tailMass P (cutoff N)/(partialMass+tailMass P (cutoff N))))≤ D.R := by
    simpa only [D,data,SourceNoisyData.data,FiniteTailNoisyGame.Data.B,
      commonPhysical,noise,tailMass,SourceMenuPopulation.upperMass,
      Nat.cast_add,Nat.cast_one] using r.owner_receipt_guard
  obtain ⟨S,hS⟩ := OrderedSourcePartialConstruction.exists_original_partial_atomless_sequence
    P ξ u Up (cap ξ k N) width N hξ hξh hu r.base_contains_bulk hRUp.le hUp
    r.base_below_nominal hw (cutoff N) r.cutoff_gt_M hL.joint
    (fun _ : ℝ=> Central.B ξ+1) measurable_const hdR (Central.B ξ+1) hBH
    (fun _ _=> le_rfl) hrare r.rivals_positive r.capacity_positive r.capacity_less_population
    hlow r.partial_below_value r.bulk_below_nominal r.partial_guard r.moment_guard
    r.upper_mass_guard hwγ r.room cats hL rfl hRUp (by
      change 2*(SourcePartialNoisyError.valueBound P+1)*(2*SourcePartialPublicGuard.badBound P ξ N)<_
      nlinarith only [hmargin])
  exact ⟨⟨r,hL,hell,hsmall,S,hS⟩⟩

theorem eventually_construct (hk : 0< k) (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)
    (hvalue : Up<2-P.w) (huB : 1+u< Central.B ξ)
    (hUpMargin : Up< Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)< ξ/1000)
    (hgap : 2*Ample.binaryKL (99/200) (1-partialMass/2)<
      jointRate (lowMass P.theta) (activeMass P.theta) partialMass (99/200)) :
    ∀ᶠ N in atTop,Nonempty (StartingPoint P ξ Up u k width hξ hξh hu hRUp hUp hw N) := by
  have hr := SourceMovingScalarGuards.eventually_range P hξ hξh hu hk hRUp hUp
    hvalue huB hUpMargin hsmall
  have hL := (tendsto_add_atTop_nat 1).eventually
    (SourceLowConstructor.eventually_construct P ξ hξ hξh.le Markets.capacity
      Markets.capacity_density hgap)
  have hmargin := OrderedSourcePartialNoisyError.eventually_downward_margin P ξ hξ
    ((Up-Central.R ξ)/2) (by linarith)
  filter_upwards [hr,hL,hmargin] with N r hN hmar
  obtain ⟨L⟩ := hN
  exact construct P ξ Up u k width hξ hξh hu hRUp hUp hw N r L hlow hwγ hmar

end FCAppendix.Affine.Tail04.OrderedSourceFiniteStartingPoint
