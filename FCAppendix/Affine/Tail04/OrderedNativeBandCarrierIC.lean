import FCAppendix.Affine.Tail04.LatentSpeciesCalculus
import FCAppendix.Affine.Tail04.SourceOrderedNoisyFixedPoint
import FCAppendix.Affine.Tail04.OrderedNativeNoisySource
import FCAppendix.Affine.Tail04.NativeDeletedCounts
import FCAppendix.Probability.ConditionalAveraging

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativeBandCarrierIC
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeNoisySource LatentNoisyPopulation
open LatentSpeciesCalculus OriginalFiniteFibers NativeDeletedCounts
open scoped BigOperators

section General
variable {N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def chargeBound (f : ℕ → ℝ) : ℝ := ∑ r : Fin 3,|f r.val|

lemma chargeBound_nonneg (f : ℕ → ℝ) : 0≤ chargeBound f :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma charge_le_bound (f : ℕ → ℝ) (r : Fin 3) : |f r.val|≤ chargeBound f := by
  unfold chargeBound
  exact Finset.single_le_sum (f:=fun k : Fin 3 => |f k.val|)
    (fun k _ => abs_nonneg (f k.val)) (Finset.mem_univ r)

lemma abs_userPayoff_bound (v b g : ℝ) (A G : ℕ → ℝ) (r : Fin 3) :
    |userPayoff v b g A G r.val|≤|v|+|b| * chargeBound A+|g| * chargeBound G := by
  have hs : |successIndicator r.val|≤1 := by unfold successIndicator;split_ifs <;> norm_num
  unfold userPayoff
  calc
    _ ≤ |v*successIndicator r.val-b*A r.val|+|g*G r.val| := abs_sub _ _
    _ ≤ |v*successIndicator r.val|+|b*A r.val|+|g*G r.val| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ _ := by
      rw [abs_mul,abs_mul,abs_mul]
      exact add_le_add
        (add_le_add (by simpa using mul_le_mul_of_nonneg_left hs (abs_nonneg v))
          (mul_le_mul_of_nonneg_left (charge_le_bound A r) (abs_nonneg b)))
        (mul_le_mul_of_nonneg_left (charge_le_bound G r) (abs_nonneg g))

lemma measurable_userPayoff {X : Type*} [MeasurableSpace X]
    (v b : X → ℝ) (g : ℝ) (A G : ℕ → ℝ) (r : X → Fin 3)
    (hv : Measurable v) (hb : Measurable b) (hr : Measurable r) :
    Measurable (fun x => userPayoff (v x) (b x) g A G (r x).val) :=
  ((hv.mul ((measurable_of_countable (fun k : Fin 3 => successIndicator k.val)).comp hr)).sub
    (hb.mul ((measurable_of_countable (fun k : Fin 3 => A k.val)).comp hr))).sub
      (measurable_const.mul ((measurable_of_countable (fun k : Fin 3 => G k.val)).comp hr))

theorem payoff_deleted_integral (Γ : FiniteGame (N+1) 2 c Seed)
    (i : Fin (N+1)) (v : ℝ) (a : JointAction 2) :
    (problem Γ i).payoff v a=
      ∫ z,userPayoff v a.bid (Γ).g (Γ).A.charge (Γ).G.charge (deletedCount Γ i a z).val
        ∂deletedSampleLaw Γ := by
  change ((problem Γ i).outcome a).utility v a.bid (Γ).g (Γ).A (Γ).G=_
  rw [raw_count_law,CountLaw.utility,FiniteLaw.expect_ofMeasure]

private lemma measurable_sample_userPayoff {Ω : Type*} [MeasurableSpace Ω]
    (Γ : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1))
    (v : Ω→ℝ) (a : Ω→JointAction 2) (s : Ω→Sample (N+1) 2 Seed)
    (hv : Measurable v) (ha : Measurable a) (hs : Measurable s) :
    Measurable (fun z => userPayoff (v z) (a z).bid (Γ).g (Γ).A.charge (Γ).G.charge
      (focalCount Γ i (a z) (s z)).val) := by
  have hb : Measurable (fun z => (a z).bid) := (measurable_bid 2).comp ha
  have hc : Measurable (fun z => focalCount Γ i (a z) (s z)) := by
    change Measurable ((fun p : JointAction 2×Sample (N+1) 2 Seed => focalCount Γ i p.1 p.2) ∘
      (fun z => (a z,s z)))
    exact (measurable_focalCount_joint Γ i).comp (ha.prodMk hs)
  exact measurable_userPayoff v (fun z => (a z).bid) (Γ).g (Γ).A.charge (Γ).G.charge
    (fun z => focalCount Γ i (a z) (s z)) hv hb hc

end General

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v → H≤ upperBid v)
  (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
      (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

local notation "Γ" => OrderedNativeNoisySource.game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid

abbrev Background (N : ℕ) := (Fin N → Draw)×(Fin 2 → NativeLocalPolicy.Seed)

def background : Measure (Background N) :=
  (Measure.pi (fun _ : Fin N => μ)).prod (Measure.pi (fun _ : Fin 2 => (Γ).seedLaw))

instance background_probability :
    IsProbabilityMeasure (background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare) := by
  unfold background
  infer_instance

def nativeDeleted (z : Background N×Equiv.Perm (Fin 2)) :
    DeletedSample N NativeLocalPolicy.Seed :=
  ((fun k => realize D (z.1.1 k),z.1.2),z.2)

lemma measurable_nativeDeleted : Measurable (nativeDeleted D (N:=N)) :=
  ((measurable_pi_lambda _ (fun k => (measurable_realize D).comp (measurable_pi_apply k))).prodMap
    measurable_id).prodMap measurable_id

theorem nativeDeleted_law :
    ((background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare).prod (permLaw 2)).map
      (nativeDeleted D (N:=N))=deletedSampleLaw Γ := by
  unfold background nativeDeleted deletedSampleLaw
  let f : (Fin N→Draw)→(Fin N→UserDraw 2) := fun x k => realize D (x k)
  have hf : Measurable f := measurable_pi_lambda _
    (fun k => (measurable_realize D).comp (measurable_pi_apply k))
  change Measure.map (Prod.map (Prod.map f id) id)
    (((Measure.pi (fun _ : Fin N => μ)).prod
      (Measure.pi (fun _ : Fin 2 => (Γ).seedLaw))).prod (permLaw 2))=_
  rw [←Measure.map_prod_map _ _ (hf.prodMap measurable_id) measurable_id,
    ←Measure.map_prod_map _ _ hf measurable_id]
  simp only [Measure.map_id]
  dsimp only [f]
  rw [Measure.pi_map_pi (fun _ => (measurable_realize D).aemeasurable)]
  simp only [realize_original_user D P t ht πL π upperBid hupperBid hdR H hBH hfloor (N+1) hrare]
  have huser :
      userLaw (NativeNoisySource.game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare)=
        userLaw Γ := by
    rw [NativeNoisySource.game_original_user,OrderedNativeNoisySource.game_original_user]
    rfl
  simp only [huser]

def physicalBandAction (k : Fin 3)
    (x : Icc (valueLo P k) (valueHi P t k)×Icc (bidLo D k) (bidHi D k))
    (u : unitInterval) : JointAction 2 :=
  noisyAction D.eps D.heps.le (bandBase D P t k x).2 u

lemma measurable_physicalBandAction (k : Fin 3) :
    Measurable (fun z : (Icc (valueLo P k) (valueHi P t k)×Icc (bidLo D k) (bidHi D k))×unitInterval => physicalBandAction D P t k z.1 z.2) :=
  (measurable_noisyAction D.eps D.heps.le).comp
    (((measurable_snd.comp (measurable_bandBase D P t k)).comp measurable_fst).prodMk measurable_snd)

def bandPay (i : Fin (N+1)) (k : Fin 3) (z : BandDraw D P t k×Background N) : ℝ :=
  let a := physicalBandAction D P t k z.1.1.1 z.1.1.2
  userPayoff (z.1.1.1.1:ℝ) a.bid (Γ).g (Γ).A.charge (Γ).G.charge
    (deletedCount Γ i a (nativeDeleted D (N:=N) (z.2,z.1.2))).val

lemma measurable_bandPay (i : Fin (N+1)) (k : Fin 3) :
    Measurable (bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k) := by
  let a := fun z : BandDraw D P t k×Background N =>
    physicalBandAction D P t k z.1.1.1 z.1.1.2
  have ha : Measurable a := (measurable_physicalBandAction D P t k).comp measurable_fst.fst
  have hs : Measurable (fun z : BandDraw D P t k×Background N =>
      restoreSample i (nativeDeleted D (N:=N) (z.2,z.1.2))) :=
    (measurable_restoreSample i).comp ((measurable_nativeDeleted D (N:=N)).comp
      (measurable_snd.prodMk measurable_fst.snd))
  change Measurable (fun z : BandDraw D P t k×Background N =>
    userPayoff (z.1.1.1.1:ℝ) (a z).bid (Γ).g (Γ).A.charge (Γ).G.charge
      (focalCount Γ i (a z) (restoreSample i (nativeDeleted D (N:=N) (z.2,z.1.2)))).val)
  exact measurable_sample_userPayoff Γ i
    (fun z : BandDraw D P t k×Background N => (z.1.1.1.1:ℝ)) a
    (fun z => restoreSample i (nativeDeleted D (N:=N) (z.2,z.1.2)))
    measurable_fst.fst.fst.fst.subtype_val ha hs

def bandPayBound (k : Fin 3) : ℝ :=
  |valueLo P k|+|valueHi P t k|+
    (bidHi D k*(1+D.eps))*chargeBound (Γ).A.charge+|(Γ).g| * chargeBound (Γ).G.charge

lemma bandPayBound_nonneg (k : Fin 3) :
    0≤ bandPayBound D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare k := by
  have hh := (bidLo_pos D k).le.trans (bidLo_le_hi D k)
  have hA := chargeBound_nonneg (Γ).A.charge
  have hG := chargeBound_nonneg (Γ).G.charge
  have hε : 0≤1+D.eps := by linarith [D.heps]
  unfold bandPayBound
  positivity

lemma bandPay_bound (i : Fin (N+1)) (k : Fin 3) (z : BandDraw D P t k×Background N) :
    ‖bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k z‖≤
      bandPayBound D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare k := by
  have hv : |(z.1.1.1.1:ℝ)|≤|valueLo P k|+|valueHi P t k| := by
    apply abs_le.mpr
    constructor
    · linarith [z.1.1.1.1.2.1,neg_abs_le (valueLo P k),abs_nonneg (valueHi P t k)]
    · linarith [z.1.1.1.1.2.2,le_abs_self (valueHi P t k),abs_nonneg (valueLo P k)]
  have hb0 : 0≤(z.1.1.1.2:ℝ) := (bidLo_pos D k).le.trans z.1.1.1.2.2.1
  have hm : 0≤1+D.eps*(z.1.1.2:ℝ) := by linarith [mul_nonneg D.heps.le z.1.1.2.2.1]
  have hm' : 1+D.eps*(z.1.1.2:ℝ)≤1+D.eps := by
    have hh : D.eps*(z.1.1.2:ℝ)≤D.eps := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left z.1.1.2.2.2 D.heps.le
    exact add_le_add le_rfl hh
  have hb : |(physicalBandAction D P t k z.1.1.1 z.1.1.2).bid|≤ bidHi D k*(1+D.eps) := by
    change |(z.1.1.1.2:ℝ)*(1+D.eps*(z.1.1.2:ℝ))|≤_
    rw [abs_of_nonneg (mul_nonneg hb0 hm)]
    exact mul_le_mul z.1.1.1.2.2.2 hm' hm
      ((bidLo_pos D k).le.trans (bidLo_le_hi D k))
  rw [Real.norm_eq_abs]
  exact (abs_userPayoff_bound _ _ _ _ _ _).trans
    (add_le_add (add_le_add hv
      (mul_le_mul_of_nonneg_right hb (chargeBound_nonneg (Γ).A.charge))) le_rfl)

theorem bandPay_integral (i : Fin (N+1)) (k : Fin 3)
    (x : Icc (valueLo P k) (valueHi P t k)×Icc (bidLo D k) (bidHi D k))
    (u : unitInterval) :
    (∫ τ,∫ bg,bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k
      (((x,u),τ),bg) ∂background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
        ∂permLaw 2)=(problem Γ i).payoff (x.1:ℝ) (physicalBandAction D P t k x u) := by
  let f := fun z : Background N×Equiv.Perm (Fin 2) =>
    bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k (((x,u),z.2),z.1)
  have hf : Measurable f := (measurable_bandPay D P t ht πL π upperBid hupperBid
    hdR H hBH hfloor N hrare i k).comp
      ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
  have hi : Integrable f
      ((background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare).prod (permLaw 2)) :=
    Integrable.of_bound hf.aestronglyMeasurable
      (bandPayBound D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare k)
      (ae_of_all _ fun z => bandPay_bound D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k _)
  rw [←integral_prod_symm f hi,payoff_deleted_integral]
  rw [←nativeDeleted_law D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare]
  symm
  apply integral_map (measurable_nativeDeleted D (N:=N)).aemeasurable
  exact ((measurable_of_countable (fun r : Fin 3 => userPayoff (x.1:ℝ)
    (physicalBandAction D P t k x u).bid (Γ).g (Γ).A.charge (Γ).G.charge r.val)).comp
      (measurable_deletedCount Γ i (physicalBandAction D P t k x u))).aestronglyMeasurable

def bandGain (i : Fin (N+1)) (k : Fin 3)
    (dev : (Icc (valueLo P k) (valueHi P t k)×Icc (bidLo D k) (bidHi D k)) →
      Icc (bidLo D k) (bidHi D k)) (z : BandDraw D P t k×Background N) : ℝ :=
  bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k
    (((((z.1.1.1.1,dev z.1.1.1),z.1.1.2),z.1.2)),z.2)-
  bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k z

lemma measurable_bandGain (i : Fin (N+1)) (k : Fin 3) (dev) (hdev : Measurable dev) :
    Measurable (bandGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k dev) := by
  have hp := measurable_bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k
  exact (hp.comp (((((measurable_fst.fst.fst.fst.prodMk
    (hdev.comp measurable_fst.fst.fst)).prodMk measurable_fst.fst.snd).prodMk
      measurable_fst.snd)).prodMk measurable_snd)).sub hp

lemma integrable_bandGain (i : Fin (N+1)) (k : Fin 3) (dev) (hdev : Measurable dev)
    (J : Set ℝ) : Integrable
    (bandGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k dev)
    ((((((π k).1 : Measure _).restrict (typedCluster D P t k J)).prod
      (volume : Measure unitInterval)).prod (permLaw 2)).prod
        (background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)) := by
  apply Integrable.of_bound (measurable_bandGain D P t ht πL π upperBid hupperBid
    hdR H hBH hfloor N hrare i k dev hdev).aestronglyMeasurable
      (2*bandPayBound D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare k)
  apply ae_of_all
  intro z
  exact (norm_sub_le _ _).trans (by
    linarith [bandPay_bound D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k z,
      bandPay_bound D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k
        (((((z.1.1.1.1,dev z.1.1.1),z.1.1.2),z.1.2)),z.2)])

theorem integrated_band_IC_of_native_identity (i : Fin (N+1)) (k : Fin 3)
    (dev) (hdev : Measurable dev) (J : Set ℝ)
    (hidentity : ∀ x,
      (∫ u,(problem Γ i).payoff (x.1:ℝ) (physicalBandAction D P t k x u)
        ∂(volume : Measure unitInterval))=SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x))
    (hC1 : AllActionOptimal (π k) (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x))) :
    (∫ z,bandGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k dev z
      ∂((((((π k).1 : Measure _).restrict (typedCluster D P t k J)).prod
        (volume : Measure unitInterval)).prod (permLaw 2)).prod
          (background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)))≤0 := by
  have hi := integrable_bandGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k dev hdev J
  rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left,
    integral_prod _ hi.integral_prod_left.integral_prod_left]
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_of_ae hC1] with x hx
  have hp (y) : Integrable (fun z : unitInterval×(Equiv.Perm (Fin 2)×Background N) =>
      bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k
        (((y,z.1),z.2.1),z.2.2))
      ((volume : Measure unitInterval).prod ((permLaw 2).prod
        (background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare))) := by
    apply Integrable.of_bound
      ((measurable_bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k).comp
        (((measurable_const.prodMk measurable_fst).prodMk measurable_snd.fst).prodMk
          measurable_snd.snd)).aestronglyMeasurable
      (bandPayBound D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare k)
    exact ae_of_all _ fun z => bandPay_bound D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k _
  have he (y) : (∫ u,∫ τ,∫ bg,bandPay D P t ht πL π upperBid hupperBid
      hdR H hBH hfloor N hrare i k (((y,u),τ),bg)
        ∂background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
          ∂permLaw 2 ∂(volume : Measure unitInterval))=SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,y) := by
    simp_rw [bandPay_integral D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k]
    exact hidentity y
  have hpi (y) (u : unitInterval) : Integrable
      (fun z : Equiv.Perm (Fin 2)×Background N =>
        bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k (((y,u),z.1),z.2))
      ((permLaw 2).prod (background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)) := by
    apply Integrable.of_bound
      ((measurable_bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
      (bandPayBound D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare k)
    exact ae_of_all _ fun z => bandPay_bound D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k _
  have he' (y) : (∫ z : unitInterval×(Equiv.Perm (Fin 2)×Background N),
      bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k (((y,z.1),z.2.1),z.2.2)
      ∂(volume : Measure unitInterval).prod ((permLaw 2).prod
        (background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)))=
        SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,y) := by
    rw [integral_prod _ (hp y)]
    calc
      _ = ∫ u,∫ τ,∫ bg,bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k
          (((y,u),τ),bg) ∂background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
            ∂permLaw 2 ∂(volume : Measure unitInterval) :=
        integral_congr_ae (ae_of_all _ fun u => integral_prod _ (hpi y u))
      _ = _ := he y
  have hs : (∫ z : unitInterval×(Equiv.Perm (Fin 2)×Background N),
      (bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k
        ((((x.1,dev x),z.1),z.2.1),z.2.2)-
       bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k
        (((x,z.1),z.2.1),z.2.2))
      ∂(volume : Measure unitInterval).prod ((permLaw 2).prod
        (background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)))=
      ∫ u,∫ τ,∫ bg,
        (bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k ((((x.1,dev x),u),τ),bg)-
         bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k (((x,u),τ),bg))
        ∂background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
          ∂permLaw 2 ∂(volume : Measure unitInterval) := by
    calc
      _=∫ u,∫ z : Equiv.Perm (Fin 2)×Background N,
          (bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k
            ((((x.1,dev x),u),z.1),z.2)-
           bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k
            (((x,u),z.1),z.2))
          ∂(permLaw 2).prod (background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)
            ∂(volume : Measure unitInterval) := integral_prod _ ((hp (x.1,dev x)).sub (hp x))
      _=_ := integral_congr_ae (ae_of_all _ fun u =>
        integral_prod _ ((hpi (x.1,dev x) u).sub (hpi x u)))
  change (∫ u,∫ τ,∫ bg,
      (bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k ((((x.1,dev x),u),τ),bg)-
       bandPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k (((x,u),τ),bg))
      ∂background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
        ∂permLaw 2 ∂(volume : Measure unitInterval))≤0
  rw [←hs,integral_sub (hp (x.1,dev x)) (hp x),he',he']
  exact sub_nonpos.mpr (hx (dev x))

end FCAppendix.Affine.Tail04.OrderedNativeBandCarrierIC
