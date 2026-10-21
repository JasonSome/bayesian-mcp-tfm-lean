import FCAppendix.Affine.Tail04.OrderedAtomPartialCarrier
import FCAppendix.Affine.Tail04.OrderedAtomProfileCarrier

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomPartialGeometry
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeNoisySource LatentNoisyPopulation
open LatentSpeciesCalculus OrderedNativeBandCarrierIC OrderedAtomBandCarrier
open OrderedAtomSupport OrderedAtomProfileCarrier OrderedAtomPartialCarrier
open scoped BigOperators

lemma action_ext {n : ℕ} (a b : JointAction n)
    (hbid : a.bid=b.bid) (hroute : a.routeCount=b.routeCount) : a=b := by
  cases a
  cases b
  cases hbid
  cases hroute
  rfl

lemma oldAction_of_band (D : FiniteTailNoisyGame.Data) (k : Fin 3) (z : Draw)
    (hz : label z=bandSpecies k) :
    oldAction D z=noisyAction D.eps D.heps.le z.1.1.2.2 z.1.2 := by
  change (if z.1.1.1=0 ∨ z.1.1.1=4 then z.1.1.2 else
    noisyJoint D.eps D.heps.le (z.1.1.2,z.1.2)).2=_
  change z.1.1.1=bandSpecies k at hz
  rw [hz]
  fin_cases k <;> simp [bandSpecies,noisyJoint]

lemma partial_implementation (D : FiniteTailNoisyGame.Data)
    (x : ℝ) (hx : x∈Icc D.R D.Up) (u : unitInterval) :
    x*(1+D.eps*(u:ℝ))∈Icc D.R D.V := by
  have hx0 : 0≤ x := D.hR.le.trans hx.1
  have hu0 := mul_nonneg D.heps.le u.2.1
  have hu1 : D.eps*(u:ℝ)≤ D.eps := by
    simpa using mul_le_mul_of_nonneg_left u.2.2 D.heps.le
  constructor
  · nlinarith [hx.1,mul_nonneg hx0 hu0]
  · change x*(1+D.eps*(u:ℝ))≤ D.Up*(1+D.eps)
    exact mul_le_mul hx.2 (by linarith) (by linarith)
      (D.hR.le.trans D.hRUp)

lemma partial_record_physical (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ)
    (z : Draw) (hz : label z=bandSpecies 2) (hr : bandRecord D P t 2 z) :
    value z∈P.partialValues ∧ (oldAction D z).bid∈Icc D.R D.V ∧
      (oldAction D z).routeCount=1 := by
  rw [oldAction_of_band D 2 z hz]
  exact ⟨hr.1,partial_implementation D (baseBid z) hr.2.1 z.1.2,hr.2.2⟩

lemma partial_cluster_geometry (D : FiniteTailNoisyGame.Data)
    (P : ValueParameters) (t : ℝ) (heps : D.eps≤1)
    (β r : ℝ) (hr : 0< r) (y : Icc D.R D.Up) (hy : (y:ℝ)=β+2*r)
    (z : Draw) (hz : z∈bandCluster 2 (Ioo (β-r) (β+r)))
    (_hrecord : bandRecord D P t 2 z) :
    (oldAction D z).bid<(raisedAction D 2 y (D.hR.le.trans y.2.1) z).bid ∧
      (raisedAction D 2 y (D.hR.le.trans y.2.1) z).bid-(oldAction D z).bid<6*r := by
  rw [oldAction_of_band D 2 z hz.1]
  have hfactor0 : 0<1+D.eps*(z.1.2:ℝ) := by linarith [mul_nonneg D.heps.le z.1.2.2.1]
  have hfactor2 : 1+D.eps*(z.1.2:ℝ)≤2 := by
    have hmul : D.eps*(z.1.2:ℝ)≤ D.eps := by
      simpa using mul_le_mul_of_nonneg_left z.1.2.2.2 D.heps.le
    linarith
  have hgap : 0<(y:ℝ)-baseBid z := by linarith [hz.2.2]
  have hgap3 : (y:ℝ)-baseBid z<3*r := by linarith [hz.2.1]
  change baseBid z*(1+D.eps*(z.1.2:ℝ))<(y:ℝ)*(1+D.eps*(z.1.2:ℝ)) ∧
    (y:ℝ)*(1+D.eps*(z.1.2:ℝ))-baseBid z*(1+D.eps*(z.1.2:ℝ))<6*r
  constructor
  · exact mul_lt_mul_of_pos_right (by linarith) hfactor0
  · have hh := mul_le_mul_of_nonneg_left hfactor2 hgap.le
    nlinarith

lemma entire_partial_cluster_below (D : FiniteTailNoisyGame.Data)
    (P : ValueParameters) (t : ℝ) (β r : ℝ) (_hr : 0< r)
    (hnoise : D.eps*D.Up≤ r) (y : Icc D.R D.Up) (hy : (y:ℝ)=β+2*r)
    (z w : Draw) (hw : w∈bandCluster 2 (Ioo (β-r) (β+r)))
    (hrecord : bandRecord D P t 2 w) :
    (oldAction D w).bid<(raisedAction D 2 y (D.hR.le.trans y.2.1) z).bid := by
  rw [oldAction_of_band D 2 w hw.1]
  have hb0 : 0≤ baseBid w := D.hR.le.trans hrecord.2.1.1
  have hx : baseBid w*(D.eps*(w.1.2:ℝ))≤ D.eps*D.Up := by
    calc
      _ ≤ baseBid w*D.eps := mul_le_mul_of_nonneg_left
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left w.1.2.2.2 D.heps.le) hb0
      _ ≤ D.Up*D.eps := mul_le_mul_of_nonneg_right hrecord.2.1.2 D.heps.le
      _ = _ := mul_comm _ _
  have hy0 : 0≤(y:ℝ) := D.hR.le.trans y.2.1
  have hh := mul_nonneg hy0 (mul_nonneg D.heps.le z.1.2.2.1)
  change baseBid w*(1+D.eps*(w.1.2:ℝ))<(y:ℝ)*(1+D.eps*(z.1.2:ℝ))
  nlinarith [hw.2.2]

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v → H≤ upperBid v)
  (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "Γ" => OrderedNativeNoisySource.game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare

include hrare in
private lemma expanded_rare :
    (1-D.ξ)*D.B+D.ξ*D.B*(((N:ℝ)+1)*
      ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
        (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤D.R := by
  simpa only [tailMass,Nat.cast_add,Nat.cast_one] using hrare

local notation "K" => OrderedNativePayoffBindings.localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N
  (expanded_rare D P t N hrare)
local notation "Γ₀" => OrderedNativePayoffBindings.coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N
  (expanded_rare D P t N hrare)
local notation "E" => regions D P hdR H hBH

theorem source_count_mono (hlow : P.d0<1-D.ξ) (i : Fin (N+1))
    (z : ProfileSample N) (hz : ∀ l,commonSupport D P t hdR H hBH (z.1 l))
    (y : Icc D.R D.Up) (hlabel : label (z.1 i)=bandSpecies 2)
    (hraise : (oldAction D (z.1 i)).bid<
      (raisedAction D 2 y (D.hR.le.trans y.2.1) (z.1 i)).bid) :
    profileCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i (oldAction D) z≤
      profileCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i
        (raisedAction D 2 y (D.hR.le.trans y.2.1)) z := by
  obtain ⟨hv,hb,hk⟩ := partial_record_physical D P t (z.1 i) hlabel ((hz i).2 2 hlabel)
  let b : Icc (K).E.R (K).E.Rp := ⟨(oldAction D (z.1 i)).bid,hb⟩
  let b' : Icc (K).E.R (K).E.Rp :=
    ⟨(raisedAction D 2 y (D.hR.le.trans y.2.1) (z.1 i)).bid,partial_implementation D y y.2 (z.1 i).1.2⟩
  have he : oldAction D (z.1 i)=RawRoutes.action b
      (((K).E.d_nonneg.trans (K).E.d_lt_R.le).trans b.2.1) 1 := action_ext _ _ rfl hk
  have he' : raisedAction D 2 y (D.hR.le.trans y.2.1) (z.1 i)=RawRoutes.action b'
      (((K).E.d_nonneg.trans (K).E.d_lt_R.le).trans b'.2.1) 1 := action_ext _ _ rfl rfl
  unfold profileCount
  rw [OrderedNativePayoffBindings.sourceGame_focalCount,OrderedNativePayoffBindings.sourceGame_focalCount,he,he']
  exact focal_count_mono K hlow P t Γ₀ rfl (fullSample D (N:=N) i z) i b b' hraise 1
    (fun l _ => (hz l).1)

theorem source_singleton_payoff (i : Fin (N+1)) (v : ℝ) (a : JointAction 2)
    (hk : a.routeCount=1) (ω : Sample (N+1) 2 NativeLocalPolicy.Seed) :
    userPayoff v a.bid (Γ).g (Γ).A.charge (Γ).G.charge (focalCount Γ i a ω).val=
      (v-a.bid)*(focalCount Γ i a ω).val := by
  have hle := focalCount_le Γ i a ω
  rw [hk] at hle
  have hg : (Γ).g=0 := rfl
  have hA : (Γ).A=Schedule.affine 2 D.eta D.heta0 D.heta1 := rfl
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
  · simp [userPayoff,h,hg,hA,Schedule.affine,successIndicator]
  · simp [userPayoff,h,hg,hA,Schedule.affine,successIndicator]

theorem profile_partial_gain (i : Fin (N+1)) (y : Icc D.R D.Up) (J : Set ℝ)
    (z : ProfileSample N) (hz : ∀ l,commonSupport D P t hdR H hBH (z.1 l)) :
    profileGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i 2 y J z=
      if z.1 i∈bandCluster 2 J then
        (value (z.1 i)-(raisedAction D 2 y (D.hR.le.trans y.2.1) (z.1 i)).bid)*
          profileCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i
            (raisedAction D 2 y (D.hR.le.trans y.2.1)) z-
        (value (z.1 i)-(oldAction D (z.1 i)).bid)*
          profileCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i (oldAction D) z
      else 0 := by
  by_cases hi : z.1 i∈bandCluster 2 J
  · simp only [profileGain,if_pos hi,rawGain]
    rw [realizedPay_profileToCarrier,realizedPay_profileToCarrier,
      source_singleton_payoff D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i _ _ rfl,
      source_singleton_payoff D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i _ _
        (partial_record_physical D P t _ hi.1 ((hz i).2 2 hi.1)).2.2]
    rfl
  · simp only [profileGain,if_neg hi]

end FCAppendix.Affine.Tail04.OrderedAtomPartialGeometry
