import FCAppendix.Affine.Tail04.OrderedAtomPartialGeometry
import FCAppendix.Affine.Tail04.PartialCarrierAE

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomPartialFinite
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeNoisySource LatentNoisyPopulation
open LatentSpeciesCalculus OrderedNativeBandCarrierIC OrderedAtomBandCarrier
open OrderedAtomSupport OrderedAtomProfileCarrier OrderedAtomPartialGeometry
open OrderedAtomPartialCarrier PartialAtomCarrier PartialCarrierAE
open scoped BigOperators

lemma singleton_count_bounds {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (i : Fin m) (a : JointAction 2)
    (ha : a.routeCount=1) (ω : Sample m 2 Seed) :
    ((focalCount Γ i a ω).val:ℝ)∈Icc (0:ℝ) 1 := by
  refine ⟨Nat.cast_nonneg _,?_⟩
  have h := focalCount_le Γ i a ω
  rw [ha] at h
  exact_mod_cast h

lemma singleton_price_bound {v b q V B : ℝ} (hv : |v|≤ V)
    (hb : b∈Icc (0:ℝ) B) (hq : q∈Icc (0:ℝ) 1) : |(v-b)*q|≤ V+B := by
  rw [abs_mul,abs_of_nonneg hq.1]
  have hvB : |v-b|≤ V+B := (abs_sub _ _).trans (by simpa [abs_of_nonneg hb.1] using add_le_add hv hb.2)
  exact (mul_le_mul_of_nonneg_right hvB hq.1).trans
    ((mul_le_mul_of_nonneg_left hq.2
      (add_nonneg ((abs_nonneg v).trans hv) (hb.1.trans hb.2))).trans_eq (mul_one _))

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
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid
local notation "σ" => Measure.pi (fun _ : Fin 2 => FiniteGame.seedLaw Γ)
local notation "ρ" => profileLaw D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare

local instance : IsProbabilityMeasure ρ := by
  unfold profileLaw
  infer_instance

def eligible (β r : ℝ) : Set Draw := bandCluster 2 (Ioo (β-r) (β+r))
def favorable (β r : ℝ) : Set Draw :=
  {z | z∈eligible β r ∧ (0:Fin 2)∈firstK z.2 1}

lemma measurableSet_eligible (β r : ℝ) : MeasurableSet (eligible β r) :=
  measurableSet_bandCluster 2 _ measurableSet_Ioo

lemma measurableSet_favorable (β r : ℝ) : MeasurableSet (favorable β r) :=
  (measurableSet_eligible β r).inter
    ((MeasurableSet.of_discrete : MeasurableSet {τ : Equiv.Perm (Fin 2) | (0:Fin 2)∈firstK τ 1}).preimage
      measurable_snd)

def valueAt (z : ProfileSample N) (i : Fin (N+1)) : ℝ := value (z.1 i)
def oldBid (z : ProfileSample N) (i : Fin (N+1)) : ℝ := (oldAction D (z.1 i)).bid
def newBid (y : Icc D.R D.Up) (z : ProfileSample N) (i : Fin (N+1)) : ℝ :=
  (raisedAction D 2 y (D.hR.le.trans y.2.1) (z.1 i)).bid
def oldCount (z : ProfileSample N) (i : Fin (N+1)) : ℝ :=
  profileCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i (oldAction D) z
def newCount (y : Icc D.R D.Up) (z : ProfileSample N) (i : Fin (N+1)) : ℝ :=
  profileCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i
    (raisedAction D 2 y (D.hR.le.trans y.2.1)) z

theorem original_pointwise_carrier (hlow : P.d0<1-D.ξ) (hc : 0< D.c)
    (heps : D.eps≤1) (β r : ℝ) (hr : 0< r) (hnoise : D.eps*D.Up≤ r)
    (y : Icc D.R D.Up) (hy : (y:ℝ)=β+2*r) :
    ∀ᵐ z ∂ρ,
      (∀ i,z.1 i∈eligible β r →
        oldCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare z i∈Icc (0:ℝ) 1 ∧
        newCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare y z i∈Icc (0:ℝ) 1 ∧
        oldCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare z i≤
          newCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare y z i ∧
        2-P.w-D.V≤ valueAt N z i-newBid D N y z i ∧ oldBid D N z i≤ newBid D N y z i ∧
          newBid D N y z i-oldBid D N z i≤6*r) ∧
      (z∈allEvent (Z:=(Fin 2 → NativeLocalPolicy.Seed)) (N+1) (favorable β r) →
        ∀ i,newCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare y z i=1) ∧
      (z∈allEvent (Z:=(Fin 2 → NativeLocalPolicy.Seed)) (N+1) (favorable β r) →
        ∑ i,oldCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare z i≤(D.c:ℝ)) := by
  filter_upwards [original_iid_common_support D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare] with z hz
  have hb (i) (hi : z.1 i∈eligible β r) :=
    partial_record_physical D P t (z.1 i) hi.1 ((hz i).2 2 hi.1)
  refine ⟨?_,?_,?_⟩
  · intro i hi
    have hgeom := partial_cluster_geometry D P t heps β r hr y hy (z.1 i) hi ((hz i).2 2 hi.1)
    have hn := partial_implementation D y y.2 (z.1 i).1.2
    refine ⟨singleton_count_bounds Γ i _ (hb i hi).2.2 _,
      singleton_count_bounds Γ i _ rfl _,?_,?_,hgeom.1.le,hgeom.2.le⟩
    · exact source_count_mono D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
        hlow i z hz y hi.1 hgeom.1
    · have hv := (hb i hi).1.1
      change 2-P.w-D.V≤ value (z.1 i)-(y:ℝ)*(1+D.eps*((z.1 i).1.2:ℝ))
      linarith [hn.2]
  · intro he i
    have hell (l) : z.1 l∈eligible β r := (he.1 l (mem_univ l)).1
    have hroutes (l) : (realize D (z.1 l)).1.2.routeCount=1 := (hb l (hell l)).2.2
    have hsame (l) : (0:Fin 2)∈firstK (realize D (z.1 l)).2 1 := (he.1 l (mem_univ l)).2
    let b' : Icc (K).E.R (K).E.Rp := ⟨newBid D N y z i,partial_implementation D y y.2 (z.1 i).1.2⟩
    have hh := above_all_partial_included K hlow hc Γ₀ rfl (fun l => realize D (z.1 l)) z.2 0
      (fun l => (hb l (hell l)).2.1) hroutes hsame i b'
      (fun l => entire_partial_cluster_below D P t β r hr hnoise y hy (z.1 i) (z.1 l)
        (hell l) ((hz l).2 2 (hell l).1))
    have ha : raisedAction D 2 y (D.hR.le.trans y.2.1) (z.1 i)=RawRoutes.action b'
        (((K).E.d_nonneg.trans (K).E.d_lt_R.le).trans b'.2.1) 1 := action_ext _ _ rfl rfl
    unfold newCount profileCount
    rw [OrderedNativePayoffBindings.sourceGame_focalCount D P t ht hdR H hBH πL π upperBid
      hupperBid hfloor N (expanded_rare D P t N hrare),ha]
    exact_mod_cast hh
  · intro he
    have hell (l) : z.1 l∈eligible β r := (he.1 l (mem_univ l)).1
    exact all_partial_old_capacity Γ (fun l => realize D (z.1 l)) z.2 0
      (fun l => (hb l (hell l)).2.2) (fun l => (he.1 l (mem_univ l)).2)

theorem integrable_profile_partial_gain (i : Fin (N+1)) (y : Icc D.R D.Up)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    Integrable (profileGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i 2 y J) ρ := by
  apply Integrable.of_bound (measurable_profileGain D P t ht πL π upperBid hupperBid
    hdR H hBH hfloor N hrare i 2 y J hJ).aestronglyMeasurable
      (2*(|2-P.w|+|2+P.w|+D.V))
  filter_upwards [original_iid_common_support D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare] with z hz
  rw [profile_partial_gain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i y J z hz]
  by_cases hi : z.1 i∈bandCluster 2 J
  · rw [if_pos hi,Real.norm_eq_abs]
    obtain ⟨hv,hb,hk⟩ := partial_record_physical D P t _ hi.1 ((hz i).2 2 hi.1)
    have hn := partial_implementation D y y.2 (z.1 i).1.2
    have hv' : |value (z.1 i)|≤|2-P.w|+|2+P.w| := by
      apply abs_le.mpr
      constructor
      · linarith [hv.1,neg_abs_le (2-P.w),abs_nonneg (2+P.w)]
      · linarith [hv.2,le_abs_self (2+P.w),abs_nonneg (2-P.w)]
    have ho := singleton_price_bound hv' ⟨D.hR.le.trans hb.1,hb.2⟩
      (singleton_count_bounds Γ i _ hk (fullSample D (N:=N) i z))
    have hnew := singleton_price_bound hv' ⟨D.hR.le.trans hn.1,hn.2⟩
      (singleton_count_bounds Γ i (raisedAction D 2 y (D.hR.le.trans y.2.1) (z.1 i)) rfl
        (fullSample D (N:=N) i z))
    apply (abs_sub _ _).trans
    dsimp only [profileCount,raisedAction,noisyAction] at ho hnew ⊢
    linarith
  · rw [if_neg hi,norm_zero]
    have hV : 0≤ D.V := mul_nonneg (D.hR.le.trans D.hRUp) (by linarith [D.heps])
    positivity

theorem original_partial_cluster_bound (hlow : P.d0<1-D.ξ) (hc : 0< D.c)
    (heps : D.eps≤1) (hvalue : D.V≤2-P.w)
    (β r : ℝ) (hr : 0< r) (hnoise : D.eps*D.Up≤ r)
    (y : Icc D.R D.Up) (hy : (y:ℝ)=β+2*r)
    (hidentity : ∀ (i : Fin (N+1)) x,
      (∫ u,(problem Γ i).payoff (x.1:ℝ) (physicalBandAction D P t 2 x u)
        ∂(volume : Measure unitInterval))=SourceOrderedNoisyFixedPoint.payoff D P t ht N 2 (π,x))
    (hC1 : AllActionOptimal (π 2) (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N 2 (π,x))) :
    (2-P.w-D.V)*(((N+1:ℕ):ℝ)-D.c)*
      (partialMass*((π 2).1 : Measure _).real
        (typedCluster D P t 2 (Ioo (β-r) (β+r)))/2)^(N+1)≤
      6*r*(N+1:ℕ)*partialMass*((π 2).1 : Measure _).real
        (typedCluster D P t 2 (Ioo (β-r) (β+r))) := by
  let J := Ioo (β-r) (β+r)
  let v := valueAt (N:=N)
  let b := oldBid D (N:=N)
  let b' := newBid D (N:=N) y
  let q := oldCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
  let q' := newCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare y
  have heq (i : Fin (N+1)) :
      (fun z => if z.1 i∈eligible β r then (v z i-b' z i)*q' z i-(v z i-b z i)*q z i else 0)=ᵐ[ρ]
      profileGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i 2 y J := by
    filter_upwards [original_iid_common_support D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare] with z hz
    exact (profile_partial_gain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i y J z hz).symm
  have hgain (i) : Integrable
      (fun z => if z.1 i∈eligible β r then (v z i-b' z i)*q' z i-(v z i-b z i)*q z i else 0) ρ :=
    (integrable_profile_partial_gain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
      i y J measurableSet_Ioo).congr (heq i).symm
  have hIC (i) : (∫ z,if z.1 i∈eligible β r then
      (v z i-b' z i)*q' z i-(v z i-b z i)*q z i else 0 ∂ρ)≤0 := by
    rw [integral_congr_ae (heq i)]
    exact profile_noisy_carrier_IC D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
      i 2 y J measurableSet_Ioo (hidentity i) hC1
  have hh := finite_noisy_cluster_bound_ae μ σ (N+1) D.c (eligible β r) (favorable β r)
    (measurableSet_eligible β r) (measurableSet_favorable β r) (fun _ h => h.1)
    v b b' q q' (2-P.w-D.V) (6*r) (by linarith) (by positivity)
    (original_pointwise_carrier D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
      hlow hc heps β r hr hnoise y hy) hgain hIC
  have hE := original_band_cluster_recipient_mass D P t ht πL π upperBid hupperBid 2 J measurableSet_Ioo 0
  have hB := original_band_cluster_mass D P t ht πL π upperBid hupperBid 2 J measurableSet_Ioo
  have hw : (species P t ht).mass (bandSpecies 2)=partialMass := rfl
  rw [hw] at hE hB
  change (μ).real (favorable β r)=_ at hE
  change (μ).real (eligible β r)=_ at hB
  rw [hE,hB] at hh
  convert! hh using 1
  ring

end FCAppendix.Affine.Tail04.OrderedAtomPartialFinite
