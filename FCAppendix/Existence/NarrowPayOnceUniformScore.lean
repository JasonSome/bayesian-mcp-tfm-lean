import FCAppendix.Existence.NarrowPayOnceReferenceCompact
import FCAppendix.Existence.NarrowPayOnceScoreNeighborhood

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators

theorem scoreTypeJetBound_mono (n : ℕ) {lo lo' hi hi' : ℝ} (hlo : 0<lo)
    (hlower : lo≤lo') (hhi : 0≤hi') (hupper : hi'≤hi) :
    scoreTypeJetBound n lo' hi' ≤ scoreTypeJetBound n lo hi := by
  have hA := firstJetBound_mono n hlo hlower
  have hB := secondJetBound_mono n hlo hlower hhi hupper
  have hlo' : 0<lo' := hlo.trans_le hlower
  have hA0 : 0≤firstJetBound n lo' := by unfold firstJetBound; positivity
  unfold scoreTypeJetBound
  gcongr

theorem exists_uniform_interior_radius_above_lower {n : ℕ} (hn : 2≤n)
    {kappa lo hi : ℝ} (hkappa : 0<kappa) (hlo : 0<lo) (hhi : hi<1) :
    ∃eps : ℝ, 0<eps ∧ eps≤kappa/4 ∧ eps≤1 ∧
      ∀(ι : Type*) [Fintype ι] [Nonempty ι] (c : ℕ) (rho B : ℝ),
      rho∈Icc lo hi → c≤Fintype.card ι → (Fintype.card ι:ℝ)*rho=c → kappa≤B →
      ∀b : ι→ℝ, (∀i,|b i-B|≤eps) → ∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1 := by
  let eta := min lo (1-hi)
  let eps := min (kappa/4) (min 1 (eta*kappa/(16*(n:ℝ))))
  have heta : 0<eta := lt_min hlo (sub_pos.mpr hhi)
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have heps : 0<eps := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hepsk : eps≤kappa/4 := min_le_left _ _
  have heps1 : eps≤1 := (min_le_right _ _).trans (min_le_left _ _)
  have hepssmall : eps≤eta*kappa/(16*(n:ℝ)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨eps,heps,hepsk,heps1,?_⟩
  intro ι _ _ c rho B hrho hc hcap hkB b hb i
  have hB : 0<B := hkappa.trans_le hkB
  have hepsB : eps<B := hepsk.trans_lt (by linarith)
  have hri : rho∈Ioo (0:ℝ) 1 := ⟨hlo.trans_le hrho.1,hrho.2.trans_lt hhi⟩
  have hbound := kernelMarginal_uniform_difference hn hc hri heps.le hepsB hcap b hb i
  have hsmall := (le_div_iff₀ (by positivity : (0:ℝ)<16*(n:ℝ))).mp hepssmall
  have hmargin := mul_le_mul_of_nonneg_left hepsk heta.le
  have hcenter := mul_le_mul_of_nonneg_left hkB heta.le
  have hratio : 2*(n:ℝ)*eps/(B-eps)<eta := by
    apply (div_lt_iff₀ (sub_pos.mpr hepsB)).mpr
    nlinarith
  have hh := abs_lt.mp (hbound.trans_lt hratio)
  have hleft : eta≤lo := min_le_left _ _
  have hright : eta≤1-hi := min_le_right _ _
  constructor <;> linarith [hrho.1,hrho.2]

theorem exists_uniform_score_neighborhood {n : ℕ} (hn : 2≤n) {w0 lo hi : ℝ}
    (hw0 : 0<w0) (hlo : 0<lo) (hlohi : lo≤hi) (hhi : hi<1) :
    ∃kappa eps delta : ℝ, 0<kappa ∧ 0<eps ∧ 0<delta ∧ eps≤kappa/4 ∧ eps≤1 ∧ delta≤w0/2 ∧
      ∀R c : ℕ, 1≤c → c≤R → density R c∈Icc lo hi →
      let rho := density R c
      let B := referenceBid n R c w0
      kappa≤B ∧ B≤w0 ∧ kappa≤referenceCurvature n R rho w0 B ∧
      kappa≤referenceCurvature n R rho w0 B-
        |referenceCurvature n R rho w0 B-referenceCommonSensitivity n R rho w0 B| ∧
      (∀b : Fin (R+1)→ℝ, (∀i,|b i-B|≤eps) → ∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1) ∧
      (∀w : ℝ, |w-w0|≤delta → ∀b : Fin (R+1)→ℝ, (∀i,|b i-B|≤eps) →
        ‖fderiv ℝ (profileScore n c w) b-fderiv ℝ (profileScore n c w0) (fun _=>B)‖≤kappa/4) := by
  obtain ⟨kappa,hkappa,hreference⟩ := exists_uniform_finite_reference_gap hn hw0 hlo hlohi hhi
  obtain ⟨epsI,hepsI,hepsIk,hepsI1,hinterior⟩ :=
    exists_uniform_interior_radius_above_lower hn hkappa hlo hhi
  let lower := kappa/2
  let upper := w0+1
  let L := scoreJetRate n lower upper (|w0|+upper)
  let T := scoreTypeJetBound n lower upper
  let eps := min epsI (kappa/(16*(L+1)))
  let delta := min (w0/2) (kappa/(16*(T+1)))
  have hlower : 0<lower := by dsimp [lower]; positivity
  have hupper : 0≤upper := by dsimp [upper]; positivity
  have hL : 0≤L := by
    dsimp [L,scoreJetRate,thirdJetBound,secondJetBound,firstJetBound]
    positivity
  have hT : 0≤T := by dsimp [T,scoreTypeJetBound,secondJetBound,firstJetBound]; positivity
  have heps : 0<eps := lt_min hepsI (by positivity)
  have hdelta : 0<delta := lt_min (by positivity) (by positivity)
  have hepsI' : eps≤epsI := min_le_left _ _
  have hepsk : eps≤kappa/4 := hepsI'.trans hepsIk
  have heps1 : eps≤1 := hepsI'.trans hepsI1
  have hdeltaw : delta≤w0/2 := min_le_left _ _
  have hLeps : L*eps≤kappa/16 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<16*(L+1))).mp (min_le_right epsI (kappa/(16*(L+1))))
    change eps*(16*(L+1))≤kappa at hh
    nlinarith
  have hTdelta : T*delta≤kappa/16 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<16*(T+1))).mp (min_le_right (w0/2) (kappa/(16*(T+1))))
    change delta*(16*(T+1))≤kappa at hh
    nlinarith
  refine ⟨kappa,eps,delta,hkappa,heps,hdelta,hepsk,heps1,hdeltaw,?_⟩
  intro R c hc hcR hrho
  let B := referenceBid n R c w0
  obtain ⟨hkB,hBw,ha,hgap⟩ := hreference R c hc hcR hrho
  have hcap : ((R:ℝ)+1)*density R c=c := by
    have hR : (0:ℝ)<R := by exact_mod_cast (show 0<R by omega)
    unfold density
    field_simp
  have hint : ∀b : Fin (R+1)→ℝ, (∀i,|b i-B|≤eps) → ∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1 := by
    intro b hb
    exact hinterior (Fin (R+1)) c (density R c) B hrho (by simpa using (show c≤R+1 by omega))
      (by simpa using hcap) hkB b (fun i=>(hb i).trans hepsI')
  refine ⟨hkB,hBw,ha,hgap,hint,?_⟩
  intro w hw b hb
  have hloclower : 0<B-eps := by linarith
  have hlocupper : 0≤B+eps := by linarith
  have hlow : lower≤B-eps := by dsimp [lower]; linarith
  have hupp : B+eps≤upper := by dsimp [upper]; linarith
  have hbox : ∀d∈bidBox (ι:=Fin (R+1)) (B-eps) (B+eps),
      ∀i,kernelMarginal n c d i∈Ioo (0:ℝ) 1 := by
    intro d hd
    apply hint d
    intro i
    exact abs_le.mpr ⟨by linarith [(hd i).1],by linarith [(hd i).2]⟩
  have hbbox : b∈bidBox (B-eps) (B+eps) := fun i=>
    ⟨by linarith [(abs_le.mp (hb i)).1],by linarith [(abs_le.mp (hb i)).2]⟩
  have hbasebox : (fun _ : Fin (R+1)=>B)∈bidBox (B-eps) (B+eps) := fun _=>⟨by linarith,by linarith⟩
  have hnorm : ‖b-(fun _=>B)‖≤eps := by
    apply (pi_norm_le_iff_of_nonneg heps.le).mpr
    intro i
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using hb i
  have htypes := norm_fderiv_profileScore_type_sub_le hn (by omega) hloclower b hbbox (hint b hb) w w0
  have hprofiles := norm_fderiv_profileScore_sub_le hn (by omega) hloclower hbox w0
    (fun _=>B) b hbasebox hbbox
  have htypebound : scoreTypeJetBound n (B-eps) (B+eps)≤T :=
    scoreTypeJetBound_mono n hlower hlow hlocupper hupp
  have hprofilebound : scoreJetRate n (B-eps) (B+eps) (|w0|+(B+eps))≤L :=
    scoreJetRate_mono n hlower hlow hlocupper hupp (by positivity) (by dsimp [upper]; linarith)
  have ht0 : 0 ≤ scoreTypeJetBound n (B-eps) (B+eps) := by
    unfold scoreTypeJetBound secondJetBound firstJetBound
    positivity
  have hl0 : 0 ≤ scoreJetRate n (B-eps) (B+eps) (|w0|+(B+eps)) := by
    unfold scoreJetRate thirdJetBound secondJetBound firstJetBound
    positivity
  calc
    _≤‖fderiv ℝ (profileScore n c w) b-fderiv ℝ (profileScore n c w0) b‖+
        ‖fderiv ℝ (profileScore n c w0) b-fderiv ℝ (profileScore n c w0) (fun _=>B)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤T*delta+L*eps := add_le_add
      (htypes.trans (mul_le_mul htypebound hw (abs_nonneg _) hT))
      (hprofiles.trans (mul_le_mul hprofilebound hnorm (norm_nonneg _) hL))
    _≤kappa/4 := by linarith

end FCAppendix.Existence.NarrowPayOnce
