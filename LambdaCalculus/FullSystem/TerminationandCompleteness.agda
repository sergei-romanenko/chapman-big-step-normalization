module FullSystem.TerminationandCompleteness where
open import FullSystem.Utils
open import FullSystem.Syntax
open import FullSystem.OPE
open import FullSystem.OPEBigStep
open import FullSystem.OPELemmas
open import FullSystem.Embeddings
open import FullSystem.Conversion
open import FullSystem.BigStepSemantics
open import FullSystem.StrongComputability
open import FullSystem.IdentityEnvironment

mutual
  quotelema : ∀ {Γ} σ {v : Val Γ σ} → 
              SCV v → Σ (Nf Γ σ) (λ m →  quot v ⇓ m × (emb v ≈ nemb m ))
  quotelema ι {nev n} (m , p , q) = neι m , qbase p , q
  quotelema {Γ} (σ ⇒ τ) {v} sv =
    λn (proj₁ qvvZ) ,
        qarr (t1 (proj₂ svvZ)) (proj₁ (proj₂ qvvZ)) ,
            ≈trans 
              η 
              (congλ 
                (≈trans 
                  (cong$ 
                    (≈trans
                      (≈trans (cong[] (≈trans (≈sym []id) (cong[] ≈refl lemoid)) 
                                     reflˢ ) 
                             [][]) 
                      (≈sym (ovemb (skip σ oid) v))) 
                    ≈refl) 
                  (≈trans (t3 (proj₂ svvZ)) (proj₂ (proj₂ qvvZ)))))
    where
    svZ = quotelemb σ {varV (vZ {Γ})} qⁿvar ≈refl
    svvZ = sv (skip σ oid) (nev (varV vZ)) svZ
    qvvZ = quotelema τ (t2 (proj₂ svvZ))
  quotelema N {nev n}  (m , p , q) = neN m , qNn p , q
  quotelema N {zerov}  sv = zeron , qNz , ≈refl
  quotelema N {sucv v} sv =
    let  qv = quotelema N {v} sv in (sucn (proj₁ qv)) ,
                        (qNs (proj₁ (proj₂ qv)) , congsuc (proj₂ (proj₂ qv)))
  quotelema One     {v} sv = voidn , qone , ηvoid
  quotelema (σ * τ) {v} ((w , p , p' , p'') , (w' , q , q' , q'')) = 
    < proj₁ qw , proj₁ qw' >n ,
        (qprod p (proj₁ (proj₂ qw)) q (proj₁ (proj₂ qw')) ,
            ≈trans η<,> (cong<,> (≈trans p'' (proj₂ (proj₂ qw)))
                                 (≈trans q'' (proj₂ (proj₂ qw')))))
    where
    qw  = quotelema σ p'
    qw' = quotelema τ q'

  quotelemb : ∀ {Γ} σ {n : NeV Γ σ}{m : NeN Γ σ} → 
              quotⁿ n ⇓ m → embⁿ n ≈ nembⁿ m → SCV (nev n)
  quotelemb ι       {n} p q = _ , p , q
  quotelemb (σ ⇒ τ) {n}{m} p q = λ f a sa → 
    let qla = quotelema σ sa
    in  nev (appV (nevmap f n) a) ,
            (r$ne ,
                quotelemb τ 
                          (qⁿapp (quotⁿ⇓map f p) (proj₁ (proj₂ qla))) 
                          (cong$ (≈trans (onevemb f n) 
                                         (≈trans (cong[] q reflˢ) 
                                                 (≈sym (onenemb f m)))) 
                                  (proj₂ (proj₂ qla))) ,
                cong$ (≈trans (onevemb f n) (≈sym (onevemb f n))) ≈refl)
  quotelemb N {v} p q = _ , p , q
  quotelemb One     {n} p q = void 
  quotelemb (σ * τ) {n} p q = 
    (nev (fstV n) , rfstnev , qfst , ≈refl) ,
    (nev (sndV n) , rsndnev , qsnd , ≈refl)
    where
    qfst = quotelemb σ (qⁿfst p) (congfst q)
    qsnd = quotelemb τ (qⁿsnd p) (congsnd q)

SCR : ∀ {Γ σ}(z : Val Γ σ)(s : Val Γ (N ⇒ σ ⇒ σ))(v : Val Γ N) →
      SCV z → SCV s → SCV v →
      Σ (Val Γ σ) 
        λ w → (prim z & s & v ⇓ w) × 
              SCV w × 
               (prim (emb z) (emb s) (emb v) ≈ (emb w ))  
SCR {σ = σ} z s (nev n)  sz ss (m , p , q) =
  nev (primV z s n) ,
    rprn ,
        quotelemb σ (qⁿprim (proj₁ (proj₂ qlaz)) (proj₁ (proj₂ qlas)) p)
                    (congprim (proj₂ (proj₂ qlaz)) (proj₂ (proj₂ qlas)) q) ,
          ≈refl
  where
  qlaz = quotelema σ sz
  qlas = quotelema (N ⇒ σ ⇒ σ) ss

SCR z s zerov    sz ss sv = z , rprz , sz , primz
SCR z s (sucv v) sz ss sv = 
  proj₁ Sfv ,
      (rprs (helper' (sym (oidvmap s)) (t1 (proj₂ Sf))) 
            (t1 (proj₂ Sv)) 
            (helper' (sym (oidvmap (proj₁ (ss oid v sv)))) (t1 (proj₂ Sfv))) , 
          (t2 (proj₂ Sfv)) , 
          (≈trans (≈trans prims 
                        (cong$ (≈trans (≈trans (cong$ (≈trans (≈trans (≈sym []id) 
                                                                  (cong[] ≈refl lemoid))
                                                           (≈sym (ovemb oid s))) 
                                                    ≈refl) 
                                             (≈trans (≈trans (t3 (proj₂ Sf)) (≈sym []id)) 
                                                    (cong[] ≈refl lemoid))) 
                                      (≈sym (ovemb oid (proj₁ (ss oid v sv)))))
                               (t3 (proj₂ Sv)))) 
                 (t3 (proj₂ Sfv)))) 
  where 
  Sv  = SCR z s v sz ss sv
  Sf  = ss oid v sv
  Sfv = t2 (proj₂ Sf) oid (proj₁ Sv) (t2 (proj₂ Sv)) 

mutual
  fundthrm : ∀ {Γ Δ σ}(t : Tm Δ σ)(vs : Env Γ Δ) → SCE vs →
             Σ (Val Γ σ) 
               λ v → eval t & vs ⇓ v × SCV v × (t [ embˢ vs ] ≈ emb v)
  fundthrm top        (vs << v) (s<< svs sv) = v , rvar , sv , top<
  fundthrm (t [ ts ]) vs svs = 
     proj₁ sw ,
         (rsubs (t1 (proj₂ sws)) (t1 (proj₂ sw)) , 
           t2 (proj₂ sw) ,
             ≈trans (≈trans [][] (cong[] ≈refl (t3 (proj₂ sws))))
                    (t3 (proj₂ sw))) 
     where
     sws = fundthrmˢ ts vs svs
     sw  = fundthrm t (proj₁ sws) (t2 (proj₂ sws))
  fundthrm (λt t)      vs svs = 
    λv t vs ,
        rlam ,
            (λ {_} f a sa → 
              let st = fundthrm t (emap f vs << a) (s<< (scemap f vs svs) sa) 
              in  proj₁ st ,
                      r$lam (t1 (proj₂ st)) ,
                        t2 (proj₂ st) ,
                          ≈trans 
                            (≈trans 
                              (cong$ λ[] ≈refl)
                              (≈trans 
                                β 
                                (≈trans 
                                  [][] 
                                  (cong[] 
                                    ≈refl 
                                    (transˢ 
                                      comp< 
                                        (cong< 
                                          (transˢ 
                                            assoc 
                                            (transˢ 
                                              (cong○ reflˢ popcomp) 
                                              rightidˢ)) 
                                          top<)))))) 
                            (t3 (proj₂ st))) ,
            ≈refl  
  fundthrm (t $ u)    vs svs = 
    proj₁ stu ,
        (rapp (t1 (proj₂ st)) 
              (t1 (proj₂ su)) 
              (helper' (sym (oidvmap (proj₁ st))) (t1 (proj₂ stu))) ,
            t2 (proj₂ stu) ,
            ≈trans (≈trans $[] (cong$ (t3 (proj₂ st)) (t3 (proj₂ su)))) 
                   (helper'' (sym (oidvmap (proj₁ st))) {proj₁ (fundthrm u vs svs)}{proj₁ (t2 (proj₂ (fundthrm t vs svs)) oid (proj₁ (fundthrm u vs svs)) (t2 (proj₂ (fundthrm u vs svs))))} (t3 (proj₂ stu))))
    where
    st  = fundthrm t vs svs
    su  = fundthrm u vs svs
    stu = t2 (proj₂ st) oid (proj₁ su) (t2 (proj₂ su))
  fundthrm zero         vs svs = 
    zerov , rzero , void , zero[] 
  fundthrm (suc t)      vs svs = 
    sucv (proj₁ ft) ,
      rsuc (t1 (proj₂ ft)) ,
        t2 (proj₂ ft) ,
          ≈trans suc[] (congsuc (t3 (proj₂ ft)))
    where
    ft = fundthrm t vs svs
  fundthrm (prim z s t) vs svs = 
    proj₁ fv ,
      rprim (t1 (proj₂ fz)) (t1 (proj₂ fs)) (t1 (proj₂ ft)) (t1 (proj₂ fv)) ,
        t2 (proj₂ fv) ,
          ≈trans prim[] 
                 (≈trans (congprim (t3 (proj₂ fz)) (t3 (proj₂ fs))
                                   (t3 (proj₂ ft))) 
                         (t3 (proj₂ fv)))
     where
     fz = fundthrm z vs svs
     fs = fundthrm s vs svs
     ft = fundthrm t vs svs
     fv = SCR (proj₁ fz) (proj₁ fs) (proj₁ ft)
              (t2 (proj₂ fz)) (t2 (proj₂ fs)) (t2 (proj₂ ft))
  fundthrm void      vs svs = voidv , rvoid , void , void[]
  fundthrm < t , u > vs svs =
    < proj₁ ft , proj₁ fu >v ,
      (r<,> (t1 (proj₂ ft)) (t1 (proj₂ fu))) ,
        ((proj₁ ft , rfst<,> , t2 (proj₂ ft) , βfst) ,
                proj₁ fu , rsnd<,> , t2 (proj₂ fu) , βsnd) ,
          ≈trans <,>[] (cong<,> (t3 (proj₂ ft)) (t3 (proj₂ fu)))
    where 
    ft = fundthrm t vs svs
    fu = fundthrm u vs svs
  fundthrm (fst t)   vs svs = 
    proj₁ ftfst ,
      rfst (t1 (proj₂ ft)) (t1 (proj₂ ftfst)) ,
        t2 (proj₂ ftfst) ,
          ≈trans fst[] (≈trans (congfst (t3 (proj₂ ft))) (t3 (proj₂ ftfst)))
    where
    ft    = fundthrm t vs svs
    ftfst = proj₁ (t2 (proj₂ ft))
  fundthrm (snd t)   vs svs = 
    proj₁ ftsnd ,
      rsnd (t1 (proj₂ ft)) (t1 (proj₂ ftsnd)) ,
        t2 (proj₂ ftsnd) ,
          ≈trans snd[] (≈trans (congsnd (t3 (proj₂ ft))) (t3 (proj₂ ftsnd)))
    where
    ft = fundthrm t vs svs
    ftsnd = proj₂ (t2 (proj₂ ft))

  fundthrmˢ : ∀ {B Γ Δ}(ts : Sub Γ Δ)(vs : Env B Γ) → SCE vs →
              Σ (Env B Δ) 
                λ ws → 
                  evalˢ ts & vs ⇓ ws × SCE ws × (ts ○ (embˢ vs) ≃ˢ embˢ ws)
  fundthrmˢ (pop σ)   (vs << v) (s<< svs sv) = vs , rˢpop , svs , popcomp
  fundthrmˢ (ts < t)  vs        svs          = 
    proj₁ sts << proj₁ st ,
      rˢcons (t1 (proj₂ sts)) (t1 (proj₂ st)) ,
        s<< (t2 (proj₂ sts)) (t2 (proj₂ st)) ,
          transˢ comp< (cong< (t3 (proj₂ sts)) (t3 (proj₂ st)))
    where
    sts = fundthrmˢ ts vs svs
    st  = fundthrm  t  vs svs
  fundthrmˢ id        vs        svs          = vs , rˢid , svs , leftidˢ
  fundthrmˢ (ts ○ us) vs        svs          = 
    proj₁ sts ,
      rˢcomp (t1 (proj₂ sus)) (t1 (proj₂ sts)) ,
        t2 (proj₂ sts) ,
          transˢ (transˢ assoc (cong○ reflˢ (t3 (proj₂ sus)))) (t3 (proj₂ sts)) 
    where
    sus = fundthrmˢ us vs svs
    sts = fundthrmˢ ts (proj₁ sus) (t2 (proj₂ sus))

scvar : ∀ {Γ σ}(x : Var Γ σ) → SCV (nev (varV x))
scvar {σ = σ} x = quotelemb σ qⁿvar ≈refl 

scid : ∀ Γ → SCE (vid {Γ})
scid ε       = sε 
scid (Γ < σ) = s<< (scemap (weak σ) _ (scid Γ)) (scvar (vZ {σ = σ})) 

normthrm : ∀ {Γ σ}(t : Tm Γ σ) → Σ (Nf Γ σ) λ n → nf t ⇓ n × (t ≈ nemb n)
normthrm t = proj₁ qt , (norm⇓ (t1 (proj₂ ft)) (proj₁ (proj₂ qt)) ,
                         (≈trans (≈trans (≈trans (≈sym []id) (cong[] ≈refl embvid))
                                       (t3 (proj₂ ft))) 
                                (proj₂ (proj₂ qt))))  
  where
  ft = fundthrm t vid (scid _)
  qt = quotelema _ (t2 (proj₂ ft))
