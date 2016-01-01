module FiniteProducts.TerminationandCompleteness where
open import FiniteProducts.Utils
open import FiniteProducts.Syntax
open import FiniteProducts.OPE
open import FiniteProducts.OPEBigStep
open import FiniteProducts.OPELemmas
open import FiniteProducts.Embeddings
open import FiniteProducts.Conversion
open import FiniteProducts.BigStepSemantics
open import FiniteProducts.StrongComputability
open import FiniteProducts.IdentityEnvironment

mutual
  fundthrm : ∀ {Γ Δ σ}(t : Tm Δ σ)(vs : Env Γ Δ) → SCE vs →
             Σ (Val Γ σ) 
               λ v → eval t & vs ⇓ v × SCV v × (t [ embˢ vs ] ≈ emb v)
  fundthrm top        (vs << v) (s<< svs sv) = v , rvar , sv , top<
  fundthrm (t [ ts ]) vs svs = 
     proj₁ sw , 
         rsubs (t1 (proj₂ sws)) (t1 (proj₂ sw)) ,
             t2 (proj₂ sw) ,
             ≈trans (≈trans [][] (cong[] ≈refl (t3 (proj₂ sws)))) (t3 (proj₂ sw))
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
                                βλ 
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
    rapp (t1 (proj₂ st)) (t1 (proj₂ su)) 
      (helper' (sym (oidvmap (proj₁ st))) (t1 (proj₂ stu))) ,
    t2 (proj₂ stu) ,
    ≈trans (≈trans $[] (cong$ (t3 (proj₂ st)) (t3 (proj₂ su)))) 
           (vhelper'' (sym (oidvmap (proj₁ st)))
                      {proj₁ (fundthrm u vs svs)}
                      {proj₁ (t2 (proj₂ (fundthrm t vs svs)) oid
                                 (proj₁ (fundthrm u vs svs)) (t2 (proj₂ (fundthrm u vs svs))))}
                      (t3 (proj₂ stu)))
    where
    st  = fundthrm t vs svs
    su  = fundthrm u vs svs
    stu = t2 (proj₂ st) oid (proj₁ su) (t2 (proj₂ su))
  fundthrm void      vs svs = voidv , rvoid , void , void[]
  fundthrm < t , u > vs svs = 
    < proj₁ ft , proj₁ fu >v ,
        r<,> (t1 (proj₂ ft)) (t1 (proj₂ fu)) ,
           ((proj₁ ft , rfst<,> , t2 (proj₂ ft) , βfst) ,
            (proj₁ fu , rsnd<,> , t2 (proj₂ fu) , βsnd)) ,
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

mutual
  quotlema : ∀ {Γ} σ {v : Val Γ σ} → 
              SCV v → Σ (Nf Γ σ) (λ m →  quot v ⇓ m × (emb v ≈ nemb m ))
  quotlema ι {nev n} (m , p , q) = ne m , qbase p , q
  quotlema {Γ} (σ ⇒ τ) {v} sv =
    λn (proj₁ qvvZ) ,
        qarr (t1 (proj₂ svvZ)) (proj₁ (proj₂ qvvZ)) ,
            ≈trans 
              ηλ 
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
    svZ = quotlemb σ {varV (vZ {Γ})} qⁿvar ≈refl
    svvZ = sv (skip σ oid) (nev (varV vZ)) svZ
    qvvZ = quotlema τ (t2 (proj₂ svvZ))
  quotlema One     {v} sv = voidn , qone , ηvoid
  quotlema (σ * τ) {v} ((w , p , p' , p'') , (w' , q , q' , q'')) = 
    < proj₁ qw , proj₁ qw' >n ,
        qprod p (proj₁ (proj₂ qw)) q (proj₁ (proj₂ qw')) ,
        ≈trans η<,> (cong<,> (≈trans p'' (proj₂ (proj₂ qw)))
                                  (≈trans q'' (proj₂ (proj₂ qw'))))
    where
    qw  = quotlema σ p'
    qw' = quotlema τ q'

  quotlemb : ∀ {Γ} σ {n : NeV Γ σ}{m : NeN Γ σ} → 
              quotⁿ n ⇓ m → embⁿ n ≈ nembⁿ m → SCV (nev n)
  quotlemb ι       {n} p q = _ , p , q 
  quotlemb (σ ⇒ τ) {n}{m} p q = λ f a sa → 
    let qla = quotlema σ sa
    in  nev (appV (nevmap f n) a) ,
            r$ne ,
                quotlemb τ 
                           (qⁿapp (quotⁿ⇓map f p) (proj₁ (proj₂ qla))) 
                           (cong$ (≈trans (onevemb f n) 
                                         (≈trans (cong[] q reflˢ) 
                                                (≈sym (onenemb f m)))) 
                                  (proj₂ (proj₂ qla))) ,
                cong$ (≈trans (onevemb f n) (≈sym (onevemb f n))) ≈refl
  quotlemb One     {n} p q = void 
  quotlemb (σ * τ) {n} p q = 
    (nev (fstV n) , rfstnev , qfst , ≈refl) ,
    (nev (sndV n) , rsndnev , qsnd ,  ≈refl) 
    where
    qfst = quotlemb σ (qⁿfst p) (congfst q)
    qsnd = quotlemb τ (qⁿsnd p) (congsnd q)

scvar : ∀ {Γ σ}(x : Var Γ σ) → SCV (nev (varV x))
scvar {Γ} {σ} x = quotlemb σ qⁿvar ≈refl

scid : ∀ Γ → SCE (vid {Γ})
scid ε       = sε 
scid (Γ < σ) = s<< (scemap (weak σ) _ (scid Γ)) (scvar {Γ < σ} {σ} vZ)

normthrm : ∀ {Γ σ}(t : Tm Γ σ) → Σ (Nf Γ σ) λ n → nf t ⇓ n × (t ≈ nemb n)
normthrm t = proj₁ qt , norm⇓ (t1 (proj₂ ft)) (proj₁ (proj₂ qt)) ,
                         ≈trans (≈trans (≈trans (≈sym []id)
                                                 (cong[] ≈refl embvid))
                                         (t3 (proj₂ ft)))
                                 (proj₂ (proj₂ qt))
  where
  ft = fundthrm t vid (scid _)
  qt = quotlema _ (t2 (proj₂ ft))
