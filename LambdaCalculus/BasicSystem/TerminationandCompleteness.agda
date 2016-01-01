module BasicSystem.TerminationandCompleteness where
open import BasicSystem.Utils
open import BasicSystem.Syntax
open import BasicSystem.OPE
open import BasicSystem.OPEBigStep
open import BasicSystem.OPELemmas
open import BasicSystem.Embeddings
open import BasicSystem.Conversion
open import BasicSystem.BigStepSemantics
open import BasicSystem.StrongComputability
open import BasicSystem.IdentityEnvironment

mutual
  fundthrm : ∀ {Γ Δ σ}(t : Tm Δ σ)(vs : Env Γ Δ) → SCE vs →
             Σ (Val Γ σ) 
               λ v → eval t & vs ⇓ v × SCV v × (t [ embˢ vs ] ≈ emb v)
  fundthrm ø        (vs << v) (s<< svs sv) = v , rvar , sv ,  ø<
  fundthrm (t [ ts ]) vs svs = 
     proj₁ sw , 
       rsubs (proj₁ (proj₂ sws)) (proj₁ (proj₂ sw)) ,
         (proj₁ ∘ proj₂) (proj₂ sw) ,
            ≈trans (≈trans [][] (cong[] ≈refl ((proj₂ ∘ proj₂) (proj₂ sws)))) ((proj₂ ∘ proj₂) (proj₂ sw))
     where
     sws = fundthrmˢ ts vs svs
     sw  = fundthrm t (proj₁ sws) ((proj₁ ∘ proj₂) (proj₂ sws))
  fundthrm (ƛ t)      vs svs = 
    λv t vs ,
        rlam , 
            (λ {_} f a sa → 
              let st = fundthrm t (emap f vs << a) (s<< (scemap f vs svs) sa) 
              in  proj₁ st , 
                      r∙lam (proj₁ (proj₂ st)) ,
                          (proj₁ ∘ proj₂) (proj₂ st) ,
                          ≈trans 
                            (≈trans 
                              (cong∙ λ[] ≈refl)
                              (≈trans 
                                β 
                                (≈trans 
                                  [][] 
                                  (cong[] 
                                    ≈refl 
                                    (≃trans 
                                      comp< 
                                        (cong< 
                                          (≃trans 
                                            assoc 
                                            (≃trans 
                                              (cong○ ≃refl ↑comp) 
                                              rightidˢ)) 
                                          ø<)))))) 
                                  ((proj₂ ∘ proj₂) (proj₂ st))) ,
            ≈refl
  fundthrm (t ∙ u)    vs svs = 
    proj₁ stu , 
        rapp (proj₁ (proj₂ st)) 
                  (proj₁ (proj₂ su)) 
                  (helper' (sym (oidvmap (proj₁ st))) (proj₁ (proj₂ stu))) ,
            (proj₁ ∘ proj₂) (proj₂ stu) ,
            ≈trans (≈trans ∙[] ((cong∙ ((proj₂ ∘ proj₂) (proj₂ st)) ((proj₂ ∘ proj₂) (proj₂ su))))) (helper'' (sym (oidvmap (proj₁ st))) {(proj₁ (fundthrm u vs svs))}{proj₁ ((proj₁ ∘ proj₂) (proj₂ (fundthrm t vs svs)) oid (proj₁ (fundthrm u vs svs)) ((proj₁ ∘ proj₂) (proj₂ (fundthrm u vs svs))))} ((proj₂ ∘ proj₂) (proj₂ stu)))
    where
    st  = fundthrm t vs svs
    su  = fundthrm u vs svs
    stu = (proj₁ ∘ proj₂) (proj₂ st) oid (proj₁ su) ((proj₁ ∘ proj₂) (proj₂ su))

  fundthrmˢ : ∀ {B Γ Δ}(ts : Sub Γ Δ)(vs : Env B Γ) → SCE vs →
              Σ (Env B Δ) 
                λ ws → 
                  evalˢ ts & vs ⇓ ws × SCE ws × (ts ○ (embˢ vs) ≃ embˢ ws)
  fundthrmˢ (↑ σ)   (vs << v) (s<< svs sv) = vs , rˢ↑ , svs , ↑comp
  fundthrmˢ (ts < t)  vs        svs          = 
    proj₁ sts << proj₁ st ,
        rˢcons (proj₁ (proj₂ sts)) (proj₁ (proj₂ st)) ,
            s<< ((proj₁ ∘ proj₂) (proj₂ sts)) ((proj₁ ∘ proj₂) (proj₂ st)) ,
            ≃trans comp< (cong< ((proj₂ ∘ proj₂) (proj₂ sts)) ((proj₂ ∘ proj₂) (proj₂ st)))
    where
    sts = fundthrmˢ ts vs svs
    st  = fundthrm  t  vs svs
  fundthrmˢ ı        vs        svs          = vs , rˢid , svs , leftidˢ
  fundthrmˢ (ts ○ us) vs        svs          = 
    proj₁ sts ,
        rˢcomp (proj₁ (proj₂ sus)) (proj₁ (proj₂ sts)) ,
            (proj₁ ∘ proj₂) (proj₂ sts) ,
            ≃trans (≃trans assoc (cong○ ≃refl ((proj₂ ∘ proj₂) (proj₂ sus)))) ((proj₂ ∘ proj₂) (proj₂ sts))
    where
    sus = fundthrmˢ us vs svs
    sts = fundthrmˢ ts (proj₁ sus) ((proj₁ ∘ proj₂) (proj₂ sus))

mutual
  quotlema : ∀ {Γ} σ {v : Val Γ σ} → 
              SCV v → Σ (Nf Γ σ) (λ m →  quot v ⇓ m × (emb v ≈ nemb m ))
  quotlema ⋆ {nev n} (m , p , q) = ne m , qbase p , q
  quotlema {Γ} (σ ⇒ τ) {v} sv =
    λn (proj₁ qvvZ) ,
        (qarr (proj₁ (proj₂ svvZ)) (proj₁ (proj₂ qvvZ))) ,
            (≈trans 
              η 
              (congλ 
                (≈trans 
                  (cong∙ 
                    (≈trans
                      (≈trans (cong[] (≈trans (≈sym []id) (cong[] ≈refl lemoid)) 
                                     ≃refl ) 
                             [][]) 
                      (≈sym (ovemb (skip σ oid) v))) 
                    ≈refl) 
                  (≈trans ((proj₂ ∘ proj₂) (proj₂ svvZ)) (proj₂ (proj₂ qvvZ))))))
    where
    svZ = quotlemb σ {varV (vZ {Γ})} qⁿvar ≈refl
    svvZ = sv (skip σ oid) (nev (varV vZ)) svZ
    qvvZ = quotlema τ ((proj₁ ∘ proj₂) (proj₂ svvZ))

  quotlemb : ∀ {Γ} σ {n : NeV Γ σ}{m : NeN Γ σ} → 
              quotⁿ n ⇓ m → embⁿ n ≈ nembⁿ m → SCV (nev n)
  quotlemb ⋆       {n} p q = _ , p , q 
  quotlemb (σ ⇒ τ) {n}{m} p q = λ f a sa → 
    let qla = quotlema σ sa
    in  nev (appV (nevmap f n) a) ,
            r∙ne ,
                quotlemb τ 
                           (qⁿapp (quotⁿ⇓map f p) (proj₁ (proj₂ qla))) 
                           (cong∙ (≈trans (onevemb f n) 
                                         (≈trans (cong[] q ≃refl) 
                                                (≈sym (onenemb f m)))) 
                                  (proj₂ (proj₂ qla))) ,
                cong∙ (≈trans (onevemb f n) (≈sym (onevemb f n))) ≈refl


scvar : ∀ {Γ σ}(x : Var Γ σ) → SCV (nev (varV x))
scvar x = quotlemb _ qⁿvar ≈refl 

scid : ∀ Γ → SCE (vid {Γ})
scid ε       = sε 
scid (Γ < σ) = s<< (scemap (weak σ) _ (scid Γ)) (scvar vZ) 

normthrm : ∀ {Γ σ}(t : Tm Γ σ) → Σ (Nf Γ σ) λ n → nf t ⇓ n × (t ≈ nemb n)
normthrm t = proj₁ qt , norm⇓ (proj₁ (proj₂ ft)) (proj₁ (proj₂ qt)) ,
                         ≈trans (≈trans (≈trans (≈sym []id) (cong[] ≈refl embvid))
                                       ((proj₂ ∘ proj₂) (proj₂ ft))) 
                                (proj₂ (proj₂ qt))
  where
  ft = fundthrm t vid (scid _)
  qt = quotlema _ ((proj₁ ∘ proj₂) (proj₂ ft))
